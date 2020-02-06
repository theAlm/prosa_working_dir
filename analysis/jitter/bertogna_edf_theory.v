Require Import rt.util.all.
Require Import rt.model.jitter.job rt.model.jitter.task rt.model.jitter.task_arrival
               rt.model.jitter.schedule rt.model.jitter.platform rt.model.jitter.interference
               rt.model.jitter.workload rt.model.jitter.schedulability
               rt.model.jitter.priority rt.model.jitter.platform rt.model.jitter.response_time.
Require Import rt.analysis.jitter.workload_bound
               rt.analysis.jitter.interference_bound_edf.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisEDFJitter.

  Export JobWithJitter SporadicTaskset ScheduleOfSporadicTaskWithJitter Workload
         Schedulability ResponseTime Priority SporadicTaskArrival WorkloadBoundJitter
         InterferenceBoundEDFJitter Platform Interference.

  (* In this section, we prove that Bertogna and Cirinei's RTA yields
     safe response-time bounds. *)
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    Variable task_jitter: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> time.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters.
       Note: the jitter of a valid job is bounded by the jitter of its task. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                                 job_deadline job_task job_jitter j.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ...jobs execute after jitter and no longer than their execution costs. *)
    Hypothesis H_jobs_execute_after_jitter:
      jobs_execute_after_jitter job_jitter sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Also assume that jobs are sequential and that there exists
       at least one processor. *)
    Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Assume that we have a task set ts, such that all jobs come
       from the task set, and all tasks have valid parameters and
       constrained deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_all_jobs_from_taskset:
      forall (j: JobIn arr_seq), job_task j \in ts.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_constrained_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk sched.

    (* Assume a known response-time bound R is known...  *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable rt_bounds: seq task_with_response_time.

    (* ...for any task in the task set. *)
    Hypothesis H_rt_bounds_contains_all_tasks: unzip1 rt_bounds = ts.

    (* Also, assume that R is a fixed-point of the response-time recurrence, ... *)
    Let I (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds delta.
    Hypothesis H_response_time_is_fixed_point :
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        R = task_cost tsk + div_floor (I tsk R) num_cpus.
    
    (* ..., and R is no larger than the deadline. *)
    Hypothesis H_tasks_miss_no_deadlines:
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        task_jitter tsk + R <= task_deadline tsk.

    (* Assume that we have a work-conserving EDF scheduler. *)
    Hypothesis H_work_conserving: work_conserving job_cost job_jitter sched.
    Hypothesis H_edf_policy: enforces_JLDP_policy job_cost job_jitter sched (EDF job_deadline).

    (* Assume that the task set has no duplicates. This is required to
       avoid problems when counting tasks (for example, when stating
       that the number of interfering tasks is at most num_cpus). *)
    Hypothesis H_ts_is_a_set : uniq ts.

    (* In order to prove that R is a response-time bound, we first present some lemmas. *)
    Section Lemmas.

      (* Let (tsk, R) be any task to be analyzed, with its response-time bound R. *)
      Variable tsk: sporadic_task.
      Variable R: time.
      Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

      (* Consider any job j of tsk. *)
      Variable j: JobIn arr_seq.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* Let t1 be the first point in time where j can actually be scheduled. *)
      Let t1 := job_arrival j + job_jitter j.

      (* Assume that job j did not complete on time, ... *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (t1 + R).

      (* and that it is the first job not to satisfy its response-time bound. *)
      Hypothesis H_all_previous_jobs_completed_on_time :
        forall (j_other: JobIn arr_seq) tsk_other R_other,
          job_task j_other = tsk_other ->
          (tsk_other, R_other) \in rt_bounds ->
          job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R ->
          completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other).

      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_cost job_task job_jitter sched j tsk_other t1 (t1 + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_cost job_jitter sched j t1 (t1 + R).

      (* Recall Bertogna and Cirinei's workload bound ... *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W_jitter task_cost task_period task_jitter tsk_other R_other R.

      (*... and the EDF-specific bound, ... *)
      Let edf_specific_bound (tsk_other: sporadic_task) (R_other: time) :=
        edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk tsk_other R_other.

      (* ... which combined form the interference bound. *)
      Let interference_bound (tsk_other: sporadic_task) (R_other: time) :=
        interference_bound_edf task_cost task_period task_deadline task_jitter tsk R (tsk_other, R_other). 
      
      (* Also, let ts_interf be the subset of tasks that interfere with tsk. *)
      Let ts_interf := [seq tsk_other <- ts | jldp_can_interfere_with tsk tsk_other].

      Section LemmasAboutInterferingTasks.
        
        (* Let (tsk_other, R_other) be any pair of higher-priority task and
           response-time bound computed in previous iterations. *)
        Variable tsk_other: sporadic_task.
        Variable R_other: time.
        Hypothesis H_response_time_of_tsk_other: (tsk_other, R_other) \in rt_bounds.

        (* Note that tsk_other is in task set ts ...*)
        Lemma bertogna_edf_tsk_other_in_ts: tsk_other \in ts.
        Proof.
          by rewrite -H_rt_bounds_contains_all_tasks; apply/mapP; exists (tsk_other, R_other).
        Qed.

        (* Also, R_other is larger than the cost of tsk_other. *)
        Lemma bertogna_edf_R_other_ge_cost :
          R_other >= task_cost tsk_other.
        Proof.
          by rewrite [R_other](H_response_time_is_fixed_point tsk_other);
            first by apply leq_addr.
        Qed.

        (* Since tsk_other cannot interfere more than it executes, we show that
           the interference caused by tsk_other is no larger than workload bound W. *)
        Lemma bertogna_edf_workload_bounds_interference :
          x tsk_other <= workload_bound tsk_other R_other.
        Proof.
          unfold valid_sporadic_job in *.
          rename H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_valid_job_parameters into PARAMS,
                 H_valid_task_parameters into TASK_PARAMS,
                 H_constrained_deadlines into RESTR,
                 H_tasks_miss_no_deadlines into NOMISS.
          unfold x, task_interference, valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          have INts := bertogna_edf_tsk_other_in_ts.
          apply leq_trans with (n := workload job_task sched tsk_other t1 (t1 + R));
            first by apply task_interference_le_workload.
          apply workload_bounded_by_W with (task_deadline0 := task_deadline)
            (job_jitter0 := job_jitter) (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by ins); last 2 first;
            [ by apply NOMISS |
            | by ins; apply TASK_PARAMS
            | by apply RESTR
            | by apply bertogna_edf_R_other_ge_cost].
          {
            intros j0 JOB0 LT0; apply BEFOREok; try (by done).
            unfold t1 in *.
            apply leq_trans with (n := job_arrival j + job_jitter j + R); first by done.
            rewrite leq_add2r leq_add2l.
            specialize (PARAMS j); des.
            rewrite -H_job_of_tsk; apply PARAMS0.
          }
        Qed.

        (* Recall that the edf-specific interference bound also holds. *)
        Lemma bertogna_edf_specific_bound_holds :
          x tsk_other <= edf_specific_bound tsk_other R_other.
        Proof.
          by apply interference_bound_edf_bounds_interference with (job_deadline0 := job_deadline)
                                                                  (ts0 := ts); try (by done);
          [  by apply bertogna_edf_tsk_other_in_ts
          |  by apply H_tasks_miss_no_deadlines
          |  by apply leq_trans with (n := task_jitter tsk + R);
               [apply leq_addl | by apply H_tasks_miss_no_deadlines]
          |  by ins; apply H_all_previous_jobs_completed_on_time with (tsk_other := tsk_other)].
        Qed.
        
      End LemmasAboutInterferingTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.

        (* 0) Since job j did not complete by its response time bound, it follows that
              the total interference X >= R - e_k + 1. *)
        Lemma bertogna_edf_too_much_interference : X >= R - task_cost tsk + 1.
        Proof.
          rename H_completed_jobs_dont_execute into COMP,
                 H_valid_job_parameters into PARAMS, H_response_time_is_fixed_point into REC,
                 H_job_of_tsk into JOBtsk, H_j_not_completed into NOTCOMP.
          unfold completed, valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          unfold X, total_interference; rewrite addn1.
          rewrite -(ltn_add2r (task_cost tsk)).
          rewrite subh1; last by rewrite [R](REC tsk) // leq_addr.
          rewrite -addnBA // subnn addn0.
          move: (NOTCOMP) => /negP NOTCOMP'.
          rewrite neq_ltn in NOTCOMP.
          move: NOTCOMP => /orP [LT | BUG]; last first.
          {
            exfalso; rewrite ltnNge in BUG; move: BUG => /negP BUG; apply BUG.
            by apply cumulative_service_le_job_cost.
          }
          apply leq_ltn_trans with (n := (\sum_(t1 <= t < t1 + R)
                                       backlogged job_cost job_jitter sched j t) +
                                     service sched j (t1 + R)); last first.
          {
            rewrite -addn1 -addnA leq_add2l addn1.
            apply leq_trans with (n := job_cost j); first by done.
            by specialize (PARAMS j); des; rewrite -JOBtsk.
          }
          unfold service.
          rewrite -> big_cat_nat with (n := t1) (m := 0); rewrite ?leq_addr // /=.
          rewrite (cumulative_service_before_jitter_zero job_jitter) // add0n.
          rewrite -big_split /=.
          apply leq_trans with (n := \sum_(t1 <= i < t1 + R) 1);
            first by simpl_sum_const; rewrite addKn.
          apply leq_sum_nat; move => i /andP [GEi LTi] _.
          destruct (backlogged job_cost job_jitter sched j i) eqn:BACK;
            first by rewrite -addn1 addnC; apply leq_add.
          apply negbT in BACK.
          rewrite add0n lt0n -not_scheduled_no_service negbK.
          rewrite /backlogged negb_and negbK in BACK.
          move: BACK => /orP [/negP NOTPENDING | SCHED]; last by done.
          exfalso; apply NOTPENDING; unfold pending; apply/andP; split; first by done.
          apply/negP; red; intro BUG; apply NOTCOMP'.
          by apply completion_monotonic with (t := i); try (by done); apply ltnW.
        Qed.

        Let scheduled_task_other_than_tsk (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          jldp_can_interfere_with tsk tsk_other.
      
        (* 1) At all times that j is backlogged, all processors are busy with other tasks. *)
        Lemma bertogna_edf_scheduling_invariant:
          forall t,
            t1 <= t < t1 + R ->
            backlogged job_cost job_jitter sched j t ->
            count (scheduled_task_other_than_tsk t) ts = num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_valid_job_parameters into JOBPARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_sporadic_tasks into SPO,
                 H_tsk_R_in_rt_bounds into INbounds,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_rt_bounds_contains_all_tasks into UNZIP,
                 H_constrained_deadlines into RESTR,
                 H_work_conserving into WORK.
          unfold x, X, total_interference, task_interference,
                 valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          move => t /andP [LEt LTt] BACK.
          unfold scheduled_task_other_than_tsk in *.
          eapply platform_cpus_busy_with_interfering_tasks; try (by done);
            [ by apply WORK | by done | by apply SPO 
            | apply PARAMS; rewrite -JOBtsk; apply FROMTS
            | by apply JOBtsk | by apply BACK | ].
          {
            intros j0 tsk0 TSK0 LE.
            cut (tsk0 \in unzip1 rt_bounds = true); last by rewrite UNZIP -TSK0 FROMTS.
            move => /mapP [p IN EQ]; destruct p as [tsk' R0]; simpl in *; subst tsk'.
            apply completion_monotonic with (t0 := job_arrival j0 + task_jitter tsk0 + R0); try (by done).
            {
              rewrite -addnA leq_add2l TSK0.
              apply leq_trans with (n := task_deadline tsk0); first by apply NOMISS.
              by apply RESTR; rewrite -TSK0 FROMTS.
            }
            {
              apply BEFOREok with (tsk_other := tsk0); try (by done).
              apply leq_trans with (n := t1 + R); last first.
              {
                  rewrite leq_add2r leq_add2l -JOBtsk.
                  by specialize (JOBPARAMS j); des.
              }
              apply leq_ltn_trans with (n := t); last by done.
              apply leq_trans with (n := job_arrival j0 + task_period tsk0);
                last by done.
              rewrite -addnA leq_add2l.
              apply leq_trans with (n := task_deadline tsk0); first by apply NOMISS.
              by apply RESTR; rewrite -TSK0; apply FROMTS.
            }
          }
        Qed.
      
        (* 2) Prove that during the scheduling window of j, any job that is scheduled while j is
           backlogged comes from a different task. *)
        Lemma bertogna_edf_interference_by_different_tasks :
          forall t j_other,
            t1 <= t < t1 + R ->
            backlogged job_cost job_jitter sched j t ->
            scheduled sched j_other t ->
            job_task j_other != tsk.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_valid_job_parameters into JOBPARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK,
                 H_tsk_R_in_rt_bounds into INbounds,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_constrained_deadlines into CONSTR.
          unfold valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          move => t j_other /andP [LEt GEt] BACK SCHED.
          apply/eqP; red; intro SAMEtsk.
          move: SCHED => /existsP [cpu SCHED].
          assert (SCHED': scheduled sched j_other t).
            by apply/existsP; exists cpu.
          clear SCHED; rename SCHED' into SCHED.
          move: (SCHED) => PENDING.
          apply scheduled_implies_pending with (job_cost0 := job_cost) (job_jitter0 := job_jitter)
            in PENDING; try (by done).
          destruct (ltnP (job_arrival j_other) (job_arrival j)) as [BEFOREother | BEFOREj].
          {
            move: (BEFOREother) => LT; rewrite -(ltn_add2r R) in LT.
            exploit (BEFOREok j_other tsk R SAMEtsk INbounds).
            {
              rewrite -addnA [_ + R]addnC addnA -[(_ + _) + R]addnA [_ tsk + R]addnC addnA.
              by rewrite ltn_add2r.
            }
            intros COMP.
            move: PENDING => /andP [_ /negP NOTCOMP]; apply NOTCOMP.
            apply completion_monotonic with (t0 := job_arrival j_other + task_jitter tsk + R);
              try by done.
            apply leq_trans with (n := job_arrival j);
              last by apply leq_trans with (n := t1); [by apply leq_addr | by done].
            apply leq_trans with (n := job_arrival j_other + task_period tsk).
            {
              rewrite -addnA leq_add2l.
              by apply leq_trans with (n := task_deadline tsk);
                [by apply NOMISS | by apply CONSTR; rewrite -JOBtsk FROMTS].
            }
            rewrite -SAMEtsk; apply SPO; [ | by rewrite JOBtsk | by apply ltnW].
            by red; intro EQ; subst; rewrite ltnn in BEFOREother.
          }
          {
            move: PENDING => /andP [ARRIVED _].
            exploit (SPO j j_other); [ | by rewrite SAMEtsk | by done | ]; last first.
            {
              apply/negP; rewrite -ltnNge JOBtsk.
              apply leq_trans with (n := job_arrival j + task_deadline tsk);
                last by rewrite leq_add2l; apply CONSTR; rewrite -JOBtsk FROMTS.
              apply leq_trans with (n := job_arrival j + task_jitter tsk + R);
                last by rewrite -addnA leq_add2l; apply NOMISS.
              apply leq_trans with (n := t1 + R); last first.
              {
                rewrite leq_add2r leq_add2l -JOBtsk.
                by specialize (JOBPARAMS j); des.
              }
              apply leq_ltn_trans with (n := job_arrival j_other + job_jitter j_other);
                first by apply leq_addr.
              by apply leq_ltn_trans with (n := t).
            }
            by intros EQtsk; subst j_other; rewrite /backlogged SCHED andbF in BACK.
          }
        Qed.

      (* 3) Next, we prove that the sum of the interference of each task is equal
          to the total interference multiplied by the number of processors. This
          holds because interference only occurs when all processors are busy. *)
        Lemma bertogna_edf_all_cpus_busy :
          \sum_(tsk_k <- ts_interf) x tsk_k = X * num_cpus.
        Proof.
          have DIFFTASK := bertogna_edf_interference_by_different_tasks.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_work_conserving into WORK,
                 H_tsk_R_in_rt_bounds into INbounds,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_rt_bounds_contains_all_tasks into UNZIP,
                 H_constrained_deadlines into CONSTR.
          unfold sporadic_task_model in *.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /= mul1n.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _ _) _]big_mkcond.
          apply eq_big_nat; move => t /andP [GEt LTt].
          destruct (backlogged job_cost job_jitter sched j t) eqn:BACK;
            last by rewrite big1 //; ins; rewrite big1.
          rewrite big_mkcond /=.
          rewrite exchange_big /=.
          apply eq_trans with (y := \sum_(cpu < num_cpus) 1); last by simpl_sum_const.
          apply eq_bigr; intros cpu _.
          move: (WORK j t BACK cpu) => [j_other /eqP SCHED]; unfold scheduled_on in *.
          rewrite (bigD1_seq (job_task j_other)) /=; last by rewrite filter_uniq.
          {
            rewrite (eq_bigr (fun i => 0));
              last by intros i DIFF; rewrite /task_scheduled_on SCHED;apply/eqP;rewrite eqb0 eq_sym.
            simpl_sum_const; apply/eqP; rewrite eqb1.
            by unfold task_scheduled_on; rewrite SCHED.
          }
          rewrite mem_filter; apply/andP; split; last by apply FROMTS.
          unfold jldp_can_interfere_with.
          apply DIFFTASK with (t := t); [by auto | by done |].
          by apply/existsP; exists cpu; apply/eqP.
        Qed.

        (* 4) Show that by the induction hypothesis, all jobs released
           before the end of the interval complete by their periods. *)
        Lemma bertogna_edf_all_previous_jobs_complete_by_their_period:
          forall t (j0: JobIn arr_seq),
            t < t1 + R ->
            job_arrival j0 + task_period (job_task j0) <= t ->
            completed job_cost sched j0
               (job_arrival j0 + task_period (job_task j0)).
        Proof.
          rename H_valid_job_parameters into JOBPARAMS,
                 H_rt_bounds_contains_all_tasks into UNZIP,
                 H_job_of_tsk into JOBtsk,
                 H_constrained_deadlines into CONSTR,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_all_jobs_from_taskset into FROMTS,
                 H_all_previous_jobs_completed_on_time into BEFOREok.
          unfold valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          intros t j0 LEt LE.
          cut ((job_task j0) \in unzip1 rt_bounds = true); last by rewrite UNZIP FROMTS.
          move => /mapP [p IN EQ]; destruct p as [tsk' R0]; simpl in *; subst tsk'.
          apply completion_monotonic with (t0 := job_arrival j0 +
                                        task_jitter (job_task j0) + R0); first by done.
          {
            rewrite -addnA leq_add2l.
            apply leq_trans with (n := task_deadline (job_task j0));
              [by apply NOMISS | by apply CONSTR; rewrite FROMTS].
          }
          apply BEFOREok with (tsk_other := (job_task j0)); try by done.
          apply leq_ltn_trans with (n := t); last first.
          {
            apply leq_trans with (n := t1 + R); first by done.
            rewrite leq_add2r leq_add2l -JOBtsk.
            by specialize (JOBPARAMS j); des.
          }
          apply leq_trans with (n := job_arrival j0 + task_period (job_task j0)); last by done.
          by rewrite -addnA leq_add2l; apply leq_trans with (n := task_deadline (job_task j0));
            [by apply NOMISS | apply CONSTR; rewrite FROMTS].
        Qed.
        
        (* Let (cardGE delta) be the number of interfering tasks whose interference
           is larger than delta. *)
        Let cardGE (delta: time) := count (fun i => x i >= delta) ts_interf.

        (* 5) If there is at least one of such tasks (e.g., cardGE > 0), then the
           cumulative interference caused by the complementary set of interfering
           tasks fills at least (num_cpus - cardGE) processors. *)
        Lemma bertogna_edf_helper_lemma :
          forall delta,
            0 < cardGE delta < num_cpus ->
            \sum_(i <- ts_interf | x i < delta) x i >= delta * (num_cpus - cardGE delta).
        Proof.
          have COMP := bertogna_edf_all_previous_jobs_complete_by_their_period.
          have INV := bertogna_edf_scheduling_invariant.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk, H_sporadic_tasks into SPO,
                 H_tsk_R_in_rt_bounds into INbounds,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_constrained_deadlines into CONSTR, H_sequential_jobs into SEQ.
          unfold sporadic_task_model in *.
          move => delta /andP [HAS LT]. 
          rewrite -has_count in HAS.

          set some_interference_A := fun t =>
            has (fun tsk_k => backlogged job_cost job_jitter sched j t &&
                              (x tsk_k >= delta) &&
                              task_is_scheduled job_task sched tsk_k t) ts_interf.
          set total_interference_B := fun t =>
              backlogged job_cost job_jitter sched j t *
              count (fun tsk_k => (x tsk_k < delta) &&
                    task_is_scheduled job_task sched tsk_k t) ts_interf.

          apply leq_trans with ((\sum_(t1 <= t < t1 + R)
                                some_interference_A t) * (num_cpus - cardGE delta)).
          {
            rewrite leq_mul2r; apply/orP; right.
            move: HAS => /hasP HAS; destruct HAS as [tsk_a INa LEa].
            apply leq_trans with (n := x tsk_a); first by apply LEa.
            unfold x, task_interference, some_interference_A.
            apply leq_sum_nat; move => t /andP [GEt LTt] _.
            destruct (backlogged job_cost job_jitter sched j t) eqn:BACK;
              last by rewrite (eq_bigr (fun x => 0)); [by simpl_sum_const | by ins].
            destruct ([exists cpu, task_scheduled_on job_task sched tsk_a cpu t]) eqn:SCHED;
              last first.
            {
              apply negbT in SCHED; rewrite negb_exists in SCHED; move: SCHED => /forallP ALL.
              rewrite (eq_bigr (fun x => 0)); first by simpl_sum_const.
              by intros cpu _; specialize (ALL cpu); apply negbTE in ALL; rewrite ALL.
            }
            move: SCHED => /existsP [cpu SCHED].
            apply leq_trans with (n := 1); last first.
            {
              rewrite lt0b; apply/hasP; exists tsk_a; first by done.
              by rewrite LEa 2!andTb; apply/existsP; exists cpu.
            }
            rewrite (bigD1 cpu) /= // SCHED.
            rewrite (eq_bigr (fun x => 0)); first by simpl_sum_const; rewrite leq_b1.
            intros cpu' DIFF.
            apply/eqP; rewrite eqb0; apply/negP.
            intros SCHED'. 
            move: DIFF => /negP DIFF; apply DIFF; apply/eqP.
            unfold task_scheduled_on in *.
            destruct (sched cpu t) as [j1|] eqn:SCHED1; last by done.
            destruct (sched cpu' t) as [j2|] eqn:SCHED2; last by done.
            move: SCHED SCHED' => /eqP JOB /eqP JOB'.
            subst tsk_a; symmetry in JOB'.
            assert (PENDING1: pending job_cost job_jitter sched j1 t).
            {
              apply scheduled_implies_pending; try by done.
              by apply/existsP; exists cpu; apply/eqP.
            }
            assert (PENDING2: pending job_cost job_jitter sched j2 t).
            {
              apply scheduled_implies_pending; try by done.
              by apply/existsP; exists cpu'; apply/eqP.
            }
            assert (BUG: j1 = j2).
            {
              apply platform_at_most_one_pending_job_of_each_task with (task_cost0 := task_cost)
               (job_jitter0 := job_jitter) (task_period0 := task_period) (job_cost0 := job_cost)
               (task_deadline0 := task_deadline) (tsk0 := tsk) (job_task0 := job_task) (sched0 := sched)
               (j0 := j) (t0 := t);
              rewrite ?JOBtsk ?SAMEtsk //; first by apply PARAMS; rewrite -JOBtsk FROMTS.
              by intros j0 tsk0 TSK0 LE; apply (COMP t); rewrite ?TSK0.
            }
            by subst j2; apply SEQ with (j := j1) (t := t).
          }

          apply leq_trans with (\sum_(t1 <= t < t1 + R) total_interference_B t).
          {
            rewrite big_distrl /=.
            apply leq_sum_nat; move => t LEt _.
            unfold some_interference_A, total_interference_B. 
            destruct (backlogged job_cost job_jitter sched j t) eqn:BACK;
              [rewrite mul1n /= | by rewrite has_pred0 //].

            destruct (has (fun tsk_k : sporadic_task => (delta <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) ts_interf) eqn:HAS';
              last by done.
            rewrite mul1n; move: HAS => /hasP [tsk_k INk LEk].
            unfold cardGE.
            apply leq_trans with (n := num_cpus -
                         count (fun i => (x i >= delta) &&
                            task_is_scheduled job_task sched i t) ts_interf).
            {
              apply leq_sub2l.
              rewrite -2!sum1_count big_mkcond /=.
              rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
              apply leq_sum; intros i _.
              by destruct (task_is_scheduled job_task sched i t);
                [by rewrite andbT | by rewrite andbF].
            }
            rewrite -count_filter -[count _ ts_interf]count_filter.
            eapply leq_trans with (n := count (predC (fun tsk => delta <= x tsk)) _);
              last by apply eq_leq, eq_in_count; red; ins; rewrite ltnNge.
            rewrite leq_subLR count_predC size_filter.
            by apply leq_trans with (n := count (scheduled_task_other_than_tsk t) ts);
              [by rewrite INV | by rewrite count_filter].
          }
          {
            unfold x at 2, total_interference_B.
            rewrite exchange_big /=; apply leq_sum; intros t _.
            destruct (backlogged job_cost job_jitter sched j t) eqn:BACK; last by ins.
            rewrite mul1n -sum1_count.
            rewrite big_mkcond [\sum_(i <- ts_interf | _ < _) _]big_mkcond /=.
            apply leq_sum_seq; move => tsk_k IN _.
            destruct (x tsk_k < delta); [rewrite andTb | by rewrite andFb].
            destruct (task_is_scheduled job_task sched tsk_k t) eqn:SCHED; last by done.
            move: SCHED => /existsP [cpu SCHED].
            by rewrite (bigD1 cpu) /= // SCHED.
          }
        Qed.

        (* 6) Next, we prove that, for any interval delta, if the sum of per-task
              interference exceeds delta * num_cpus, the same applies for the
              sum of the minimum between the interference and delta. *)
        Lemma bertogna_edf_minimum_exceeds_interference :
          forall delta,
            \sum_(tsk_k <- ts_interf) x tsk_k >= delta * num_cpus ->
               \sum_(tsk_k <- ts_interf) minn (x tsk_k) delta >=
               delta * num_cpus.
        Proof.
          intros delta SUMLESS.
          set more_interf := fun tsk_k => x tsk_k >= delta.
          rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
          unfold more_interf, minn.
          rewrite [\sum_(_ <- _ | delta <= _)_](eq_bigr (fun i => delta));
            last by intros i COND; rewrite leqNgt in COND; destruct (delta > x i).
          rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < delta)
                                                (fun i => x i));
            [| by red; ins; rewrite ltnNge
             | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

          (* Case 1: cardGE = 0 *)
          destruct (~~ has (fun i => delta <= x i) ts_interf) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in ts_interf) && true));
              last by red; intros tsk_k; destruct (tsk_k \in ts_interf) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond.
          } apply negbFE in HASa.

          (* Case 2: cardGE >= num_cpus *)
          destruct (cardGE delta >= num_cpus) eqn:CARD.
          {
            apply leq_trans with (delta * cardGE delta);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold cardGE; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          (* Case 3: cardGE < num_cpus *)
          rewrite big_const_seq iter_addn addn0; fold cardGE.
          apply leq_trans with (n := delta * cardGE delta +
                                     delta * (num_cpus - cardGE delta));
            first by rewrite -mulnDr subnKC //; apply ltnW.
          rewrite leq_add2l; apply bertogna_edf_helper_lemma.
          by apply/andP; split; first by rewrite -has_count.
        Qed.

        (* 7) Now, we prove that the Bertogna's interference bound
              is not enough to cover the sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        Lemma bertogna_edf_sum_exceeds_total_interference:
          \sum_((tsk_other, R_other) <- rt_bounds | jldp_can_interfere_with tsk tsk_other)
            minn (x tsk_other) (R - task_cost tsk + 1) > I tsk R.
        Proof.
          have GE_COST := bertogna_edf_R_other_ge_cost.
          have EXCEEDS := bertogna_edf_minimum_exceeds_interference.
          have ALLBUSY := bertogna_edf_all_cpus_busy.
          have TOOMUCH := bertogna_edf_too_much_interference.
          rename H_rt_bounds_contains_all_tasks into UNZIP,
            H_response_time_is_fixed_point into REC.
          apply leq_trans with (n := \sum_(tsk_other <- ts_interf) minn (x tsk_other) (R - task_cost tsk + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
              last by ins; destruct i.
            move: UNZIP => UNZIP.
            assert (FILTER: filter (jldp_can_interfere_with tsk) (unzip1 rt_bounds) =
                            filter (jldp_can_interfere_with tsk) ts).
              by f_equal.
            unfold ts_interf; rewrite -FILTER; clear FILTER.
            rewrite -[\sum_(_ <- rt_bounds | _)_]big_filter.
            assert (SUBST: [seq i <- rt_bounds
                   | let '(tsk_other, _) := i in
                          jldp_can_interfere_with tsk tsk_other] = [seq i <- rt_bounds
                             | jldp_can_interfere_with tsk (fst i)]).
            {
              by apply eq_filter; red; intro i; destruct i.
            } rewrite SUBST; clear SUBST.         
            have MAP := big_map (fun x => fst x) (fun i => true) (fun i => minn (x i) (R - task_cost tsk + 1)).
            by rewrite -MAP; apply eq_leq; f_equal; rewrite filter_map.
          }

          apply ltn_div_trunc with (d := num_cpus); first by apply H_at_least_one_cpu.
          rewrite -(ltn_add2l (task_cost tsk)) -REC; last by done.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by apply GE_COST.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          apply EXCEEDS.
          apply leq_trans with (n := X * num_cpus); last by rewrite ALLBUSY.
          by rewrite leq_mul2r; apply/orP; right; apply TOOMUCH.
        Qed.

        (* 8) After concluding that the sum of the minimum exceeds (R - e_i + 1),
              we prove that there exists a tuple (tsk_k, R_k) such that
              min (x_k, R - e_i + 1) > min (W_k, edf_bound, R - e_i + 1). *)
        Lemma bertogna_edf_exists_task_that_exceeds_bound :
          exists tsk_other R_other,
            (tsk_other, R_other) \in rt_bounds /\
            (minn (x tsk_other) (R - task_cost tsk + 1) > interference_bound tsk_other R_other).
        Proof.
          have SUM := bertogna_edf_sum_exceeds_total_interference.
          have BOUND := bertogna_edf_workload_bounds_interference.
          have EDFBOUND := bertogna_edf_specific_bound_holds.
          rename H_rt_bounds_contains_all_tasks into UNZIP.
          assert (HAS: has (fun tup : task_with_response_time =>
                              let (tsk_other, R_other) := tup in
                              (tsk_other \in ts) && jldp_can_interfere_with tsk tsk_other &&
                                (minn (x tsk_other) (R - task_cost tsk + 1)  >
                                interference_bound tsk_other R_other))
                           rt_bounds).
          {
            apply/negP; unfold not; intro NOTHAS.
            move: NOTHAS => /negP /hasPn ALL.
            rewrite -[_ < _]negbK in SUM.
            move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
            unfold I, total_interference_bound_edf.
            rewrite big_seq_cond [\sum_(_ <- _ | let _ := _ in _)_]big_seq_cond.
            apply leq_sum; move => tsk_k /andP [INBOUNDSk INTERFk]; destruct tsk_k as [tsk_k R_k].
            specialize (ALL (tsk_k, R_k) INBOUNDSk).
            unfold interference_bound_edf; simpl in *.
            rewrite leq_min; apply/andP; split.
            {
              unfold interference_bound; rewrite leq_min; apply/andP; split;
                last by rewrite geq_minr.
              by apply leq_trans with (n := x tsk_k);
                [by rewrite geq_minl | by apply BOUND].
            }
            {
              apply leq_trans with (n := x tsk_k); first by rewrite geq_minl.
              by apply EDFBOUND.
            }
          }
          move: HAS => /hasP HAS; destruct HAS as [[tsk_k R_k] HPk MIN].
          move: MIN => /andP [/andP [INts INTERFk] MINk].
          by exists tsk_k, R_k; repeat split.
        Qed.

      End DerivingContradiction.
      
    End Lemmas.

    Section MainProof.
      
      (* Let (tsk, R) be any task to be analyzed, with its response-time bound R. *)
      Variable tsk: sporadic_task.
      Variable R: time.
      Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

      (* Using the lemmas above, we prove that R bounds the response time of task tsk. *)
      Theorem bertogna_cirinei_response_time_bound_edf :
        response_time_bounded_by tsk (task_jitter tsk + R).
      Proof.
        have EXISTS := bertogna_edf_exists_task_that_exceeds_bound.
        have BASICBOUND := bertogna_edf_workload_bounds_interference.
        have EDFBOUND := bertogna_edf_specific_bound_holds.
        rename H_valid_job_parameters into JOBPARAMS.
        unfold valid_sporadic_job_with_jitter, valid_sporadic_job in *.
        intros j JOBtsk.

        rewrite addnA.
        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        remember (job_arrival j + task_jitter tsk + R) as ctime.

        revert H_tsk_R_in_rt_bounds.
        generalize dependent R; generalize dependent tsk; generalize dependent j.
      
        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime IH] using strong_ind.

        intros j tsk' JOBtsk R' EQc INbounds; subst ctime.

        (* First, let's simplify the induction hypothesis. *)
        assert (BEFOREok: forall (j0: JobIn arr_seq) tsk R0,
                                 job_task j0 = tsk ->
                               (tsk, R0) \in rt_bounds ->
                               job_arrival j0 + task_jitter tsk + R0 < job_arrival j + task_jitter tsk' + R' ->
                               service sched j0 (job_arrival j0 + task_jitter tsk + R0) == job_cost j0).
        {
            by ins; apply IH with (tsk := tsk0) (R := R0).
        }
        clear IH.
        
        (* The proof follows by contradiction. Assume that job j does not complete by its
           response-time bound. By the induction hypothesis, all jobs with absolute
           response-time bound t < (job_arrival j + R) have correct response-time bounds. *)
        destruct (completed job_cost sched j (job_arrival j + job_jitter j + R')) eqn:NOTCOMP.
        {
          apply completion_monotonic with (t := job_arrival j + job_jitter j + R'); try (by done).
          rewrite leq_add2r leq_add2l.
          specialize (JOBPARAMS j); des.
          by rewrite -JOBtsk; apply JOBPARAMS0.
        }
        apply negbT in NOTCOMP; exfalso.
        
        (* Next, we derive a contradiction using the previous lemmas. *)
        exploit (EXISTS tsk' R' INbounds j JOBtsk NOTCOMP).
        {
          by ins; apply IH with (tsk := tsk_other) (R := R_other).
        } 
        intro EX; destruct EX as [tsk_other [R_other [HP LTmin]]].
        unfold interference_bound_edf, interference_bound_generic in LTmin.
        rewrite minnAC in LTmin; apply min_lt_same in LTmin.
        specialize (BASICBOUND tsk' R' j JOBtsk BEFOREok tsk_other R_other HP).
        specialize (EDFBOUND tsk' R' INbounds j JOBtsk BEFOREok tsk_other R_other HP).
        unfold minn in LTmin; clear -LTmin HP BASICBOUND EDFBOUND tsk; desf.
        {
          by apply (leq_ltn_trans BASICBOUND) in LTmin; rewrite ltnn in LTmin. 
        }
        {
          by apply (leq_ltn_trans EDFBOUND) in LTmin; rewrite ltnn in LTmin.
        }
      Qed.

    End MainProof.
    
  End ResponseTimeBound.

End ResponseTimeAnalysisEDFJitter.