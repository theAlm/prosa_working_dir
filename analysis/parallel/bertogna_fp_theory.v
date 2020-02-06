Require Import rt.util.all.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.task_arrival
               rt.model.basic.schedule rt.model.basic.platform rt.model.basic.platform_fp
               rt.model.basic.workload rt.model.basic.schedulability rt.model.basic.priority
               rt.model.basic.response_time rt.model.basic.interference.
Require Import rt.analysis.parallel.workload_bound rt.analysis.parallel.interference_bound_fp.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference InterferenceBoundFP
         Platform PlatformFP Schedulability ResponseTime Priority SporadicTaskArrival WorkloadBound.
    
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ...jobs do not execute before their arrival times nor longer
       than their execution costs. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Assume that there exists at least one processor. *)
    Hypothesis H_at_least_one_cpu :
      num_cpus > 0.

    (* Assume that we have a task set (with no duplicates) where all jobs
       come from the task set and all tasks have valid parameters and constrained deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_ts_is_a_set: uniq ts.
    Hypothesis H_all_jobs_from_taskset:
      forall (j: JobIn arr_seq), job_task j \in ts.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_constrained_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    (* Next, consider a task tsk that is to be analyzed. *)
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk sched.

    (* Assume a known response-time bound for any interfering task *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    
    (* For FP scheduling, assume there exists a fixed task priority. *)
    Variable higher_eq_priority: FP_policy sporadic_task.

    Let can_interfere_with_tsk := fp_can_interfere_with higher_eq_priority tsk.
    
    (* Assume that hp_bounds has exactly the tasks that interfere with tsk,... *)
    Hypothesis H_hp_bounds_has_interfering_tasks:
      [seq tsk_hp <- ts | can_interfere_with_tsk tsk_hp] = unzip1 hp_bounds.

    (* ...and that all values in the pairs contain valid response-time bounds *)
    Hypothesis H_response_time_of_interfering_tasks_is_known:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        response_time_bounded_by hp_tsk R.

    (* Assume that the scheduler is work-conserving and enforces the FP policy. *)
    Hypothesis H_work_conserving: work_conserving job_cost sched.
    Hypothesis H_enforces_FP_policy:
      enforces_FP_policy job_cost job_task sched higher_eq_priority.
    
    (* Let R be the fixed point of Bertogna and Cirinei's recurrence, ...*)
    Variable R: time.
    Hypothesis H_response_time_recurrence_holds :
      R = task_cost tsk +
          div_floor
            (total_interference_bound_fp task_cost task_period tsk hp_bounds R higher_eq_priority)
            num_cpus.

    (* ... and assume that R is no larger than the deadline of tsk.*)
    Hypothesis H_response_time_no_larger_than_deadline:
      R <= task_deadline tsk.

    (* In order to prove that R is a response-time bound, we first present some lemmas. *)
    Section Lemmas.

      (* Consider any job j of tsk. *)
      Variable j: JobIn arr_seq.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* Assume that job j is the first job of tsk not to complete by the response time bound. *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (job_arrival j + R).
      Hypothesis H_previous_jobs_of_tsk_completed :
        forall (j0: JobIn arr_seq),
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + R).
      
      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_cost job_task sched j
                          tsk_other (job_arrival j) (job_arrival j + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_cost sched j (job_arrival j) (job_arrival j + R).

      (* Recall Bertogna and Cirinei's workload bound. *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W task_cost task_period tsk_other R_other R.

      (* Also, let ts_interf be the subset of tasks that interfere with tsk. *)
      Let ts_interf := [seq tsk_other <- ts | can_interfere_with_tsk tsk_other].

      Section LemmasAboutInterferingTasks.
        
        (* Let (tsk_other, R_other) be any pair of higher-priority task and
           response-time bound computed in previous iterations. *)
        Variable tsk_other: sporadic_task.
        Variable R_other: time.
        Hypothesis H_response_time_of_tsk_other: (tsk_other, R_other) \in hp_bounds.

        (* Note that tsk_other is in task set ts ...*)
        Lemma bertogna_fp_tsk_other_in_ts: tsk_other \in ts.
          Proof.
            rename H_hp_bounds_has_interfering_tasks into UNZIP,
                   H_response_time_of_tsk_other into INbounds.
            move: UNZIP => UNZIP.
            cut (tsk_other \in ts_interf = true);
              first by rewrite mem_filter; move => /andP [_ IN].
            unfold ts_interf; rewrite UNZIP.
            by apply/mapP; exists (tsk_other, R_other).
        Qed.

        (*... and interferes with task tsk. *)
        Lemma bertogna_fp_tsk_other_interferes: can_interfere_with_tsk tsk_other.
          Proof.
            rename H_hp_bounds_has_interfering_tasks into UNZIP,
                   H_response_time_of_tsk_other into INbounds.
            move: UNZIP => UNZIP.
            cut (tsk_other \in ts_interf = true);
              first by rewrite mem_filter; move => /andP [INTERF _].
            unfold ts_interf; rewrite UNZIP.
            by apply/mapP; exists (tsk_other, R_other).
        Qed.

        (* Since tsk_other cannot interfere more than it executes, we show that
           the interference caused by tsk_other is no larger than workload bound W. *)
        Lemma bertogna_fp_workload_bounds_interference :
          x tsk_other <= workload_bound tsk_other R_other.
        Proof.
          unfold response_time_bounded_by, is_response_time_bound_of_task,
                 completed, completed_jobs_dont_execute, valid_sporadic_job in *.
          rename H_valid_task_parameters into TASK_PARAMS,
                 H_response_time_of_interfering_tasks_is_known into RESP.
          unfold x, workload_bound.
          have INts := bertogna_fp_tsk_other_in_ts.
          apply leq_trans with (n := workload job_task sched tsk_other
                                              (job_arrival j) (job_arrival j + R));
            first by apply task_interference_le_workload.
          by apply workload_bounded_by_W with (task_deadline0 := task_deadline)
                    (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by ins);
              [ by ins; apply TASK_PARAMS
              | by ins; apply RESP with (hp_tsk := tsk_other)].
        Qed.

      End LemmasAboutInterferingTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.

        (* 0) Since job j did not complete by its response time bound, it follows that
              the total interference X >= R - e_k + 1. *)
        Lemma bertogna_fp_too_much_interference : X >= R - task_cost tsk + 1.
        Proof.
          rename H_completed_jobs_dont_execute into COMP,
                 H_valid_job_parameters into PARAMS,
                 H_response_time_recurrence_holds into REC,
                 H_job_of_tsk into JOBtsk,
                 H_j_not_completed into NOTCOMP.
          unfold completed, valid_sporadic_job in *.
          unfold X, total_interference; rewrite addn1.
          rewrite -(ltn_add2r (task_cost tsk)).
          rewrite subh1; last by rewrite REC leq_addr.
          rewrite -addnBA // subnn addn0.
          move: (NOTCOMP) => /negP NOTCOMP'.
          rewrite neq_ltn in NOTCOMP.
          move: NOTCOMP => /orP [LT | BUG]; last first.
          {
            exfalso; rewrite ltnNge in BUG; move: BUG => /negP BUG; apply BUG.
            by apply cumulative_service_le_job_cost.
          }
          apply leq_ltn_trans with (n := (\sum_(job_arrival j <= t < job_arrival j + R)
                                       backlogged job_cost sched j t) +
                                     service sched j (job_arrival j + R)); last first.
          {
            rewrite -addn1 -addnA leq_add2l addn1.
            apply leq_trans with (n := job_cost j); first by done.
            by specialize (PARAMS j); des; rewrite -JOBtsk.
          }
          unfold service; rewrite service_before_arrival_eq_service_during //.
          rewrite -big_split /=.
          apply leq_trans with (n := \sum_(job_arrival j <= i < job_arrival j + R) 1);
            first by rewrite big_const_nat iter_addn mul1n addn0 addKn.
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true) _]big_nat_cond.
          apply leq_sum; move => i /andP [/andP [GEi LTi] _].
          destruct (backlogged job_cost sched j i) eqn:BACK;
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
          can_interfere_with_tsk tsk_other.
        
        (* 1) Next, we prove that the sum of the interference of each task is equal
              to the total interference multiplied by the number of processors. This
              holds because interference only occurs when all processors are busy. *)
        Lemma bertogna_fp_all_cpus_busy :
          \sum_(tsk_k <- ts_interf) x tsk_k = X * num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_sporadic_tasks into SPO,
                 H_work_conserving into WORK,
                 H_constrained_deadlines into RESTR,
                 H_enforces_FP_policy into FP,
                 H_previous_jobs_of_tsk_completed into BEFOREok,
                 H_response_time_no_larger_than_deadline into NOMISS.
          unfold sporadic_task_model, enforces_FP_policy,
                 enforces_JLDP_policy, FP_to_JLDP in *.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _) _]big_mkcond.
          apply eq_big_nat; move => t /andP [GEt LTt].
          destruct (backlogged job_cost sched j t) eqn:BACK; last first.
          {
            rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
            by intros i _; rewrite (eq_bigr (fun i => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
          }
          rewrite big_mkcond mul1n /=.
          rewrite exchange_big /=.
          apply eq_trans with (y := \sum_(cpu < num_cpus) 1);
            last by rewrite big_const_ord iter_addn mul1n addn0.
          apply eq_bigr; intros cpu _.
          specialize (WORK j t BACK cpu); des.
          move: WORK => /eqP SCHED.
          rewrite (bigD1_seq (job_task j_other)) /=; last by rewrite filter_uniq.
          {
            rewrite (eq_bigr (fun i => 0));
              last by intros i DIFF; rewrite /task_scheduled_on SCHED;apply/eqP;rewrite eqb0 eq_sym.
            rewrite big_const_seq iter_addn mul0n 2!addn0; apply/eqP; rewrite eqb1.
            by unfold task_scheduled_on; rewrite SCHED.
          }
          rewrite mem_filter; apply/andP; split; last by apply FROMTS.
          unfold can_interfere_with_tsk, fp_can_interfere_with.
          apply/andP; split.
          {
            rewrite -JOBtsk; apply FP with (t := t); first by done.
            by apply/existsP; exists cpu; apply/eqP. 
          }
          {
            apply/eqP; intro SAMEtsk.
            assert (SCHED': scheduled sched j_other t).
            {
              unfold scheduled, scheduled_on.
              by apply/existsP; exists cpu; rewrite SCHED.
            } clear SCHED; rename SCHED' into SCHED.
            move: (SCHED) => PENDING.
            apply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING; try (by done).
            destruct (ltnP (job_arrival j_other) (job_arrival j)) as [BEFOREother | BEFOREj].
            {
              specialize (BEFOREok j_other SAMEtsk BEFOREother).
              move: PENDING => /andP [_ /negP NOTCOMP]; apply NOTCOMP.
              apply completion_monotonic with (t0 := job_arrival j_other + R); try (by done).
              apply leq_trans with (n := job_arrival j); last by done.
              apply leq_trans with (n := job_arrival j_other + task_deadline tsk);
              first by rewrite leq_add2l; apply NOMISS.
              apply leq_trans with (n := job_arrival j_other + task_period tsk);
                first by rewrite leq_add2l; apply RESTR; rewrite -JOBtsk FROMTS.
              rewrite -SAMEtsk; apply SPO; [ | by rewrite JOBtsk | by apply ltnW].
              by red; intro EQ; rewrite EQ ltnn in BEFOREother.
            }
            {
              move: PENDING => /andP [ARRIVED _].
              exploit (SPO j j_other); [ | by rewrite SAMEtsk | by done | ]; last first.
              {
                apply/negP; rewrite -ltnNge.
                apply leq_ltn_trans with (n := t); first by done.
                apply leq_trans with (n := job_arrival j + R); first by done.
                by rewrite leq_add2l; apply leq_trans with (n := task_deadline tsk);
                [by apply NOMISS | by rewrite JOBtsk RESTR // -JOBtsk FROMTS].
              }
              by red; intros EQjob; rewrite EQjob /backlogged SCHED andbF in BACK.
            }
          }
        Qed.

        (* 2) Now, we prove that the Bertogna's interference bound
              is not enough to cover the sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        Lemma bertogna_fp_sum_exceeds_total_interference:
          \sum_((tsk_k, R_k) <- hp_bounds)
           x tsk_k > total_interference_bound_fp task_cost task_period tsk
                                            hp_bounds R higher_eq_priority.
        Proof.
          have TOOMUCH := bertogna_fp_too_much_interference.
          rename H_hp_bounds_has_interfering_tasks into UNZIP,
                 H_response_time_recurrence_holds into REC.
          apply leq_trans with (n := \sum_(tsk_k <- ts_interf) x tsk_k);
              last first.
          {
            rewrite (eq_bigr (fun i => x (fst i)));
              last by ins; destruct i.
            rewrite big_filter.
            have MAP := big_map (fun x => fst x) (fun i => true) (fun i => x i).
            by unfold unzip1 in *; rewrite -MAP -UNZIP -big_filter.
          }
          apply ltn_div_trunc with (d := num_cpus);
            first by apply H_at_least_one_cpu.
          rewrite -(ltn_add2l (task_cost tsk)) -REC.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by rewrite REC; apply leq_addr.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          rewrite bertogna_fp_all_cpus_busy.
          by rewrite leq_mul2r; apply/orP; right; apply TOOMUCH.
        Qed.

        (* 3) After concluding that the sum of the minimum exceeds (R - e_i + 1),
              we prove that there exists a tuple (tsk_k, R_k) such that x_k > W_k. *)
        Lemma bertogna_fp_exists_task_that_exceeds_bound :
          exists tsk_k R_k,
            (tsk_k, R_k) \in hp_bounds /\
            x tsk_k > workload_bound tsk_k R_k.
        Proof.
          have INTERFk := bertogna_fp_tsk_other_interferes.
          have SUM := bertogna_fp_sum_exceeds_total_interference.
          rename H_hp_bounds_has_interfering_tasks into UNZIP.
          assert (HAS: has (fun tup : task_with_response_time =>
                             let (tsk_k, R_k) := tup in
                               x tsk_k > workload_bound tsk_k R_k)
                            hp_bounds).
          {
            apply/negP; unfold not; intro NOTHAS.
            move: NOTHAS => /negP /hasPn ALL.
            rewrite -[_ < _]negbK in SUM.
            move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
            unfold total_interference_bound_fp.
            rewrite [\sum_(i <- _ | let '(tsk_other, _) := i in _)_]big_mkcond.
            rewrite big_seq_cond [\sum_(i <- _ | true) _]big_seq_cond.
            apply leq_sum; move => tsk_k /andP [HPk _]; destruct tsk_k as [tsk_k R_k].
            specialize (ALL (tsk_k, R_k) HPk).
            rewrite -leqNgt in ALL.
            specialize (INTERFk tsk_k R_k HPk).
            fold (can_interfere_with_tsk); rewrite INTERFk.
            unfold interference_bound_generic. by apply ALL.
          }
          move: HAS => /hasP HAS; destruct HAS as [[tsk_k R_k] HPk MINk]; exists tsk_k, R_k.
          by repeat split.
        Qed.

      End DerivingContradiction.

    End Lemmas.
    
    (* Using the lemmas above, we prove that R bounds the response time of task tsk. *)
    Theorem bertogna_cirinei_response_time_bound_fp :
      response_time_bounded_by tsk R.
    Proof.
      have EX := bertogna_fp_exists_task_that_exceeds_bound.
      have BOUND := bertogna_fp_workload_bounds_interference.
      rename H_response_time_recurrence_holds into REC,
             H_response_time_of_interfering_tasks_is_known into RESP,
             H_hp_bounds_has_interfering_tasks into UNZIP,
             H_response_time_no_larger_than_deadline into LEdl.
      intros j JOBtsk.
       
      (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
      remember (job_arrival j + R) as ctime.
      
      (* Now, we apply strong induction on the absolute response-time bound. *)
      generalize dependent j.
      induction ctime as [ctime IH] using strong_ind.

      intros j JOBtsk EQc; subst ctime.

      (* First, let's simplify the induction hypothesis. *)
      assert (BEFOREok: forall (j0: JobIn arr_seq),
                          job_task j0 = tsk ->
                          job_arrival j0 < job_arrival j ->
                          service sched j0 (job_arrival j0 + R) == job_cost j0).
      {
        by ins; apply IH; try (by done); rewrite ltn_add2r.
      } clear IH.
              
      unfold response_time_bounded_by, is_response_time_bound_of_task,
             completed, completed_jobs_dont_execute, valid_sporadic_job in *.

      (* Now we start the proof. Assume by contradiction that job j
         is not complete at time (job_arrival j + R). *)
      destruct (completed job_cost sched j (job_arrival j + R)) eqn:NOTCOMP;
        first by done.
      apply negbT in NOTCOMP; exfalso.

      (* We derive a contradiction using the previous lemmas. *)
      specialize (EX j JOBtsk NOTCOMP BEFOREok).
      destruct EX as [tsk_k [R_k [HPk LTmin]]].
      specialize (BOUND j tsk_k R_k HPk).
      by apply (leq_ltn_trans BOUND) in LTmin; rewrite ltnn in LTmin.
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.