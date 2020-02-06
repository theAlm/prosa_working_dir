Require Import rt.util.all.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.task_arrival
               rt.model.basic.schedule rt.model.basic.platform rt.model.basic.interference
               rt.model.basic.workload rt.model.basic.schedulability rt.model.basic.priority
               rt.model.basic.platform rt.model.basic.response_time.
Require Import rt.analysis.parallel.workload_bound rt.analysis.parallel.interference_bound_edf.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisEDF.

  Export Job SporadicTaskset Schedule ScheduleOfSporadicTask Workload Schedulability ResponseTime
         Priority SporadicTaskArrival WorkloadBound InterferenceBoundEDF
         Interference Platform.

  (* In this section, we prove that Bertogna and Cirinei's RTA yields
     safe response-time bounds. *)
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

    (* Assume that we have a task set ts such that all jobs come from
       the task set, and all tasks have valid parameters and
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
      total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta.
    Hypothesis H_response_time_is_fixed_point :
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        R = task_cost tsk + div_floor (I tsk R) num_cpus.
    
    (* ..., and R is no larger than the deadline. *)
    Hypothesis H_tasks_miss_no_deadlines:
      forall tsk_other R,
        (tsk_other, R) \in rt_bounds -> R <= task_deadline tsk_other.

    (* Assume that we have a work-conserving EDF scheduler. *)
    Hypothesis H_work_conserving: work_conserving job_cost sched.
    Hypothesis H_edf_policy: enforces_JLDP_policy job_cost sched (EDF job_deadline).
    
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

      (* Assume that job j did not complete on time, ... *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (job_arrival j + R).

      (* and that it is the first job not to satisfy its response-time bound. *)
      Hypothesis H_all_previous_jobs_completed_on_time :
        forall (j_other: JobIn arr_seq) tsk_other R_other,
          job_task j_other = tsk_other ->
          (tsk_other, R_other) \in rt_bounds ->
          job_arrival j_other + R_other < job_arrival j + R ->
          completed job_cost sched j_other (job_arrival j_other + R_other).

      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_cost job_task sched j
                          tsk_other (job_arrival j) (job_arrival j + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_cost sched j (job_arrival j) (job_arrival j + R).

      (* Recall Bertogna and Cirinei's workload bound ... *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W task_cost task_period tsk_other R_other R.

      (*... and the EDF-specific bound, ... *)
      Let edf_specific_bound (tsk_other: sporadic_task) (R_other: time) :=
        edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other.

      (* ... which combined form the interference bound. *)
      Let interference_bound (tsk_other: sporadic_task) (R_other: time) :=
        interference_bound_edf task_cost task_period task_deadline tsk R (tsk_other, R_other). 
      
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
          unfold x, task_interference.
          have INts := bertogna_edf_tsk_other_in_ts.
          apply leq_trans with (n := workload job_task sched tsk_other
                                         (job_arrival j) (job_arrival j + R));
            first apply task_interference_le_workload.
          
          apply workload_bounded_by_W with (task_deadline0 := task_deadline)
                                             (job_cost0 := job_cost) (job_deadline0 := job_deadline); try (by ins).
            - by ins; apply TASK_PARAMS.
            - by ins; apply BEFOREok with (tsk_other := tsk_other).
        Qed.

        (* Recall that the edf-specific interference bound also holds. *)
        Lemma bertogna_edf_specific_bound_holds :
          x tsk_other <= edf_specific_bound tsk_other R_other.
        Proof.
          rename H_job_of_tsk into JOBtsk, H_all_jobs_from_taskset into FROMTS.
          apply interference_bound_edf_bounds_interference with (job_deadline0 := job_deadline)
                                                                  (ts0 := ts); try (by done);
          [ by rewrite -JOBtsk FROMTS
          | by apply bertogna_edf_tsk_other_in_ts
          | by apply H_tasks_miss_no_deadlines
          | by ins; apply H_all_previous_jobs_completed_on_time with (tsk_other := tsk_other)].
        Qed.
        
      End LemmasAboutInterferingTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.
        
      (* 0) Since job j did not complete by its response time bound, it follows that
            the total interference X >= R - e_k + 1. *)
      Lemma bertogna_edf_too_much_interference : X >= R - task_cost tsk + 1.
      Proof.
        rename H_completed_jobs_dont_execute into COMP,
               H_valid_job_parameters into PARAMS,
               H_response_time_is_fixed_point into REC,
               H_job_of_tsk into JOBtsk,
               H_j_not_completed into NOTCOMP.
        unfold completed, valid_sporadic_job in *.
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

      (* 1) Next, we prove that the sum of the interference of each task is equal
            to the total interference multiplied by the number of processors. This
            holds because interference only occurs when all processors are busy. *)
      Lemma bertogna_edf_all_cpus_busy :
        \sum_(tsk_k <- ts_interf) x tsk_k = X * num_cpus.
      Proof.
        rename H_all_jobs_from_taskset into FROMTS,
               H_valid_task_parameters into PARAMS,
               H_job_of_tsk into JOBtsk,
               H_sporadic_tasks into SPO,
               H_work_conserving into WORK,
               H_tsk_R_in_rt_bounds into INbounds,
               H_all_previous_jobs_completed_on_time into BEFOREok,
               H_tasks_miss_no_deadlines into NOMISS,
               H_rt_bounds_contains_all_tasks into UNZIP,
               H_constrained_deadlines into RESTR.
        unfold sporadic_task_model in *.
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
        unfold jldp_can_interfere_with.
        apply/eqP; red; intro SAMEtsk.
        assert (SCHED': scheduled sched j_other t).
        {
          unfold scheduled, scheduled_on.
          by apply/existsP; exists cpu; rewrite SCHED.
        }
        clear SCHED; rename SCHED' into SCHED.
        move: (SCHED) => PENDING.
apply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING; try (by done).
        destruct (ltnP (job_arrival j_other) (job_arrival j)) as [BEFOREother | BEFOREj].
         {
          move: (BEFOREother) => LT; rewrite -(ltn_add2r R) in LT.
          specialize (BEFOREok j_other tsk R SAMEtsk INbounds LT).
          move: PENDING => /andP [_ /negP NOTCOMP]; apply NOTCOMP.
          apply completion_monotonic with (t0 := job_arrival j_other + R); try (by done).
          apply leq_trans with (n := job_arrival j); last by done.
          apply leq_trans with (n := job_arrival j_other + task_deadline tsk);
            first by rewrite leq_add2l; apply NOMISS.
          apply leq_trans with (n := job_arrival j_other + task_period tsk);
            first by rewrite leq_add2l; apply RESTR; rewrite -JOBtsk FROMTS.
          rewrite -SAMEtsk; apply SPO; [ | by rewrite JOBtsk | by apply ltnW].
          by red; intro EQ; subst; rewrite ltnn in BEFOREother.
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
          by red; intros EQtsk; subst; rewrite /backlogged SCHED andbF in BACK.
        }
      Qed.

      (* 2) Now, we prove that the Bertogna's interference bound
            is not enough to cover the sum of the "minimum" term over
            all tasks (artifact of the proof by contradiction). *)
      Lemma bertogna_edf_sum_exceeds_total_interference:
        \sum_((tsk_other, R_other) <- rt_bounds | jldp_can_interfere_with tsk tsk_other)
          x tsk_other > I tsk R.
      Proof.
        have GE_COST := bertogna_edf_R_other_ge_cost.
        have ALLBUSY := bertogna_edf_all_cpus_busy.
        have TOOMUCH := bertogna_edf_too_much_interference.
        rename H_rt_bounds_contains_all_tasks into UNZIP,
               H_response_time_is_fixed_point into REC.
        apply leq_trans with (n := \sum_(tsk_other <- ts_interf) x tsk_other);
          last first.
        {
          rewrite (eq_bigr (fun i => x (fst i))); last by ins; destruct i.
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
          have MAP := big_map (fun x => fst x) (fun i => true) (fun i => x i).
          by rewrite -MAP; apply eq_leq; f_equal; rewrite filter_map.
        }
        
        apply ltn_div_trunc with (d := num_cpus); first by apply H_at_least_one_cpu.
        rewrite -(ltn_add2l (task_cost tsk)) -REC; last by done.
        rewrite -addn1 -leq_subLR.
        rewrite -[R + 1 - _]subh1; last by apply GE_COST.
        rewrite leq_divRL; last by apply H_at_least_one_cpu.
        rewrite ALLBUSY.
        by rewrite leq_mul2r; apply/orP; right; apply TOOMUCH.
      Qed.

      (* 3) After concluding that the sum of the minimum exceeds (R - e_i + 1),
            we prove that there exists a tuple (tsk_k, R_k) such that
            min (x_k, R - e_i + 1) > min (W_k, edf_bound, R - e_i + 1). *)
      Lemma bertogna_edf_exists_task_that_exceeds_bound :
        exists tsk_other R_other,
          (tsk_other, R_other) \in rt_bounds /\
          x tsk_other > interference_bound tsk_other R_other.
      Proof.
        have SUM := bertogna_edf_sum_exceeds_total_interference.
        have BOUND := bertogna_edf_workload_bounds_interference.
        have EDFBOUND := bertogna_edf_specific_bound_holds.
        rename H_rt_bounds_contains_all_tasks into UNZIP.
        assert (HAS: has (fun tup : task_with_response_time =>
                       let (tsk_other, R_other) := tup in
                         (tsk_other \in ts) && jldp_can_interfere_with tsk tsk_other &&
                        (x tsk_other  > interference_bound tsk_other R_other))
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
          by rewrite leq_min; apply/andP; split;
            [by apply BOUND | by apply EDFBOUND].
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
        response_time_bounded_by tsk R.
      Proof.
        intros j JOBtsk.
       
        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        remember (job_arrival j + R) as ctime.

        revert H_tsk_R_in_rt_bounds.
        generalize dependent R; generalize dependent tsk; generalize dependent j.
      
        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime IH] using strong_ind.

        intros j tsk' JOBtsk R' EQc INbounds; subst ctime.

        (* First, let's simplify the induction hypothesis. *)
        assert (BEFOREok: forall (j0: JobIn arr_seq) tsk R0,
                                 job_task j0 = tsk ->
                               (tsk, R0) \in rt_bounds ->
                               job_arrival j0 + R0 < job_arrival j + R' ->
                               service sched j0 (job_arrival j0 + R0) == job_cost j0).
        {
            by ins; apply IH with (tsk := tsk0) (R := R0).
        }
        clear IH.
        
        (* The proof follows by contradiction. Assume that job j does not complete by its
           response-time bound. By the induction hypothesis, all jobs with absolute
           response-time bound t < (job_arrival j + R) have correct response-time bounds. *)
        destruct (completed job_cost sched j (job_arrival j + R')) eqn:NOTCOMP;
          first by done.
        apply negbT in NOTCOMP; exfalso.
        
        (* Next, we derive a contradiction using the previous lemmas. *)
        exploit (bertogna_edf_exists_task_that_exceeds_bound tsk' R' INbounds j JOBtsk NOTCOMP).
        {
          by ins; apply IH with (tsk := tsk_other) (R := R_other).
        } 
        intro EX; destruct EX as [tsk_other [R_other [HP LTmin]]].
        unfold interference_bound_edf, interference_bound_generic in LTmin.
        have BASICBOUND := bertogna_edf_workload_bounds_interference R' j BEFOREok tsk_other R_other HP.
        have EDFBOUND := (bertogna_edf_specific_bound_holds tsk' R' j JOBtsk BEFOREok tsk_other R_other HP).
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

End ResponseTimeAnalysisEDF.