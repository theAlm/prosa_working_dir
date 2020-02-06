Require Import rt.util.all.
Require Import rt.model.jitter.task rt.model.jitter.job rt.model.jitter.schedule
               rt.model.jitter.task_arrival rt.model.jitter.interference
               rt.model.jitter.priority rt.model.jitter.platform.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module PlatformFP.

  Import Job SporadicTaskset ScheduleOfSporadicTaskWithJitter SporadicTaskset
         SporadicTaskArrival Interference Priority Platform.

  Section Lemmas.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> time.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* Consider any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.
    
    (* Assume all jobs have valid parameters, ...*)
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    Section JobInvariantAsTaskInvariant.

      (* Assume any work-conserving priority-based scheduler. *)
      Variable higher_eq_priority: FP_policy sporadic_task.
      Hypothesis H_work_conserving: work_conserving job_cost job_jitter sched.
      Hypothesis H_enforces_JLDP_policy:
        enforces_FP_policy job_cost job_task job_jitter sched higher_eq_priority.

      (* Consider task set ts. *)
      Variable ts: taskset_of sporadic_task.

      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.
      (* ... and all jobs come from the taskset. *)
      Hypothesis H_all_jobs_from_taskset:
        forall (j: JobIn arr_seq), job_task j \in ts.

      (* Suppose that jobs are sequential, ...*)
      Hypothesis H_sequential_jobs: sequential_jobs sched.
      (* ... jobs only execute after the jitter, ... *)
      Hypothesis H_jobs_execute_after_jitter:
        jobs_execute_after_jitter job_jitter sched.
      (* ... and jobs do not execute after completion. *)
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      (* Assume that the schedule satisfies the sporadic task model ...*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period arr_seq job_task.

      (* Consider a valid task tsk, ...*)
      Variable tsk: sporadic_task.
      Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.

      (*... whose job j ... *)
      Variable j: JobIn arr_seq.
      Variable H_job_of_tsk: job_task j = tsk.

      (*... is backlogged at time t <= job_arrival j + task_period tsk. *)
      Variable t: time.
      Hypothesis H_j_backlogged: backlogged job_cost job_jitter sched j t.
      Hypothesis H_t_before_period: t < job_arrival j + task_period tsk.

      Let can_interfere_with_tsk := fp_can_interfere_with higher_eq_priority tsk.

      (* Assume that any jobs of higher-priority tasks complete by their period. *)
      Hypothesis H_all_previous_jobs_completed :
        forall (j_other: JobIn arr_seq) tsk_other,
          job_task j_other = tsk_other ->
          can_interfere_with_tsk tsk_other ->
          completed job_cost sched j_other (job_arrival j_other + task_period tsk_other).

      (* Assume that any jobs of tsk prior to j complete by their period. *)
      Hypothesis H_all_previous_jobs_of_tsk_completed :
        forall j0 : JobIn arr_seq,
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + task_period tsk).
      
      Definition scheduled_task_with_higher_eq_priority (tsk tsk_other: sporadic_task) :=
        task_is_scheduled job_task sched tsk_other t &&
        can_interfere_with_tsk tsk_other.
                             
      (* Then, there can be at most one pending job of higher-priority tasks at time t. *)
      Lemma platform_fp_no_multiple_jobs_of_interfering_tasks :
          forall j1 j2,
            pending job_cost job_jitter sched j1 t ->
            pending job_cost job_jitter sched j2 t ->
            job_task j1 = job_task j2 ->
            can_interfere_with_tsk (job_task j1) ->
            j1 = j2.
      Proof.
        unfold sporadic_task_model in *.
        rename H_sporadic_tasks into SPO, H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_all_previous_jobs_completed into PREV.
        intros j1 j2 PENDING1 PENDING2 SAMEtsk INTERF.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF.
        move: PENDING1 PENDING2 => /andP [ARRIVED1 /negP NOTCOMP1] /andP [ARRIVED2 /negP NOTCOMP2].
        destruct (leqP (job_arrival j1) (job_arrival j2)) as [BEFORE1 | BEFORE2].
        {
          specialize (SPO j1 j2 DIFF SAMEtsk BEFORE1).
          assert (LEt: job_arrival j1 + task_period (job_task j1) <= t).
          {
            apply leq_trans with (n := job_arrival j2); first by done.
            by apply leq_trans with (n := job_arrival j2 + job_jitter j2); first by apply leq_addr.
          }
          exploit (PREV j1 (job_task j1)); [by done | by apply INTERF | intros COMP1].
          apply NOTCOMP1.
          by apply completion_monotonic with (t0 := job_arrival j1 + task_period (job_task j1)). 
        }
        {
          apply ltnW in BEFORE2.
          exploit (SPO j2 j1); [by red; ins; subst j2 | by rewrite SAMEtsk | by done | intro SPO'].
          assert (LEt: job_arrival j2 + task_period (job_task j2) <= t).
          {
            apply leq_trans with (n := job_arrival j1); first by done.
            by apply leq_trans with (n := job_arrival j1 + job_jitter j1); first by apply leq_addr.
          }
          exploit (PREV j2 (job_task j2));
            [by done | by rewrite -SAMEtsk | intro COMP2 ].
          apply NOTCOMP2.
          by apply completion_monotonic with (t0 := job_arrival j2 + task_period (job_task j2)).
        }
      Qed.
      
      (* Also, there can be at most one pending job of tsk at time t. *)
      Lemma platform_fp_no_multiple_jobs_of_tsk :
          forall j',
            pending job_cost job_jitter sched j' t ->
            job_task j' = tsk ->
            j' = j.
      Proof.
        unfold sporadic_task_model in *.
        rename H_sporadic_tasks into SPO,
               H_valid_task into PARAMS,
               H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_all_previous_jobs_completed into PREV,
               H_j_backlogged into BACK, H_job_of_tsk into JOBtsk.
        intros j' PENDING' SAMEtsk.
        apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF.
        move: BACK PENDING' => /andP [/andP [ARRIVED /negP NOTCOMP] NOTSCHED]
                               /andP [ARRIVED' /negP NOTCOMP'].
        destruct (leqP (job_arrival j') (job_arrival j)) as [BEFORE | BEFORE'].
        {
          exploit (SPO j' j DIFF); [by rewrite JOBtsk | by done | intro SPO'].
          assert (LEt: job_arrival j' + task_period tsk <= t).
          {
            apply leq_trans with (n := job_arrival j); first by rewrite -SAMEtsk.
            by apply leq_trans with (n := job_arrival j + job_jitter j); first by apply leq_addr.
          }
          apply NOTCOMP'.
          apply completion_monotonic with (t0 := job_arrival j' + task_period tsk); [by done | by done |].
          apply PREVtsk; first by done.
          apply leq_trans with (n := job_arrival j' + task_period tsk); last by rewrite -SAMEtsk.
          rewrite -addn1; apply leq_add; first by done.
          by unfold is_valid_sporadic_task in *; des.
        }
        {
          unfold jitter_has_passed, actual_arrival in *.
          rewrite leqNgt in ARRIVED'; move: ARRIVED' => /negP BUG; apply BUG.
          apply leq_trans with (n := job_arrival j'); last by apply leq_addr.
          apply leq_trans with (n := job_arrival j + task_period tsk); first by done.
          by rewrite -JOBtsk; apply SPO;
            [by red; ins; subst j' | by rewrite SAMEtsk | by apply ltnW].
        }
      Qed.
      
      (* Therefore, all processors are busy with tasks other than tsk. *)
      Lemma platform_fp_cpus_busy_with_interfering_tasks :      
        count (scheduled_task_with_higher_eq_priority tsk) ts = num_cpus.
      Proof.
        have UNIQ := platform_fp_no_multiple_jobs_of_interfering_tasks.
        have UNIQ' := platform_fp_no_multiple_jobs_of_tsk. 
        rename H_all_jobs_from_taskset into FROMTS,
               H_sequential_jobs into SEQUENTIAL,
               H_work_conserving into WORK,
               H_enforces_JLDP_policy into PRIO,
               H_j_backlogged into BACK,
               H_job_of_tsk into JOBtsk,
               H_sporadic_tasks into SPO,
               H_valid_job_parameters into JOBPARAMS,
               H_valid_task into TASKPARAMS,
               H_all_previous_jobs_completed into PREV,
               H_completed_jobs_dont_execute into COMP,
               H_all_previous_jobs_of_tsk_completed into PREVtsk,
               H_jobs_execute_after_jitter into JITTER.
        apply work_conserving_eq_work_conserving_count in WORK.
        unfold valid_sporadic_job, valid_realtime_job,
               enforces_FP_policy, enforces_JLDP_policy, FP_to_JLDP,
               task_precedence_constraints, completed_jobs_dont_execute,
               sporadic_task_model, is_valid_sporadic_task,
               jobs_of_same_task_dont_execute_in_parallel,
               sequential_jobs,
               can_interfere_with_tsk in *.
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        {
          apply leq_trans with (n := count (fun x => task_is_scheduled job_task sched x t) ts);
            first by apply sub_count; red; move => x /andP [SCHED _].
          unfold task_is_scheduled.
          apply count_exists; first by done.
          {
            intros cpu x1 x2 SCHED1 SCHED2.
            destruct (sched cpu t); last by done.
            move: SCHED1 SCHED2 => /eqP SCHED1 /eqP SCHED2.
            by rewrite -SCHED1 -SCHED2.
          }
        }
        {
          rewrite -(WORK j t) // -count_predT.
          apply leq_trans with (n := count (fun j: JobIn arr_seq =>
            scheduled_task_with_higher_eq_priority tsk (job_task j)) (jobs_scheduled_at sched t));
            last first.
          {
            rewrite -count_map.
            apply leq_trans with (n := count predT [seq x <- (map (fun (j: JobIn arr_seq) => job_task j) (jobs_scheduled_at sched t)) | scheduled_task_with_higher_eq_priority tsk x]);
              first  by rewrite count_filter; apply sub_count; red; ins.
            apply leq_trans with (n := count predT [seq x <- ts | scheduled_task_with_higher_eq_priority tsk x]);
              last by rewrite count_predT size_filter.
            apply count_sub_uniqr;
              last first.
            {
              red; intros tsk' IN'.
              rewrite mem_filter in IN'; move: IN' => /andP [SCHED IN'].
              rewrite mem_filter; apply/andP; split; first by done.
              by move: IN' => /mapP [j' _] ->; apply FROMTS.
            }
            {
              rewrite filter_map.
              rewrite map_inj_in_uniq; first by apply filter_uniq, scheduled_jobs_uniq.
              red; intros j1 j2 SCHED1 SCHED2 SAMEtsk.
              rewrite 2!mem_filter in SCHED1 SCHED2.
              move: SCHED1 SCHED2 => /andP [/andP [_ HP1] SCHED1] /andP [/andP [_ HP2] SCHED2].
              rewrite 2!mem_scheduled_jobs_eq_scheduled in SCHED1 SCHED2.
              apply scheduled_implies_pending with (job_cost0 := job_cost)
                      (job_jitter0 := job_jitter) in SCHED1; try (by done).
              apply scheduled_implies_pending with (job_cost0 := job_cost)
                      (job_jitter0 := job_jitter) in SCHED2; try (by done).
              by apply UNIQ.
            }
          }
          {
            apply sub_in_count; intros j' SCHED' _.
            rewrite mem_scheduled_jobs_eq_scheduled in SCHED'.
            apply/andP; split.
            {
              move: SCHED' => /existsP [cpu /eqP SCHED'].
              by apply/existsP; exists cpu; rewrite /task_scheduled_on SCHED' eq_refl.
            }
            apply/andP; split; first by rewrite -JOBtsk; apply PRIO with (t := t).
            {
              apply/eqP; red; intro SAMEtsk.
              generalize SCHED'; intro PENDING'.
              apply scheduled_implies_pending with (job_cost0 := job_cost)
                    (job_jitter0 := job_jitter) in PENDING'; try (by done).
              specialize (UNIQ' j' PENDING' SAMEtsk); subst j'.
              by move: BACK => /andP [_ NOTSCHED]; rewrite SCHED' in NOTSCHED.
            }
          }
        }
      Qed.

    End JobInvariantAsTaskInvariant.

  End Lemmas.
  
End PlatformFP.