Require Import rt.util.all.
Require Import rt.model.jitter.job rt.model.jitter.task
               rt.model.jitter.schedule rt.model.jitter.schedulability
               rt.model.jitter.priority rt.model.jitter.platform.
Require Import rt.analysis.jitter.workload_bound
               rt.analysis.jitter.interference_bound_edf
               rt.analysis.jitter.bertogna_edf_comp.
Require Import rt.implementation.jitter.job
               rt.implementation.jitter.task
               rt.implementation.jitter.schedule
               rt.implementation.jitter.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq bigop div.

Module ResponseTimeAnalysisEDF.

  Import JobWithJitter ScheduleWithJitter SporadicTaskset Priority Schedulability Platform InterferenceBoundEDFJitter WorkloadBoundJitter ResponseTimeIterationEDF.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  Section ExampleRTA.

    Let tsk1 := {| task_id := 1; task_cost := 2; task_period := 5; task_deadline := 3; task_jitter := 1|}.
    Let tsk2 := {| task_id := 2; task_cost := 4; task_period := 6; task_deadline := 5; task_jitter := 0|}.
    Let tsk3 := {| task_id := 3; task_cost := 2; task_period := 12; task_deadline := 11; task_jitter := 2|}.

    (* Let ts be a task set containing these three tasks. *)
    Let ts := [:: tsk1; tsk2; tsk3].

    Section FactsAboutTaskset.

      Fact ts_is_a_set: uniq ts.
      Proof.
        by compute.
      Qed.
      
      Fact ts_has_valid_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.
      Proof.
        intros tsk IN.
        repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
      Qed.

      Fact ts_has_constrained_deadlines:
        forall tsk,
          tsk \in ts ->
          task_deadline tsk <= task_period tsk.
      Proof.
        intros tsk IN.
        repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute); by done.
      Qed.
      
    End FactsAboutTaskset.

    (* Assume there are two processors. *)
    Let num_cpus := 2.

    (* Recall the EDF RTA schedulability test. *)
    Let schedulability_test :=
      edf_schedulable task_cost task_period task_deadline task_jitter num_cpus.

    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      unfold schedulability_test, edf_schedulable, edf_claimed_bounds; desf.
      apply negbT in Heq; move: Heq => /negP ALL.
      exfalso; apply ALL; clear ALL.
      assert (STEPS: \sum_(tsk <- ts) (task_deadline tsk - task_cost tsk) + 1 = 12).
      {
        by rewrite unlock; compute.
      } rewrite STEPS; clear STEPS.
      
      Ltac f :=
        unfold edf_rta_iteration; simpl;
        unfold edf_response_time_bound, div_floor, total_interference_bound_edf, interference_bound_edf, interference_bound_generic, W_jitter; simpl;
        repeat rewrite addnE;
        repeat rewrite big_cons; repeat rewrite big_nil;
        repeat rewrite addnE; simpl;
        unfold num_cpus, divn; simpl.

      rewrite [edf_rta_iteration]lock; simpl.

      unfold locked at 12; destruct master_key; f.
      unfold locked at 11; destruct master_key; f.
      unfold locked at 10; destruct master_key; f.
      unfold locked at 9; destruct master_key; f.
      unfold locked at 8; destruct master_key; f.
      unfold locked at 7; destruct master_key; f.
      unfold locked at 6; destruct master_key; f.
      unfold locked at 5; destruct master_key; f.
      unfold locked at 4; destruct master_key; f.
      unfold locked at 3; destruct master_key; f.
      unfold locked at 2; destruct master_key; f.
      by unfold locked at 1; destruct master_key; f.
    Qed.

    (* Let arr_seq be the periodic arrival sequence from ts. *)
    Let arr_seq := periodic_arrival_sequence ts.

    (* Let sched be the work-conserving EDF scheduler. *)
    Let sched := scheduler job_cost job_jitter num_cpus arr_seq (EDF job_deadline).

    (* Recall the definition of deadline miss. *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_cost job_deadline job_task sched.

    (* Next, we prove that ts is schedulable with the result of the test. *)
    Corollary ts_is_schedulable:
      forall tsk,
        tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
      intros tsk IN.
      have VALID := periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters.
      have EDFVALID := @edf_valid_policy _ arr_seq job_deadline.
      unfold valid_JLDP_policy, valid_sporadic_job_with_jitter,
             valid_sporadic_job, valid_realtime_job in *; des.
      apply taskset_schedulable_by_edf_rta with (task_cost := task_cost) (task_period := task_period) (task_deadline := task_deadline) (ts0 := ts) (task_jitter := task_jitter) (job_jitter := job_jitter).
      - by apply ts_is_a_set.
      - by apply ts_has_valid_parameters. 
      - by apply ts_has_constrained_deadlines.
      - by apply periodic_arrivals_all_jobs_from_taskset.
      - by apply periodic_arrivals_valid_job_parameters, ts_has_valid_parameters.
      - by apply periodic_arrivals_are_sporadic.
      - by compute.
      - by apply scheduler_jobs_execute_after_jitter.
      - apply scheduler_completed_jobs_dont_execute; intro j'.
        -- by specialize (VALID j'); des.
        -- by apply periodic_arrivals_is_a_set.
      - by apply scheduler_sequential_jobs, periodic_arrivals_is_a_set.
      - by apply scheduler_work_conserving.
      - by apply scheduler_enforces_policy; ins.
      - by apply schedulability_test_succeeds.
      - by apply IN.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisEDF.