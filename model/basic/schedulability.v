Require Import rt.util.all.
Require Import rt.model.basic.job rt.model.basic.task rt.model.basic.schedule.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq bigop.

(* Definitions of deadline miss. *)
Module Schedulability.

  Import Schedule SporadicTaskset Job.

  Section SchedulableDefs.

    (* Assume that the cost and deadline of a job is known. *)
    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
  
    Section ScheduleOfJobs.

      (* For any job j in schedule sched, ...*)
      Context {num_cpus: nat}.
      Variable sched: schedule num_cpus arr_seq.

      Variable j: JobIn arr_seq.

      (* job j misses no deadline in sched if it completed by its absolute deadline. *)
      Definition job_misses_no_deadline :=
        completed job_cost sched j (job_arrival j + job_deadline j).

    End ScheduleOfJobs.

    Section ScheduleOfTasks.

      Context {sporadic_task: eqType}.
      Variable job_task: Job -> sporadic_task.
    
      Context {num_cpus: nat}.
      Variable sched: schedule num_cpus arr_seq.

      (* Consider any task tsk. *)
      Variable tsk: sporadic_task.

      (* Task tsk doesn't miss its deadline iff all of its jobs don't miss their deadline. *)
      Definition task_misses_no_deadline :=
        forall (j: JobIn arr_seq),
          job_task j = tsk ->
          job_misses_no_deadline sched j.

      (* Task tsk doesn't miss its deadline before time t' iff all of its jobs don't miss
         their deadline by that time. *)
      Definition task_misses_no_deadline_before (t': time) :=
        forall (j: JobIn arr_seq),
          job_task j = tsk ->
          job_arrival j + job_deadline j < t' ->
          job_misses_no_deadline sched j.

    End ScheduleOfTasks.

  End SchedulableDefs.

  Section BasicLemmas.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    Context {arr_seq: arrival_sequence Job}.
    
    (* Consider any valid schedule... *)
    Context {num_cpus : nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* ... where jobs dont execute after completion. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    Section SpecificJob.

      (* Then, for any job j ...*)
      Variable j: JobIn arr_seq.
      
      (* ...that doesn't miss a deadline in this schedule, ... *)
      Hypothesis no_deadline_miss:
        job_misses_no_deadline job_cost job_deadline sched j.

      (* the service received by j at any time t' after its deadline is 0. *)
      Lemma service_after_job_deadline_zero :
        forall t',
          t' >= job_arrival j + job_deadline j ->
          service_at sched j t' = 0.
      Proof.
        intros t' LE.
        rename no_deadline_miss into NOMISS,
               H_completed_jobs_dont_execute into EXEC.
        unfold job_misses_no_deadline, completed, completed_jobs_dont_execute in *.
        apply/eqP; rewrite -leqn0.
        rewrite <- leq_add2l with (p := job_cost j).
        move: NOMISS => /eqP NOMISS; rewrite -{1}NOMISS addn0.
        apply leq_trans with (n := service sched j t'.+1); last by apply EXEC.
        unfold service; rewrite -> big_cat_nat with
                                   (p := t'.+1) (n := job_arrival j + job_deadline j);
            [rewrite leq_add2l /= | by ins | by apply ltnW].
          by rewrite big_nat_recr // /=; apply leq_addl.
      Qed.

      (* The same applies for the cumulative service of job j. *)
      Lemma cumulative_service_after_job_deadline_zero :
        forall t' t'',
          t' >= job_arrival j + job_deadline j ->
          \sum_(t' <= t < t'') service_at sched j t = 0.
      Proof.
        ins; apply/eqP; rewrite -leqn0.
        rewrite big_nat_cond; rewrite -> eq_bigr with (F2 := fun i => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
        intro i; rewrite andbT; move => /andP [LE _].
        by rewrite service_after_job_deadline_zero;
          [by ins | by apply leq_trans with (n := t')].
      Qed.
      
    End SpecificJob.
    
    Section AllJobs.

      (* Consider any task tsk ...*)
      Variable tsk: sporadic_task.

      (* ... that doesn't miss any deadline. *)
      Hypothesis no_deadline_misses:
        task_misses_no_deadline job_cost job_deadline job_task sched tsk.

      (* Then, for any valid job j of this task, ...*)
      Variable j: JobIn arr_seq.
      Hypothesis H_job_of_task: job_task j = tsk.
      Hypothesis H_valid_job:
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
      
      (* the service received by job j at any time t' after the deadline is 0. *)
      Lemma service_after_task_deadline_zero :
        forall t',
          t' >= job_arrival j + task_deadline tsk ->
          service_at sched j t' = 0.
      Proof.
        rename H_valid_job into PARAMS; unfold valid_sporadic_job in *; des; intros t'.
        rewrite -H_job_of_task -PARAMS1.
        by apply service_after_job_deadline_zero, no_deadline_misses.
      Qed.

      (* The same applies for the cumulative service of job j. *)
      Lemma cumulative_service_after_task_deadline_zero :
        forall t' t'',
          t' >= job_arrival j + task_deadline tsk ->
          \sum_(t' <= t < t'') service_at sched j t = 0.
      Proof.
        rename H_valid_job into PARAMS; unfold valid_sporadic_job in *; des; intros t' t''.
        rewrite -H_job_of_task -PARAMS1.
        by apply cumulative_service_after_job_deadline_zero, no_deadline_misses.
      Qed.
      
    End AllJobs.

  End BasicLemmas.

End Schedulability.