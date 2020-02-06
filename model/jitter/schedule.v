Require Import rt.util.all.
Require Import rt.model.jitter.job rt.model.jitter.task rt.model.jitter.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Definition, properties and lemmas about schedules. *)
Module ScheduleWithJitter.

  (* We import the original schedule module and redefine whatever is required. *)
  Require Export rt.model.basic.schedule.
  Export ArrivalSequence Schedule.
  
  (* We need to redefine the properties of a job that depend on the arrival time. *)
  Section ArrivalDependentProperties.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Given an arrival sequence, ... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... we define the following properties for job j in schedule sched. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    Section JobProperties.

      Variable j: JobIn arr_seq.

      (* The actual arrival of job j occurs after the jitter. *)
      Definition actual_arrival := job_arrival j + job_jitter j.

      (* Whether job j's jitter has passed by time t. *)
      Definition jitter_has_passed (t: time) := actual_arrival <= t.

      (* Whether job j actually arrived before time t. *)
      Definition actual_arrival_before (t: time) := actual_arrival < t.

      (* Job j is pending at time t iff the jitter has passed but j has not completed. *)
      Definition pending (t: time) := jitter_has_passed t && ~~ completed job_cost sched j t.

      (* Job j is backlogged at time t iff it is pending and not scheduled. *)
      Definition backlogged (t: time) := pending t && ~~ scheduled sched j t.

      (* Job j is carry-in in interval [t1, t2) iff it arrives before t1 and is
         not complete at time t1 *)
      Definition carried_in (t1: time) := actual_arrival_before t1 && ~~ completed job_cost sched j t1.

      (* Job j is carry-out in interval [t1, t2) iff it arrives after t1 and is
         not complete at time t2 *)
      Definition carried_out (t1 t2: time) := actual_arrival_before t2 && ~~ completed job_cost sched j t2.

    End JobProperties.

    Section ScheduleProperties.

      (* A job can only be scheduled after the jitter has passed. *)
      Definition jobs_execute_after_jitter :=
        forall j t,
          scheduled sched j t -> jitter_has_passed j t.

    End ScheduleProperties.
    
    Section BasicLemmas.

      (* Assume that jobs can only execute after the jitter. *)
      Hypothesis H_jobs_execute_after_jitter:
        jobs_execute_after_jitter.

      Section Pending.
      
        (* Assume that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.

        (* Then, if job j is scheduled, it must be pending. *)
        Lemma scheduled_implies_pending:
          forall j t,
            scheduled sched j t ->
            pending j t.
        Proof.
          rename H_jobs_execute_after_jitter into JITTER,
                 H_completed_jobs into COMP.
          unfold jobs_execute_after_jitter, completed_jobs_dont_execute in *.
          intros j t SCHED.
          unfold pending; apply/andP; split; first by apply JITTER.
          apply/negP; unfold not; intro COMPLETED.
          have BUG := COMP j t.+1.
          rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
          unfold service; rewrite -addn1 big_nat_recr // /=.
          apply leq_add;
            first by move: COMPLETED => /eqP COMPLETED; rewrite -COMPLETED.
          rewrite lt0n; apply/eqP; red; move => /eqP NOSERV.
          rewrite -not_scheduled_no_service in NOSERV.
          by rewrite SCHED in NOSERV.
        Qed.

      End Pending.

      Section Service.
      
        (* If a job only executes after the jitter, it also only
           executes after its arrival time. *)
        Lemma arrival_before_jitter :
          jobs_must_arrive_to_execute sched.
          Proof.
            unfold jobs_execute_after_jitter, jobs_must_arrive_to_execute.
            intros j t SCHED; unfold ArrivalSequence.has_arrived.

            rewrite -(leq_add2r (job_jitter j)).
            by apply leq_trans with (n := t);
              [by apply H_jobs_execute_after_jitter | by apply leq_addr].
          Qed.

        Lemma service_before_jitter_zero :
          forall j t,
            t < job_arrival j + job_jitter j ->
            service_at sched j t = 0.
        Proof.
          rename H_jobs_execute_after_jitter into AFTER; intros j t LT.
          apply/eqP; rewrite -not_scheduled_no_service; apply/negP; red; intro SCHED.
          by apply AFTER, (leq_trans LT) in SCHED; rewrite ltnn in SCHED.
        Qed.

        Lemma cumulative_service_before_jitter_zero :
          forall j t1 t2,
            t2 <= job_arrival j + job_jitter j ->
            \sum_(t1 <= t < t2) service_at sched j t = 0.
        Proof.
          intros j t1 t2 LE.
          apply/eqP; rewrite -leqn0.
          apply leq_trans with (n := \sum_(t1 <= t < t2) 0);
            last by rewrite big_const_nat iter_addn mul0n addn0.
          rewrite big_nat_cond [\sum_(_ <= _ < _)_]big_nat_cond.
          apply leq_sum; move => t /andP [/andP [_ LT] _].
          rewrite leqn0; apply/eqP; apply service_before_jitter_zero.
          by apply (leq_trans LT).
        Qed.

      End Service.
      
    End BasicLemmas.

  End ArrivalDependentProperties.

End ScheduleWithJitter.

(* Specific properties of a schedule of sporadic jobs. *)
Module ScheduleOfSporadicTaskWithJitter.

  Import SporadicTask Job.
  Export ScheduleWithJitter.

  Section ScheduledJobs.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> sporadic_task.
    
    (* Consider any schedule. *)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Given a task tsk, ...*)
    Variable tsk: sporadic_task.

    (* ..., we we can state that tsk is scheduled on cpu at time t as follows. *)
    Definition task_scheduled_on (cpu: processor num_cpus) (t: time) :=
      if (sched cpu t) is Some j then
        (job_task j == tsk)
      else false.

    (* Likewise, we can state that tsk is scheduled on some processor. *)
      Definition task_is_scheduled (t: time) :=
        [exists cpu, task_scheduled_on cpu t].
    
    (* We also define the list of jobs scheduled during [t1, t2). *)
    Definition jobs_of_task_scheduled_between (t1 t2: time) :=
      filter (fun (j: JobIn arr_seq) => job_task j == tsk)
             (jobs_scheduled_between sched t1 t2).
    
  End ScheduledJobs.
  
  Section ScheduleProperties.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.    
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Consider any schedule. *)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Next we define intra-task parallelism, ... *)
    Definition jobs_of_same_task_dont_execute_in_parallel :=
      forall (j j': JobIn arr_seq) t,
        job_task j = job_task j' ->
        scheduled sched j t -> scheduled sched j' t -> j = j'.

    (* ... and task precedence constraints. *)
    Definition task_precedence_constraints :=
      forall (j j': JobIn arr_seq) t,
        job_task j = job_task j' ->
        job_arrival j < job_arrival j' ->
        pending job_cost job_jitter sched j t -> ~~ scheduled sched j' t.
    
  End ScheduleProperties.

  Section BasicLemmas.

    (* Assume the job cost and task are known. *)
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.    
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Then, in a valid schedule of sporadic tasks ...*)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* ...such that jobs do not execute after completion, ...*)
    Hypothesis jobs_dont_execute_after_completion :
       completed_jobs_dont_execute job_cost sched.

    Variable tsk: sporadic_task.
    
    Variable j: JobIn arr_seq.
    Hypothesis H_job_of_task: job_task j = tsk.
    Hypothesis valid_job:
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    
    (* Remember that for any job of tsk, service <= task_cost tsk *)
    Lemma cumulative_service_le_task_cost :
        forall t t',
          service_during sched j t t' <= task_cost tsk.
    Proof.
      rename valid_job into VALID; unfold valid_sporadic_job in *; ins; des.
      apply leq_trans with (n := job_cost j);
        last by rewrite -H_job_of_task; apply VALID0.
      by apply cumulative_service_le_job_cost.
    Qed.

  End BasicLemmas.
  
End ScheduleOfSporadicTaskWithJitter.