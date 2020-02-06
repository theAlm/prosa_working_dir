Require Import rt.util.all.
Require Import rt.model.basic.job rt.model.basic.task rt.model.basic.schedule
               rt.model.basic.task_arrival rt.model.basic.response_time
               rt.model.basic.schedulability.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq div fintype bigop path.

Module Workload.

  Import Job SporadicTaskset Schedule ScheduleOfSporadicTask SporadicTaskArrival ResponseTime Schedulability.

  (* Let's define the workload. *)
  Section WorkloadDef.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> sporadic_task.
    Context {arr_seq: arrival_sequence Job}.
    
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Consider some task *)
    Variable tsk: sporadic_task.

    (* First, we define a function that returns the amount of service
       received by this task in a particular processor. *)
    Definition service_of_task (cpu: processor num_cpus)
                               (j: option (JobIn arr_seq)) : time :=
      match j with
        | Some j' => (job_task j' == tsk)
        | None => 0
      end.

    (* Next, workload is defined as the service received by jobs of
       the task in the interval [t1,t2). *)
    Definition workload (t1 t2: time) :=
      \sum_(t1 <= t < t2)
        \sum_(cpu < num_cpus)
          service_of_task cpu (sched cpu t).
 
    (* Now, we define workload by summing up the cumulative service
       during [t1,t2) of the scheduled jobs, but only those spawned
       by the task that we care about. *)
    Definition workload_joblist (t1 t2: time) :=
      \sum_(j <- jobs_of_task_scheduled_between job_task sched tsk t1 t2)
        service_during sched j t1 t2.

    (* Next, we show that the two definitions are equivalent. *)
    Lemma workload_eq_workload_joblist :
      forall t1 t2,
      workload t1 t2 = workload_joblist t1 t2.
    Proof.
      intros t1 t2; unfold workload, workload_joblist, service_during.
      rewrite big_filter [\sum_(j <- jobs_scheduled_between _ _ _ | _) _]exchange_big /=.
      apply eq_big_nat; unfold service_at; intros t LEt.
      rewrite [\sum_(i <- jobs_scheduled_between _ _ _ | _) _](eq_bigr (fun i =>
               \sum_(cpu < num_cpus) (sched cpu t == Some i)));
        last by ins; rewrite big_mkcond; apply eq_bigr; ins; rewrite mulnbl.
      rewrite exchange_big /=; apply eq_bigr.
      intros cpu LEcpu; rewrite -big_filter.
      destruct (sched cpu t) eqn:SCHED; simpl;
        last by rewrite big_const_seq iter_addn mul0n addn0. 
      destruct (job_task j == tsk) eqn:EQtsk;
        try rewrite mul1n; try rewrite mul0n.
      {  
        rewrite -> bigD1_seq with (j := j); last by rewrite filter_undup undup_uniq.
        { 
          rewrite -> eq_bigr with (F2 := fun i => 0); last first.
          {
            intros i DIFF.
            destruct (Some j == Some i) eqn:SOME; rewrite SOME; last by done.
            move: SOME => /eqP SOME; inversion SOME as [EQ].
            by rewrite EQ eq_refl in DIFF.
          }
          by rewrite /= big_const_seq iter_addn mul0n 2!addn0 eq_refl.
        }
        {
          rewrite mem_filter; apply/andP; split; first by ins.
          rewrite mem_undup.
          apply mem_bigcat_nat with (j := t); first by ins.
          apply mem_bigcat_ord with (j := cpu); first by apply ltn_ord.
          by rewrite SCHED inE; apply/eqP.
        }
      }
      {
        rewrite big_filter; rewrite -> eq_bigr with (F2 := fun i => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0.
        intros i EQtsk2; destruct (Some j == Some i) eqn:SOME; last by done.
        move: SOME => /eqP SOME; inversion SOME; subst.
        by rewrite EQtsk2 in EQtsk. 
      }
    Qed.
 
  End WorkloadDef.

End Workload.
