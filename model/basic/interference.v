Require Import rt.util.all.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.schedule
               rt.model.basic.priority rt.model.basic.workload.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Interference.

  Import Schedule ScheduleOfSporadicTask Priority Workload.

  Section PossibleInterferingTasks.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Section FP.

      (* Assume an FP policy. *)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* Under constrained deadlines, tsk_other can only interfere with tsk
         if it's a different task with higher or equal priority. *)
      Definition fp_can_interfere_with (tsk tsk_other: sporadic_task) :=
        higher_eq_priority tsk_other tsk && (tsk_other != tsk).

    End FP.

    Section JLFP.

      (* Under JLFP/JLDP policies, any two different tasks can interfere with
         each other. *)
      Definition jldp_can_interfere_with (tsk tsk_other: sporadic_task) :=
        tsk_other != tsk.

    End JLFP.
    
  End PossibleInterferingTasks.
  
  Section InterferenceDefs.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Assume any job arrival sequence...*)
    Context {arr_seq: arrival_sequence Job}.

    (* ... and any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Consider any job j that incurs interference. *)
    Variable j: JobIn arr_seq.

    (* Recall the definition of backlogged (pending and not scheduled). *)
    Let job_is_backlogged (t: time) :=
      backlogged job_cost sched j t.

    Section TotalInterference.
      
      (* First, we define the total interference incurred by job j during [t1, t2)
         as the cumulative time in which j is backlogged in this interval. *)
      Definition total_interference (t1 t2: time) :=
        \sum_(t1 <= t < t2) job_is_backlogged t.

    End TotalInterference.
    
    Section JobInterference.

      (* Let job_other be a job that interferes with j. *)
      Variable job_other: JobIn arr_seq.

      (* We define the total interference caused by job_other during [t1, t2) as the
         cumulative service received by job_other while j is backlogged. *)
      Definition job_interference (t1 t2: time) :=
        \sum_(t1 <= t < t2)
          \sum_(cpu < num_cpus)
            (job_is_backlogged t && scheduled_on sched job_other cpu t).

    End JobInterference.

    Section TaskInterference.

      (* In order to define task interference, consider any interfering task tsk_other. *)
      Variable tsk_other: sporadic_task.
      
      (* We define the total interference caused by tsk during [t1, t2) as
         the cumulative service received by tsk while j is backlogged. *)
      Definition task_interference (t1 t2: time) :=
        \sum_(t1 <= t < t2)
          \sum_(cpu < num_cpus)
            (job_is_backlogged t &&
            task_scheduled_on job_task sched tsk_other cpu t).

    End TaskInterference.

    Section TaskInterferenceJobList.

      Variable tsk_other: sporadic_task.

      Definition task_interference_joblist (t1 t2: time) :=
        \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_other)
         job_interference j t1 t2.

    End TaskInterferenceJobList.

    Section BasicLemmas.

      (* Interference cannot be larger than the considered time window. *)
      Lemma total_interference_le_delta :
        forall t1 t2,
          total_interference t1 t2 <= t2 - t1.
      Proof.
        unfold total_interference; intros t1 t2.
        apply leq_trans with (n := \sum_(t1 <= t < t2) 1);
          first by apply leq_sum; ins; apply leq_b1.
        by rewrite big_const_nat iter_addn mul1n addn0 leqnn.
      Qed.

      Lemma job_interference_le_service :
        forall j_other t1 t2,
          job_interference j_other t1 t2 <= service_during sched j_other t1 t2.
      Proof.
        intros j_other t1 t2; unfold job_interference, service_during.
        apply leq_sum; intros t _.
        unfold service_at; rewrite [\sum_(_ < _ | scheduled_on _ _ _  _)_]big_mkcond.
        apply leq_sum; intros cpu _.
        destruct (job_is_backlogged t); [rewrite andTb | by rewrite andFb].
        by destruct (scheduled_on sched j_other cpu t).
      Qed.
      
      Lemma task_interference_le_workload :
        forall tsk t1 t2,
          task_interference tsk t1 t2 <= workload job_task sched tsk t1 t2.
      Proof.
        unfold task_interference, workload; intros tsk t1 t2.
        apply leq_sum; intros t _.
        apply leq_sum; intros cpu _.
        destruct (job_is_backlogged t); [rewrite andTb | by rewrite andFb].
        unfold task_scheduled_on, service_of_task.
        by destruct (sched cpu t).
      Qed.

    End BasicLemmas.

    Section InterferenceSequentialJobs.

      (* If jobs are sequential, ... *)
      Hypothesis H_sequential_jobs: sequential_jobs sched.
    
      (* ... then the interference incurred by a job in an interval
         of length delta is at most delta. *)
      Lemma job_interference_le_delta :
        forall j_other t1 delta,
          job_interference j_other t1 (t1 + delta) <= delta.
      Proof.
        rename H_sequential_jobs into SEQ.
        unfold job_interference, sequential_jobs in *.
        intros j_other t1 delta.
        apply leq_trans with (n := \sum_(t1 <= t < t1 + delta) 1);
          last by rewrite big_const_nat iter_addn mul1n addn0 addKn leqnn.
        apply leq_sum; intros t _.
        destruct ([exists cpu, scheduled_on sched j_other cpu t]) eqn:EX.
        {
          move: EX => /existsP [cpu SCHED].
          rewrite (bigD1 cpu) // /=.
          rewrite big_mkcond (eq_bigr (fun x => 0)) /=;
            first by simpl_sum_const; rewrite leq_b1.
          intros cpu' _; des_if_goal; last by done.
          destruct (scheduled_on sched j_other cpu' t) eqn:SCHED'; last by rewrite andbF.
          move: SCHED SCHED' => /eqP SCHED /eqP SCHED'.
          by specialize (SEQ j_other t cpu cpu' SCHED SCHED'); rewrite SEQ in Heq.
        }
        {
          apply negbT in EX; rewrite negb_exists in EX.
          move: EX => /forallP EX.
          rewrite (eq_bigr (fun x => 0)); first by simpl_sum_const.
          by intros cpu _; specialize (EX cpu); apply negbTE in EX; rewrite EX andbF.
        }
      Qed.

    End InterferenceSequentialJobs.

    (* The sequential per-job interference bounds the actual interference. *)    
    Section BoundUsingPerJobInterference.
      
      Lemma interference_le_interference_joblist :
        forall tsk t1 t2,
          task_interference tsk t1 t2 <= task_interference_joblist tsk t1 t2.
      Proof.
        intros tsk t1 t2.
        unfold task_interference, task_interference_joblist, job_interference, job_is_backlogged.
        rewrite [\sum_(_ <- _ sched _ _ | _) _]exchange_big /=.
        rewrite big_nat_cond [\sum_(_ <= _ < _ | true) _]big_nat_cond.
        apply leq_sum; move => t /andP [LEt _].
        rewrite exchange_big /=.
        apply leq_sum; intros cpu _.
        destruct (backlogged job_cost sched j t) eqn:BACK;      
          last by rewrite andFb (eq_bigr (fun x => 0));
            first by rewrite big_const_seq iter_addn mul0n addn0.
        rewrite andTb.
        destruct (task_scheduled_on job_task sched tsk cpu t) eqn:SCHED; last by done.
        unfold scheduled_on, task_scheduled_on in *.
        destruct (sched cpu t) as [j' |] eqn:SOME; last by done.
        rewrite big_mkcond /= (bigD1_seq j') /=; last by apply undup_uniq.
        {
          by rewrite SCHED eq_refl.
        }
        {
          unfold jobs_scheduled_between.
          rewrite mem_undup; apply mem_bigcat_nat with (j := t);
            first by done.
          apply mem_bigcat_ord with (j := cpu); first by apply ltn_ord.
          by unfold make_sequence; rewrite SOME mem_seq1 eq_refl.
        }
      Qed.
        
    End BoundUsingPerJobInterference.
    
  End InterferenceDefs.

End Interference.