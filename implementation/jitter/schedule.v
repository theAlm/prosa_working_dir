Require Import rt.util.all.
Require Import rt.model.jitter.job rt.model.jitter.arrival_sequence rt.model.jitter.schedule
               rt.model.jitter.platform rt.model.jitter.priority.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import Job ArrivalSequence ScheduleWithJitter Platform Priority.
  
  Section Implementation.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Let num_cpus denote the number of processors, ...*)
    Variable num_cpus: nat.

    (* ... and let arr_seq be any arrival sequence.*)
    Variable arr_seq: arrival_sequence Job.

    (* Assume a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.

    (* Consider the list of pending jobs at time t. *)
    Definition jobs_pending_at (sched: schedule num_cpus arr_seq) (t: time) :=
      [seq j <- jobs_arrived_up_to arr_seq t | pending job_cost job_jitter sched j t].

    (* Next, we sort this list by priority. *)
    Definition sorted_pending_jobs (sched: schedule num_cpus arr_seq) (t: time) :=
      sort (higher_eq_priority t) (jobs_pending_at sched t).

    (* Starting from the empty schedule as a base, ... *)
    Definition empty_schedule : schedule num_cpus arr_seq :=
      fun t cpu => None.

    (* ..., we redefine the mapping of jobs to processors at any time t as follows.
       The i-th job in the sorted list is assigned to the i-th cpu, or to None
       if the list is short. *)
    Definition update_schedule (prev_sched: schedule num_cpus arr_seq)
                               (t_next: time) : schedule num_cpus arr_seq :=
      fun cpu t =>
        if t == t_next then
          nth_or_none (sorted_pending_jobs prev_sched t) cpu
        else prev_sched cpu t.
    
    (* The schedule is iteratively constructed by applying assign_jobs at every time t, ... *)
    Fixpoint schedule_prefix (t_max: time) : schedule num_cpus arr_seq := 
      if t_max is t_prev.+1 then
        (* At time t_prev + 1, schedule jobs that have not completed by time t_prev. *)
        update_schedule (schedule_prefix t_prev) t_prev.+1
      else
        (* At time 0, schedule any jobs that arrive. *)
        update_schedule empty_schedule 0.

    Definition scheduler (cpu: processor num_cpus) (t: time) := (schedule_prefix t) cpu t.

  End Implementation.

  Section Proofs.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Assume a positive number of processors. *)
    Variable num_cpus: nat.
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Let arr_seq be any arrival sequence of jobs where ...*)
    Variable arr_seq: arrival_sequence Job.
    (* ...jobs have positive cost and...*)
    Hypothesis H_job_cost_positive:
      forall (j: JobIn arr_seq), job_cost_positive job_cost j.
    (* ... at any time, there are no duplicates of the same job. *)
    Hypothesis H_arrival_sequence_is_a_set :
      arrival_sequence_is_a_set arr_seq.

    (* Consider any JLDP policy higher_eq_priority that is transitive and total. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.
    Hypothesis H_priority_transitive: forall t, transitive (higher_eq_priority t).
    Hypothesis H_priority_total: forall t, total (higher_eq_priority t).

    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_cost job_jitter num_cpus arr_seq higher_eq_priority.

    (* Next, we provide some helper lemmas about the scheduler construction. *)
    Section HelperLemmas.
      
      (* First, we show that the scheduler preserves its prefixes. *)
      Lemma scheduler_same_prefix :
        forall t t_max cpu,
          t <= t_max ->
          schedule_prefix job_cost job_jitter num_cpus arr_seq higher_eq_priority t_max cpu t =
          scheduler job_cost job_jitter num_cpus arr_seq higher_eq_priority cpu t.
      Proof.
        intros t t_max cpu LEt.
        induction t_max.
        {
          by rewrite leqn0 in LEt; move: LEt => /eqP EQ; subst.
        }
        {
          rewrite leq_eqVlt in LEt.
          move: LEt => /orP [/eqP EQ | LESS]; first by subst.
          {
            feed IHt_max; first by done.
            unfold schedule_prefix, update_schedule at 1.
            assert (FALSE: t == t_max.+1 = false).
            {
              by apply negbTE; rewrite neq_ltn LESS orTb.
            } rewrite FALSE.
            by rewrite -IHt_max.
          }
        }
      Qed.

      (* With respect to the sorted list of pending jobs, ...*)
      Let sorted_jobs (t: time) :=
        sorted_pending_jobs job_cost job_jitter num_cpus arr_seq higher_eq_priority sched t.

      (* ..., we show that a job is mapped to a processor based on that list, ... *)
      Lemma scheduler_nth_or_none_mapping :
        forall t cpu x,
          sched cpu t = x ->
          nth_or_none (sorted_jobs t) cpu = x.
      Proof.
        intros t cpu x SCHED.
        unfold sched, scheduler, schedule_prefix in *.
        destruct t.
        {
          unfold update_schedule in SCHED; rewrite eq_refl in SCHED.
          rewrite -SCHED; f_equal.
          unfold sorted_jobs, sorted_pending_jobs; f_equal.
          unfold jobs_pending_at; apply eq_filter; red; intro j'.
          unfold pending; f_equal; f_equal.
          unfold completed, service.
          by rewrite big_geq // big_geq //.
        }
        {
          unfold update_schedule at 1 in SCHED; rewrite eq_refl in SCHED.
          rewrite -SCHED; f_equal.
          unfold sorted_jobs, sorted_pending_jobs; f_equal.
          unfold jobs_pending_at; apply eq_filter; red; intro j'.
          unfold pending; f_equal; f_equal.
          unfold completed, service; f_equal.
          apply eq_big_nat; move => t0 /andP [_ LT].
          unfold service_at; apply eq_bigl; red; intros cpu'.
          unfold scheduled_on; f_equal.
          fold (schedule_prefix job_cost job_jitter num_cpus arr_seq higher_eq_priority).
          by rewrite 2?scheduler_same_prefix ?leqnn //.
        }
      Qed.
      
      (* ..., a scheduled job is mapped to a cpu corresponding to its position, ... *)
      Lemma scheduler_nth_or_none_scheduled :
        forall j t,
          scheduled sched j t ->
          exists (cpu: processor num_cpus),
            nth_or_none (sorted_jobs t) cpu = Some j. 
      Proof.
        move => j t /existsP [cpu /eqP SCHED]; exists cpu.
        by apply scheduler_nth_or_none_mapping.
      Qed.

      (* ..., and that a backlogged job has a position larger than or equal to the number
         of processors. *)
      Lemma scheduler_nth_or_none_backlogged :
        forall j t,
          backlogged job_cost job_jitter sched j t ->
          exists i,
            nth_or_none (sorted_jobs t) i = Some j /\ i >= num_cpus.
      Proof.
        intros j t BACK.
        move: BACK => /andP [PENDING /negP NOTCOMP].
        assert (IN: j \in sorted_jobs t).
        {
          rewrite mem_sort mem_filter PENDING andTb.
          move: PENDING => /andP [ARRIVED _].
          rewrite JobIn_has_arrived.
          by apply leq_trans with (n := job_arrival j + job_jitter j);
            first by apply leq_addr.
        }
        apply nth_or_none_mem_exists in IN; des.
        exists n; split; first by done.
        rewrite leqNgt; apply/negP; red; intro LT.
        apply NOTCOMP; clear NOTCOMP PENDING.
        apply/existsP; exists (Ordinal LT); apply/eqP.
        unfold sorted_jobs in *; clear sorted_jobs.
        unfold sched, scheduler, schedule_prefix in *; clear sched.
        destruct t. 
        {
          unfold update_schedule; rewrite eq_refl.
          rewrite -IN; f_equal.
          fold (schedule_prefix job_cost job_jitter num_cpus arr_seq higher_eq_priority).
          unfold sorted_pending_jobs; f_equal.
          apply eq_filter; red; intros x.
          unfold pending; f_equal; f_equal.
          unfold completed; f_equal.
          by unfold service; rewrite 2?big_geq //.
        }
        {
          unfold update_schedule at 1; rewrite eq_refl.
          rewrite -IN; f_equal.
          unfold sorted_pending_jobs; f_equal.
          apply eq_filter; red; intros x.
          unfold pending; f_equal; f_equal.
          unfold completed; f_equal.
          unfold service; apply eq_big_nat; move => i /andP [_ LTi].
          unfold service_at; apply eq_bigl; red; intro cpu.
          unfold scheduled_on; f_equal.
          fold (schedule_prefix job_cost job_jitter num_cpus arr_seq higher_eq_priority).
          by rewrite scheduler_same_prefix //.
        }
      Qed.

    End HelperLemmas.

    (* Now, we prove the important properties about the implementation. *)
    
    (* Jobs do not execute before the jitter, ...*)
    Theorem scheduler_jobs_execute_after_jitter:
      jobs_execute_after_jitter job_jitter sched.
    Proof.
      unfold jobs_must_arrive_to_execute.
      intros j t SCHED.
      move: SCHED => /existsP [cpu /eqP SCHED].
      unfold sched, scheduler, schedule_prefix in SCHED.
      destruct t.
      {
        rewrite /update_schedule eq_refl in SCHED.
        apply (nth_or_none_mem _ cpu j) in SCHED.
        rewrite mem_sort mem_filter in SCHED.
        by move: SCHED => /andP [/andP [PENDING _] _]. 
      }
      {
        unfold update_schedule at 1 in SCHED; rewrite eq_refl /= in SCHED.
        apply (nth_or_none_mem _ cpu j) in SCHED.
        rewrite mem_sort mem_filter in SCHED.
        by move: SCHED => /andP [/andP [PENDING _] _].
      }
    Qed.

    (* ..., jobs are sequential, ... *)
    Theorem scheduler_sequential_jobs: sequential_jobs sched.
    Proof.
      unfold sequential_jobs, sched, scheduler, schedule_prefix.
      intros j t cpu1 cpu2 SCHED1 SCHED2.
      destruct t; rewrite /update_schedule eq_refl in SCHED1 SCHED2;
      have UNIQ := nth_or_none_uniq _ cpu1 cpu2 j _ SCHED1 SCHED2; (apply ord_inj, UNIQ);
      rewrite sort_uniq filter_uniq //;
      by apply JobIn_uniq.
    Qed.
               
    (* ... and jobs do not execute after completion. *)
    Theorem scheduler_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.
    Proof.
      rename H_job_cost_positive into GT0.
      unfold completed_jobs_dont_execute, service.
      intros j t.
      induction t; first by rewrite big_geq.
      {
        rewrite big_nat_recr // /=.
        rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LESS]; last first.
        {
          destruct (job_cost j); first by rewrite ltn0 in LESS.
          rewrite -addn1; rewrite ltnS in LESS.
          apply leq_add; first by done.
          by apply service_at_most_one, scheduler_sequential_jobs.
        }
        rewrite EQ -{2}[job_cost j]addn0; apply leq_add; first by done.
        destruct t.
        {
          rewrite big_geq // in EQ.
          specialize (GT0 j); unfold job_cost_positive in *.
          by rewrite -EQ ltn0 in GT0.
        }
        {
          unfold service_at; rewrite big_mkcond.
          apply leq_trans with (n := \sum_(cpu < num_cpus) 0);
            last by rewrite big_const_ord iter_addn mul0n addn0.
          apply leq_sum; intros cpu _; desf.
          move: Heq => /eqP SCHED.
          unfold scheduler, schedule_prefix in SCHED.
          unfold sched, scheduler, schedule_prefix, update_schedule at 1 in SCHED.
          rewrite eq_refl in SCHED.
          apply (nth_or_none_mem _ cpu j) in SCHED.
          rewrite mem_sort mem_filter in SCHED.
          fold (update_schedule job_cost job_jitter num_cpus arr_seq higher_eq_priority) in SCHED.
          move: SCHED => /andP [/andP [_ /negP NOTCOMP] _].
          exfalso; apply NOTCOMP; clear NOTCOMP.
          unfold completed; apply/eqP.
          unfold service; rewrite -EQ.
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
          apply eq_bigr; move => i /andP [/andP [_ LT] _].
          apply eq_bigl; red; ins.
          unfold scheduled_on; f_equal.
          fold (schedule_prefix job_cost job_jitter num_cpus arr_seq higher_eq_priority).
          by rewrite scheduler_same_prefix.
        }
      }
    Qed.

    (* In addition, the scheduler is work conserving ... *)
    Theorem scheduler_work_conserving:
      work_conserving job_cost job_jitter sched.
    Proof.
      unfold work_conserving; intros j t BACK cpu.
      set jobs := sorted_pending_jobs job_cost job_jitter num_cpus arr_seq higher_eq_priority sched t.
      destruct (sched cpu t) eqn:SCHED; first by exists j0; apply/eqP.
      apply scheduler_nth_or_none_backlogged in BACK.
      destruct BACK as [cpu_out [NTH GE]].
      exfalso; rewrite leqNgt in GE; move: GE => /negP GE; apply GE.
      apply leq_ltn_trans with (n := cpu); last by done.
      apply scheduler_nth_or_none_mapping in SCHED.
      apply nth_or_none_size_none in SCHED.
      apply leq_trans with (n := size jobs); last by done.
      by apply nth_or_none_size_some in NTH; apply ltnW.
    Qed.

    (* ... and enforces the JLDP policy. *)
    Theorem scheduler_enforces_policy :
      enforces_JLDP_policy job_cost job_jitter sched higher_eq_priority.
    Proof.
      unfold enforces_JLDP_policy; intros j j_hp t BACK SCHED.
      set jobs := sorted_pending_jobs job_cost job_jitter num_cpus arr_seq higher_eq_priority sched t.
      apply scheduler_nth_or_none_backlogged in BACK.
      destruct BACK as [cpu_out [SOME GE]].
      apply scheduler_nth_or_none_scheduled in SCHED.
      destruct SCHED as [cpu SCHED].
      have EQ1 := nth_or_none_nth jobs cpu j_hp j SCHED.
      have EQ2 := nth_or_none_nth jobs cpu_out j j SOME.
      rewrite -EQ1 -{2}EQ2.
      apply sorted_lt_idx_implies_rel; [by done | by apply sort_sorted | |].
      - by apply leq_trans with (n := num_cpus).
      - by apply nth_or_none_size_some in SOME.
    Qed.

  End Proofs.
    
End ConcreteScheduler.