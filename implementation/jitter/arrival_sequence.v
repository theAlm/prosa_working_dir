Require Import rt.util.all.
Require Import rt.model.jitter.arrival_sequence rt.model.jitter.job
               rt.model.jitter.task rt.model.jitter.task_arrival.
Require Import rt.implementation.jitter.task rt.implementation.jitter.job.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq div.

Module ConcreteArrivalSequence.

  Import JobWithJitter ArrivalSequence ConcreteTask ConcreteJob SporadicTaskset SporadicTaskArrival.

  Section PeriodicArrivals.

    Variable ts: concrete_taskset.

    (* At any time t, we release Some job of tsk if t is a multiple of the period,
       otherwise we release None. *)
    Definition add_job (t: time) (tsk: concrete_task) :=
      if task_period tsk %| t  then
        Some (Build_concrete_job (t %/ task_period tsk) (task_cost tsk) (task_deadline tsk) (task_jitter tsk) tsk)
      else
        None.

    (* The arrival sequence at any time t is simply the partial map of add_job. *)
    Definition periodic_arrival_sequence (t: time) := pmap (add_job t) ts.

  End PeriodicArrivals.

  Section Proofs.

    (* Let ts be any concrete task set with valid parameters. *)
    Variable ts: concrete_taskset.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    
    (* Regarding the periodic arrival sequence built from ts, we prove that...*)
    Let arr_seq := periodic_arrival_sequence ts.

    (* ... every job comes from the task set, ... *)
    Theorem periodic_arrivals_all_jobs_from_taskset:
      forall (j: JobIn arr_seq),
        job_task (_job_in arr_seq j) \in ts. (* TODO: fix coercion *)
    Proof.
      intros j.
      destruct j as [j arr ARRj]; simpl.
      unfold arr_seq, arrives_at, periodic_arrival_sequence in *.
      rewrite mem_pmap in ARRj.
      move: ARRj => /mapP ARRj; destruct ARRj as [tsk IN SOME].
      by unfold add_job in *; desf.
    Qed.

    (* ..., jobs have valid parameters, ... *)
    Theorem periodic_arrivals_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j.
    Proof.
      rename H_valid_task_parameters into PARAMS.
      unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
      intros j; destruct j as [j arr ARRj]; simpl.
      unfold arrives_at, arr_seq, periodic_arrival_sequence in ARRj.
      rewrite mem_pmap in ARRj; move: ARRj => /mapP [tsk IN SOME].
      unfold add_job in SOME; desf.
      specialize (PARAMS tsk IN); des.
      unfold valid_sporadic_job, valid_realtime_job, job_cost_positive.
      by repeat split; try (by done); apply leqnn.
    Qed.

    (* ... job arrivals satisfy the sporadic task model, ... *)
    Theorem periodic_arrivals_are_sporadic:
      sporadic_task_model task_period arr_seq job_task.
    Proof.
      unfold sporadic_task_model; move => j j' /eqP DIFF SAMEtsk LE.
      destruct j as [j arr ARR], j' as [j' arr' ARR']; simpl in *.
      rewrite eqE /= /jobin_eqdef negb_and /= in DIFF.
      unfold arrives_at, arr_seq, periodic_arrival_sequence in *.
      rewrite 2!mem_pmap in ARR ARR'.
      move: ARR ARR' => /mapP [tsk_j INj SOMEj] /mapP [tsk_j' INj' SOMEj'].
      unfold add_job in SOMEj, SOMEj'; desf; simpl in *;
      move: Heq0 Heq => /dvdnP [k DIV] /dvdnP [k' DIV'].
      {
        rewrite DIV DIV' -mulSnr.
        rewrite leq_eqVlt in LE; move: LE => /orP [/eqP EQ | LESS].
        { 
          exfalso; move: DIFF => /negP DIFF; apply DIFF.
          by subst; rewrite EQ.
        }
        subst; rewrite leq_mul2r; apply/orP; right.
        by rewrite ltn_mul2r in LESS; move: LESS => /andP [_ LT].
      }
      {
        assert (LT: arr < arr'). by rewrite ltn_neqAle; apply/andP.
        clear LE DIFF; subst tsk_j' arr arr'.
        rewrite ltn_mul2r in LT; move: LT => /andP [_ LT].
        by apply leq_trans with (n := k.+1 * task_period tsk_j);
          [by rewrite mulSnr | by rewrite leq_mul2r; apply/orP; right].
      }
    Qed.

    (* ... and if the task set has no duplicates, the same applies to
       the arrival sequence. *)
    Theorem periodic_arrivals_is_a_set:
      uniq ts -> arrival_sequence_is_a_set arr_seq.
    Proof.
      intros UNIQ t.
      unfold arr_seq, periodic_arrival_sequence.
      apply (pmap_uniq) with (g := job_task); last by done.
      by unfold add_job, ocancel; intro tsk; desf.
    Qed.
      
  End Proofs.
  
End ConcreteArrivalSequence.