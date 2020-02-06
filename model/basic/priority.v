Require Import rt.util.all.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Set Implicit Arguments.

(* Definitions of FP and JLFP/JLDP priority relations. *)
Module Priority.

  Import SporadicTask Schedule.

  Section PriorityDefs.

    (* Assume a given job arrival sequence. *)
    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.

    Section Definitions.
      
      (* In the following, we define all priority relations as non-strict, i.e., they specify that
         "job_high has higher priority than (or the same priority as) job_low". *)

      (* A JLDP policy is a generic relation between two jobs of an arrival sequence
         that can vary with time. *)
      Definition JLDP_policy := time -> JobIn arr_seq -> JobIn arr_seq -> bool.

      (* FP policy is simply a relation between tasks.
         Because our model of processor platform is based on a generic JLDP policy,
         we generate a JLDP policy from an FP policy whenever required. *)
      Variable sporadic_task: eqType.
      Definition FP_policy := sporadic_task -> sporadic_task -> bool.

    End Definitions.
    
    Section ValidJLFPPolicy.

      Variable is_higher_priority: JLDP_policy.

      (* A policy is reflexive, since a job has the same priority as itself. *)
      Definition JLFP_is_reflexive :=
        forall t, reflexive (is_higher_priority t).

      (* A policy is transitive. *)
      Definition JLFP_is_transitive :=
        forall t, transitive (is_higher_priority t).
      
      (* A policy is total, since it must know the priority of any two jobs at any time. *)
      Definition JLFP_is_total :=
        forall t, total (is_higher_priority t).

      (* A JLDP policy is valid iff it satisfies the three properties.
         Note that, for generality, we don't enforce antisymmetry and allow multiple
         jobs with same priority. *)
      Definition valid_JLDP_policy :=
        JLFP_is_reflexive /\ JLFP_is_transitive /\ JLFP_is_total.

    End ValidJLFPPolicy.

    Section MonotonicPriorities.

      Context {sporadic_task: eqType}.
      Variable job_task: Job -> sporadic_task.
      Variable higher_eq_priority: JLDP_policy.
            
      Definition monotonic_priorities :=
        forall (j j': JobIn arr_seq) t,
          job_task j = job_task j' ->
          job_arrival j < job_arrival j' ->
          higher_eq_priority t j j'.
      
    End MonotonicPriorities.
    
    Section ValidFPPolicy.

      Context {sporadic_task: eqType}.
      
      Variable is_higher_priority: FP_policy sporadic_task.

      Definition FP_is_reflexive := reflexive is_higher_priority.

      Definition FP_is_transitive := transitive is_higher_priority.
      
      Definition FP_is_total := total is_higher_priority.

      (* We enforce the same restrictions for FP policy: reflexive, transitive, total. *)
      Definition valid_FP_policy :=
        FP_is_reflexive /\ FP_is_transitive /\ FP_is_total.

    End ValidFPPolicy.

  End PriorityDefs.
  
  Section RateDeadlineMonotonic.

    Context {sporadic_task: eqType}.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    (* Rate-Monotonic and Deadline-Monotonic as priority order *)
    Definition RM (tsk1 tsk2: sporadic_task) := task_period tsk1 <= task_period tsk2.

    Definition DM (tsk1 tsk2: sporadic_task) := task_deadline tsk1 <= task_deadline tsk2.

    (* Rate-Montonic is a valid FP policy. *)
    Lemma rm_is_valid : valid_FP_policy RM.
    Proof.
      unfold valid_FP_policy, FP_is_reflexive, FP_is_transitive, RM;
        repeat (split; try red); first by ins.
      by intros x y z XY YZ; apply leq_trans with (n := task_period x).
      by red; intros tsk1 tsk2; apply/orP; destruct (leqP (task_period tsk1) (task_period tsk2));
        [by left | by right; apply ltnW].
    Qed.

    (* Deadline-Monotonic is a valid FP policy. *)
    Lemma dm_is_valid : valid_FP_policy DM.
    Proof.
      unfold valid_FP_policy, FP_is_reflexive, FP_is_transitive, DM;
      repeat (split; try red); first by ins.
        by intros x y z; apply leq_trans.
        by red; intros tsk1 tsk2; apply/orP; destruct (leqP (task_deadline tsk1) (task_deadline tsk2));
          [by left | by right; apply ltnW].
    Qed.

  End RateDeadlineMonotonic.

  Section GeneralizeFP.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> sporadic_task.
    Variable arr_seq: arrival_sequence Job.
    Variable num_cpus: nat.

    (* We define a function to get from FP to JLDP policy. *)
    Definition FP_to_JLDP (task_hp: FP_policy sporadic_task) : JLDP_policy arr_seq :=
      fun (t: time) (jhigh jlow: JobIn arr_seq) =>
        task_hp (job_task jhigh) (job_task jlow).

    (* With this function, from a valid FP policy comes a valid JLDP policy. *)
    Lemma valid_FP_is_valid_JLDP :
      forall task_hp (FP: valid_FP_policy task_hp),
        valid_JLDP_policy (FP_to_JLDP task_hp).
    Proof.
      unfold FP_to_JLDP, valid_FP_policy, valid_JLDP_policy,
             FP_is_reflexive, FP_is_transitive, FP_is_total,
             JLFP_is_reflexive, JLFP_is_transitive, JLFP_is_total, reflexive, transitive.
      ins; destruct FP as [REFL [TRANS TOTAL]]; repeat (split; try red); des; last by ins.
        by ins; rewrite REFL.
        by intros sched t y x z; apply TRANS.
    Qed.

  End GeneralizeFP.

  Section JLFPDefs.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Context {num_cpus: nat}.
    Context {arr_seq: arrival_sequence Job}.

    Variable is_higher_priority: JLDP_policy arr_seq.

    (* JLFP policy is a JLDP policy where the priorities do not vary with time. *)
    Definition is_JLFP_policy (is_higher_priority: JLDP_policy arr_seq) :=
      forall j1 j2 t t',
        is_higher_priority t j1 j2 -> is_higher_priority t' j1 j2.

    (* Lemma: every FP policy is a JLFP policy. *)
    Variable job_task: Job -> sporadic_task.
    Lemma FP_is_JLFP :
      forall FP_higher_priority,
        is_JLFP_policy (FP_to_JLDP job_task FP_higher_priority).
    Proof.
      by unfold is_JLFP_policy, valid_FP_policy.
    Qed.

  End JLFPDefs.

  Section EDFDefs.

    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.
    Variable job_deadline: Job -> time.
      
    Definition EDF (t: time) (j1 j2: JobIn arr_seq) :=
      job_arrival j1 + job_deadline j1 <= job_arrival j2 + job_deadline j2.

    (* Lemma: EDF is a JLFP policy. *)
    Lemma edf_JLFP : is_JLFP_policy EDF. 
    Proof.
      by unfold is_JLFP_policy, EDF.
    Qed.

    Lemma edf_valid_policy : valid_JLDP_policy EDF.
    Proof.
      unfold valid_JLDP_policy, EDF, JLFP_is_reflexive, JLFP_is_transitive, reflexive, transitive.
      repeat (split; try red).
        by ins; apply leqnn.
        by intros sched t y x z; apply leq_trans.
        by intros _; red; intros j1 j2; apply/orP;
          destruct (leqP (job_arrival j1 + job_deadline j1) (job_arrival j2 + job_deadline j2));
            [by left | by right; apply ltnW].
    Qed.

  End EDFDefs.

End Priority.