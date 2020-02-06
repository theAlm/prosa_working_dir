Require Import rt.util.all.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.schedule
               rt.model.basic.priority rt.model.basic.task_arrival rt.model.basic.interference.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import Job SporadicTaskset Schedule ScheduleOfSporadicTask SporadicTaskset SporadicTaskArrival Interference Priority.

  Section SchedulingInvariants.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Consider any job arrival sequence ... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... and any schedule of this arrival sequence. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    Section WorkConserving.

      (* A scheduler is work-conserving iff when a job j is backlogged,
         all processors are busy with other jobs. *)
      Definition work_conserving :=
        forall j t,
          backlogged job_cost sched j t ->
          forall cpu, exists j_other,
            scheduled_on sched j_other cpu t.

      (* We also provide an alternative, equivalent definition of work-conserving
         based on counting the number of scheduled jobs. *)
      Definition work_conserving_count :=
        forall j t,
          backlogged job_cost sched j t ->
          size (jobs_scheduled_at sched t) = num_cpus.
      
    End WorkConserving.

    Section JLDP.

      (* A JLFP/JLDP policy ...*)
      Variable higher_eq_priority: JLDP_policy arr_seq.

      (* ... is enforced by the scheduler iff at any time t,
         a scheduled job has higher (or same) priority than (as)
         a backlogged job. *)
      Definition enforces_JLDP_policy :=
        forall (j j_hp: JobIn arr_seq) t,
          backlogged job_cost sched j t ->
          scheduled sched j_hp t ->
          higher_eq_priority t j_hp j.
      
    End JLDP.
    
    Section FP.

      (* Given an FP policy, ...*)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* ... this policy is enforced by the scheduler iff
         a corresponding JLDP policy is enforced by the scheduler. *)
      Definition enforces_FP_policy :=
        enforces_JLDP_policy (FP_to_JLDP job_task higher_eq_priority).

    End FP.
    
    Section Lemmas.

      (* Assume all jobs have valid parameters, ...*)
      Hypothesis H_valid_job_parameters:
        forall (j: JobIn arr_seq),
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

      (* In this section, we prove that the two definitions of work-conserving are equivalent. *)
      Section EquivalentDefinitions.

        Lemma work_conserving_eq_work_conserving_count :
          work_conserving <-> work_conserving_count.
        Proof.
          unfold work_conserving, work_conserving_count; split.
          {
            intros EX j t BACK.
            specialize (EX j t BACK).
            apply eq_trans with (y := size (enum (processor num_cpus)));
              last by rewrite size_enum_ord.
            unfold jobs_scheduled_at.
            apply eq_trans with (y := size ((\cat_(cpu < num_cpus) map (fun x => Some x)
                                              (make_sequence (sched cpu t)))));
              first by rewrite -map_bigcat_ord size_map.
            apply eq_trans with (y := size (\cat_(cpu < num_cpus) [:: sched cpu t])).
            {
              f_equal; apply eq_bigr; intros cpu _.
              destruct (sched cpu t) eqn:SCHED; first by done.
              by specialize (EX cpu); des; move: EX => /eqP EX; rewrite EX in SCHED.
            }
            rewrite size_bigcat_ord.
            apply eq_trans with (y := \sum_(i < num_cpus) 1);
              last by rewrite big_const_ord iter_addn mul1n addn0 size_enum_ord.
            by apply eq_bigr.
          }
          {
            intros SIZE j t BACK cpu.
            specialize (SIZE j t BACK).
            destruct ([exists cpu, sched cpu t == None]) eqn:EX; last first.
            {
              apply negbT in EX; rewrite negb_exists in EX.
              move: EX => /forallP ALL; specialize (ALL cpu).
              destruct (sched cpu t) eqn:SOME; last by done.
              by exists j0; apply/eqP.
            }
            {
              move: EX => /existsP [cpu' /eqP EX].
              unfold jobs_scheduled_at in SIZE.
              move: SIZE => /eqP SIZE; rewrite -[size _ == _]negbK in SIZE.
              move: SIZE => /negP SIZE; exfalso; apply SIZE; clear SIZE.
              rewrite neq_ltn; apply/orP; left.
              rewrite size_bigcat_ord.
              rewrite -> big_mkord_ord with (x0 := 0).
              have MKORD := big_mkord (fun x => true); rewrite -MKORD.
              have CAT := big_cat_nat _ (fun x => true).
              rewrite -> CAT with (n := cpu'); [simpl | by done | by apply ltnW, ltn_ord].   
              assert (DIFF: exists k, num_cpus = (cpu' + k).+1).
              {
                exists (num_cpus - cpu').-1.
                rewrite -addnS prednK; last by rewrite ltn_subRL addn0 ltn_ord.
                rewrite addnBA; last by apply ltnW, ltn_ord.
                by rewrite addnC -addnBA // subnn addn0.
              } 
              des; rewrite {5}DIFF.
              rewrite big_nat_recl; last by apply leq_addr.
              apply leq_trans with (n := (\sum_(0 <= i < cpu') 1) + 1 + (\sum_(cpu' <= i < cpu' + k) 1));
                last first.
              {
                rewrite 2!big_const_nat 2!iter_addn 2!mul1n addn0 subn0.
                rewrite [cpu' + k]addnC -addnBA // subnn 2!addn0.
                by rewrite -addnA [1 + k]addnC addnA addn1 -DIFF.
              }
              {
                rewrite -addn1 addnC [_ + 1]addnC -addnA.
                apply leq_add; first by done.
                rewrite eq_fun_ord_to_nat; unfold make_sequence at 2; rewrite EX /= add0n. 
                apply leq_add; apply leq_sum; ins; unfold fun_ord_to_nat; des_eqrefl; try done;
                by unfold make_sequence; desf.
              }
            }
          }
        Qed.
          
      End EquivalentDefinitions.
      
      Section JobInvariantAsTaskInvariant.

        (* Assume any work-conserving priority-based scheduler. *)
        Variable higher_eq_priority: JLDP_policy arr_seq.
        Hypothesis H_work_conserving: work_conserving.
        Hypothesis H_enforces_JLDP_policy: enforces_JLDP_policy higher_eq_priority.
                   
        (* Consider task set ts. *)
        Variable ts: taskset_of sporadic_task.

        (* Assume the task set has no duplicates, ... *)
        Hypothesis H_ts_is_a_set: uniq ts.
        (* ... and all jobs come from the taskset. *)
        Hypothesis H_all_jobs_from_taskset:
          forall (j: JobIn arr_seq), job_task j \in ts.

        (* Suppose that jobs are sequential, ...*)
        Hypothesis H_sequential_jobs: sequential_jobs sched.
        (* ... jobs must arrive to execute, ... *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
        (* ... and jobs do not execute after completion. *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute sched.

        (* Assume that the schedule satisfies the sporadic task model ...*)
        Hypothesis H_sporadic_tasks:
          sporadic_task_model task_period arr_seq job_task.

        (* Consider a valid task tsk, ...*)
        Variable tsk: sporadic_task.
        Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.

        (*... whose job j ... *)
        Variable j: JobIn arr_seq.
        Variable H_job_of_tsk: job_task j = tsk.

        (*... is backlogged at time t. *)
        Variable t: time.
        Hypothesis H_j_backlogged: backlogged job_cost sched j t.

        (* Assume that any previous jobs of tsk have completed by the period. *)
        Hypothesis H_all_previous_jobs_completed :
          forall (j_other: JobIn arr_seq) tsk_other,
            job_task j_other = tsk_other ->
            job_arrival j_other + task_period tsk_other <= t ->
            completed job_cost sched j_other (job_arrival j_other + task_period (job_task j_other)).

        Let scheduled_task_other_than (tsk tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t && (tsk_other != tsk).

        (* Then, there can be at most one pending job of each task at time t. *)
        Lemma platform_at_most_one_pending_job_of_each_task :
          forall j1 j2,
            pending job_cost sched j1 t ->
            pending job_cost sched j2 t ->
            job_task j1 = job_task j2 ->
            j1 = j2.
        Proof.
          rename H_sporadic_tasks into SPO, H_all_previous_jobs_completed into PREV.
          intros j1 j2 PENDING1 PENDING2 SAMEtsk.
          apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF. 
          move: PENDING1 PENDING2 => /andP [ARRIVED1 /negP NOTCOMP1] /andP [ARRIVED2 /negP NOTCOMP2].
          destruct (leqP (job_arrival j1) (job_arrival j2)) as [BEFORE1 | BEFORE2].
          {
            specialize (SPO j1 j2 DIFF SAMEtsk BEFORE1).
            exploit (PREV j1 (job_task j1));
              [by done | by apply leq_trans with (n := job_arrival j2) | intros COMP1].
            apply NOTCOMP1.
            apply completion_monotonic with (t0 := job_arrival j1 + task_period (job_task j1));
              try (by done).
            by apply leq_trans with (n := job_arrival j2). 
          }
          {
            apply ltnW in BEFORE2.
            exploit (SPO j2 j1); [by red; ins; subst | by rewrite SAMEtsk | by done | intro SPO'].
            exploit (PREV j2 (job_task j2));
              [by done | by apply leq_trans with (n := job_arrival j1) | intros COMP2].
            apply NOTCOMP2.
            apply completion_monotonic with (t0 := job_arrival j2 + task_period (job_task j2));
              try (by done).
            by apply leq_trans with (n := job_arrival j1).
          }
        Qed.

        (* Therefore, all processors are busy with tasks other than tsk. *)
        Lemma platform_cpus_busy_with_interfering_tasks :      
          count (scheduled_task_other_than tsk) ts = num_cpus.
        Proof.
          have UNIQ := platform_at_most_one_pending_job_of_each_task.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_sequential_jobs into SEQUENTIAL,
                 H_work_conserving into WORK,
                 H_enforces_JLDP_policy into PRIO,
                 H_j_backlogged into BACK,
                 H_job_of_tsk into JOBtsk,
                 H_valid_job_parameters into JOBPARAMS,
                 H_valid_task into TASKPARAMS,
                 H_all_previous_jobs_completed into PREV,
                 H_completed_jobs_dont_execute into COMP,
                 H_jobs_must_arrive_to_execute into ARRIVE.
          apply work_conserving_eq_work_conserving_count in WORK.
          unfold valid_sporadic_job, valid_realtime_job,
                 enforces_JLDP_policy,
                 task_precedence_constraints, completed_jobs_dont_execute,
                 sporadic_task_model, is_valid_sporadic_task,
                 jobs_of_same_task_dont_execute_in_parallel,
                 sequential_jobs in *.  
          apply/eqP; rewrite eqn_leq; apply/andP; split.
          {
            apply leq_trans with (n := count (fun x => task_is_scheduled job_task sched x t) ts);
              first by apply sub_count; first by red; move => x /andP [SCHED _].    
            unfold task_is_scheduled.
            apply count_exists; first by done.
            {
              intros cpu x1 x2 SCHED1 SCHED2.
              unfold task_scheduled_on in *.
              destruct (sched cpu t); last by done.
              move: SCHED1 SCHED2 => /eqP SCHED1 /eqP SCHED2.
              by rewrite -SCHED1 -SCHED2.
            }
          }
          {
            rewrite -(WORK j t) // -count_predT.       
            apply leq_trans with (n := count (fun j: JobIn arr_seq => scheduled_task_other_than tsk (job_task j)) (jobs_scheduled_at sched t));
              last first.
            {
              rewrite -count_map.
              apply count_sub_uniqr;
                last by red; move => tsk' /mapP [j' _ JOBtsk']; subst; apply FROMTS.
              rewrite map_inj_in_uniq; first by apply scheduled_jobs_uniq.
              red; intros j1 j2 SCHED1 SCHED2 SAMEtsk.
              rewrite 2!mem_scheduled_jobs_eq_scheduled in SCHED1 SCHED2.
              apply scheduled_implies_pending with (job_cost0 := job_cost) in SCHED1; try (by done).
              apply scheduled_implies_pending with (job_cost0 := job_cost) in SCHED2; try (by done).
              by apply UNIQ.
            }
            {
              apply sub_in_count; intros j' SCHED' _.
              rewrite mem_scheduled_jobs_eq_scheduled in SCHED'.
              unfold scheduled_task_other_than; apply/andP; split.
              {
                move: SCHED' => /existsP [cpu /eqP SCHED'].
                by apply/existsP; exists cpu; rewrite /task_scheduled_on SCHED' eq_refl.
              }
              {
                apply/eqP; red; intro SAMEtsk; symmetry in SAMEtsk.
                move: BACK => /andP [PENDING NOTSCHED].
                generalize SCHED'; intro PENDING'.
                apply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING'; try (by done).
                exploit (UNIQ j j' PENDING PENDING'); [by rewrite -SAMEtsk | intro EQjob; subst].
                by rewrite SCHED' in NOTSCHED.
              }
            }
          }
        Qed.

      End JobInvariantAsTaskInvariant.

    End Lemmas.

  End SchedulingInvariants.
  
End Platform.