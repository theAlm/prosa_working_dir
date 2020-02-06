Require Import rt.util.all.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.schedule
               rt.model.basic.task_arrival rt.model.basic.response_time
               rt.model.basic.workload rt.model.basic.schedulability.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq div fintype bigop path.

Module WorkloadBound.
  
  Import Job SporadicTaskset Schedule ScheduleOfSporadicTask SporadicTaskArrival ResponseTime Schedulability Workload.

  Section WorkloadBoundDef.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.

    (* Consider any task tsk with response-time bound R_tsk,
       that is scheduled in an interval of length delta. *)
    Variable tsk: sporadic_task.
    Variable R_tsk: time.
    Variable delta: time.
    
    (* Based on the number of jobs that execute completely in the interval, ... *)
    Definition max_jobs :=
      div_floor (delta + R_tsk - task_cost tsk) (task_period tsk).

    (* ... Bertogna and Cirinei's workload bound is defined as follows. *)
    Definition W :=
      let e_k := (task_cost tsk) in
      let p_k := (task_period tsk) in            
        minn e_k (delta + R_tsk - e_k - max_jobs * p_k) + max_jobs * e_k.

  End WorkloadBoundDef.
  
  Section BasicLemmas.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.

    (* Let tsk be any task...*)
    Variable tsk: sporadic_task.

    (* ... with period > 0. *)
    Hypothesis H_period_positive: task_period tsk > 0.

    (* Let R1 <= R2 be two response-time bounds that
       are larger than the cost of the tsk. *)
    Variable R1 R2: time.
    Hypothesis H_R_lower_bound: R1 >= task_cost tsk.
    Hypothesis H_R1_le_R2: R1 <= R2.
      
    Let workload_bound := W task_cost task_period tsk.

    (* Then, Bertogna and Cirinei's workload bound is monotonically increasing. *) 
    Lemma W_monotonic :
      forall t1 t2,
        t1 <= t2 ->
        workload_bound R1 t1 <= workload_bound R2 t2.
    Proof.
      intros t1 t2 LEt.
      unfold workload_bound, W, max_jobs, div_floor; rewrite 2!subndiv_eq_mod.
      set e := task_cost tsk; set p := task_period tsk.
      set x1 := t1 + R1.
      set x2 := t2 + R2.
      set delta := x2 - x1.
      rewrite -[x2](addKn x1) -addnBA; fold delta;
        last by apply leq_add.
      
      induction delta; first by rewrite addn0 leqnn.
      {
         apply (leq_trans IHdelta).

         (* Prove special case for p <= 1. *)
         destruct (leqP p 1) as [LTp | GTp].
         {
           rewrite leq_eqVlt in LTp; move: LTp => /orP LTp; des;
             last by rewrite ltnS in LTp; apply (leq_trans H_period_positive) in LTp. 
           {
             rewrite LTp 2!modn1 2!divn1.
             rewrite leq_add2l leq_mul2r; apply/orP; right.
             by rewrite leq_sub2r // leq_add2l.
           }
         }
         (* Harder case: p > 1. *)
         {
           assert (EQ: (x1 + delta.+1 - e) = (x1 + delta - e).+1).
           {
             rewrite -[(x1 + delta - e).+1]addn1.
             rewrite [_+1]addnC addnBA; last first.
             {
               apply (leq_trans H_R_lower_bound).
               by rewrite -addnA addnC -addnA leq_addr.
             }
             by rewrite [1 + _]addnC -addnA addn1.
           } rewrite -> EQ in *; clear EQ.
         
         have DIV := divSn_cases (x1 + delta - e) p GTp; des.
         {
           rewrite DIV leq_add2r leq_min; apply/andP; split;
             first by rewrite geq_minl.
           by apply leq_trans with (n := (x1 + delta - e) %% p);
             [by rewrite geq_minr | by rewrite -DIV0 addn1 leqnSn].
         }
         {
           rewrite -[minn e _]add0n -addnA; apply leq_add; first by ins.
           rewrite -DIV mulnDl mul1n [_ + e]addnC.
           by apply leq_add; [by rewrite geq_minl | by ins].
         }
       }
     }
   Qed.

  End BasicLemmas.
 
  Section ProofWorkloadBound.
 
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_deadline: Job -> time.

    Variable arr_seq: arrival_sequence Job.

    (* Assume that all jobs have valid parameters *)
    Hypothesis H_jobs_have_valid_parameters :
      forall (j: JobIn arr_seq),
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    
    (* Consider any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Assumption: jobs only execute if they arrived.
       This is used to eliminate jobs that arrive after end of the interval t1 + delta. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.

    (* Assumption: jobs do not execute after they completed.
       This is used to eliminate jobs that complete before the start of the interval t1. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Assumption: Jobs are sequential.
       This is required to use interval lengths as a measure of service. *)
    Hypothesis H_sequential_jobs: sequential_jobs sched.

    (* Assumption: sporadic task model.
       This is necessary to conclude that consecutive jobs ordered by arrival times
       are separated by at least 'period' times units. *)
    Hypothesis H_sporadic_tasks: sporadic_task_model task_period arr_seq job_task.

    (* Before starting the proof, let's give simpler names to the definitions. *)
    Let job_has_completed_by := completed job_cost sched.

    Let workload_of (tsk: sporadic_task) (t1 t2: time) :=
      workload job_task sched tsk t1 t2.

    (* Now we define the theorem. Let tsk be any task in the taskset. *)
    Variable tsk: sporadic_task.

    (* Assumption: the task must have valid parameters:
         a) period > 0 (used in divisions)
         b) deadline of the jobs = deadline of the task
         c) cost <= period
            (used to prove that the distance between the first and last
             jobs is at least (cost + n*period), where n is the number
             of middle jobs. If cost >> period, the claim does not hold
             for every task set. *)
    Hypothesis H_valid_task_parameters:
      is_valid_sporadic_task task_cost task_period task_deadline tsk.

    (* Assumption: the task must have a constrained deadline.
       This is required to prove that n_k (max_jobs) from Bertogna
       and Cirinei's formula accounts for at least the number of
       middle jobs (i.e., number of jobs - 2 in the worst case). *)
    Hypothesis H_constrained_deadline: task_deadline tsk <= task_period tsk.
      
    (* Consider an interval [t1, t1 + delta). *)
    Variable t1 delta: time.

    (* Assume that a response-time bound R_tsk for that task in any
       schedule of this processor platform is also given, ... *)
    Variable R_tsk: time.

    Hypothesis H_response_time_bound :    
      forall (j: JobIn arr_seq),
      job_task j = tsk ->
      job_arrival j + R_tsk < t1 + delta ->
      job_has_completed_by j (job_arrival j + R_tsk).

    (* ... such that R_tsk >= task_cost tsk and R_tsk <= task_deadline tsk. *)    
    Hypothesis H_response_time_ge_cost: R_tsk >= task_cost tsk.
    Hypothesis H_no_deadline_miss: R_tsk <= task_deadline tsk.
    
    Section MainProof.

      (* In this section, we prove that the workload of a task in the
         interval [t1, t1 + delta) is bounded by W. *)

      (* Let's simplify the names a bit. *)
      Let t2 := t1 + delta.
      Let n_k := max_jobs task_cost task_period tsk R_tsk delta.
      Let workload_bound := W task_cost task_period tsk R_tsk delta.
      
      (* Since we only care about the workload of tsk, we restrict
         our view to the set of jobs of tsk scheduled in [t1, t2). *)
      Let scheduled_jobs :=
        jobs_of_task_scheduled_between job_task sched tsk t1 t2.

      (* Now, let's consider the list of interfering jobs sorted by arrival time. *)
      Let earlier_arrival := fun (x y: JobIn arr_seq) => job_arrival x <= job_arrival y.
      Let sorted_jobs := (sort earlier_arrival scheduled_jobs).

      (* The first step consists in simplifying the sum corresponding
         to the workload. *)
      Section SimplifyJobSequence.

        (* After switching to the definition of workload based on a list
           of jobs, we show that sorting the list preserves the sum. *)
        Lemma workload_bound_simpl_by_sorting_scheduled_jobs :
          workload_joblist job_task sched tsk t1 t2 =
           \sum_(i <- sorted_jobs) service_during sched i t1 t2.
        Proof.
          unfold workload_joblist; fold scheduled_jobs.
          rewrite (eq_big_perm sorted_jobs) /= //.
          by rewrite -(perm_sort earlier_arrival).
        Qed.

        (* Remember that both sequences have the same set of elements *)
        Lemma workload_bound_job_in_same_sequence :
          forall j,
            (j \in scheduled_jobs) = (j \in sorted_jobs).
        Proof.
          by apply perm_eq_mem; rewrite -(perm_sort earlier_arrival).
        Qed.

        (* Remember that all jobs in the sorted sequence is an
           interfering job of task tsk. *)
        Lemma workload_bound_all_jobs_from_tsk :
          forall j_i,
            j_i \in sorted_jobs ->
            job_task j_i = tsk /\
            service_during sched j_i t1 t2 != 0 /\
            j_i \in jobs_scheduled_between sched t1 t2.
        Proof.
          intros j_i LTi.
          rewrite -workload_bound_job_in_same_sequence mem_filter in LTi; des.
          repeat split; [by done | | by done].
          unfold jobs_scheduled_between in *; rewrite mem_undup in LTi0.
          apply mem_bigcat_nat_exists in LTi0; des.
          rewrite mem_scheduled_jobs_eq_scheduled in LTi0.
          apply service_implies_cumulative_service with (t := i);
            first by apply/andP; split.
          by rewrite -not_scheduled_no_service negbK.
        Qed.

        (* Remember that consecutive jobs are ordered by arrival. *)
        Lemma workload_bound_jobs_ordered_by_arrival :
          forall i elem,
            i < (size sorted_jobs).-1 ->
            earlier_arrival (nth elem sorted_jobs i) (nth elem sorted_jobs i.+1).
        Proof.
          intros i elem LT.
          assert (SORT: sorted earlier_arrival sorted_jobs).
            by apply sort_sorted; unfold total, earlier_arrival; ins; apply leq_total.
          by destruct sorted_jobs; simpl in *; [by rewrite ltn0 in LT | by apply/pathP].
        Qed.

      End SimplifyJobSequence.

      (* Next, we show that if the number of jobs is no larger than n_k,
         the workload bound trivially holds. *)
      Section WorkloadNotManyJobs.

        Lemma workload_bound_holds_for_at_most_n_k_jobs :
          size sorted_jobs <= n_k ->
          \sum_(i <- sorted_jobs) service_during sched i t1 t2 <=
            workload_bound.
        Proof.
        intros LEnk.
        rewrite -[\sum_(_ <- _ | _) _]add0n leq_add //.
        apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk);
          last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
        {
          rewrite [\sum_(_ <- _) service_during _ _ _ _]big_seq_cond.
          rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
          apply leq_sum; intros j_i; move/andP => [INi _].
          apply workload_bound_all_jobs_from_tsk in INi; des. 
          eapply cumulative_service_le_task_cost;
            [by apply H_completed_jobs_dont_execute | by apply INi |].
          by apply H_jobs_have_valid_parameters.
        }
      Qed.

      End WorkloadNotManyJobs.

      (* Otherwise, assume that the number of jobs is larger than n_k >= 0.
         First, consider the simple case with only one job. *)
      Section WorkloadSingleJob.

        (* Assume that there's at least one job in the sorted list. *)
        Hypothesis H_at_least_one_job: size sorted_jobs > 0.

        Variable elem: JobIn arr_seq.
        Let j_fst := nth elem sorted_jobs 0.

        (* The first job is an interfering job of task tsk. *)
        Lemma workload_bound_j_fst_is_job_of_tsk :
          job_task j_fst = tsk /\
          service_during sched j_fst t1 t2 != 0 /\
          j_fst \in jobs_scheduled_between sched t1 t2.
        Proof.
          by apply workload_bound_all_jobs_from_tsk, mem_nth.
        Qed.

        (* The workload bound holds for the single job. *)
        Lemma workload_bound_holds_for_a_single_job :
          \sum_(0 <= i < 1) service_during sched (nth elem sorted_jobs i) t1 t2 <=
          workload_bound.
        Proof.
          unfold workload_bound, W; fold n_k.
          have INfst := workload_bound_j_fst_is_job_of_tsk; des.
          rewrite big_nat_recr // big_geq // [nth]lock /= -lock add0n.
          destruct n_k; last first.
          {
            rewrite -[service_during _ _ _ _]add0n; rewrite leq_add //.
            rewrite -[service_during _ _ _ _]add0n [_* task_cost tsk]mulSnr.
            apply leq_add; first by done.
            by eapply cumulative_service_le_task_cost;
              [| by apply INfst
               | by apply H_jobs_have_valid_parameters].
          }
          {
            rewrite 2!mul0n addn0 subn0 leq_min; apply/andP; split.
            {
              by eapply cumulative_service_le_task_cost;
                 [| by apply INfst
                | by apply H_jobs_have_valid_parameters].
            }
            {
              rewrite -addnBA // -[service_during _ _ _ _]addn0.
              apply leq_add; last by done.
              by apply cumulative_service_le_delta.
            }
          }
        Qed.

      End WorkloadSingleJob.

      (* Next, consider the last case where there are at least two jobs:
         the first job j_fst, and the last job j_lst. *)
      Section WorkloadTwoOrMoreJobs.

        (* There are at least two jobs. *)
        Variable num_mid_jobs: nat.
        Hypothesis H_at_least_two_jobs : size sorted_jobs = num_mid_jobs.+2.
        
        Variable elem: JobIn arr_seq.
        Let j_fst := nth elem sorted_jobs 0.
        Let j_lst := nth elem sorted_jobs num_mid_jobs.+1.

        (* The last job is an interfering job of task tsk. *)
        Lemma workload_bound_j_lst_is_job_of_tsk :
          job_task j_lst = tsk /\
          service_during sched j_lst t1 t2 != 0 /\
          j_lst \in jobs_scheduled_between sched t1 t2.
        Proof.
          apply workload_bound_all_jobs_from_tsk, mem_nth.
          by rewrite H_at_least_two_jobs.
        Qed.

        (* The response time of the first job must fall inside the interval. *)
        Lemma workload_bound_response_time_of_first_job_inside_interval :
          t1 <= job_arrival j_fst + R_tsk.
        Proof.
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          exploit workload_bound_all_jobs_from_tsk.
          {
            apply mem_nth; instantiate (1 := 0).
            apply ltn_trans with (n := 1); [by done | by rewrite H_at_least_two_jobs].
          }
          instantiate (1 := elem); move => [FSTtsk [/eqP FSTserv FSTin]].
          apply FSTserv.
          apply (cumulative_service_after_job_rt_zero job_cost) with (R := R_tsk);
            try (by done); last by apply ltnW.
          apply H_response_time_bound; first by done.
          by apply leq_trans with (n := t1); last by apply leq_addr.
        Qed.

        (* The arrival of the last job must also fall inside the interval. *)
        Lemma workload_bound_last_job_arrives_before_end_of_interval :
          job_arrival j_lst < t2.
        Proof.
          rewrite leqNgt; apply/negP; unfold not; intro LT2.
          exploit workload_bound_all_jobs_from_tsk.
          {
            apply mem_nth; instantiate (1 := num_mid_jobs.+1).
            by rewrite -(ltn_add2r 1) addn1 H_at_least_two_jobs addn1.
          }  
          instantiate (1 := elem); move => [LSTtsk [/eqP LSTserv LSTin]].
          by unfold service_during; apply LSTserv, cumulative_service_before_job_arrival_zero.
        Qed.

        (* Next, we upper-bound the service of the first and last jobs using their arrival times. *)
        Lemma workload_bound_service_of_first_and_last_jobs :
          service_during sched j_fst t1 t2 +
          service_during sched j_lst t1 t2 <=
            (job_arrival j_fst  + R_tsk - t1) + (t2 - job_arrival j_lst).
        Proof.
          apply leq_add; unfold service_during.
          {
            rewrite -[_ + _ - _]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
            apply leq_trans with (n := \sum_(t1 <= t < job_arrival j_fst + R_tsk)
                                        service_at sched j_fst t);
              last by apply leq_sum; ins; apply service_at_most_one.
            destruct (job_arrival j_fst + R_tsk < t2) eqn:LEt2; last first.
            {
              unfold t2; apply negbT in LEt2; rewrite -ltnNge in LEt2.
              rewrite -> big_cat_nat with (n := t1 + delta) (p := job_arrival j_fst + R_tsk);
                [by apply leq_addr | by apply leq_addr | by done].
            }
            {
              rewrite -> big_cat_nat with (n := job_arrival j_fst + R_tsk);
                [| by apply workload_bound_response_time_of_first_job_inside_interval
                 | by apply ltnW].
              rewrite -{2}[\sum_(_ <= _ < _) _]addn0 /= leq_add2l leqn0; apply/eqP.
              apply (cumulative_service_after_job_rt_zero job_cost) with (R := R_tsk); try (by done).
              apply H_response_time_bound; last by done.
              exploit workload_bound_all_jobs_from_tsk.
                by apply mem_nth; instantiate (1 := 0); rewrite H_at_least_two_jobs.
              by instantiate (1 := elem); move => [FSTtsk _].
            }
          }
          {
            rewrite -[_ - _]mul1n -[1 * _]addn0 -iter_addn -big_const_nat.
            destruct (job_arrival j_lst <= t1) eqn:LT.
            {
              apply leq_trans with (n := \sum_(job_arrival j_lst <= t < t2)
                                          service_at sched j_lst t);
                first by rewrite -> big_cat_nat with (m := job_arrival j_lst) (n := t1);
                  [by apply leq_addl | by ins | by apply leq_addr].
              by apply leq_sum; ins; apply service_at_most_one.
            }
            {
              apply negbT in LT; rewrite -ltnNge in LT.
              rewrite -> big_cat_nat with (n := job_arrival j_lst);
                [| by apply ltnW
                 | by apply ltnW, workload_bound_last_job_arrives_before_end_of_interval].
              rewrite /= -[\sum_(_ <= _ < _) 1]add0n; apply leq_add.
              rewrite cumulative_service_before_job_arrival_zero;
                [by apply leqnn | by ins | by apply leqnn].
              by apply leq_sum; ins; apply service_at_most_one.
            }
          }
        Qed.

        (* Simplify the expression from the previous lemma. *)
        Lemma workload_bound_simpl_expression_with_first_and_last :
          job_arrival j_fst + R_tsk - t1 + (t2 - job_arrival j_lst) =
                       delta + R_tsk - (job_arrival j_lst - job_arrival j_fst).
        Proof.
          have lemma1 := workload_bound_last_job_arrives_before_end_of_interval.
          have lemma2 := workload_bound_response_time_of_first_job_inside_interval.
          rewrite addnBA; last by apply ltnW.
          rewrite subh1 // -addnBA; last by apply leq_addr.
          rewrite addnC [job_arrival _ + _]addnC.
          unfold t2; rewrite [t1 + _]addnC -[delta + t1 - _]subnBA // subnn subn0.
          rewrite addnA -subnBA; first by ins.
          unfold j_fst, j_lst. rewrite -[_.+1]add0n.
          apply prev_le_next; last by rewrite H_at_least_two_jobs add0n leqnn.
          by ins; apply workload_bound_jobs_ordered_by_arrival.
        Qed.

        (* Bound the service of the middle jobs. *)
        Lemma workload_bound_service_of_middle_jobs :
          \sum_(0 <= i < num_mid_jobs)
            service_during sched (nth elem sorted_jobs i.+1) t1 t2 <=
            num_mid_jobs * task_cost tsk.
        Proof.
          apply leq_trans with (n := num_mid_jobs * task_cost tsk);
            last by rewrite leq_mul2l; apply/orP; right. 
          apply leq_trans with (n := \sum_(0 <= i < num_mid_jobs) task_cost tsk);
            last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
          rewrite big_nat_cond [\sum_(0 <= i < num_mid_jobs) task_cost _]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          eapply cumulative_service_le_task_cost;
            [by apply H_completed_jobs_dont_execute | | by apply H_jobs_have_valid_parameters].
          exploit workload_bound_all_jobs_from_tsk.
          {
            instantiate (1 := nth elem sorted_jobs i.+1).
            apply mem_nth; rewrite H_at_least_two_jobs.
            by rewrite ltnS; apply leq_trans with (n := num_mid_jobs).
          }
          by ins; des.
        Qed.

        (* Conclude that the distance between first and last is at least num_mid_jobs + 1 periods. *)
        Lemma workload_bound_many_periods_in_between :
          job_arrival j_lst - job_arrival j_fst >= num_mid_jobs.+1 * (task_period tsk).
        Proof.
          assert (EQnk: num_mid_jobs.+1=(size sorted_jobs).-1).
            by rewrite H_at_least_two_jobs.
          unfold j_fst, j_lst; rewrite EQnk telescoping_sum;
            last by ins; apply workload_bound_jobs_ordered_by_arrival.
          rewrite -[_ * _ tsk]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
          rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.

          (* To simplify, call the jobs 'cur' and 'next' *)
          set cur := nth elem sorted_jobs i.
          set next := nth elem sorted_jobs i.+1.

          (* Show that cur arrives earlier than next *)
          assert (ARRle: job_arrival cur <= job_arrival next).
            by unfold cur, next; apply workload_bound_jobs_ordered_by_arrival.
             
          (* Show that both cur and next are in the arrival sequence *)
          assert (INnth: cur \in scheduled_jobs /\ next \in scheduled_jobs).
          {
            rewrite 2!workload_bound_job_in_same_sequence; split.
              by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs; ins.
              by apply mem_nth; destruct sorted_jobs; ins.
          }
          rewrite 2?mem_filter in INnth; des.

          (* Use the sporadic task model to conclude that cur and next are separated
             by at least (task_period tsk) units. Of course this only holds if cur != next.
             Since we don't know much about the list (except that it's sorted), we must
             also prove that it doesn't contain duplicates. *)
          assert (CUR_LE_NEXT: job_arrival cur + task_period (job_task cur) <= job_arrival next).
          {
            apply H_sporadic_tasks; last by ins.
            unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
            rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
              by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
              by destruct sorted_jobs; ins.
              by rewrite sort_uniq -/scheduled_jobs filter_uniq // undup_uniq.
              by rewrite INnth INnth0.  
          }
          by rewrite subh3 // addnC -INnth.
        Qed.

        (* Prove that n_k is at least the number of the middle jobs *)
        Lemma workload_bound_n_k_covers_middle_jobs :
          n_k >= num_mid_jobs.
        Proof.
          rename H_valid_task_parameters into PARAMS.
          unfold is_valid_sporadic_task in *; des.
          rewrite leqNgt; apply/negP; unfold not; intro LTnk.
          assert (DISTmax: job_arrival j_lst - job_arrival j_fst >= delta + task_period tsk).
          {
            apply leq_trans with (n := n_k.+2 * task_period tsk).
            {
              rewrite -addn1 mulnDl mul1n leq_add2r.
              apply leq_trans with (n := delta + R_tsk - task_cost tsk);
                first by rewrite -addnBA //; apply leq_addr.
              by apply ltnW, ltn_ceil, PARAMS0.
            }
            apply leq_trans with (num_mid_jobs.+1 * task_period tsk); 
              first by rewrite leq_mul2r; apply/orP; right.
            by apply workload_bound_many_periods_in_between.
          }
          rewrite <- leq_add2r with (p := job_arrival j_fst) in DISTmax.
          rewrite addnC subh1 in DISTmax; last first.
          {
            unfold j_fst, j_lst; rewrite -[_.+1]add0n.
            apply prev_le_next; last by rewrite H_at_least_two_jobs add0n leqnn.
            by ins; apply workload_bound_jobs_ordered_by_arrival.
          }
          rewrite -subnBA // subnn subn0 in DISTmax.
          rewrite [delta + task_period tsk]addnC addnA in DISTmax.
          have BEFOREt2 := workload_bound_last_job_arrives_before_end_of_interval.
          generalize BEFOREt2; move: BEFOREt2; rewrite {1}ltnNge; move => /negP BEFOREt2'.
          intros BEFOREt2; apply BEFOREt2'; clear BEFOREt2'.
          apply leq_trans with (n := job_arrival j_fst + task_deadline tsk + delta);
            last by apply leq_trans with (n := job_arrival j_fst + task_period tsk + delta);
              [rewrite leq_add2r leq_add2l; apply H_constrained_deadline | apply DISTmax].
          unfold t2; rewrite leq_add2r.
          apply leq_trans with (n := job_arrival j_fst + R_tsk);
            last by rewrite leq_add2l.
          by apply workload_bound_response_time_of_first_job_inside_interval.
        Qed.

        (* If n_k = num_mid_jobs, then the workload bound holds. *)
        Lemma workload_bound_n_k_equals_num_mid_jobs :
          num_mid_jobs = n_k ->
          service_during sched j_lst t1 t2 +
            service_during sched j_fst t1 t2 +
            \sum_(0 <= i < num_mid_jobs)
             service_during sched (nth elem sorted_jobs i.+1) t1 t2
          <= workload_bound.
        Proof.
          rename H_valid_task_parameters into PARAMS.
          unfold is_valid_sporadic_task in *; des.
          unfold workload_bound, W; fold n_k.
          move => NK; rewrite -NK.
          apply leq_add;
            last by apply workload_bound_service_of_middle_jobs.
          apply leq_trans with (delta + R_tsk - (job_arrival j_lst - job_arrival j_fst)).
          {
            rewrite addnC -workload_bound_simpl_expression_with_first_and_last.
            by apply workload_bound_service_of_first_and_last_jobs.
          }
          rewrite leq_min; apply/andP; split.
          {
            rewrite leq_subLR [_ + task_cost _]addnC -leq_subLR.
            apply leq_trans with (num_mid_jobs.+1 * task_period tsk);
              last by apply workload_bound_many_periods_in_between.
            rewrite NK ltnW // -ltn_divLR;
              last by apply PARAMS0.
            by unfold n_k, max_jobs, div_floor.
          }
          {
            rewrite -subnDA; apply leq_sub2l.
            apply leq_trans with (n := num_mid_jobs.+1 * task_period tsk);
              last by apply workload_bound_many_periods_in_between.
            rewrite -addn1 addnC mulnDl mul1n.
            by rewrite leq_add2l; last by apply PARAMS3.
          }
        Qed.

        (* If n_k = num_mid_jobs + 1, then the workload bound holds. *)
        Lemma workload_bound_n_k_equals_num_mid_jobs_plus_1 :
          num_mid_jobs.+1 = n_k ->
          service_during sched j_lst t1 t2 +
            service_during sched j_fst t1 t2 +
            \sum_(0 <= i < num_mid_jobs)
             service_during sched (nth elem sorted_jobs i.+1) t1 t2
          <= workload_bound.
        Proof.
          unfold workload_bound, W; fold n_k.
          move => NK; rewrite -NK.
          rewrite -{2}addn1 mulnDl mul1n [_* _ + _]addnC addnA addn_minl.
          apply leq_add; last by apply workload_bound_service_of_middle_jobs. 
          rewrite leq_min; apply/andP; split.
          {
            assert (SIZE: 0 < size sorted_jobs).
              by rewrite H_at_least_two_jobs.
            have INfst := workload_bound_j_fst_is_job_of_tsk SIZE elem;
            have INlst := workload_bound_j_lst_is_job_of_tsk; des.
            by apply leq_add; apply cumulative_service_le_task_cost with (task_deadline0 := task_deadline)
                             (job_cost0 := job_cost) (job_deadline0 := job_deadline) (job_task0 := job_task).
          }
          {
            rewrite subnAC subnK; last first.
            {
              assert (TMP: delta + R_tsk = task_cost tsk + (delta + R_tsk - task_cost tsk));
                first by rewrite subnKC; [by ins | by rewrite -[task_cost _]add0n; apply leq_add].
              rewrite TMP; clear TMP.
              rewrite -{1}[task_cost _]addn0 -addnBA NK; [by apply leq_add | by apply leq_trunc_div].
            }
            apply leq_trans with (delta + R_tsk - (job_arrival j_lst - job_arrival j_fst)).
            {
              rewrite addnC -workload_bound_simpl_expression_with_first_and_last.
              by apply workload_bound_service_of_first_and_last_jobs.
            }
            {
              by apply leq_sub2l, workload_bound_many_periods_in_between.
            }
          }
        Qed.
        
      End WorkloadTwoOrMoreJobs.

      (* Using the lemmas above, we prove the main theorem about the workload bound. *)
      Theorem workload_bounded_by_W :
        workload_of tsk t1 (t1 + delta) <= workload_bound.
      Proof.
        unfold workload_of, workload_bound, W in *; ins; des.
        fold n_k.

        (* Use the definition of workload based on list of jobs. *)
        rewrite workload_eq_workload_joblist.

        (* Now we order the list by job arrival time. *)
        rewrite workload_bound_simpl_by_sorting_scheduled_jobs.

        (* Next, we show that the workload bound holds if n_k
           is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k) eqn:NUM;
          first by apply workload_bound_holds_for_at_most_n_k_jobs.
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Find some dummy element to use in the nth function *)
        assert (EX: exists elem: JobIn arr_seq, True).
          destruct sorted_jobs; [ by rewrite ltn0 in NUM | by exists j].
        destruct EX as [elem _].

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First, we show that the bound holds for an empty list of jobs. *)
        destruct (size sorted_jobs) as [| n] eqn:SIZE;
          first by rewrite big_geq.
        
        (* Then, we show the same for a singleton set of jobs. *)
        destruct n as [| num_mid_jobs];
          first by apply workload_bound_holds_for_a_single_job; rewrite SIZE.
        
        (* Knowing that we have at least two elements, we take first and last out of the sum *) 
        rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
        rewrite addnA addnC addnA.
    
        (* There are two cases to be analyze since n <= n_k < n + 2,
           where n is the number of middle jobs. *)
        have NK := workload_bound_n_k_covers_middle_jobs num_mid_jobs SIZE elem.
        move: NK; rewrite leq_eqVlt orbC leq_eqVlt; move => /orP [NK | /eqP NK].
        move: NK => /orP [/eqP NK | NK]; last by rewrite ltnS leqNgt NK in NUM.
        {
          (* Case 1: n_k = n + 1, where n is the number of middle jobs. *)
          by apply (workload_bound_n_k_equals_num_mid_jobs_plus_1 num_mid_jobs).
        }
        {
          (* Case 2: n_k = n, where n is the number of middle jobs. *)
          by apply (workload_bound_n_k_equals_num_mid_jobs num_mid_jobs).
        }
      Qed.

    End MainProof.
    
  End ProofWorkloadBound.

End WorkloadBound.