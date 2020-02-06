Require Import rt.util.all.
Require Import rt.model.jitter.arrival_sequence rt.model.jitter.schedule
               rt.model.jitter.interference rt.model.jitter.priority.
Require Import rt.analysis.jitter.workload_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module InterferenceBoundJitter.

  Import ArrivalSequence WorkloadBoundJitter Priority Interference.

  Section Definitions.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    Variable task_jitter: sporadic_task -> time.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section PerTask.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.
    
      (* Based on the workload bound, Bertogna and Cirinei define the
         following interference bound for a task. *)
      Definition interference_bound_generic :=
        minn (W_jitter task_cost task_period task_jitter tsk_other R_other delta) (delta - (task_cost tsk) + 1).

    End PerTask.

    Section AllTasks.
      
      (* Assume an FP policy. *)
      Variable higher_eq_priority: FP_policy sporadic_task.

      Let can_interfere_with_tsk := fp_can_interfere_with higher_eq_priority tsk.
      
      (* The total interference incurred by tsk is bounded by the sum
         of individual task interferences. *)
      Definition total_interference_bound_fp :=
        \sum_((tsk_other, R_other) <- R_prev | can_interfere_with_tsk tsk_other)
           interference_bound_generic (tsk_other, R_other).
      
    End AllTasks.

  End Definitions.

End InterferenceBoundJitter.