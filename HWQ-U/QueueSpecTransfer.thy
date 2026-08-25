theory QueueSpecTransfer
  imports QueueSpecLemmas
begin

text \<open>
This theory contains paper-facing wrappers for the queue-specification transfer
used in the HWQ case study.  The older theorem names with ``old_queue_spec''
and ``true_queue_spec'' are kept only for backwards compatibility with the
existing proof scripts.  In the paper-facing layer, ``auxiliary queue
invariants'' refers to the internal legality predicate `Legal_Queue_Seq`, and
``QueueSeqSpec'' refers to the standard FIFO queue sequential specification
`HWQ_QueueSeqSpec`.
\<close>

(* ========================================================== *)
(* Paper-level queue-spec transfer theorems for HWQ-U.         *)
(* ========================================================== *)

subsection \<open>Linearization sequence satisfies the queue specification\<close>

theorem HWQ_linearization_sequence_satisfies_old_queue_spec:
  assumes INV: "system_invariant s"
  shows "Legal_Queue_Seq (lin_seq s)"
  using INV
  by (rule system_invariant_lin_seq_Legal_Queue_Seq)


theorem HWQ_linearization_sequence_satisfies_true_queue_spec:
  assumes INV: "system_invariant s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
  using INV
  by (rule system_invariant_lin_seq_in_HWQ_QueueSeqSpec)


theorem reachable_HWQ_linearization_sequence_satisfies_true_queue_spec:
  assumes REACH: "Reachable_Sys s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
  using REACH
  by (rule reachable_lin_seq_in_HWQ_QueueSeqSpec)


theorem HWQ_linearization_sequence_satisfies_Queue:
  assumes INV: "system_invariant s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
  using INV
  by (rule HWQ_linearization_sequence_satisfies_true_queue_spec)


subsection \<open>Recorded history is linearizable with respect to Queue\<close>

theorem HWQ_recorded_history_linearizable_by_true_queue_spec:
  assumes INV: "system_invariant s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using INV
  by (rule system_invariant_his_seq_true_queue_linearizable)


theorem reachable_HWQ_recorded_history_linearizable_by_true_queue_spec:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using REACH
  by (rule reachable_his_seq_true_queue_linearizable)


theorem HWQ_recorded_history_linearizable_wrt_Queue:
  assumes INV: "system_invariant s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using INV
  by (rule HWQ_recorded_history_linearizable_by_true_queue_spec)


theorem reachable_HWQ_recorded_history_linearizable_wrt_Queue:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using REACH
  by (rule reachable_HWQ_recorded_history_linearizable_by_true_queue_spec)




subsection \<open>Clean paper-facing aliases\<close>

theorem HWQ_linearization_sequence_satisfies_auxiliary_queue_invariants:
  assumes INV: "system_invariant s"
  shows "Legal_Queue_Seq (lin_seq s)"
  using INV
  by (rule HWQ_linearization_sequence_satisfies_old_queue_spec)


theorem HWQ_linearization_sequence_satisfies_QueueSeqSpec:
  assumes INV: "system_invariant s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
  using INV
  by (rule HWQ_linearization_sequence_satisfies_true_queue_spec)


theorem reachable_HWQ_linearization_sequence_satisfies_QueueSeqSpec:
  assumes REACH: "Reachable_Sys s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
  using REACH
  by (rule reachable_HWQ_linearization_sequence_satisfies_true_queue_spec)


theorem HWQ_recorded_history_linearizable_wrt_QueueSeqSpec:
  assumes INV: "system_invariant s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using INV
  by (rule HWQ_recorded_history_linearizable_by_true_queue_spec)


theorem reachable_HWQ_recorded_history_linearizable_wrt_QueueSeqSpec:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using REACH
  by (rule reachable_HWQ_recorded_history_linearizable_by_true_queue_spec)


subsection \<open>Packaged transfer statements\<close>

theorem HWQ_linearization_sequence_satisfies_old_and_true_queue_spec:
  assumes INV: "system_invariant s"
  shows "Legal_Queue_Seq (lin_seq s) \<and>
         lin_seq s \<in> HWQ_QueueSeqSpec"
  using INV
  by (rule system_invariant_lin_seq_satisfies_old_and_true_queue_spec)


theorem reachable_HWQ_linearization_sequence_satisfies_old_and_true_queue_spec:
  assumes REACH: "Reachable_Sys s"
  shows "Legal_Queue_Seq (lin_seq s) \<and>
         lin_seq s \<in> HWQ_QueueSeqSpec"
  using REACH
  by (rule reachable_lin_seq_satisfies_old_and_true_queue_spec)


theorem HWQ_recorded_history_linearizable_wrt_queue_spec_transfer:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using REACH
  by (rule reachable_his_seq_true_queue_linearizable)

end
