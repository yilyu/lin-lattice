theory HWQQueueLemmas
  imports USpecMembership
begin

(* ========================================================== *)
(* Auxiliary results for the HWQ queue linearizability proof.  *)
(* ========================================================== *)

subsection \<open>USpec membership of reachable HWQ-U states\<close>

theorem reachable_HWQU_U_component_satisfies_USpec:
  assumes REACH: "Reachable_Sys s"
  shows "HWQU_U_satisfies_USpec s"
  using REACH
  by (rule reachable_HWQU_U_satisfies_USpec)


theorem system_invariant_HWQU_U_component_satisfies_USpec:
  assumes INV: "system_invariant s"
  shows "HWQU_U_satisfies_USpec s"
  using INV
  by (rule system_invariant_HWQU_U_satisfies_USpec)


subsection \<open>Recorded histories\<close>

theorem system_invariant_HWQU_recorded_history_true_queue_linearizable:
  assumes INV: "system_invariant s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using INV
  by (rule system_invariant_his_seq_true_queue_linearizable)


theorem reachable_HWQU_recorded_history_true_queue_linearizable:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using REACH
  by (rule reachable_his_seq_true_queue_linearizable)


theorem HWQ_recorded_history_linearizable_wrt_queue_spec:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
  using REACH
  by (rule reachable_HWQU_recorded_history_true_queue_linearizable)


subsection \<open>Projected real histories\<close>

theorem system_invariant_HWQU_projected_real_history_true_queue_linearizable:
  assumes INV: "system_invariant s"
      and PROJ: "RealHistoryProjection realH s"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
  using INV PROJ
  by (rule system_invariant_projected_real_history_true_queue_linearizable)


theorem reachable_HWQU_projected_real_history_true_queue_linearizable:
  assumes REACH: "Reachable_Sys s"
      and PROJ: "RealHistoryProjection realH s"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
  using REACH PROJ
  by (rule reachable_projected_real_history_true_queue_linearizable)


theorem HWQ_projected_real_history_linearizable_wrt_queue_spec:
  assumes REACH: "Reachable_Sys s"
      and PROJ: "RealHistoryProjection realH s"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
  using REACH PROJ
  by (rule reachable_HWQU_projected_real_history_true_queue_linearizable)

end
