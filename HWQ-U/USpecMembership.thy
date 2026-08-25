theory USpecMembership
  imports USpecMembershipLemmas
begin

(* ========================================================== *)
(* Proof that the U component maintained by HWQ-U satisfies    *)
(* the USpec-side obligations.                                *)
(* ========================================================== *)

subsection \<open>USpec membership of invariant states\<close>

theorem system_invariant_HWQU_U_satisfies_USpec:
  assumes INV: "system_invariant s"
  shows "HWQU_U_satisfies_USpec s"
proof -
  have U1: "uI1_USpec_EffOps_Lin s"
    using INV
    unfolding system_invariant_def
    by blast

  have U2: "uI2_USpec_E1UE2 s"
    using INV
    unfolding system_invariant_def
    by blast

  have U3: "uI3_USpec_D3UD2 s"
    using INV
    unfolding system_invariant_def
    by blast

  have EFF: "uspec_effOps s = set (lin_seq s)"
    using U1
    unfolding uI1_USpec_EffOps_Lin_def
    by simp

  have FIN: "finite (uspec_effOps s)"
    using EFF
    by simp

  have EQ: "Equivalent_History (his_seq s) (lin_seq s)"
    using INV
    by (rule system_invariant_his_lin_equiv)

  have CALLED:
    "\<forall>a \<in> set (lin_seq s). OpCalledInHis (his_seq s) a"
    using EQ
    by (meson Equivalent_History_imp_all_ops_called)

  have HB: "HB_consistent (lin_seq s) (his_seq s)"
    using INV
    by (rule system_invariant_lin_seq_HB_consistent)

  have QSPEC: "lin_seq s \<in> HWQ_QueueSeqSpec"
    using INV
    by (rule system_invariant_lin_seq_in_HWQ_QueueSeqSpec)

  have DI: "data_independent (lin_seq s)"
    using INV
    unfolding system_invariant_def
    by blast

  show ?thesis
    unfolding HWQU_U_satisfies_USpec_def
    using U1 U2 U3 EFF FIN CALLED HB QSPEC DI
    by blast
qed

theorem HWQU_U_component_satisfies_USpec_from_invariant:
  assumes INV: "system_invariant s"
  shows "HWQU_U_satisfies_USpec s"
  using INV
  by (rule system_invariant_HWQU_U_satisfies_USpec)


subsection \<open>USpec membership of reachable states\<close>

corollary reachable_HWQU_U_satisfies_USpec:
  assumes REACH: "Reachable_Sys s"
  shows "HWQU_U_satisfies_USpec s"
proof -
  have INV: "system_invariant s"
    using REACH
    by (rule Reachable_Sys_in_SimRel_U)

  show ?thesis
    using INV
    by (rule system_invariant_HWQU_U_satisfies_USpec)
qed

theorem HWQU_U_component_satisfies_USpec_from_reachable_state:
  assumes REACH: "Reachable_Sys s"
  shows "HWQU_U_satisfies_USpec s"
  using REACH
  by (rule reachable_HWQU_U_satisfies_USpec)


subsection \<open>Paper-facing membership statements\<close>

theorem HWQU_state_satisfies_USpec_membership:
  assumes INV: "system_invariant s"
  shows "HWQU_U_satisfies_USpec s"
  using INV
  by (rule system_invariant_HWQU_U_satisfies_USpec)

theorem reachable_HWQU_state_satisfies_USpec_membership:
  assumes REACH: "Reachable_Sys s"
  shows "HWQU_U_satisfies_USpec s"
  using REACH
  by (rule reachable_HWQU_U_satisfies_USpec)


subsection \<open>Effective operations coincide with linearization operations\<close>

theorem HWQU_linearization_operations_are_effective_operations:
  assumes INV: "system_invariant s"
  shows "uspec_effOps s = set (lin_seq s)"
proof -
  have SAT: "HWQU_U_satisfies_USpec s"
    using INV
    by (rule HWQU_state_satisfies_USpec_membership)

  show ?thesis
    using SAT
    unfolding HWQU_U_satisfies_USpec_def
    by blast
qed

theorem reachable_HWQU_linearization_operations_are_effective_operations:
  assumes REACH: "Reachable_Sys s"
  shows "uspec_effOps s = set (lin_seq s)"
proof -
  have INV: "system_invariant s"
    using REACH
    by (rule Reachable_Sys_in_SimRel_U)

  show ?thesis
    using INV
    by (rule HWQU_linearization_operations_are_effective_operations)
qed

theorem HWQU_effective_operations_are_linearization_operations:
  assumes INV: "system_invariant s"
  shows "uspec_effOps s = set (lin_seq s)"
  using INV
  by (rule HWQU_linearization_operations_are_effective_operations)

theorem reachable_HWQU_effective_operations_are_linearization_operations:
  assumes REACH: "Reachable_Sys s"
  shows "uspec_effOps s = set (lin_seq s)"
  using REACH
  by (rule reachable_HWQU_linearization_operations_are_effective_operations)

end
