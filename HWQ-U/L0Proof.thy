theory L0Proof
  imports
    Model
    PureLib
    StateLib
    DeqLib
    EnqLib
    L0Lemmas
begin

(* ========================================================== *)
(* Preservation of the system invariant for the L0 transition  *)
(* ========================================================== *)

lemma L0_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "L0 p s s'"
  shows "system_invariant s'"
proof -
  note bridge_defs =
    program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def
    i_var_def j_var_def l_var_def x_var_def v_var_def
    s_var_def lin_seq_def his_seq_def

  have Simulate_PC_s: "Simulate_PC s"
    and TypeOK_s: "TypeOK s"
    and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s"
    and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s"
    and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s"
    and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s"
    and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s"
    and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s"
    and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
    and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s"
    and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s"
    using INV unfolding system_invariant_def by auto

  have pc_L0: "program_counter s p = ''L0''"
    and Simulate_PC_s': "Simulate_PC s'"
    using L0_step_facts[OF STEP] by auto

  have pc_cases: "program_counter s' p = ''E1'' \<or> program_counter s' p = ''D1''"
    using L0_pc_cases[OF STEP] .

  show ?thesis
  proof (cases "program_counter s' p = ''E1''")
    case True

    have s'_def: "s' = L0_E1_update_state s p"
      using L0_E1_state[OF STEP True] .
    have lin_seq_eq: "lin_seq s' = lin_seq s"
      using L0_E1_lin_unchanged[OF STEP True] .

    have TypeOK_s': "TypeOK s'"
      using TypeOK_s s'_def
      unfolding TypeOK_def L0_E1_update_state_def V_var_def
      by (auto simp: Let_def bridge_defs Val_def BOT_def)

    have sI1_s': "sI1_Zero_Index_BOT s'"
      using sI1_Zero_Index_BOT_s s'_def
      unfolding sI1_Zero_Index_BOT_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI2_s': "sI2_X_var_Upper_Bound s'"
      using sI2_X_var_Upper_Bound_s s'_def
      unfolding sI2_X_var_Upper_Bound_def L0_E1_update_state_def V_var_def
      by (auto simp: Let_def bridge_defs Val_def BOT_def)

    have sI3_s': "sI3_E2_Slot_Exclusive s'"
      using sI3_E2_Slot_Exclusive_s pc_L0 s'_def
      unfolding sI3_E2_Slot_Exclusive_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI4_s': "sI4_E3_Qback_Written s'"
      using sI4_E3_Qback_Written_s pc_L0 s'_def
      unfolding sI4_E3_Qback_Written_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI5_s': "sI5_D2_Local_Bound s'"
      using sI5_D2_Local_Bound_s pc_L0 s'_def
      unfolding sI5_D2_Local_Bound_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI6_s': "sI6_D3_Scan_Pointers s'"
      using sI6_D3_Scan_Pointers_s pc_L0 s'_def
      unfolding sI6_D3_Scan_Pointers_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI7_s': "sI7_D4_Deq_Result s'"
      using sI7_D4_Deq_Result_s pc_L0 s'_def
      unfolding sI7_D4_Deq_Result_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI8_s': "sI8_Q_Qback_Sync s'"
      using sI8_Q_Qback_Sync_s s'_def
      unfolding sI8_Q_Qback_Sync_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI9_s': "sI9_Qback_Discrepancy_E3 s'"
      using sI9_Qback_Discrepancy_E3_s s'_def
      unfolding sI9_Qback_Discrepancy_E3_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI10_s': "sI10_Qback_Unique_Vals s'"
      using sI10_Qback_Unique_Vals_s s'_def
      unfolding sI10_Qback_Unique_Vals_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    (* The large history and linearization proof block for this branch has been moved to L0Lemmas.thy. *)
    (* As in D3Proof.thy, we keep only the main proof skeleton and the final assembly here. *)
    have E1_rest:
      "hI3_L0_E_Phase_Bounds s' \<and>
       hI2_SSN_Bounds s' \<and>
       sI11_x_var_Scope s' \<and>
       hI1_E_Phase_Pending_Enq s' \<and>
       sI12_D3_Scanned_Prefix s' \<and>
       hI4_X_var_Lin_Sync s' \<and>
       hI7_His_WF s' \<and>
       hI8_Val_Unique s' \<and>
       hI5_SSN_Unique s' \<and>
       hI6_SSN_Order s' \<and>
       hI9_Deq_Ret_Unique s' \<and>
       hI10_Enq_Call_Existence s' \<and>
       hI11_Enq_Ret_Existence s' \<and>
       hI12_D_Phase_Pending_Deq s' \<and>
       hI13_Qback_Deq_Sync s' \<and>
       hI14_Pending_Enq_Qback_Exclusivity s' \<and>
       hI15_Deq_Result_Exclusivity s' \<and>
       hI16_BO_BT_No_HB s' \<and>
       hI17_BT_BT_No_HB s' \<and>
       hI18_Idx_Order_No_Rev_HB s' \<and>
       hI19_Scanner_Catches_Later_Enq s' \<and>
       hI20_Enq_Val_Valid s' \<and>
       hI21_Ret_Implies_Call s' \<and>
       hI22_Deq_Local_Pattern s' \<and>
       hI23_Deq_Call_Ret_Balanced s' \<and>
       hI24_HB_Implies_Idx_Order s' \<and>
       hI25_Enq_Call_Ret_Balanced s' \<and>
       hI26_DeqRet_D4_Mutex s' \<and>
       hI27_Pending_PC_Sync s' \<and>
       hI28_Fresh_Enq_Immunity s' \<and>
       hI29_E2_Scanner_Immunity s' \<and>
       hI30_Ticket_HB_Immunity s' \<and>
       lI1_Op_Sets_Equivalence s' \<and>
       lI2_Op_Cardinality s' \<and>
       lI3_HB_Ret_Lin_Sync s' \<and>
       lI4_FIFO_Semantics s' \<and>
       lI5_SA_Prefix s' \<and>
       lI6_D4_Deq_Linearized s' \<and>
       lI7_D4_Deq_Deq_HB s' \<and>
       lI8_D3_Deq_Returned s' \<and>
       lI9_D1_D2_Deq_Returned s' \<and>
       lI10_D4_Enq_Deq_HB s' \<and>
       lI11_D4_Deq_Unique s' \<and>
       data_independent (lin_seq s')"
      using L0_E1_preserves_rest[OF INV STEP True] .

    from E1_rest have
      hI3_s': "hI3_L0_E_Phase_Bounds s'"
      and hI2_s': "hI2_SSN_Bounds s'"
      and sI11_s': "sI11_x_var_Scope s'"
      and hI1_s': "hI1_E_Phase_Pending_Enq s'"
      and sI12_s': "sI12_D3_Scanned_Prefix s'"
      and hI4_s': "hI4_X_var_Lin_Sync s'"
      and hI7_s': "hI7_His_WF s'"
      and hI8_s': "hI8_Val_Unique s'"
      and hI5_s': "hI5_SSN_Unique s'"
      and hI6_s': "hI6_SSN_Order s'"
      and hI9_s': "hI9_Deq_Ret_Unique s'"
      and hI10_s': "hI10_Enq_Call_Existence s'"
      and hI11_s': "hI11_Enq_Ret_Existence s'"
      and hI12_s': "hI12_D_Phase_Pending_Deq s'"
      and hI13_s': "hI13_Qback_Deq_Sync s'"
      and hI14_s': "hI14_Pending_Enq_Qback_Exclusivity s'"
      and hI15_s': "hI15_Deq_Result_Exclusivity s'"
      and hI16_s': "hI16_BO_BT_No_HB s'"
      and hI17_s': "hI17_BT_BT_No_HB s'"
      and hI18_s': "hI18_Idx_Order_No_Rev_HB s'"
      and hI19_s': "hI19_Scanner_Catches_Later_Enq s'"
      and hI20_s': "hI20_Enq_Val_Valid s'"
      and hI21_s': "hI21_Ret_Implies_Call s'"
      and hI22_s': "hI22_Deq_Local_Pattern s'"
      and hI23_s': "hI23_Deq_Call_Ret_Balanced s'"
      and hI24_s': "hI24_HB_Implies_Idx_Order s'"
      and hI25_s': "hI25_Enq_Call_Ret_Balanced s'"
      and hI26_s': "hI26_DeqRet_D4_Mutex s'"
      and hI27_s': "hI27_Pending_PC_Sync s'"
      and hI28_s': "hI28_Fresh_Enq_Immunity s'"
      and hI29_s': "hI29_E2_Scanner_Immunity s'"
      and hI30_s': "hI30_Ticket_HB_Immunity s'"
      and lI1_s': "lI1_Op_Sets_Equivalence s'"
      and lI2_s': "lI2_Op_Cardinality s'"
      and lI3_s': "lI3_HB_Ret_Lin_Sync s'"
      and lI4_s': "lI4_FIFO_Semantics s'"
      and lI5_s': "lI5_SA_Prefix s'"
      and lI6_s': "lI6_D4_Deq_Linearized s'"
      and lI7_s': "lI7_D4_Deq_Deq_HB s'"
      and lI8_s': "lI8_D3_Deq_Returned s'"
      and lI9_s': "lI9_D1_D2_Deq_Returned s'"
      and lI10_s': "lI10_D4_Enq_Deq_HB s'"
      and lI11_s': "lI11_D4_Deq_Unique s'"
      and di_s': "data_independent (lin_seq s')"
      by simp_all

    show ?thesis
      unfolding system_invariant_def
      using Simulate_PC_s' TypeOK_s'
        sI1_s' sI2_s' sI3_s' sI4_s' sI5_s' sI6_s' sI7_s' hI3_s' sI8_s' sI9_s' sI10_s'
        hI2_s' sI11_s' hI1_s' sI12_s' hI4_s' hI7_s' hI8_s' hI5_s' hI6_s' hI9_s' hI10_s'
        hI11_s' hI12_s' hI13_s' hI14_s' hI15_s' hI16_s' hI17_s' hI18_s' hI19_s' hI20_s'
        hI21_s' hI22_s' hI23_s' hI24_s' hI25_s' hI26_s' hI27_s' hI28_s' hI29_s' hI30_s'
        lI1_s' lI2_s' lI3_s' lI4_s' lI5_s' lI6_s' lI7_s' lI8_s' lI9_s' lI10_s' lI11_s' di_s'
      by blast
  next
    case False
    then have D1: "program_counter s' p = ''D1''"
      using pc_cases by blast

    have s'_def: "s' = L0_D1_update_state s p"
      using L0_D1_state[OF STEP D1] .
    have lin_seq_eq: "lin_seq s' = lin_seq s"
      using L0_D1_lin_unchanged[OF STEP D1] .

    have TypeOK_s': "TypeOK s'"
      using TypeOK_s s'_def
      unfolding TypeOK_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI1_s': "sI1_Zero_Index_BOT s'"
      using sI1_Zero_Index_BOT_s s'_def
      unfolding sI1_Zero_Index_BOT_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI2_s': "sI2_X_var_Upper_Bound s'"
      using sI2_X_var_Upper_Bound_s s'_def
      unfolding sI2_X_var_Upper_Bound_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI3_s': "sI3_E2_Slot_Exclusive s'"
      using sI3_E2_Slot_Exclusive_s pc_L0 s'_def
      unfolding sI3_E2_Slot_Exclusive_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI4_s': "sI4_E3_Qback_Written s'"
      using sI4_E3_Qback_Written_s pc_L0 s'_def
      unfolding sI4_E3_Qback_Written_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI5_s': "sI5_D2_Local_Bound s'"
      using sI5_D2_Local_Bound_s pc_L0 s'_def
      unfolding sI5_D2_Local_Bound_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI6_s': "sI6_D3_Scan_Pointers s'"
      using sI6_D3_Scan_Pointers_s pc_L0 s'_def
      unfolding sI6_D3_Scan_Pointers_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI7_s': "sI7_D4_Deq_Result s'"
      using sI7_D4_Deq_Result_s pc_L0 s'_def
      unfolding sI7_D4_Deq_Result_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI8_s': "sI8_Q_Qback_Sync s'"
      using sI8_Q_Qback_Sync_s s'_def
      unfolding sI8_Q_Qback_Sync_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI9_s': "sI9_Qback_Discrepancy_E3 s'"
      using sI9_Qback_Discrepancy_E3_s s'_def
      unfolding sI9_Qback_Discrepancy_E3_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI10_s': "sI10_Qback_Unique_Vals s'"
      using sI10_Qback_Unique_Vals_s s'_def
      unfolding sI10_Qback_Unique_Vals_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    (* The large history and linearization proof block for this branch has been moved to L0Lemmas.thy. *)
    (* As in D3Proof.thy, we keep only the main proof skeleton and the final assembly here. *)
    have D1_rest:
      "hI3_L0_E_Phase_Bounds s' \<and>
       hI2_SSN_Bounds s' \<and>
       sI11_x_var_Scope s' \<and>
       hI1_E_Phase_Pending_Enq s' \<and>
       sI12_D3_Scanned_Prefix s' \<and>
       hI4_X_var_Lin_Sync s' \<and>
       hI7_His_WF s' \<and>
       hI8_Val_Unique s' \<and>
       hI5_SSN_Unique s' \<and>
       hI6_SSN_Order s' \<and>
       hI9_Deq_Ret_Unique s' \<and>
       hI10_Enq_Call_Existence s' \<and>
       hI11_Enq_Ret_Existence s' \<and>
       hI12_D_Phase_Pending_Deq s' \<and>
       hI13_Qback_Deq_Sync s' \<and>
       hI14_Pending_Enq_Qback_Exclusivity s' \<and>
       hI15_Deq_Result_Exclusivity s' \<and>
       hI16_BO_BT_No_HB s' \<and>
       hI17_BT_BT_No_HB s' \<and>
       hI18_Idx_Order_No_Rev_HB s' \<and>
       hI19_Scanner_Catches_Later_Enq s' \<and>
       hI20_Enq_Val_Valid s' \<and>
       hI21_Ret_Implies_Call s' \<and>
       hI22_Deq_Local_Pattern s' \<and>
       hI23_Deq_Call_Ret_Balanced s' \<and>
       hI24_HB_Implies_Idx_Order s' \<and>
       hI25_Enq_Call_Ret_Balanced s' \<and>
       hI26_DeqRet_D4_Mutex s' \<and>
       hI27_Pending_PC_Sync s' \<and>
       hI28_Fresh_Enq_Immunity s' \<and>
       hI29_E2_Scanner_Immunity s' \<and>
       hI30_Ticket_HB_Immunity s' \<and>
       lI1_Op_Sets_Equivalence s' \<and>
       lI2_Op_Cardinality s' \<and>
       lI3_HB_Ret_Lin_Sync s' \<and>
       lI4_FIFO_Semantics s' \<and>
       lI5_SA_Prefix s' \<and>
       lI6_D4_Deq_Linearized s' \<and>
       lI7_D4_Deq_Deq_HB s' \<and>
       lI8_D3_Deq_Returned s' \<and>
       lI9_D1_D2_Deq_Returned s' \<and>
       lI10_D4_Enq_Deq_HB s' \<and>
       lI11_D4_Deq_Unique s' \<and>
       data_independent (lin_seq s')"
      using L0_D1_preserves_rest[OF INV STEP D1] .

    from D1_rest have
      hI3_s': "hI3_L0_E_Phase_Bounds s'"
      and hI2_s': "hI2_SSN_Bounds s'"
      and sI11_s': "sI11_x_var_Scope s'"
      and hI1_s': "hI1_E_Phase_Pending_Enq s'"
      and sI12_s': "sI12_D3_Scanned_Prefix s'"
      and hI4_s': "hI4_X_var_Lin_Sync s'"
      and hI7_s': "hI7_His_WF s'"
      and hI8_s': "hI8_Val_Unique s'"
      and hI5_s': "hI5_SSN_Unique s'"
      and hI6_s': "hI6_SSN_Order s'"
      and hI9_s': "hI9_Deq_Ret_Unique s'"
      and hI10_s': "hI10_Enq_Call_Existence s'"
      and hI11_s': "hI11_Enq_Ret_Existence s'"
      and hI12_s': "hI12_D_Phase_Pending_Deq s'"
      and hI13_s': "hI13_Qback_Deq_Sync s'"
      and hI14_s': "hI14_Pending_Enq_Qback_Exclusivity s'"
      and hI15_s': "hI15_Deq_Result_Exclusivity s'"
      and hI16_s': "hI16_BO_BT_No_HB s'"
      and hI17_s': "hI17_BT_BT_No_HB s'"
      and hI18_s': "hI18_Idx_Order_No_Rev_HB s'"
      and hI19_s': "hI19_Scanner_Catches_Later_Enq s'"
      and hI20_s': "hI20_Enq_Val_Valid s'"
      and hI21_s': "hI21_Ret_Implies_Call s'"
      and hI22_s': "hI22_Deq_Local_Pattern s'"
      and hI23_s': "hI23_Deq_Call_Ret_Balanced s'"
      and hI24_s': "hI24_HB_Implies_Idx_Order s'"
      and hI25_s': "hI25_Enq_Call_Ret_Balanced s'"
      and hI26_s': "hI26_DeqRet_D4_Mutex s'"
      and hI27_s': "hI27_Pending_PC_Sync s'"
      and hI28_s': "hI28_Fresh_Enq_Immunity s'"
      and hI29_s': "hI29_E2_Scanner_Immunity s'"
      and hI30_s': "hI30_Ticket_HB_Immunity s'"
      and lI1_s': "lI1_Op_Sets_Equivalence s'"
      and lI2_s': "lI2_Op_Cardinality s'"
      and lI3_s': "lI3_HB_Ret_Lin_Sync s'"
      and lI4_s': "lI4_FIFO_Semantics s'"
      and lI5_s': "lI5_SA_Prefix s'"
      and lI6_s': "lI6_D4_Deq_Linearized s'"
      and lI7_s': "lI7_D4_Deq_Deq_HB s'"
      and lI8_s': "lI8_D3_Deq_Returned s'"
      and lI9_s': "lI9_D1_D2_Deq_Returned s'"
      and lI10_s': "lI10_D4_Enq_Deq_HB s'"
      and lI11_s': "lI11_D4_Deq_Unique s'"
      and di_s': "data_independent (lin_seq s')"
      by simp_all

    show ?thesis
      unfolding system_invariant_def
      using Simulate_PC_s' TypeOK_s'
        sI1_s' sI2_s' sI3_s' sI4_s' sI5_s' sI6_s' sI7_s' hI3_s' sI8_s' sI9_s' sI10_s'
        hI2_s' sI11_s' hI1_s' sI12_s' hI4_s' hI7_s' hI8_s' hI5_s' hI6_s' hI9_s' hI10_s'
        hI11_s' hI12_s' hI13_s' hI14_s' hI15_s' hI16_s' hI17_s' hI18_s' hI19_s' hI20_s'
        hI21_s' hI22_s' hI23_s' hI24_s' hI25_s' hI26_s' hI27_s' hI28_s' hI29_s' hI30_s'
        lI1_s' lI2_s' lI3_s' lI4_s' lI5_s' lI6_s' lI7_s' lI8_s' lI9_s' lI10_s' lI11_s' di_s'
      by blast
  qed
qed

end
