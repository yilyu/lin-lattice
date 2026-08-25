(* Invariantprove *)
theory D3Proof
  imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    DeqLib
    D3Lemmas
begin

(* ========== transition rule of invariantpreserveprove ========== *)
lemma D3_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_D3 p s s'"
  shows "system_invariant s'"
proof -
    (* Heredefinition one one of unfoldset *)
    note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                       Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def

  (* ================================================================= *)
  (* 1. splitcurrent state of invariant *)
  (* ================================================================= *)
  have TypeOK_s: "TypeOK s" and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s"
    and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s" and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s" and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s" and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s" and sI11_x_var_Scope_s: "sI11_x_var_Scope s"
    and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s"
    and uI1_USpec_EffOps_Lin_s: "uI1_USpec_EffOps_Lin s" and uI2_USpec_E1UE2_s: "uI2_USpec_E1UE2 s" and uI3_USpec_D3UD2_s: "uI3_USpec_D3UD2 s"
    and hI4_X_var_Lin_Sync_s: "hI4_X_var_Lin_Sync s"
    and hI7_His_WF_s: "hI7_His_WF s" and hI8_Val_Unique_s: "hI8_Val_Unique s"
    and hI5_SSN_Unique_s: "hI5_SSN_Unique s" and hI6_SSN_Order_s: "hI6_SSN_Order s"
    and hI9_Deq_Ret_Unique_s: "hI9_Deq_Ret_Unique s" and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" and hI11_Enq_Ret_Existence_s: "hI11_Enq_Ret_Existence s" and hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s"
    and hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s" and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" and hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s" and hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s"
    and hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s" and hI18_Idx_Order_No_Rev_HB_s: "hI18_Idx_Order_No_Rev_HB s" and hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s" and hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s"
    and hI21_Ret_Implies_Call_s: "hI21_Ret_Implies_Call s" and hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s" and hI23_Deq_Call_Ret_Balanced_s: "hI23_Deq_Call_Ret_Balanced s" and hI24_HB_Implies_Idx_Order_s: "hI24_HB_Implies_Idx_Order s"
    and hI25_Enq_Call_Ret_Balanced_s: "hI25_Enq_Call_Ret_Balanced s" and hI26_DeqRet_D4_Mutex_s: "hI26_DeqRet_D4_Mutex s"
    and hI27_Pending_PC_Sync_s: "hI27_Pending_PC_Sync s" and hI28_Fresh_Enq_Immunity_s: "hI28_Fresh_Enq_Immunity s"
    and hI29_E2_Scanner_Immunity_s: "hI29_E2_Scanner_Immunity s"  and hI30_Ticket_HB_Immunity_s: "hI30_Ticket_HB_Immunity s"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s"
    and lI5_SA_Prefix_s: "lI5_SA_Prefix s" and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" and lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" and lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s" and lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s"
    and di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  (* ================================================================= *)
  (* 2. extract D3 of key and update *)
  (* ================================================================= *)
  (* Extractlocal *)
  define jp where "jp = j_var s p"
  define lp where "lp = l_var s p"
  define q_val where "q_val = Q_arr s jp"

  (* Extract *)
  define current_lin where "current_lin = lin_seq s"
  define current_his where "current_his = his_seq s"

  (* Q_val base_lin (modify) *)
  define base_lin where "base_lin =
    (if q_val = BOT then current_lin
     else if should_modify current_lin current_his q_val
          then modify_lin current_lin current_his q_val
          else current_lin)"

(* ================================================================= *)
  (* Proof step: s' is one (CState, UState), must unfold fst and snd of update *)
  (* ================================================================= *)
  have D3_unfolded:
    "program_counter s p = ''D3''"
    "s' = (
       (fst s)\<lparr>
         c_program_counter := (\<lambda>x. if x = p then
                                  (if q_val = BOT then
                                     (if jp = lp - 1 then ''D1'' else ''D3'')
                                   else ''D4'')
                                else CState.c_program_counter (fst s) x),
         Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
         j_var := (\<lambda>x. if x = p then
                      (if q_val = BOT \<and> jp \<noteq> lp - 1 then jp + 1 else jp)
                    else CState.j_var (fst s) x),
         x_var := (\<lambda>x. if x = p then q_val else CState.x_var (fst s) x)
       \<rparr>,
       (if q_val = BOT then
          snd s
        else
          (snd s)\<lparr>
            u_program_counter := (\<lambda>x. if x = p then ''UD3'' else u_program_counter (snd s) x),
            u_lin_seq := base_lin @ [mk_op deq q_val p (s_var s p)],
            u_eff_ops := insert (mk_op deq q_val p (s_var s p)) (u_eff_ops (snd s))
          \<rparr>)
    )"
    using D3_step_unfolded[OF STEP jp_def lp_def q_val_def current_lin_def current_his_def base_lin_def] .

  (* ================================================================= *)
  (* 3. caseprove: Case Empty (q_val = BOT) vs Case Success (q_val \<noteq> BOT) *)
  (* ================================================================= *)
  show ?thesis
  proof (cases "q_val = BOT")
    case True
    (* --------------------------------------------------------------- *)
    (* Case 1: queue empty (has dequeue, has) *)
    (* --------------------------------------------------------------- *)
      note q_is_bot = True

    have D3_bot_simp:
      "lin_seq s' = lin_seq s"
      "his_seq s' = his_seq s"
      "base_lin = lin_seq s"
      "s' = (
        (fst s)\<lparr>
          c_program_counter := (\<lambda>x. if x = p then
               (if jp = lp - 1 then ''D1'' else ''D3'')
             else CState.c_program_counter (fst s) x),
          Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
          j_var := (\<lambda>x. if x = p then
               (if jp \<noteq> lp - 1 then jp + 1 else jp)
             else CState.j_var (fst s) x),
          x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
        \<rparr>,
        snd s
      )"
      using D3_bot_branch_simp[
        OF STEP jp_def lp_def q_val_def current_lin_def current_his_def base_lin_def q_is_bot
    ] .

    note lin_seq_eq = D3_bot_simp(1)
    note his_seq_eq = D3_bot_simp(2)
    note lin_seq_unchanged = D3_bot_simp(3)
    note s'_simple = D3_bot_simp(4)

(* --- prove invariant (Case 1) --- *)

    (* --------------------------------------------------------------- *)
    (* BOT branch of one basic invariantpreserve *)
    (* --------------------------------------------------------------- *)

    have D3_bot_basic:
      "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
      "Q_arr s jp = BOT"
      "TypeOK s'"
      "sI1_Zero_Index_BOT s'"
      "sI2_X_var_Upper_Bound s'"
      "sI3_E2_Slot_Exclusive s'"
      "sI4_E3_Qback_Written s'"
      "sI5_D2_Local_Bound s'"
      "sI6_D3_Scan_Pointers s'"
      using D3_bot_preserves_basic_invariants[
        OF INV
           TypeOK_s
           sI1_Zero_Index_BOT_s
           sI2_X_var_Upper_Bound_s
           sI3_E2_Slot_Exclusive_s
           sI5_D2_Local_Bound_s
           sI6_D3_Scan_Pointers_s
           jp_def lp_def q_val_def q_is_bot
           D3_unfolded(1)
           s'_simple
    ] .

    have pc_update:
      "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
      using D3_bot_basic(1) .

    have Q_jp_bot: "Q_arr s jp = BOT"
      using D3_bot_basic(2) .

    have TypeOK_s': "TypeOK s'"
      using D3_bot_basic(3) .

    have sI1_Zero_Index_BOT_s': "sI1_Zero_Index_BOT s'"
      using D3_bot_basic(4) .

    have sI2_X_var_Upper_Bound_s': "sI2_X_var_Upper_Bound s'"
      using D3_bot_basic(5) .

    have sI3_E2_Slot_Exclusive_s': "sI3_E2_Slot_Exclusive s'"
      using D3_bot_basic(6) .

    have sI4_E3_Qback_Written_s': "sI4_E3_Qback_Written s'"
      using D3_bot_basic(7) .

    have sI5_D2_Local_Bound_s': "sI5_D2_Local_Bound s'"
      using D3_bot_basic(8) .

    have sI6_D3_Scan_Pointers_s': "sI6_D3_Scan_Pointers s'"
      using D3_bot_basic(9) .

    (* ================================================================= *)
    (* BOT branch after: its physical/historyinvariantpreserve *)
    (* ================================================================= *)

    have D3_bot_more:
      "sI7_D4_Deq_Result s'"
      "hI3_L0_E_Phase_Bounds s'"
      "sI8_Q_Qback_Sync s'"
      "sI9_Qback_Discrepancy_E3 s'"
      "sI10_Qback_Unique_Vals s'"
      "hI2_SSN_Bounds s'"
      "sI11_x_var_Scope s'"
      using D3_bot_preserves_more_invariants[
        OF INV
           s'_simple
           his_seq_eq
           D3_unfolded(1)
           sI4_E3_Qback_Written_s'
           Q_jp_bot
           sI7_D4_Deq_Result_s
           hI3_L0_E_Phase_Bounds_s
           sI8_Q_Qback_Sync_s
           sI9_Qback_Discrepancy_E3_s
           sI10_Qback_Unique_Vals_s
           sI11_x_var_Scope_s
    ] .

    have sI7_D4_Deq_Result_s': "sI7_D4_Deq_Result s'"
      using D3_bot_more(1) .

    have hI3_L0_E_Phase_Bounds_s': "hI3_L0_E_Phase_Bounds s'"
      using D3_bot_more(2) .

    have sI8_Q_Qback_Sync_s': "sI8_Q_Qback_Sync s'"
      using D3_bot_more(3) .

    have sI9_Qback_Discrepancy_E3_s': "sI9_Qback_Discrepancy_E3 s'"
      using D3_bot_more(4) .

    have sI10_Qback_Unique_Vals_s': "sI10_Qback_Unique_Vals s'"
      using D3_bot_more(5) .

    have hI2_SSN_Bounds_s': "hI2_SSN_Bounds s'"
      using D3_bot_more(6) .

    have sI11_x_var_Scope_s': "sI11_x_var_Scope s'"
      using D3_bot_more(7) .

    (* ================================================================= *)
    (* BOT branch: Pending / SetA / SetB / TypeB / sI12 *)
    (* ================================================================= *)

    have D3_bot_pending_prefix:
      "hI1_E_Phase_Pending_Enq s'"
      "Q_arr s' = Q_arr s"
      "Qback_arr s' = Qback_arr s"
      "SetA s' = SetA s"
      "SetB s' = SetB s"
      "(\<forall>x. TypeB s' x \<longleftrightarrow> TypeB s x)"
      "sI12_D3_Scanned_Prefix s'"
      using D3_bot_preserves_pending_and_prefix[
        OF INV
           s'_simple[unfolded lp_def]
           his_seq_eq
           D3_unfolded(1)
           jp_def
           q_val_def
           q_is_bot
           sI12_D3_Scanned_Prefix_s
    ] .

    have hI1_E_Phase_Pending_Enq_s': "hI1_E_Phase_Pending_Enq s'"
      using D3_bot_pending_prefix(1) .

    have Q_unchanged: "Q_arr s' = Q_arr s"
      using D3_bot_pending_prefix(2) .

    have T_unchanged: "Qback_arr s' = Qback_arr s"
      using D3_bot_pending_prefix(3) .

    have basic_conservation:
      "his_seq s' = his_seq s"
      "Qback_arr s' = Qback_arr s"
      "SetA s' = SetA s"
      "SetB s' = SetB s"
    proof -
      show "his_seq s' = his_seq s"
        using his_seq_eq .
      show "Qback_arr s' = Qback_arr s"
        using D3_bot_pending_prefix(3) .
      show "SetA s' = SetA s"
        using D3_bot_pending_prefix(4) .
      show "SetB s' = SetB s"
        using D3_bot_pending_prefix(5) .
    qed

    have Q_eq: "Q_arr s' = Q_arr s"
      using D3_bot_pending_prefix(2) .

    have TypeB_eq: "\<And>x. TypeB s' x \<longleftrightarrow> TypeB s x"
      using D3_bot_pending_prefix(6)
      by blast

    have sI12_D3_Scanned_Prefix_s': "sI12_D3_Scanned_Prefix s'"
      using D3_bot_pending_prefix(7) .

    (* ========================================================================= *)
    (* BOT branch: history tail *)
    (* ========================================================================= *)

    have D3_bot_history_tail:
      "hI4_X_var_Lin_Sync s'"
      "hI7_His_WF s'"
      "hI8_Val_Unique s'"
      "hI6_SSN_Order s'"
      "hI5_SSN_Unique s'"
      "hI9_Deq_Ret_Unique s'"
      "hI10_Enq_Call_Existence s'"
      "hI11_Enq_Ret_Existence s'"
      "hI12_D_Phase_Pending_Deq s'"
      "hI13_Qback_Deq_Sync s'"
      "hI14_Pending_Enq_Qback_Exclusivity s'"
      "hI18_Idx_Order_No_Rev_HB s'"
      "hI20_Enq_Val_Valid s'"
      "hI21_Ret_Implies_Call s'"
      "hI22_Deq_Local_Pattern s'"
      "hI23_Deq_Call_Ret_Balanced s'"
      "hI24_HB_Implies_Idx_Order s'"
      "hI25_Enq_Call_Ret_Balanced s'"
      "hI26_DeqRet_D4_Mutex s'"
      "hI27_Pending_PC_Sync s'"
      "hI28_Fresh_Enq_Immunity s'"
      using D3_bot_preserves_history_tail[
        OF INV
           D3_unfolded(1)
           s'_simple
           his_seq_eq
           lin_seq_eq
           Q_unchanged
           T_unchanged
    ] .

    have hI4_X_var_Lin_Sync_s': "hI4_X_var_Lin_Sync s'"
      using D3_bot_history_tail(1) .

    have hI7_His_WF_s': "hI7_His_WF s'"
      using D3_bot_history_tail(2) .

    have hI8_Val_Unique_s': "hI8_Val_Unique s'"
      using D3_bot_history_tail(3) .

    have hI6_SSN_Order_s': "hI6_SSN_Order s'"
      using D3_bot_history_tail(4) .

    have hI5_SSN_Unique_s': "hI5_SSN_Unique s'"
      using D3_bot_history_tail(5) .

    have hI9_Deq_Ret_Unique_s': "hI9_Deq_Ret_Unique s'"
      using D3_bot_history_tail(6) .

    have hI10_Enq_Call_Existence_s': "hI10_Enq_Call_Existence s'"
      using D3_bot_history_tail(7) .

    have hI11_Enq_Ret_Existence_s': "hI11_Enq_Ret_Existence s'"
      using D3_bot_history_tail(8) .

    have hI12_D_Phase_Pending_Deq_s': "hI12_D_Phase_Pending_Deq s'"
      using D3_bot_history_tail(9) .

    have hI13_Qback_Deq_Sync_s': "hI13_Qback_Deq_Sync s'"
      using D3_bot_history_tail(10) .

    have hI14_Pending_Enq_Qback_Exclusivity_s': "hI14_Pending_Enq_Qback_Exclusivity s'"
      using D3_bot_history_tail(11) .

    have "hI15_Deq_Result_Exclusivity s'"
      using D3_BOT_preserves_hI15_Deq_Result_Exclusivity[OF INV D3_unfolded(1) s'_simple his_seq_eq Q_unchanged] .

    have "hI16_BO_BT_No_HB s'"
      using D3_BOT_preserves_hI16_BO_BT_No_HB[OF INV D3_unfolded(1) jp_def lp_def q_val_def q_is_bot s'_simple his_seq_eq Q_unchanged T_unchanged] .

    have "hI17_BT_BT_No_HB s'"
      using D3_BOT_preserves_hI17_BT_BT_No_HB[OF INV D3_unfolded(1) jp_def lp_def q_val_def q_is_bot s'_simple his_seq_eq Q_unchanged T_unchanged] .

    have hI18_Idx_Order_No_Rev_HB_s': "hI18_Idx_Order_No_Rev_HB s'"
      using D3_bot_history_tail(12) .

    have hI20_Enq_Val_Valid_s': "hI20_Enq_Val_Valid s'"
      using D3_bot_history_tail(13) .

    have hI21_Ret_Implies_Call_s': "hI21_Ret_Implies_Call s'"
      using D3_bot_history_tail(14) .

    have "hI19_Scanner_Catches_Later_Enq s'"
      using D3_BOT_preserves_hI19_Scanner_Catches_Later_Enq[OF INV D3_unfolded(1) jp_def lp_def q_val_def q_is_bot s'_simple his_seq_eq Q_unchanged T_unchanged] .

    have hI22_Deq_Local_Pattern_s': "hI22_Deq_Local_Pattern s'"
      using D3_bot_history_tail(15) .

    have hI23_Deq_Call_Ret_Balanced_s': "hI23_Deq_Call_Ret_Balanced s'"
      using D3_bot_history_tail(16) .

    have hI24_HB_Implies_Idx_Order_s': "hI24_HB_Implies_Idx_Order s'"
      using D3_bot_history_tail(17) .

    have hI25_Enq_Call_Ret_Balanced_s': "hI25_Enq_Call_Ret_Balanced s'"
      using D3_bot_history_tail(18) .

    have hI26_DeqRet_D4_Mutex_s': "hI26_DeqRet_D4_Mutex s'"
      using D3_bot_history_tail(19) .

    have hI27_Pending_PC_Sync_s': "hI27_Pending_PC_Sync s'"
      using D3_bot_history_tail(20) .

    have hI28_Fresh_Enq_Immunity_s': "hI28_Fresh_Enq_Immunity s'"
      using D3_bot_history_tail(21) .

    have q_bot_fact: "Q_arr s (j_var s p) = BOT"
      using q_is_bot unfolding Let_def
      using Q_jp_bot jp_def by auto

    have "hI29_E2_Scanner_Immunity s'"
      by (rule hI21_D3_step_helper[OF INV STEP q_bot_fact])

    have "hI30_Ticket_HB_Immunity s'"
      using D3_BOT_preserves_hI30_Ticket_HB_Immunity[OF INV D3_unfolded(1) jp_def lp_def q_val_def q_is_bot s'_simple his_seq_eq Q_unchanged T_unchanged] .

    (* ========================================================================= *)
    (* BOT branch: linearization tail *)
    (* ========================================================================= *)

    have D3_bot_linear_tail:
      "OPLin s' = OPLin s"
      "lI1_Op_Sets_Equivalence s'"
      "lI2_Op_Cardinality s'"
      "lI3_HB_Ret_Lin_Sync s'"
      "lI4_FIFO_Semantics s'"
      "lI5_SA_Prefix s'"
      "lI6_D4_Deq_Linearized s'"
      "lI7_D4_Deq_Deq_HB s'"
      "lI8_D3_Deq_Returned s'"
      "lI9_D1_D2_Deq_Returned s'"
      "lI10_D4_Enq_Deq_HB s'"
      "lI11_D4_Deq_Unique s'"
      "data_independent (lin_seq s')"
      "Simulate_PC s'"
      using D3_bot_preserves_linearization_tail[
        OF INV
           STEP
           D3_unfolded(1)
           s'_simple
           his_seq_eq
           lin_seq_eq
           Q_unchanged
           T_unchanged
           basic_conservation(3)
           basic_conservation(4)
    ] .

    have OPLin_eq: "OPLin s' = OPLin s"
      using D3_bot_linear_tail(1) .

    have "lI1_Op_Sets_Equivalence s'"
      using D3_bot_linear_tail(2) .

    have "lI2_Op_Cardinality s'"
      using D3_bot_linear_tail(3) .

    have "lI3_HB_Ret_Lin_Sync s'"
      using D3_bot_linear_tail(4) .

    have "lI4_FIFO_Semantics s'"
      using D3_bot_linear_tail(5) .

    have "lI5_SA_Prefix s'"
      using D3_bot_linear_tail(6) .

    have "lI6_D4_Deq_Linearized s'"
      using D3_bot_linear_tail(7) .

    have "lI7_D4_Deq_Deq_HB s'"
      using D3_bot_linear_tail(8) .

    have "lI8_D3_Deq_Returned s'"
      using D3_bot_linear_tail(9) .

    have "lI9_D1_D2_Deq_Returned s'"
      using D3_bot_linear_tail(10) .

    have "lI10_D4_Enq_Deq_HB s'"
      using D3_bot_linear_tail(11) .

    have "lI11_D4_Deq_Unique s'"
      using D3_bot_linear_tail(12) .

    have "data_independent (lin_seq s')"
      using D3_bot_linear_tail(13) .

    have "Simulate_PC s'"
      using D3_bot_linear_tail(14) .

    (* ================================================================= *)
    (* BOT branch: new USpec invariant uI1/uI2/uI3 *)
    (* ================================================================= *)

    have uI1_USpec_EffOps_Lin_s': "uI1_USpec_EffOps_Lin s'"
      using uI1_USpec_EffOps_Lin_s s'_simple lin_seq_eq
      unfolding uI1_USpec_EffOps_Lin_def uspec_effOps_def
      by simp

    have uI2_USpec_E1UE2_s': "uI2_USpec_E1UE2 s'"
    proof (unfold uI2_USpec_E1UE2_def, intro allI impI)
      fix pa
      assume pc_pa: "program_counter s' pa \<in> {''E1'', ''E2''}"
      assume upc_pa: "u_program_counter (snd s') pa = ''UE2''"

      have snd_eq: "snd s' = snd s"
        using s'_simple by simp

      have pa_ne_p: "pa \<noteq> p"
        using pc_pa pc_update by (cases "jp = lp - 1") auto

      have pc_old: "program_counter s pa \<in> {''E1'', ''E2''}"
        using pc_pa pc_update pa_ne_p by simp

      have upc_old: "u_program_counter (snd s) pa = ''UE2''"
        using upc_pa snd_eq by simp

      have old_gen:
        "USpec_GenLin (u_his_seq (snd s)) (u_eff_ops (snd s))
          (mk_op enq (v_var s pa) pa (s_var s pa))
          (u_lin_seq (snd s) @ [mk_op enq (v_var s pa) pa (s_var s pa)])"
        using uI2_USpec_E1UE2_s pc_old upc_old
        unfolding uI2_USpec_E1UE2_def
        by blast

      have v_eq: "v_var s' pa = v_var s pa"
        using s'_simple by (simp add: v_var_def)

      have s_eq: "s_var s' pa = s_var s pa"
        using snd_eq by (simp add: s_var_def)

      show "USpec_GenLin (u_his_seq (snd s')) (u_eff_ops (snd s'))
              (mk_op enq (v_var s' pa) pa (s_var s' pa))
              (u_lin_seq (snd s') @ [mk_op enq (v_var s' pa) pa (s_var s' pa)])"
        using old_gen snd_eq v_eq s_eq by simp
    qed

    have uI3_USpec_D3UD2_s': "uI3_USpec_D3UD2 s'"
    proof (unfold uI3_USpec_D3UD2_def, intro allI impI)
      fix pa
      assume pc_pa': "program_counter s' pa = ''D3''"
      assume qj_pa': "Q_arr s' (j_var s' pa) \<noteq> BOT"
      assume upc_pa': "u_program_counter (snd s') pa = ''UD2''"

      have snd_eq: "snd s' = snd s"
        using s'_simple by simp

      have lin_eq: "lin_seq s' = lin_seq s"
        using lin_seq_eq .

      have his_eq: "his_seq s' = his_seq s"
        using his_seq_eq .

      have eff_eq: "uspec_effOps s' = uspec_effOps s"
        using snd_eq
        unfolding uspec_effOps_def
        by simp

      have svar_eq: "s_var s' = s_var s"
        using snd_eq
        unfolding s_var_def
        by simp

      have qarr_eq: "Q_arr s' = Q_arr s"
        using Q_unchanged .

      show "let cur_lin = lin_seq s';
                cur_his = his_seq s';
                x_val = Q_arr s' (j_var s' pa);
                op = mk_op deq x_val pa (s_var s' pa);
                new_lin =
                  (if should_modify cur_lin cur_his x_val
                   then modify_lin cur_lin cur_his x_val
                   else cur_lin) @ [op]
            in USpec_GenLin cur_his (uspec_effOps s') op new_lin"
      proof (cases "pa = p")
        case False

        have pc_old: "program_counter s pa = ''D3''"
          using pc_pa' pc_update False
          by simp

        have j_old: "j_var s' pa = j_var s pa"
          using False s'_simple
          unfolding j_var_def
          by simp

        have qj_old: "Q_arr s (j_var s pa) \<noteq> BOT"
          using qj_pa' qarr_eq j_old
          by simp

        have upc_old: "u_program_counter (snd s) pa = ''UD2''"
          using upc_pa' snd_eq
          by simp

        have old_rule:
          "let cur_lin = lin_seq s;
               cur_his = his_seq s;
               x_val = Q_arr s (j_var s pa);
               op = mk_op deq x_val pa (s_var s pa);
               new_lin =
                 (if should_modify cur_lin cur_his x_val
                  then modify_lin cur_lin cur_his x_val
                  else cur_lin) @ [op]
           in USpec_GenLin cur_his (uspec_effOps s) op new_lin"
          using uI3_USpec_D3UD2_s pc_old qj_old upc_old
          unfolding uI3_USpec_D3UD2_def
          by blast

        show ?thesis
          using old_rule lin_eq his_eq eff_eq svar_eq qarr_eq j_old
          by simp

      next
        case True
        then have pa_eq: "pa = p" .

        have pc_p_s': "program_counter s' p = ''D3''"
          using pc_pa' pa_eq
          by simp

        have not_last: "jp \<noteq> lp - 1"
        proof
          assume last: "jp = lp - 1"

          have "program_counter s' p = ''D1''"
            using s'_simple last
            unfolding program_counter_def jp_def lp_def
            by simp

          thus False
            using pc_p_s'
            by simp
        qed

        have j_p_s':
          "j_var s' p = jp + 1"
          using s'_simple not_last
          unfolding j_var_def jp_def lp_def
          by simp

        have next_nonbot:
          "Q_arr s (jp + 1) \<noteq> BOT"
        proof -
          have "Q_arr s' (j_var s' p) \<noteq> BOT"
            using qj_pa' pa_eq
            by simp

          thus ?thesis
            using qarr_eq j_p_s'
            by simp
        qed

        have jp_bot:
          "Q_arr s jp = BOT"
          using q_is_bot q_val_def
          by simp

        have cur_rule:
          "let cur_lin = lin_seq s;
               cur_his = his_seq s;
               x_val = Q_arr s (jp + 1);
               op = mk_op deq x_val p (s_var s p);
               new_lin =
                 (if should_modify cur_lin cur_his x_val
                  then modify_lin cur_lin cur_his x_val
                  else cur_lin) @ [op]
           in USpec_GenLin cur_his (uspec_effOps s) op new_lin"
          by (rule D3_bot_advance_current_uI3[
                OF INV D3_unfolded(1) jp_def lp_def
                   jp_bot not_last next_nonbot
            ])

        show ?thesis
          using cur_rule pa_eq lin_eq his_eq eff_eq svar_eq qarr_eq j_p_s'
          by simp
      qed
    qed


    (* Case 1 *)
    show ?thesis
      unfolding system_invariant_def
      using `Simulate_PC s'`
      using `TypeOK s'`  `sI1_Zero_Index_BOT s'`
      `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'`  `hI3_L0_E_Phase_Bounds s'`
      `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'` `sI12_D3_Scanned_Prefix s'`
      `uI1_USpec_EffOps_Lin s'` `uI2_USpec_E1UE2 s'` `uI3_USpec_D3UD2 s'` `hI4_X_var_Lin_Sync s'`
      `hI7_His_WF s'` `hI8_Val_Unique s'`  `hI5_SSN_Unique s'` `hI6_SSN_Order s'`
      `hI9_Deq_Ret_Unique s'` `hI10_Enq_Call_Existence s'` `hI11_Enq_Ret_Existence s'` `hI12_D_Phase_Pending_Deq s'`  `hI13_Qback_Deq_Sync s'` `hI14_Pending_Enq_Qback_Exclusivity s'` `hI15_Deq_Result_Exclusivity s'`
      `hI16_BO_BT_No_HB s'` `hI17_BT_BT_No_HB s'` `hI18_Idx_Order_No_Rev_HB s'` `hI19_Scanner_Catches_Later_Enq s'` `hI20_Enq_Val_Valid s'` `hI21_Ret_Implies_Call s'` `hI22_Deq_Local_Pattern s'`
      `hI23_Deq_Call_Ret_Balanced s'` `hI24_HB_Implies_Idx_Order s'`  `hI25_Enq_Call_Ret_Balanced s'`  `hI26_DeqRet_D4_Mutex s'`
      `hI27_Pending_PC_Sync s'`  `hI28_Fresh_Enq_Immunity s'` `hI29_E2_Scanner_Immunity s'`
      `hI30_Ticket_HB_Immunity s'`
      `lI1_Op_Sets_Equivalence s'` `lI2_Op_Cardinality s'` `lI3_HB_Ret_Lin_Sync s'` `lI4_FIFO_Semantics s'` `lI5_SA_Prefix s'` `lI6_D4_Deq_Linearized s'`
      `lI7_D4_Deq_Deq_HB s'` `lI8_D3_Deq_Returned s'` `lI9_D1_D2_Deq_Returned s'` `lI10_D4_Enq_Deq_HB s'` `lI11_D4_Deq_Unique s'`
      `data_independent (lin_seq s')`
      by blast

        next
      case False
      (* ================================================================= *)
      (* Case 2: successdequeue (q_val \<noteq> BOT) *)
      (* ================================================================= *)
      note q_not_bot = False

      have success_basic:
        "q_val = Qback_arr s (j_var s p)"
        "s' = Sys_D3_success_update s p"
        "TypeOK s'"
        "sI1_Zero_Index_BOT s'"
        "sI2_X_var_Upper_Bound s'"
        "sI3_E2_Slot_Exclusive s'"
        "sI4_E3_Qback_Written s'"
        "sI5_D2_Local_Bound s'"
        "sI6_D3_Scan_Pointers s'"
        "sI7_D4_Deq_Result s'"
        "sI8_Q_Qback_Sync s'"
        "sI9_Qback_Discrepancy_E3 s'"
        "sI10_Qback_Unique_Vals s'"
        "his_seq s' = his_seq s"
        "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
        "x_var s' = (\<lambda>x. if x = p then Qback_arr s (j_var s p) else x_var s x)"
        "i_var s' = i_var s"
        "j_var s' = j_var s"
        "v_var s' = v_var s"
        "l_var s' = l_var s"
        "Qback_arr s' = Qback_arr s"
        "Q_arr s' = (Q_arr s)(jp := BOT)"
        "program_counter s' = (program_counter s)(p := ''D4'')"
        "v_var s' = v_var s"
        using D3_success_basic_facts[
          OF INV STEP D3_unfolded(1) jp_def q_val_def q_not_bot
             sI1_Zero_Index_BOT_s
             sI3_E2_Slot_Exclusive_s
             sI4_E3_Qback_Written_s
             sI5_D2_Local_Bound_s
             sI6_D3_Scan_Pointers_s
             sI8_Q_Qback_Sync_s
      ] .

      note val_eq = success_basic(1)
      note s'_is_update = success_basic(2)

      have phys_invs:
        "TypeOK s' \<and> sI2_X_var_Upper_Bound s' \<and> sI7_D4_Deq_Result s' \<and>
         sI8_Q_Qback_Sync s' \<and> sI9_Qback_Discrepancy_E3 s' \<and> sI10_Qback_Unique_Vals s'"
        using success_basic(3,5,10,11,12,13) by blast

      have "TypeOK s'" using success_basic(3) .
      have "sI1_Zero_Index_BOT s'" using success_basic(4) .
      have "sI2_X_var_Upper_Bound s'" using success_basic(5) .
      have "sI3_E2_Slot_Exclusive s'" using success_basic(6) .
      have "sI4_E3_Qback_Written s'" using success_basic(7) .
      have "sI5_D2_Local_Bound s'" using success_basic(8) .
      have "sI6_D3_Scan_Pointers s'" using success_basic(9) .
      have "sI7_D4_Deq_Result s'" using success_basic(10) .
      have "sI8_Q_Qback_Sync s'" using success_basic(11) .
      have "sI9_Qback_Discrepancy_E3 s'" using success_basic(12) .
      have "sI10_Qback_Unique_Vals s'" using success_basic(13) .

      have his_seq_eq: "his_seq s' = his_seq s"
        using success_basic(14) .

      have pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
        using success_basic(15) .

      have x_var_eq: "x_var s' = (\<lambda>x. if x = p then Qback_arr s (j_var s p) else x_var s x)"
        using success_basic(16) .

      have other_vars_eq:
        "i_var s' = i_var s \<and> j_var s' = j_var s \<and> v_var s' = v_var s \<and> l_var s' = l_var s"
        using success_basic(17,18,19,20) by blast

      have his_unchanged: "his_seq s' = his_seq s"
        using his_seq_eq .

      have T_unchanged: "Qback_arr s' = Qback_arr s"
        using success_basic(21) .

      have prem1_Q: "Q_arr s' = (Q_arr s)(jp := BOT)"
        using success_basic(22) .

      have prem2_PC: "program_counter s' = (program_counter s)(p := ''D4'')"
        using success_basic(23) .

      have prem3_V: "v_var s' = v_var s"
        using success_basic(24) .

      note success_set_lin_raw =
        D3_success_set_and_lin_facts[
          OF INV TypeOK_s D3_unfolded(1) jp_def q_val_def
             current_lin_def current_his_def base_lin_def
             q_not_bot val_eq
             sI8_Q_Qback_Sync_s
             sI10_Qback_Unique_Vals_s
             \<open>TypeOK s'\<close>
             \<open>sI7_D4_Deq_Result s'\<close>
             s'_is_update
             pc_eq
             other_vars_eq
             T_unchanged
             prem1_Q
             prem2_PC
             prem3_V
      ]

      have q_in_SetB: "q_val \<in> SetB s"
        using success_set_lin_raw(1) .

      have setb_update: "SetB s' = SetB s - {q_val}"
        using success_set_lin_raw(2) .

      have TypeB_update: "\<And>x. x \<in> Val \<Longrightarrow> TypeB s' x \<longleftrightarrow> TypeB s x \<and> x \<noteq> q_val"
        using success_set_lin_raw(3) .

      have bridge_lin: "u_lin_seq (snd s) = current_lin"
        using success_set_lin_raw(4) .

      have bridge_his: "u_his_seq (snd s) = current_his"
        using success_set_lin_raw(5) .

      have bridge_q: "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
        using success_set_lin_raw(6) .

      have bridge:
        "u_lin_seq (snd s) = current_lin"
        "u_his_seq (snd s) = current_his"
        "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
      proof -
        show "u_lin_seq (snd s) = current_lin"
          using bridge_lin .
        show "u_his_seq (snd s) = current_his"
          using bridge_his .
        show "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
          using bridge_q .
      qed

      have Q_upd: "Q_arr s' = (Q_arr s)(jp := BOT)"
        using success_set_lin_raw(7) .

      have set_base_eq: "set base_lin = set (lin_seq s)"
        using success_set_lin_raw(8) .

      have lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
        using success_set_lin_raw(9) .

      have seta_update: "SetA s' = SetA s \<union> {q_val} \<and> SetB s' = SetB s - {q_val}"
        using success_set_lin_raw(10) .

            note success_set_lin_raw =
        D3_success_set_and_lin_facts[
          OF INV TypeOK_s D3_unfolded(1) jp_def q_val_def
             current_lin_def current_his_def base_lin_def
             q_not_bot val_eq
             sI8_Q_Qback_Sync_s
             sI10_Qback_Unique_Vals_s
             \<open>TypeOK s'\<close>
             \<open>sI7_D4_Deq_Result s'\<close>
             s'_is_update
             pc_eq
             other_vars_eq
             T_unchanged
             prem1_Q
             prem2_PC
             prem3_V
      ]

      have q_in_SetB: "q_val \<in> SetB s"
        using success_set_lin_raw(1) .

      have setb_update: "SetB s' = SetB s - {q_val}"
        using success_set_lin_raw(2) .

      have TypeB_update: "\<And>x. x \<in> Val \<Longrightarrow> TypeB s' x \<longleftrightarrow> TypeB s x \<and> x \<noteq> q_val"
        using success_set_lin_raw(3) .

      have bridge_lin: "u_lin_seq (snd s) = current_lin"
        using success_set_lin_raw(4) .

      have bridge_his: "u_his_seq (snd s) = current_his"
        using success_set_lin_raw(5) .

      have bridge_q: "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
        using success_set_lin_raw(6) .

      have bridge:
        "u_lin_seq (snd s) = current_lin"
        "u_his_seq (snd s) = current_his"
        "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
      proof -
        show "u_lin_seq (snd s) = current_lin"
          using bridge_lin .
        show "u_his_seq (snd s) = current_his"
          using bridge_his .
        show "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
          using bridge_q .
      qed

      have Q_upd: "Q_arr s' = (Q_arr s)(jp := BOT)"
        using success_set_lin_raw(7) .

      have set_base_eq: "set base_lin = set (lin_seq s)"
        using success_set_lin_raw(8) .

      have lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
        using success_set_lin_raw(9) .

      have seta_update: "SetA s' = SetA s \<union> {q_val} \<and> SetB s' = SetB s - {q_val}"
        using success_set_lin_raw(10) .

         have hI3_L0_E_Phase_Bounds_s': "hI3_L0_E_Phase_Bounds s'"
        using D3_success_preserves_hI3_L0_E_Phase_Bounds[
          OF hI3_L0_E_Phase_Bounds_s s'_is_update his_seq_eq pc_eq prem3_V T_unchanged
      ] .

      have hI2_SSN_Bounds_s': "hI2_SSN_Bounds s'"
        using D3_success_preserves_hI2_SSN_Bounds[
          OF hI2_SSN_Bounds_s s'_is_update his_seq_eq pc_eq
      ] .

      have sI11_x_var_Scope_s': "sI11_x_var_Scope s'"
        using D3_success_preserves_sI11_x_var_Scope[
          OF sI11_x_var_Scope_s pc_eq x_var_eq
      ] .

         have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s"
        using INV unfolding system_invariant_def by blast

      have j_var_eq: "j_var s' = j_var s"
        using s'_is_update
        unfolding Sys_D3_success_update_def Let_def j_var_def bridge_defs
        by (auto simp: fun_eq_iff)

      have Q_jp_bot: "Q_arr s' jp = BOT"
        using s'_is_update q_not_bot
        unfolding Sys_D3_success_update_def Let_def jp_def bridge_defs
        by simp

      have Q_other_eq: "\<And>k. k \<noteq> jp \<Longrightarrow> Q_arr s' k = Q_arr s k"
        using s'_is_update q_not_bot
        unfolding Sys_D3_success_update_def Let_def jp_def bridge_defs
        by simp

      have hI1_E_Phase_Pending_Enq_s': "hI1_E_Phase_Pending_Enq s'"
        using D3_success_preserves_hI1_E_Phase_Pending_Enq[
          OF hI1_E_Phase_Pending_Enq_s s'_is_update his_seq_eq pc_eq
      ] .

      have sI12_D3_Scanned_Prefix_s': "sI12_D3_Scanned_Prefix s'"
        using D3_success_preserves_sI12_D3_Scanned_Prefix[
          OF INV sI12_D3_Scanned_Prefix_s q_not_bot pc_eq j_var_eq
             q_val_def Q_jp_bot Q_other_eq
             sI8_Q_Qback_Sync_s sI10_Qback_Unique_Vals_s TypeB_update
      ] .

(* ========================================================================= *)
    (* HI4_X_var_Lin_Sync: physical- mappingconsistency (q_val \<noteq> BOT branch) *)
    (* ========================================================================= *)
    let ?base_lin = "if should_modify (lin_seq s) (his_seq s) q_val
                     then modify_lin (lin_seq s) (his_seq s) q_val
                     else lin_seq s"
    let ?new_act = "mk_op deq q_val p (s_var s p)"

    have lin_seq_eq: "lin_seq s' = ?base_lin @ [?new_act]"
      using s'_is_update
      unfolding Sys_D3_success_update_def Let_def lin_seq_def bridge_defs snd_conv
      using base_lin_def bridge(1) current_his_def lin_s'_eq lin_seq_def q_not_bot
      by fastforce

    have count_eq: "LinEnqCount s' (length (lin_seq s')) = LinEnqCount s (length (lin_seq s))"
    proof -
      have "LinEnqCount s' (length (lin_seq s')) =
            length (filter (\<lambda>act. op_name act = enq) (lin_seq s'))"
        unfolding LinEnqCount_def by simp
      also have "... = length (filter (\<lambda>act. op_name act = enq) (?base_lin @ [?new_act]))"
        using lin_seq_eq by simp
      also have "... = length (filter (\<lambda>act. op_name act = enq) ?base_lin) +
                       length (filter (\<lambda>act. op_name act = enq) [?new_act])"
        by simp
      also have "... = length (filter (\<lambda>act. op_name act = enq) ?base_lin)"
        by (simp add: mk_op_def op_name_def)
      also have "... = length (filter (\<lambda>act. op_name act = enq) (lin_seq s))"
      proof -
        have "length (filter (\<lambda>act. op_name act = enq) ?base_lin) =
              length (filter (\<lambda>act. op_name act = enq) (lin_seq s))"
        proof (cases "should_modify (lin_seq s) (his_seq s) q_val")
          case True
          then have "?base_lin = modify_lin (lin_seq s) (his_seq s) q_val"
            by simp
          then show ?thesis
            using modify_lin_preserves_enq_count by simp
        next
          case False
          then have "?base_lin = lin_seq s"
            by simp
          then show ?thesis
            by simp
        qed
        then show ?thesis by simp
      qed
      finally show ?thesis
        unfolding LinEnqCount_def by simp
    qed

    have hI4_X_var_Lin_Sync_s': "hI4_X_var_Lin_Sync s'"
      using D3_success_preserves_hI4_X_var_Lin_Sync[
        OF INV D3_unfolded(1) s'_is_update count_eq
    ] .

        have hI7_His_WF_s': "hI7_His_WF s'"
        using D3_success_preserves_basic_history_facts(1)[OF INV his_seq_eq] .

      have hI8_Val_Unique_s': "hI8_Val_Unique s'"
        using D3_success_preserves_basic_history_facts(2)[OF INV his_seq_eq] .

      have hI5_SSN_Unique_s': "hI5_SSN_Unique s'"
        using D3_success_preserves_basic_history_facts(3)[OF INV his_seq_eq] .

      have hI6_SSN_Order_s': "hI6_SSN_Order s'"
        using D3_success_preserves_basic_history_facts(4)[OF INV his_seq_eq] .

      have hI9_Deq_Ret_Unique_s': "hI9_Deq_Ret_Unique s'"
        using D3_success_preserves_basic_history_facts(5)[OF INV his_seq_eq] .

      have hI10_Enq_Call_Existence_s': "hI10_Enq_Call_Existence s'"
        using D3_success_preserves_hI10_Enq_Call_Existence[
          OF INV s'_is_update his_seq_eq T_unchanged pc_eq D3_unfolded(1)
      ] .

      have hI11_Enq_Ret_Existence_s': "hI11_Enq_Ret_Existence s'"
        using D3_success_preserves_hI11_Enq_Ret_Existence[
          OF INV s'_is_update his_seq_eq T_unchanged pc_eq D3_unfolded(1)
      ] .

      have hI12_D_Phase_Pending_Deq_s': "hI12_D_Phase_Pending_Deq s'"
        using D3_success_preserves_hI12_D_Phase_Pending_Deq[
          OF INV s'_is_update his_seq_eq pc_eq D3_unfolded(1)
      ] .

        have q_val_phys: "q_val = Q_arr s (j_var s p)"
        using q_val_def jp_def by simp

      have q_not_bot_phys: "Q_arr s (j_var s p) \<noteq> BOT"
        using q_not_bot q_val_def jp_def by simp

      have hI13_Qback_Deq_Sync_s': "hI13_Qback_Deq_Sync s'"
        using D3_preserves_hI13_Qback_Deq_Sync[
          OF hI13_Qback_Deq_Sync_s sI8_Q_Qback_Sync_s D3_unfolded(1)
             jp_def q_val_def q_not_bot s'_is_update
      ] .

      have hI14_Pending_Enq_Qback_Exclusivity_s': "hI14_Pending_Enq_Qback_Exclusivity s'"
        using D3_success_preserves_hI14_Pending_Enq_Qback_Exclusivity[
          OF INV D3_unfolded(1) s'_is_update
      ] .

      have hI15_Deq_Result_Exclusivity_s': "hI15_Deq_Result_Exclusivity s'"
        using D3_preserves_hI15_Deq_Result_Exclusivity[
          OF INV D3_unfolded(1) s'_is_update q_val_phys q_not_bot_phys
      ] .

      have hI18_Idx_Order_No_Rev_HB_s': "hI18_Idx_Order_No_Rev_HB s'"
        using D3_success_preserves_hI18_Idx_Order_No_Rev_HB[
          OF hI18_Idx_Order_No_Rev_HB_s his_seq_eq T_unchanged
      ] .

      have hI16_BO_BT_No_HB_s': "hI16_BO_BT_No_HB s'"
        using s'_is_update
              D3_preserves_hI16_BO_BT_No_HB[OF INV D3_unfolded(1) q_not_bot_phys]
        by simp

      have hI17_BT_BT_No_HB_s': "hI17_BT_BT_No_HB s'"
        using s'_is_update
              D3_preserves_hI17_BT_BT_No_HB[OF INV D3_unfolded(1) q_not_bot_phys]
        by simp

        have hI19_Scanner_Catches_Later_Enq_s': "hI19_Scanner_Catches_Later_Enq s'"
      using D3_success_preserves_hI19_Scanner_Catches_Later_Enq[
        OF INV s'_is_update his_seq_eq T_unchanged TypeB_update
    ] .

    have hI20_Enq_Val_Valid_s': "hI20_Enq_Val_Valid s'"
      using D3_success_preserves_hI20_Enq_Val_Valid[
        OF hI20_Enq_Val_Valid_s his_seq_eq
    ] .

    have hI21_Ret_Implies_Call_s': "hI21_Ret_Implies_Call s'"
      using D3_success_preserves_hI21_Ret_Implies_Call[
        OF hI21_Ret_Implies_Call_s his_seq_eq
    ] .

     have hI22_Deq_Local_Pattern_s': "hI22_Deq_Local_Pattern s'"
    using D3_success_preserves_hI22_Deq_Local_Pattern[
      OF INV D3_unfolded(1) s'_is_update his_seq_eq T_unchanged jp_def q_val_def q_not_bot
  ] .

    have "hI23_Deq_Call_Ret_Balanced s'"
      using hI23_Deq_Call_Ret_Balanced_s his_seq_eq unfolding hI23_Deq_Call_Ret_Balanced_def by simp

    have "hI24_HB_Implies_Idx_Order s'"
      using hI24_HB_Implies_Idx_Order_D3_success_update[OF hI24_HB_Implies_Idx_Order_s hI20_Enq_Val_Valid_s s'_is_update his_unchanged] .

      have hI25_Enq_Call_Ret_Balanced_s': "hI25_Enq_Call_Ret_Balanced s'"
      using D3_success_preserves_hI25_Enq_Call_Ret_Balanced[
        OF hI25_Enq_Call_Ret_Balanced_s his_seq_eq pc_eq D3_unfolded(1)
    ] .
    have x_var_eq_qval: "x_var s' = (\<lambda>x. if x = p then q_val else x_var s x)"
      using x_var_eq val_eq
      by (simp add: fun_eq_iff)

    have hI26_DeqRet_D4_Mutex_s': "hI26_DeqRet_D4_Mutex s'"
      using D3_success_preserves_hI26_DeqRet_D4_Mutex[
        OF hI26_DeqRet_D4_Mutex_s hI15_Deq_Result_Exclusivity_s his_seq_eq pc_eq x_var_eq_qval q_val_phys
    ] .

(* ========================================================================= *)
    (* HI19: and physical PC of (success branch - factversion) *)
    (* ========================================================================= *)
    have "hI27_Pending_PC_Sync s'"
    proof (unfold hI27_Pending_PC_Sync_def, intro conjI allI impI)
      (* Extract the old state of hI19 *)
      have hI19_s: "hI27_Pending_PC_Sync s" using INV unfolding system_invariant_def by blast
      (* The of prem3_V, when prove s_var of definitelyequivalence *)
      have s_var_eq: "s_var s' = s_var s"
        using s'_is_update unfolding Sys_D3_success_update_def Let_def
        by (simp add: s_var_def)

      (* --------------------------------------------------------------------- *)
      (* Goal 1: Deq (PendingDeq -> PC in D) *)
      (* --------------------------------------------------------------------- *)
      show "\<And>p'. HasPendingDeq s' p' \<Longrightarrow> program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof -
        fix p'
        assume pending_prime: "HasPendingDeq s' p'"

        (* Use Let_def and the of his_seq_eq! *)
        have pend_deq_eq: "HasPendingDeq s' p' = HasPendingDeq s p'"
          unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
          using his_seq_eq s_var_eq by simp

        have pending_s: "HasPendingDeq s p'"
          using pending_prime pend_deq_eq by simp

        show "program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
        proof (cases "p' = p")
          case True
          (* Use the definition of pc_eq: if x = p then ''D4'' else... *)
          have "program_counter s' p = ''D4''"
            using pc_eq by auto
          thus ?thesis using True by simp
        next
          case False
          have "program_counter s' p' = program_counter s p'"
            using False pc_eq by auto
          moreover have "program_counter s p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
            using hI19_s pending_s unfolding hI27_Pending_PC_Sync_def by blast
          ultimately show ?thesis by simp
        qed
      qed

    next
      (* --------------------------------------------------------------------- *)
      (* Goal 2: Enq (PendingEnq -> PC in E) *)
      (* --------------------------------------------------------------------- *)
      show "\<And>p'. HasPendingEnq s' p' (v_var s' p') \<Longrightarrow> program_counter s' p' \<in> {''E1'', ''E2'', ''E3''}"
      proof -
        fix p'
        assume pending_enq_prime: "HasPendingEnq s' p' (v_var s' p')"

        have s_var_eq: "s_var s' = s_var s"
          using s'_is_update unfolding Sys_D3_success_update_def Let_def
          by (simp add: s_var_def)

        (* From the of other_vars_eq in extract v_var of equivalence *)
        have pend_enq_eq: "HasPendingEnq s' p' (v_var s' p') = HasPendingEnq s p' (v_var s p')"
          unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def Let_def
          using his_seq_eq s_var_eq other_vars_eq by simp

        have pending_enq_s: "HasPendingEnq s p' (v_var s p')"
          using pending_enq_prime pend_enq_eq by simp

        show "program_counter s' p' \<in> {''E1'', ''E2'', ''E3''}"
        proof (cases "p' = p")
          case True
          have "program_counter s p = ''D3''"
            using D3_unfolded(1) by simp
          moreover have "program_counter s p \<in> {''E1'', ''E2'', ''E3''}"
            using True hI27_Pending_PC_Sync_def hI27_Pending_PC_Sync_s
              pending_enq_s by presburger
          ultimately show ?thesis by simp
        next
          case False
          have "program_counter s' p' = program_counter s p'"
            using False pc_eq by auto
          moreover have "program_counter s p' \<in> {''E1'', ''E2'', ''E3''}"
            using hI27_Pending_PC_Sync_def hI27_Pending_PC_Sync_s
              pending_enq_s by auto
          ultimately show ?thesis by simp
        qed
      qed
    qed

    (* ========================================================================= *)
    (* HI20: enqueuevalue of definitelynew (success branch - factversion - fixguard) *)
    (* ========================================================================= *)
    have "hI28_Fresh_Enq_Immunity s'"
    proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI)
      fix p_enq q_deq a sn

      (* Key correction: one assume \<and> of premise, and E3 *)
      assume prems: "program_counter s' p_enq \<in> {''E1'', ''E2''} \<and>
                     v_var s' p_enq = a \<and>
                     a \<noteq> BOT"

      (* After inside it split into three of fact, after use *)
      hence pc_e_prime: "program_counter s' p_enq \<in> {''E1'', ''E2''}"
        and v_eq_prime: "v_var s' p_enq = a"
        and a_not_bot: "a \<noteq> BOT" by auto

      have hI20_s: "hI28_Fresh_Enq_Immunity s" using INV unfolding system_invariant_def by blast

      (* When prove s_var of definitelyequivalence *)
      have s_var_eq: "s_var s' = s_var s"
        using s'_is_update unfolding Sys_D3_success_update_def Let_def
        by (auto simp: bridge_defs s_var_def fun_eq_iff)

      show "\<not> DeqRetInHis s' q_deq a sn"
      proof (rule notI)
        assume his_prime: "DeqRetInHis s' q_deq a sn"

        (* Use the of his_seq_eq and of s_var_eq historymapping *)
        have his_eq: "DeqRetInHis s' q_deq a sn = DeqRetInHis s q_deq a sn"
          unfolding DeqRetInHis_def using his_seq_eq s_var_eq by simp

        have his_s: "DeqRetInHis s q_deq a sn"
          using his_prime his_eq by simp

        show False
        proof (cases "p_enq = p", goal_cases)
          case 1
          (* At this point 1 premise p_enq = p *)
          (* Use the definition of pc_eq obtain p of new PC *)
          have "program_counter s' p = ''D4''"
            using pc_eq by auto
          with pc_e_prime 1 show False by auto
        next
          case 2
          (* At this point 2 premise p_enq \<noteq> p *)
          have old_pc: "program_counter s p_enq \<in> {''E1'', ''E2''}"
            using pc_e_prime 2 pc_eq by auto

          (* From other_vars_eq in extract v_var of *)
          have old_v: "v_var s p_enq = a"
            using v_eq_prime 2 other_vars_eq by auto

          from hI20_s[unfolded hI28_Fresh_Enq_Immunity_def] old_pc old_v a_not_bot his_s
          show False by blast
        qed
      qed
    qed

     have hI29_E2_Scanner_Immunity_s': "hI29_E2_Scanner_Immunity s'"
      using D3_success_preserves_hI29_E2_Scanner_Immunity[
        OF INV s'_is_update his_seq_eq T_unchanged pc_eq TypeB_update
    ] .

    have hI30_Ticket_HB_Immunity_s': "hI30_Ticket_HB_Immunity s'"
      using D3_success_preserves_hI30_Ticket_HB_Immunity[
        OF INV s'_is_update his_seq_eq T_unchanged pc_eq
    ] .

      (* ----------------------------------------------------------------- *)
      (* 5. prove (use D3DI.thy and D3Lemmas.thy) *)
      (* ----------------------------------------------------------------- *)
      (* Basicdata: modify preserveproperty *)
      have di_base: "data_independent base_lin"
        unfolding base_lin_def
        using di_lin_s modify_preserves_data_independent
        using current_lin_def by presburger

    (* ========================================================================= *)
    (* A. provenew of data (in new Freshness of derivation) *)
    (* ========================================================================= *)
     have di_s': "data_independent (lin_seq s')"
      proof -
        let ?sn_deq = "s_var s p"

        define base where
          "base = (if should_modify (lin_seq s) (his_seq s) q_val
                   then modify_lin (lin_seq s) (his_seq s) q_val
                   else lin_seq s)"

        have lin_eq: "lin_seq s' = base @ [mk_op deq q_val p ?sn_deq]"
          using D3_unfolded(2) q_not_bot base_def lin_s'_eq
          unfolding base_lin_def current_lin_def current_his_def s_var_def
          by auto

        show ?thesis
          by (rule D3_success_preserves_data_independent_lin_seq[
                where s = s and s' = s' and p = p and sn = ?sn_deq and q_val = q_val and base_lin = base,
                OF INV q_in_SetB base_def lin_eq
            ])
      qed

        have lI1_Op_Sets_Equivalence_s': "lI1_Op_Sets_Equivalence s'"
      using D3_success_preserves_lI1_Op_Sets_Equivalence[
        OF INV D3_unfolded(1) his_seq_eq q_in_SetB set_base_eq lin_s'_eq seta_update
    ] .

      (* ================================================================= *)
      (* B. prove lI2_Op_Cardinality (uniqueness) *)
      (* Core: near mset with already of SetA/SetB *)
      (* ================================================================= *)
      have "lI2_Op_Cardinality s'"
      proof -
        (* Proof step: use new of physical ticket reader s_var s p *)
        let ?sn_deq = "s_var s p"
        let ?deq_act = "mk_op deq q_val p ?sn_deq"

        (* 1. premise: mset (use avoid timeout) *)
        have mset_eq: "mset (lin_seq s') = mset (lin_seq s) + {# ?deq_act #}"
        proof -
          (* In lI1_Op_Sets_Equivalence in use of physical *)
          have bridge:
            "u_lin_seq (snd s) = current_lin"
            "u_his_seq (snd s) = current_his"
            "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
            unfolding lin_seq_def his_seq_def current_lin_def current_his_def q_val_def jp_def
            by (simp_all add: bridge_defs)

          (* Prove base_lin of mset *)
          have "mset base_lin = mset (lin_seq s)"
            unfolding base_lin_def current_lin_def current_his_def
            using modify_preserves_mset q_not_bot by presburger

          (* Proof note *)
          moreover have "lin_seq s' = base_lin @ [?deq_act]"
            using s'_is_update q_not_bot
            unfolding lin_seq_def Sys_D3_success_update_def base_lin_def Let_def s_var_def
            by (simp add: bridge bridge_defs)

          ultimately show ?thesis by simp
        qed

        (* 2. apply lI2_Op_Cardinality of core *)
        show ?thesis
          apply (rule lI2_Op_Cardinality_D3_step_lemma)
          using INV apply simp             (* system_invariant s *)
          using q_in_SetB apply simp       (* q_val \<in> SetB s *)
          using mset_eq apply simp         (* mset(lin_seq s') = ... *)
          using seta_update apply simp     (* SetA s' = SetA s \<union> {q_val} *)
          using setb_update apply simp     (* SetB s' = SetB s - {q_val} *)
          done
      qed

      (* ================================================================= *)
      (* C. prove lI3_HB_Ret_Lin_Sync (Happens-Before consistency) *)
      (* ================================================================= *)
      have base_succ_def:
        "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                     then modify_lin (lin_seq s) (his_seq s) q_val
                     else lin_seq s)"
        using base_lin_def q_not_bot
        unfolding current_lin_def current_his_def
        by simp

      have val_eq_jp: "q_val = Qback_arr s jp"
        using val_eq jp_def by simp

      have lI3_HB_Ret_Lin_Sync_s': "lI3_HB_Ret_Lin_Sync s'"
        using D3_success_preserves_lI3_HB_Ret_Lin_Sync[
          OF INV D3_unfolded(1) jp_def q_val_def val_eq_jp q_not_bot q_in_SetB
             base_succ_def lin_s'_eq his_seq_eq
      ] .

      (* ----------------------------------------------------------------- *)
      (* Provegoal: lI4_FIFO_Semantics s' (FIFO propertypreserve) - already packaging as helper lemma *)
      (* ----------------------------------------------------------------- *)
      have "lI4_FIFO_Semantics s'"
      proof -
        (* Proof step: use new of physical ticket reader s_var s p *)
        let ?sn_deq = "s_var s p"

        (* 1. definition base *)
        define base where "base = (if should_modify (lin_seq s) (his_seq s) q_val
                                   then modify_lin (lin_seq s) (his_seq s) q_val
                                   else lin_seq s)"

        (* 2. proveequivalencefact (in?sn_deq) *)
        have lin_eq: "lin_seq s' = base @ [mk_op deq q_val p ?sn_deq]"
          using D3_unfolded(2) q_not_bot base_def lin_s'_eq
          unfolding base_lin_def current_lin_def current_his_def s_var_def
          by auto

        (* 3. [ alignversion] match *)
        show ?thesis
        proof (rule lI4_FIFO_Semantics_deq_step_preservation[where s=s and q_val=q_val and s'=s' and p=p])
          (* In one premise, Isabelle the one match *)
          show "system_invariant s" using INV .
          show "q_val \<in> SetB s" using q_in_SetB .
          show "q_val \<noteq> BOT" using q_not_bot .

          show "base = (if should_modify (lin_seq s) (his_seq s) q_val then modify_lin (lin_seq s) (his_seq s) q_val else lin_seq s)"
            using base_def .

          (* Proof step: goal also?sn_deq *)
          show "lin_seq s' = base @ [mk_op deq q_val p ?sn_deq]"
            using lin_eq .
        qed
      qed

      (* ----------------------------------------------------------------- *)
      (* Provegoal: lI5_SA_Prefix s' (data preserve) *)
      (* ----------------------------------------------------------------- *)
      have "lI5_SA_Prefix s'"
      proof -
        (* Proof step: use new of physical ticket reader s_var s p *)
        let ?sn_deq = "s_var s p"

        (* 1. align base *)
        define base where "base = (if should_modify (lin_seq s) (his_seq s) q_val
                                   then modify_lin (lin_seq s) (his_seq s) q_val
                                   else lin_seq s)"

        (* 2. alignlistappendfact *)
        have lin_eq: "lin_seq s' = base @ [mk_op deq q_val p ?sn_deq]"
          using D3_unfolded(2) q_not_bot base_def lin_s'_eq
          unfolding base_lin_def current_lin_def current_his_def s_var_def
          by auto

        (* 3. one direct closure *)
        show ?thesis
          by (rule lI5_SA_Prefix_deq_step_preservation[where s=s and base_lin=base, OF INV q_in_SetB q_not_bot base_def lin_eq])
      qed

      (* ----------------------------------------------------------------- *)
      (* LI6_D4_Deq_Linearized: D4 must already in action (q_val \<noteq> BOT success branch) *)
      (* ----------------------------------------------------------------- *)
          have s_var_eq_succ: "s_var s' = s_var s"
        using s'_is_update
        unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
        by auto

      have x_var_eq_qval: "x_var s' = (\<lambda>x. if x = p then q_val else x_var s x)"
        using x_var_eq val_eq
        by (simp add: fun_eq_iff)

      have pc_s'_upd: "program_counter s' = (program_counter s)(p := ''D4'')"
        using pc_eq
        by (simp add: fun_eq_iff)

      have lI8_s_point:
        "\<forall>q. program_counter s q = ''D3'' \<longrightarrow>
            (\<forall>k < length (lin_seq s).
              (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q) \<longrightarrow>
              DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))"
        using INV
        unfolding system_invariant_def lI8_D3_Deq_Returned_def
        by auto

      have x_eq_other: "\<forall>q. q \<noteq> p \<longrightarrow> x_var s' q = x_var s q"
        using x_var_eq_qval by simp

      have sn_eq_other: "\<forall>q. q \<noteq> p \<longrightarrow> s_var s' q = s_var s q"
        using s_var_eq_succ by simp

      have base_succ_def:
        "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                     then modify_lin (lin_seq s) (his_seq s) q_val
                     else lin_seq s)"
        using base_lin_def q_not_bot
        unfolding current_lin_def current_his_def
        by simp

      have q_val_phys: "q_val = Q_arr s (j_var s p)"
        using q_val_def jp_def by simp

      have lI6_D4_Deq_Linearized_s': "lI6_D4_Deq_Linearized s'"
        using D3_success_preserves_lI6_D4_Deq_Linearized[
          OF lI6_D4_Deq_Linearized_s pc_eq x_var_eq_qval s_var_eq_succ lin_s'_eq set_base_eq
      ] .

      have lI7_D4_Deq_Deq_HB_s': "lI7_D4_Deq_Deq_HB s'"
        using D3_success_preserves_lI7_D4_Deq_Deq_HB[
          OF INV q_in_SetB q_not_bot q_val_phys base_succ_def lin_s'_eq his_seq_eq
             pc_s'_upd D3_unfolded(1) lI8_s_point x_eq_other sn_eq_other
      ] .

      have lI8_D3_Deq_Returned_s': "lI8_D3_Deq_Returned s'"
        using D3_success_preserves_lI8_D3_Deq_Returned[
          OF lI8_D3_Deq_Returned_s pc_eq lin_s'_eq his_seq_eq set_base_eq
      ] .

    have lI9_D1_D2_Deq_Returned_s': "lI9_D1_D2_Deq_Returned s'"
      using D3_success_preserves_lI9_D1_D2_Deq_Returned[
        OF lI9_D1_D2_Deq_Returned_s pc_eq lin_s'_eq his_seq_eq set_base_eq
    ] .
    have xv_s'_upd: "x_var s' = (x_var s)(p := q_val)"
      using x_var_eq_qval
      by (simp add: fun_eq_iff)

    have sv_s'_eq: "s_var s' = s_var s"
      using s_var_eq_succ .

    have pc_s'_eq: "program_counter s' = (program_counter s)(p := ''D4'')"
      using pc_s'_upd .

    have lI10_D4_Enq_Deq_HB_s': "lI10_D4_Enq_Deq_HB s'"
      using D3_success_preserves_lI10_D4_Enq_Deq_HB[
        OF INV q_in_SetB q_not_bot q_val_phys base_succ_def lin_s'_eq
           xv_s'_upd sv_s'_eq his_seq_eq pc_s'_eq D3_unfolded(1) lI8_s_point
    ] .

    have lI11_D4_Deq_Unique_s': "lI11_D4_Deq_Unique s'"
      using D3_success_preserves_lI11_D4_Deq_Unique[
        OF INV q_in_SetB q_not_bot jp_def q_val_def val_eq_jp
           base_succ_def lin_s'_eq xv_s'_upd sv_s'_eq his_seq_eq
           pc_s'_eq D3_unfolded(1) lI8_s_point
    ] .

      (* ================================================================= *)
      (* Successdequeuebranch: new USpec invariant uI1/uI2/uI3 *)
      (* ================================================================= *)

      have eff_ops_s'_eq:
        "uspec_effOps s' = insert (mk_op deq q_val p (s_var s p)) (uspec_effOps s)"
      proof -
        have q_phys: "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
          using bridge_q .
        show ?thesis
          using s'_is_update q_phys
          unfolding Sys_D3_success_update_def uspec_effOps_def s_var_def Let_def
          by simp
      qed

      have s_var_s'_eq: "s_var s' = s_var s"
        using s'_is_update
        unfolding Sys_D3_success_update_def Let_def s_var_def
        by (simp add: fun_eq_iff)

      have upc_s'_eq:
        "u_program_counter (snd s') =
           (\<lambda>x. if x = p then ''UD3'' else u_program_counter (snd s) x)"
        using s'_is_update
        unfolding Sys_D3_success_update_def Let_def
        by (simp add: fun_eq_iff)

      have uI1_USpec_EffOps_Lin_s': "uI1_USpec_EffOps_Lin s'"
      proof -
        have "uspec_effOps s' = insert (mk_op deq q_val p (s_var s p)) (set (lin_seq s))"
          using eff_ops_s'_eq uI1_USpec_EffOps_Lin_s
          unfolding uI1_USpec_EffOps_Lin_def
          by simp
        also have "... = set (base_lin @ [mk_op deq q_val p (s_var s p)])"
          using set_base_eq by simp
        also have "... = set (lin_seq s')"
          using lin_s'_eq by simp
        finally show ?thesis
          unfolding uI1_USpec_EffOps_Lin_def .
      qed

      have QueueSpecLin_append_enq:
        "\<And>L v q sn. QueueSpecLin L \<Longrightarrow> QueueSpecLin (L @ [mk_op enq v q sn])"
      proof -
        fix L v q sn
        assume QS: "QueueSpecLin L"
        show "QueueSpecLin (L @ [mk_op enq v q sn])"
          unfolding QueueSpecLin_def lI4_FIFO_Semantics_list_def Let_def
        proof (intro allI impI)
          fix k1
          assume k1_lt: "k1 < length (L @ [mk_op enq v q sn])"
          assume k1_deq: "op_name ((L @ [mk_op enq v q sn]) ! k1) = deq"

          have k1_old: "k1 < length L"
          proof (rule ccontr)
            assume "\<not> k1 < length L"
            hence k1_eq: "k1 = length L"
              using k1_lt by simp
            hence "op_name ((L @ [mk_op enq v q sn]) ! k1) = enq"
              by (simp add: mk_op_def op_name_def)
            thus False
              using k1_deq by simp
          qed

          have old_deq: "op_name (L ! k1) = deq"
            using k1_deq k1_old by (simp add: nth_append)

          obtain k2 where
            k2_lt: "k2 < k1"
            and k2_enq: "op_name (L ! k2) = enq"
            and k2_val: "op_val (L ! k2) = op_val (L ! k1)"
            and before:
              "\<forall>k3<k2.
                  op_name (L ! k3) = enq \<longrightarrow>
                  (\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                         op_name (L ! k4) = deq \<and>
                         op_val (L ! k4) = op_val (L ! k3))"
            using QS k1_old old_deq
            unfolding QueueSpecLin_def lI4_FIFO_Semantics_list_def Let_def
            by blast

          show "\<exists>k2<k1.
                  op_name ((L @ [mk_op enq v q sn]) ! k2) = enq \<and>
                  op_val ((L @ [mk_op enq v q sn]) ! k2) =
                    op_val ((L @ [mk_op enq v q sn]) ! k1) \<and>
                  (\<forall>k3<k2.
                     op_name ((L @ [mk_op enq v q sn]) ! k3) = enq \<longrightarrow>
                     (\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                            op_name ((L @ [mk_op enq v q sn]) ! k4) = deq \<and>
                            op_val ((L @ [mk_op enq v q sn]) ! k4) =
                              op_val ((L @ [mk_op enq v q sn]) ! k3)))"
          proof (intro exI conjI)
            show "k2 < k1"
              using k2_lt .
          next
            show "op_name ((L @ [mk_op enq v q sn]) ! k2) = enq"
              using k2_lt k1_old k2_enq by (simp add: nth_append)
          next
            show "op_val ((L @ [mk_op enq v q sn]) ! k2) =
                  op_val ((L @ [mk_op enq v q sn]) ! k1)"
              using k2_lt k1_old k2_val by (simp add: nth_append)
          next
            show "\<forall>k3<k2.
                    op_name ((L @ [mk_op enq v q sn]) ! k3) = enq \<longrightarrow>
                    (\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                           op_name ((L @ [mk_op enq v q sn]) ! k4) = deq \<and>
                           op_val ((L @ [mk_op enq v q sn]) ! k4) =
                             op_val ((L @ [mk_op enq v q sn]) ! k3))"
            proof (intro allI impI)
              fix k3
              assume k3_lt: "k3 < k2"
              assume k3_enq':
                "op_name ((L @ [mk_op enq v q sn]) ! k3) = enq"

              have k3_old: "k3 < length L"
                using k3_lt k2_lt k1_old by linarith

              have k3_enq: "op_name (L ! k3) = enq"
                using k3_enq' k3_old by (simp add: nth_append)

              obtain k4 where
                k4_gt: "k3 < k4"
                and k4_lt: "k4 < k1"
                and k4_deq: "op_name (L ! k4) = deq"
                and k4_val: "op_val (L ! k4) = op_val (L ! k3)"
                using before k3_lt k3_enq by blast

              have k4_old: "k4 < length L"
                using k4_lt k1_old by linarith

              show "\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                         op_name ((L @ [mk_op enq v q sn]) ! k4) = deq \<and>
                         op_val ((L @ [mk_op enq v q sn]) ! k4) =
                           op_val ((L @ [mk_op enq v q sn]) ! k3)"
                using k4_gt k4_lt k4_deq k4_val k3_old k4_old
                by (intro exI[where x=k4]) (simp add: nth_append)
            qed
          qed
        qed
      qed

      have append_enq_fresh_from_DI:
        "\<And>L v q sn.
          data_independent (L @ [mk_op enq v q sn]) \<Longrightarrow>
          (\<forall>a\<in>set L. op_name a = enq \<longrightarrow> op_val a \<noteq> v)"
      proof (intro ballI impI)
        fix L v q sn a
        assume DI: "data_independent (L @ [mk_op enq v q sn])"
        assume a_in: "a \<in> set L"
        assume a_enq: "op_name a = enq"

        obtain i where i_lt: "i < length L" and a_eq: "a = L ! i"
          using a_in by (metis in_set_conv_nth)

        let ?L = "L @ [mk_op enq v q sn]"

        have i_lt': "i < length ?L"
          using i_lt by simp
        have last_lt': "length L < length ?L"
          by simp
        have i_ne_last: "i \<noteq> length L"
          using i_lt by simp
        have enq_i: "op_name (?L ! i) = enq"
          using i_lt a_eq a_enq
          by (simp add: nth_append)
        have enq_last: "op_name (?L ! length L) = enq"
          by (simp add: nth_append mk_op_def op_name_def)

        have val_neq:
          "op_val (?L ! i) \<noteq> op_val (?L ! length L)"
          using unique_enq_value[OF DI i_lt' last_lt' i_ne_last enq_i enq_last] .

        show "op_val a \<noteq> v"
          using val_neq i_lt a_eq
          by (simp add: nth_append mk_op_def op_val_def)
      qed

      have no_HB_from_pending_enq:
        "\<And>pa x.
          program_counter s' pa \<in> {''E1'', ''E2''} \<Longrightarrow>
          \<not> HB (his_seq s')
                (mk_op enq (v_var s' pa) pa (s_var s' pa))
                x"
      proof -
        fix pa x
        assume pc_pa': "program_counter s' pa \<in> {''E1'', ''E2''}"

        have pending:
          "HasPendingEnq s' pa (v_var s' pa)"
          using hI1_E_Phase_Pending_Enq_s' pc_pa'
          unfolding hI1_E_Phase_Pending_Enq_def
          by auto

        show "\<not> HB (his_seq s')
                  (mk_op enq (v_var s' pa) pa (s_var s' pa))
                  x"
        proof
          assume hb:
            "HB (his_seq s')
                (mk_op enq (v_var s' pa) pa (s_var s' pa))
                x"

          then obtain k1 where
            mr: "match_ret (his_seq s') k1
                  (mk_op enq (v_var s' pa) pa (s_var s' pa))"
            unfolding HB_def by blast

          have ret_idx_lt: "k1 < length (his_seq s')"
            using mr
            unfolding match_ret_def
            by simp

          have ret_props:
            "act_pid (his_seq s' ! k1) = pa \<and>
             act_ssn (his_seq s' ! k1) = s_var s' pa \<and>
             act_cr (his_seq s' ! k1) = ret"
            using mr
            unfolding match_ret_def Let_def
            by (auto simp: mk_op_def op_pid_def op_ssn_def)

          have "\<exists>e\<in>set (his_seq s').
              act_pid e = pa \<and>
              act_ssn e = s_var s' pa \<and>
              act_cr e = ret"
          proof
            show "his_seq s' ! k1 \<in> set (his_seq s')"
              using ret_idx_lt by (rule nth_mem)
          next
            show "act_pid (his_seq s' ! k1) = pa \<and>
                  act_ssn (his_seq s' ! k1) = s_var s' pa \<and>
                  act_cr (his_seq s' ! k1) = ret"
              using ret_props .
          qed

          then show False
            using pending
            unfolding HasPendingEnq_def Let_def
            by blast
        qed
      qed

      have deq_called:
        "OpCalledInHis (his_seq s) (mk_op deq q_val p (s_var s p))"
      proof -
        have pending_deq: "HasPendingDeq s p"
          using hI12_D_Phase_Pending_Deq_s D3_unfolded(1)
          unfolding hI12_D_Phase_Pending_Deq_def
          by auto

        have call_deq: "DeqCallInHis s p (s_var s p)"
          using pending_deq
          unfolding HasPendingDeq_def Let_def
          by blast

        obtain e where
          e_in: "e \<in> set (his_seq s)"
          and e_pid: "act_pid e = p"
          and e_ssn: "act_ssn e = s_var s p"
          and e_name: "act_name e = deq"
          and e_cr: "act_cr e = call"
          and e_val: "act_val e = BOT"
          using call_deq
          unfolding DeqCallInHis_def
          by blast

        obtain k where
          k_lt: "k < length (his_seq s)"
          and e_eq: "his_seq s ! k = e"
          using e_in
          by (meson in_set_conv_nth)

        have mc:
          "match_call (his_seq s) k (mk_op deq q_val p (s_var s p))"
          using k_lt e_eq e_pid e_ssn e_name e_cr e_val
          unfolding match_call_def Let_def
          by (simp add: mk_op_def op_name_def op_pid_def op_ssn_def op_val_def)

        show ?thesis
          unfolding OpCalledInHis_def
          using mc
          by blast
      qed

      have uI2_USpec_E1UE2_s': "uI2_USpec_E1UE2 s'"
      proof (unfold uI2_USpec_E1UE2_def, intro allI impI)
        fix pa
        assume pc_pa': "program_counter s' pa \<in> {''E1'', ''E2''}"
        assume upc_pa': "u_program_counter (snd s') pa = ''UE2''"

        let ?enq' = "mk_op enq (v_var s' pa) pa (s_var s' pa)"
        let ?enq  = "mk_op enq (v_var s pa) pa (s_var s pa)"
        let ?deq  = "mk_op deq q_val p (s_var s p)"

        have pa_ne_p: "pa \<noteq> p"
          using pc_pa' pc_eq by auto

        have pc_pa_old: "program_counter s pa \<in> {''E1'', ''E2''}"
          using pc_pa' pc_eq pa_ne_p by auto

        have upc_pa_old: "u_program_counter (snd s) pa = ''UE2''"
          using upc_pa' upc_s'_eq pa_ne_p by simp

        have enq_eq: "?enq' = ?enq"
          using prem3_V s_var_s'_eq
          by simp

        have old_gen:
          "USpec_GenLin (his_seq s)
                         (uspec_effOps s)
                         ?enq
                         (lin_seq s @ [?enq])"
          using uI2_USpec_E1UE2_s pc_pa_old upc_pa_old
          unfolding uI2_USpec_E1UE2_def his_seq_def lin_seq_def uspec_effOps_def
          by blast

        have old_called_all:
          "\<forall>a\<in>set (lin_seq s @ [?enq]). OpCalledInHis (his_seq s) a"
          using old_gen
          unfolding USpec_GenLin_def
          by blast

        have called_base:
          "\<forall>a\<in>set base_lin. OpCalledInHis (his_seq s') a"
        proof
          fix a
          assume a_base: "a \<in> set base_lin"
          hence a_old: "a \<in> set (lin_seq s)"
            using set_base_eq by simp
          hence "OpCalledInHis (his_seq s) a"
            using old_called_all by auto
          thus "OpCalledInHis (his_seq s') a"
            using his_seq_eq by simp
        qed

        have called_deq':
          "OpCalledInHis (his_seq s') ?deq"
          using deq_called his_seq_eq by simp

        have called_enq':
          "OpCalledInHis (his_seq s') ?enq'"
        proof -
          have "OpCalledInHis (his_seq s) ?enq"
            using old_called_all by auto
          thus ?thesis
            using his_seq_eq enq_eq by simp
        qed

        have called_lin_s':
          "\<forall>a\<in>set (lin_seq s'). OpCalledInHis (his_seq s') a"
        proof
          fix a
          assume a_in: "a \<in> set (lin_seq s')"
          hence "a \<in> set base_lin \<or> a = ?deq"
            using lin_s'_eq by auto
          thus "OpCalledInHis (his_seq s') a"
            using called_base called_deq' by auto
        qed

        have hb_lin_s':
          "HB_consistent (lin_seq s') (his_seq s')"
          using lI3_HB_Ret_Lin_Sync_s'
          unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def HB_consistent_def
          by simp

        have hb_append:
          "HB_consistent (lin_seq s' @ [?enq']) (his_seq s')"
        proof (rule HB_consistent_append)
          show "HB_consistent (lin_seq s') (his_seq s')"
            using hb_lin_s' .
        next
          show "\<forall>x\<in>set (lin_seq s'). \<not> HB (his_seq s') ?enq' x"
            using no_HB_from_pending_enq[OF pc_pa'] by blast
        next
          show "\<not> HB (his_seq s') ?enq' ?enq'"
            using no_HB_from_pending_enq[OF pc_pa'] .
        qed

        have qs_lin_s':
          "QueueSpecLin (lin_seq s')"
          using \<open>lI4_FIFO_Semantics s'\<close>
          unfolding QueueSpecLin_def lI4_FIFO_Semantics_def
          by simp

        have qs_append:
          "QueueSpecLin (lin_seq s' @ [?enq'])"
          using QueueSpecLin_append_enq[OF qs_lin_s'] .

        have old_di_append:
          "data_independent (lin_seq s @ [?enq])"
          using old_gen
          unfolding USpec_GenLin_def
          by blast

        have fresh_old_set:
          "\<forall>a\<in>set (lin_seq s). op_name a = enq \<longrightarrow> op_val a \<noteq> v_var s pa"
          using append_enq_fresh_from_DI[OF old_di_append]
          by simp

        have fresh_base:
          "\<forall>a\<in>set base_lin. op_name a = enq \<longrightarrow> op_val a \<noteq> v_var s pa"
          using fresh_old_set set_base_eq
          by auto

        have fresh_lin_s'_set:
          "\<forall>a\<in>set (lin_seq s'). op_name a = enq \<longrightarrow> op_val a \<noteq> v_var s' pa"
        proof
          fix a
          assume a_in: "a \<in> set (lin_seq s')"
          show "op_name a = enq \<longrightarrow> op_val a \<noteq> v_var s' pa"
          proof
            assume a_enq: "op_name a = enq"
            have "a \<in> set base_lin \<or> a = ?deq"
              using a_in lin_s'_eq by auto
            thus "op_val a \<noteq> v_var s' pa"
            proof
              assume "a \<in> set base_lin"
              thus ?thesis
                using fresh_base a_enq prem3_V by auto
            next
              assume "a = ?deq"
              thus ?thesis
                using a_enq by (simp add: mk_op_def op_name_def)
            qed
          qed
        qed

        have fresh_lin_s'_idx:
          "\<forall>i<length (lin_seq s').
             op_name (lin_seq s' ! i) = enq \<longrightarrow>
             op_val (lin_seq s' ! i) \<noteq> v_var s' pa"
          using fresh_lin_s'_set
          by (meson nth_mem)

        have di_append:
          "data_independent (lin_seq s' @ [?enq'])"
          using data_independent_append_enq_fresh[
            OF di_s' fresh_lin_s'_idx,
            of pa "s_var s' pa"
        ]
          by simp

        have eff_set_s':
          "uspec_effOps s' = set (lin_seq s')"
          using uI1_USpec_EffOps_Lin_s'
          unfolding uI1_USpec_EffOps_Lin_def .

        have gen_sys:
          "USpec_GenLin (his_seq s')
                         (uspec_effOps s')
                         ?enq'
                         (lin_seq s' @ [?enq'])"
          unfolding USpec_GenLin_def
        proof (intro conjI)
          show "finite (uspec_effOps s')"
            using eff_set_s' by simp
        next
          show "uspec_effOps s' \<subseteq> set (lin_seq s' @ [?enq'])"
            using eff_set_s' by auto
        next
          show "?enq' \<in> set (lin_seq s' @ [?enq'])"
            by simp
        next
          show "\<forall>a\<in>set (lin_seq s' @ [?enq']). OpCalledInHis (his_seq s') a"
            using called_lin_s' called_enq' by auto
        next
          show "HB_consistent (lin_seq s' @ [?enq']) (his_seq s')"
            using hb_append .
        next
          show "QueueSpecLin (lin_seq s' @ [?enq'])"
            using qs_append .
        next
          show "data_independent (lin_seq s' @ [?enq'])"
            using di_append .
        qed

        show "USpec_GenLin (u_his_seq (snd s'))
                           (u_eff_ops (snd s'))
                           ?enq'
                           (u_lin_seq (snd s') @ [?enq'])"
          using gen_sys
          unfolding his_seq_def lin_seq_def uspec_effOps_def
          by simp
      qed

        have TypeOK_s': "TypeOK s'"
          using \<open>TypeOK s'\<close> .

        have sI6_D3_Scan_Pointers_s': "sI6_D3_Scan_Pointers s'"
          using \<open>sI6_D3_Scan_Pointers s'\<close> .

        have sI8_Q_Qback_Sync_s': "sI8_Q_Qback_Sync s'"
          using \<open>sI8_Q_Qback_Sync s'\<close> .

        have sI10_Qback_Unique_Vals_s': "sI10_Qback_Unique_Vals s'"
          using \<open>sI10_Qback_Unique_Vals s'\<close> .

        have lI5_SA_Prefix_s': "lI5_SA_Prefix s'"
          using \<open>lI5_SA_Prefix s'\<close> .

      have uI3_USpec_D3UD2_s': "uI3_USpec_D3UD2 s'"
      proof (unfold uI3_USpec_D3UD2_def, intro allI impI)
        fix pa
        assume pc_pa': "program_counter s' pa = ''D3''"
        assume qj_pa': "Q_arr s' (j_var s' pa) \<noteq> BOT"
        assume upc_pa': "u_program_counter (snd s') pa = ''UD2''"

        have lI1_Op_Sets_Equivalence_s':
          "lI1_Op_Sets_Equivalence s'"
          using \<open>lI1_Op_Sets_Equivalence s'\<close> .

        have lI2_Op_Cardinality_s':
          "lI2_Op_Cardinality s'"
          using \<open>lI2_Op_Cardinality s'\<close> .

        have lI4_FIFO_Semantics_s':
          "lI4_FIFO_Semantics s'"
          using \<open>lI4_FIFO_Semantics s'\<close> .

        have hI5_SSN_Unique_s':
          "hI5_SSN_Unique s'"
          using \<open>hI5_SSN_Unique s'\<close> .

        have hI7_His_WF_s':
          "hI7_His_WF s'"
          using \<open>hI7_His_WF s'\<close> .

        have hI16_BO_BT_No_HB_s':
          "hI16_BO_BT_No_HB s'"
          using \<open>hI16_BO_BT_No_HB s'\<close> .

        have hI17_BT_BT_No_HB_s':
          "hI17_BT_BT_No_HB s'"
          using \<open>hI17_BT_BT_No_HB s'\<close> .

        have hI20_Enq_Val_Valid_s':
          "hI20_Enq_Val_Valid s'"
          using \<open>hI20_Enq_Val_Valid s'\<close> .

        let ?x = "Q_arr s' (j_var s' pa)"
        let ?op = "mk_op deq ?x pa (s_var s' pa)"
        let ?base =
          "(if should_modify (lin_seq s') (his_seq s') ?x
            then modify_lin (lin_seq s') (his_seq s') ?x
            else lin_seq s')"
        let ?L = "?base @ [?op]"
        let ?H = "his_seq s'"

        have pa_ne_p: "pa \<noteq> p"
        proof
          assume pa_eq: "pa = p"
          have "program_counter s' p = ''D4''"
            using pc_eq by simp
          thus False
            using pc_pa' pa_eq by simp
        qed

        have pending_pa:
          "HasPendingDeq s' pa"
          using hI12_D_Phase_Pending_Deq_s' pc_pa'
          unfolding hI12_D_Phase_Pending_Deq_def
          by auto

        have deq_call_pa:
          "DeqCallInHis s' pa (s_var s' pa)"
          using pending_pa
          unfolding HasPendingDeq_def Let_def
          by blast

        have op_called:
          "OpCalledInHis ?H ?op"
          using DeqCallInHis_imp_OpCalledInHis[OF deq_call_pa, of ?x]
          by simp

        have no_HB_from_op:
          "\<forall>x. \<not> HB ?H ?op x"
        proof
          fix x
          show "\<not> HB ?H ?op x"
          proof
            assume hb: "HB ?H ?op x"

            then obtain k1 where
              mr: "match_ret ?H k1 ?op"
              unfolding HB_def
              by blast

            have k1_lt:
              "k1 < length ?H"
              using mr
              unfolding match_ret_def Let_def
              by simp

            have pid_eq:
              "act_pid (?H ! k1) = pa"
              using mr
              unfolding match_ret_def Let_def
              by (simp add: mk_op_def op_pid_def)

            have ssn_eq:
              "act_ssn (?H ! k1) = s_var s' pa"
              using mr
              unfolding match_ret_def Let_def
              by (simp add: mk_op_def op_ssn_def)

            have cr_eq:
              "act_cr (?H ! k1) = ret"
              using mr
              unfolding match_ret_def Let_def
              by simp

            have in_his:
              "?H ! k1 \<in> set ?H"
              using k1_lt
              by simp

            have no_ret:
              "\<forall>e\<in>set ?H.
                 \<not> (act_pid e = pa \<and>
                      act_ssn e = s_var s' pa \<and>
                      act_cr e = ret)"
              using pending_pa
              unfolding HasPendingDeq_def Let_def
              by blast

            show False
              using no_ret in_his pid_eq ssn_eq cr_eq
              by blast
          qed
        qed

        have hb_lin_s':
          "HB_consistent (lin_seq s') (his_seq s')"
          using lI3_HB_Ret_Lin_Sync_s'
          unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def HB_consistent_def
          by simp

        have qs_lin_s':
          "QueueSpecLin (lin_seq s')"
          using \<open>lI4_FIFO_Semantics s'\<close>
          unfolding QueueSpecLin_def lI4_FIFO_Semantics_def
          by simp

        have eff_eq_s':
          "uspec_effOps s' = set (lin_seq s')"
          using uI1_USpec_EffOps_Lin_s'
          unfolding uI1_USpec_EffOps_Lin_def
          by simp

        have finite_eff_s':
          "finite (uspec_effOps s')"
          using eff_eq_s'
          by simp

        have set_base_eq_s':
          "set ?base = set (lin_seq s')"
        proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
          case True
          hence base_eq:
            "?base = modify_lin (lin_seq s') (his_seq s') ?x"
            by simp

          hence "mset ?base = mset (lin_seq s')"
            using modify_preserves_mset
            by simp

          thus ?thesis
            by (metis set_mset_mset)
        next
          case False
          thus ?thesis
            by simp
        qed

        have eff_subset:
          "uspec_effOps s' \<subseteq> set ?L"
          using eff_eq_s' set_base_eq_s'
          by auto

        have op_in:
          "?op \<in> set ?L"
          by simp

        have lin_called_s':
          "\<forall>a\<in>set (lin_seq s'). OpCalledInHis (his_seq s') a"
        proof
          fix a
          assume a_in: "a \<in> set (lin_seq s')"

          have a_oplin: "a \<in> OPLin s'"
            using a_in
            unfolding OPLin_def
            by simp

          have cases:
            "a \<in> OP_A_enq s' \<or> a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
            using lI1_Op_Sets_Equivalence_s' a_oplin
            unfolding lI1_Op_Sets_Equivalence_def
            by blast

          thus "OpCalledInHis (his_seq s') a"
          proof
            assume "a \<in> OP_A_enq s'"
            then obtain q v sn where
              a_eq: "a = mk_op enq v q sn"
              and call: "EnqCallInHis s' q v sn"
              unfolding OP_A_enq_def
              by blast

            show ?thesis
              using EnqCallInHis_imp_OpCalledInHis[OF call]
              unfolding a_eq
              by simp
          next
            assume rest: "a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
            thus ?thesis
            proof
              assume "a \<in> OP_A_deq s'"

              hence name_deq: "op_name a = deq"
                and call: "DeqCallInHis s' (op_pid a) (op_ssn a)"
                unfolding OP_A_deq_def
                by auto

              have a_mk:
                "mk_op deq (op_val a) (op_pid a) (op_ssn a) = a"
                using name_deq
                by (cases a)
                   (simp add: mk_op_def op_name_def op_val_def op_pid_def op_ssn_def)

              have called_mk:
                "OpCalledInHis (his_seq s')
                   (mk_op deq (op_val a) (op_pid a) (op_ssn a))"
                using DeqCallInHis_imp_OpCalledInHis[OF call, of "op_val a"] .

              show ?thesis
                using called_mk a_mk
                by simp
            next
              assume "a \<in> OP_B_enq s'"
              then obtain q v sn where
                a_eq: "a = mk_op enq v q sn"
                and call: "EnqCallInHis s' q v sn"
                unfolding OP_B_enq_def
                by blast

              show ?thesis
                using EnqCallInHis_imp_OpCalledInHis[OF call]
                unfolding a_eq
                by simp
            qed
          qed
        qed

        have base_called:
          "\<forall>a\<in>set ?base. OpCalledInHis ?H a"
          using lin_called_s' set_base_eq_s'
          by auto

        have all_called:
          "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
          using base_called op_called
          by auto

        have lI4_list_s':
          "lI4_FIFO_Semantics_list (lin_seq s')"
          using \<open>lI4_FIFO_Semantics s'\<close>
          unfolding lI4_FIFO_Semantics_def
          by simp


        have lI5_list_s':
          "lI5_SA_Prefix_list (lin_seq s')"
          using lI5_SA_Prefix_s'
          unfolding lI5_SA_Prefix_def
          by simp

        have x_val:
          "?x \<in> Val"
          using TypeOK_s' qj_pa'
          unfolding TypeOK_def
          by auto

        have x_TypeB:
          "TypeB s' ?x"
          unfolding TypeB_def QHas_def
          by blast

        have x_SetB:
          "?x \<in> SetB s'"
          unfolding SetB_def
          using x_val x_TypeB
          by simp

        have typeBT_x_s':
          "TypeBT s' ?x"
          using D3_j_nonBOT_TypeBT_from_local[
            OF sI6_D3_Scan_Pointers_s'
               sI8_Q_Qback_Sync_s'
               sI10_Qback_Unique_Vals_s'
               pc_pa' qj_pa'
        ] .

        have mset_modify_s':
          "mset (modify_lin (lin_seq s') (his_seq s') ?x) = mset (lin_seq s')"
          using modify_preserves_mset[
            of "lin_seq s'" "his_seq s'" ?x
        ] .

        have mset_base_eq:
          "mset ?base = mset (lin_seq s')"
        proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
          case True
          hence base_eq:
            "?base = modify_lin (lin_seq s') (his_seq s') ?x"
            by simp

          show ?thesis
            unfolding base_eq
            using mset_modify_s' .
        next
          case False
          hence base_eq:
            "?base = lin_seq s'"
            by simp

          show ?thesis
            unfolding base_eq
            by simp
        qed

        have enq_exists_x_lin:
          "\<exists>k < length (lin_seq s').
             op_name (lin_seq s' ! k) = enq \<and>
             op_val (lin_seq s' ! k) = ?x"
          using SetB_implies_enq_in_lin_from_LI2[
            OF \<open>lI2_Op_Cardinality s'\<close> x_SetB
        ] .

        have pending_x_lin:
          "\<forall>i < length (lin_seq s').
             op_val (lin_seq s' ! i) = ?x \<longrightarrow>
             op_name (lin_seq s' ! i) \<noteq> deq"
          using SetB_implies_no_deq_in_lin_from_LI2[
            OF \<open>lI2_Op_Cardinality s'\<close> x_SetB
        ] .


        have pending_x_base:
          "\<forall>i < length ?base.
             op_val (?base ! i) = ?x \<longrightarrow>
             op_name (?base ! i) \<noteq> deq"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < length ?base"
          assume val_i: "op_val (?base ! i) = ?x"

          have act_in_base:
            "?base ! i \<in> set ?base"
            using i_lt
            by simp

          hence act_in_lin:
            "?base ! i \<in> set (lin_seq s')"
            using mset_base_eq
            by (metis set_mset_mset)

          then obtain j where
            j_lt: "j < length (lin_seq s')"
            and j_eq: "lin_seq s' ! j = ?base ! i"
            by (auto simp: in_set_conv_nth)

          have val_j:
            "op_val (lin_seq s' ! j) = ?x"
            using j_eq val_i
            by simp

          have name_j:
            "op_name (lin_seq s' ! j) \<noteq> deq"
            using pending_x_lin j_lt val_j
            by blast

          have base_i_eq_j:
            "?base ! i = lin_seq s' ! j"
            using j_eq
            by simp

          show "op_name (?base ! i) \<noteq> deq"
            using name_j base_i_eq_j
            by metis
        qed

        have no_deq_x_base:
          "\<forall>i < length ?base.
             op_name (?base ! i) = deq \<longrightarrow>
             op_val (?base ! i) \<noteq> ?x"
          using pending_x_base
          by blast

        have enq_exists_x_base:
          "\<exists>k < length ?base.
             op_name (?base ! k) = enq \<and>
             op_val (?base ! k) = ?x"
        proof -
          obtain k where
            k_lt: "k < length (lin_seq s')"
            and k_enq: "op_name (lin_seq s' ! k) = enq"
            and k_val: "op_val (lin_seq s' ! k) = ?x"
            using enq_exists_x_lin
            by blast

          have act_in_lin:
            "lin_seq s' ! k \<in> set (lin_seq s')"
            using k_lt
            by simp

          hence act_in_base:
            "lin_seq s' ! k \<in> set ?base"
            using mset_base_eq
            by (metis set_mset_mset)

          then obtain kb where
            kb_lt: "kb < length ?base"
            and kb_eq: "?base ! kb = lin_seq s' ! k"
            by (auto simp: in_set_conv_nth)

          have kb_enq:
            "op_name (?base ! kb) = enq"
            using kb_eq k_enq
            by metis

          have kb_val:
            "op_val (?base ! kb) = ?x"
            using kb_eq k_val
            by metis

          show ?thesis
          proof (rule exI[where x = kb])
            show "kb < length ?base \<and>
                  op_name (?base ! kb) = enq \<and>
                  op_val (?base ! kb) = ?x"
              using kb_lt kb_enq kb_val
              by simp
          qed
        qed

        have not_sa_x_base:
          "\<not> in_SA ?x ?base"
        proof -
          have no_deq_act:
            "\<forall>a \<in> set ?base.
              op_val a = ?x \<longrightarrow> op_name a \<noteq> deq"
          proof
            fix a
            assume a_in: "a \<in> set ?base"
            then obtain i where
              i_lt: "i < length ?base"
              and a_eq: "?base ! i = a"
              by (auto simp: in_set_conv_nth)

            show "op_val a = ?x \<longrightarrow> op_name a \<noteq> deq"
            proof
              assume val_a: "op_val a = ?x"

              have val_i:
                "op_val (?base ! i) = ?x"
                using a_eq val_a
                by metis

              have name_i:
                "op_name (?base ! i) \<noteq> deq"
                using pending_x_base i_lt val_i
                by blast

              show "op_name a \<noteq> deq"
                using name_i a_eq
                by metis
            qed
          qed

          show ?thesis
            by (rule not_in_SA_if_no_deq_act[OF no_deq_act])
        qed

        have dist_zero_base:
          "Distance ?base ?x = 0"
        proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
          case True
          hence base_eq:
            "?base = modify_lin (lin_seq s') (his_seq s') ?x"
            by simp

          show ?thesis
            using modify_lin_Distance_zero_internal[
              OF di_s' lI4_list_s' lI5_list_s'
                 pending_x_lin enq_exists_x_lin
          ]
            unfolding base_eq
            by simp
        next
          case False

          have dist_zero_lin:
            "Distance (lin_seq s') ?x = 0"
          proof (rule ccontr)
            assume dist_not_zero:
              "Distance (lin_seq s') ?x \<noteq> 0"

            have "should_modify (lin_seq s') (his_seq s') ?x"
              using should_modify_completeness[
                OF di_s' lI5_list_s'
                   pending_x_lin enq_exists_x_lin dist_not_zero
            ] .

            thus False
              using False
              by simp
          qed

          show ?thesis
            using False dist_zero_lin
            by simp
        qed

        have hb_base:
          "HB_consistent ?base ?H"
        proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
          case False
          thus ?thesis
            using hb_lin_s'
            by simp
        next
          case True
          hence base_eq:
            "?base = modify_lin (lin_seq s') (his_seq s') ?x"
            by simp

          show ?thesis
            unfolding base_eq
            by (rule modify_preserves_HB_consistent_from_local_invs[
                  where s = s'
                    and L = "lin_seq s'"
                    and H = "his_seq s'"
                    and bt_val = ?x
              ])
               (simp_all add:
                  hb_lin_s'
                  di_s'
                  typeBT_x_s'
                  lI1_Op_Sets_Equivalence_s'
                  lI2_Op_Cardinality_s'
                  lI4_FIFO_Semantics_s'
                  hI5_SSN_Unique_s'
                  hI7_His_WF_s'
                  hI16_BO_BT_No_HB_s'
                  hI17_BT_BT_No_HB_s'
                  hI20_Enq_Val_Valid_s')

        qed

        have hb_final:
          "HB_consistent ?L ?H"
        proof (rule HB_consistent_append)
          show "HB_consistent ?base ?H"
            using hb_base .
        next
          show "\<forall>a\<in>set ?base. \<not> HB ?H ?op a"
            using no_HB_from_op
            by blast
        next
          show "\<not> HB ?H ?op ?op"
            using no_HB_from_op
            by blast
        qed

        have qs_base:
          "QueueSpecLin ?base"
        proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
          case False
          thus ?thesis
            using qs_lin_s'
            by simp
        next
          case True
          hence base_eq:
            "?base = modify_lin (lin_seq s') (his_seq s') ?x"
            by simp

          have base_list:
            "lI4_FIFO_Semantics_list ?base"
            unfolding base_eq
            by (rule move_pending_enq_preserves_lI4_FIFO_Semantics[
                  where L = "lin_seq s'"
                    and H = "his_seq s'"
                    and v = ?x
              ])
               (simp_all add:
                  lI4_list_s'
                  di_s'
                  lI5_list_s'
                  pending_x_lin)

          show ?thesis
            using base_list
            unfolding QueueSpecLin_def
            by simp
        qed


        have di_base:
          "data_independent ?base"
        proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
          case False
          thus ?thesis
            using di_s'
            by simp
        next
          case True
          hence base_eq:
            "?base = modify_lin (lin_seq s') (his_seq s') ?x"
            by simp

          show ?thesis
            unfolding base_eq
            using di_s' modify_preserves_data_independent
            by presburger
        qed

        have qs_final:
          "QueueSpecLin ?L"
        proof -
          have base_list:
            "lI4_FIFO_Semantics_list ?base"
            using qs_base
            unfolding QueueSpecLin_def
            by simp

          have final_list:
            "lI4_FIFO_Semantics_list (?base @ [?op])"
          proof (rule lI4_FIFO_Semantics_append_deq_success[where v = ?x])
            show "lI4_FIFO_Semantics_list ?base"
              using base_list .

            show "data_independent ?base"
              using di_base .

            show "op_name ?op = deq"
              by (simp add: mk_op_def op_name_def)

            show "op_val ?op = ?x"
              by (simp add: mk_op_def op_val_def)

            show "\<exists>k < length ?base.
                    op_name (?base ! k) = enq \<and>
                    op_val (?base ! k) = ?x"
              using enq_exists_x_base .

            show "\<not> in_SA ?x ?base"
              using not_sa_x_base .

            show "Distance ?base ?x = 0"
              using dist_zero_base .
          qed

          show ?thesis
            using final_list
            unfolding QueueSpecLin_def
            by simp
        qed


        have di_final:
          "data_independent ?L"
        proof -
          have "data_independent (?base @ [mk_op deq ?x pa (s_var s' pa)])"
            using data_independent_append_deq_fresh[
              OF di_base no_deq_x_base
          ] .

          thus ?thesis
            by simp
        qed


        show "let cur_lin = lin_seq s';
                  cur_his = his_seq s';
                  x_val = Q_arr s' (j_var s' pa);
                  op = mk_op deq x_val pa (s_var s' pa);
                  new_lin =
                    (if should_modify cur_lin cur_his x_val
                     then modify_lin cur_lin cur_his x_val
                     else cur_lin) @ [op]
              in USpec_GenLin cur_his (uspec_effOps s') op new_lin"
          unfolding USpec_GenLin_def Let_def
          using finite_eff_s' eff_subset op_in all_called hb_final qs_final di_final
          by simp
      qed

      (* ----------------------------------------------------------------- *)
      (* Prove Simulate_PC s' (precisealignversion) *)
      (* ----------------------------------------------------------------- *)
      have "Simulate_PC s'"
      proof -
        (* 1. old state of PC mapping *)
        have old_refine: "Simulate_PC s"
          using `system_invariant s` unfolding system_invariant_def by simp

        (* 2. synchronizeunfoldpremise and conclusion, make auto *)
        show ?thesis
          using s'_is_update old_refine
          unfolding Simulate_PC_def Sys_D3_success_update_def Let_def
          by auto
      qed

      (* ----------------------------------------------------------------- *)
      (* 6. conclusion *)
      (* ----------------------------------------------------------------- *)
    show ?thesis
      unfolding system_invariant_def
      using `Simulate_PC s'` `TypeOK s'` `sI1_Zero_Index_BOT s'`
      `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'` `hI3_L0_E_Phase_Bounds s'`
      `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'` `sI12_D3_Scanned_Prefix s'`
      `uI1_USpec_EffOps_Lin s'` `uI2_USpec_E1UE2 s'` `uI3_USpec_D3UD2 s'` `hI4_X_var_Lin_Sync s'`
      `hI7_His_WF s'` `hI8_Val_Unique s'` `hI5_SSN_Unique s'` `hI6_SSN_Order s'`
      `hI9_Deq_Ret_Unique s'` `hI10_Enq_Call_Existence s'` `hI11_Enq_Ret_Existence s'` `hI12_D_Phase_Pending_Deq s'`  `hI13_Qback_Deq_Sync s'` `hI14_Pending_Enq_Qback_Exclusivity s'` `hI15_Deq_Result_Exclusivity s'`
      `hI16_BO_BT_No_HB s'` `hI17_BT_BT_No_HB s'` `hI18_Idx_Order_No_Rev_HB s'` `hI19_Scanner_Catches_Later_Enq s'` `hI20_Enq_Val_Valid s'` `hI21_Ret_Implies_Call s'` `hI22_Deq_Local_Pattern s'`
      `hI23_Deq_Call_Ret_Balanced s'` `hI24_HB_Implies_Idx_Order s'` `hI25_Enq_Call_Ret_Balanced s'` `hI26_DeqRet_D4_Mutex s'`
      `hI27_Pending_PC_Sync  s'` `hI28_Fresh_Enq_Immunity  s'` `hI29_E2_Scanner_Immunity  s'`
      `hI30_Ticket_HB_Immunity s'`
      `lI1_Op_Sets_Equivalence s'` `lI2_Op_Cardinality s'` `lI3_HB_Ret_Lin_Sync s'` `lI4_FIFO_Semantics s'` `lI5_SA_Prefix s'`  `lI6_D4_Deq_Linearized s'`
      `lI7_D4_Deq_Deq_HB s'` `lI8_D3_Deq_Returned s'` `lI9_D1_D2_Deq_Returned s'` `lI10_D4_Enq_Deq_HB s'` `lI11_D4_Deq_Unique s'`
      `data_independent (lin_seq s')`
      by blast
    qed
qed

end
