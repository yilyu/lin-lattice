(* Framework of the system-invariant proof *)
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

(* ========== Preservation of the system invariant for the D3 transition rule ========== *)
lemma D3_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_D3 p s s'"  
  shows "system_invariant s'"
proof -    
    (* Introduce a shared bundle of bridge definitions *)
    note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                       Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def

  (* ================================================================= *)
  (* 1. unpack the invariants of the current state *)
  (* ================================================================= *)
  have TypeOK_s: "TypeOK s" and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s" 
    and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s" and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s" 
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s" and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s" and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s" and sI11_x_var_Scope_s: "sI11_x_var_Scope s"
    and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s" and hI4_X_var_Lin_Sync_s: "hI4_X_var_Lin_Sync s"
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
  (* 2. extract the key variables and state updates of the D3 step *)
  (* ================================================================= *)
  (* extract local abbreviations *)
  define jp where "jp = j_var s p"
  define lp where "lp = l_var s p"
  define q_val where "q_val = Q_arr s jp"
  
  (* extract the current history and linearization *)
  define current_lin where "current_lin = lin_seq s"
  define current_his where "current_his = his_seq s"

  (* compute base_lin according to q_val and the modify_lin condition *)
  define base_lin where "base_lin = 
    (if q_val = BOT then current_lin 
     else if should_modify current_lin current_his q_val 
          then modify_lin current_lin current_his q_val 
          else current_lin)"

(* ================================================================= *)
  (* Unfold s' as a pair update on both the concrete and abstract components *)
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
            u_lin_seq := base_lin @ [mk_op deq q_val p (s_var s p)]
          \<rparr>)
    )"
    using D3_step_unfolded[OF STEP jp_def lp_def q_val_def current_lin_def current_his_def base_lin_def] .

  (* ================================================================= *)
  (* 3. Case split: q_val = BOT versus q_val \<noteq> BOT *)
  (* ================================================================= *)
  show ?thesis
  proof (cases "q_val = BOT")
    case True
    (* --------------------------------------------------------------- *)
    (* Case 1: the scanned queue slot is empty (no successful dequeue and no linearization change) *)
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

(* --- Begin the preservation proof for the BOT branch --- *)
    
    (* --------------------------------------------------------------- *)
    (* BOT branch: preservation of the basic invariants *)
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
    (* BOT branch: preservation of the remaining concrete and history invariants *)
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
    (* BOT branch: history-tail properties *)
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
    (* BOT branch: linearization-tail properties *)
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

    (* Assemble the result of Case 1 *)
    show ?thesis 
      unfolding system_invariant_def
      using `Simulate_PC s'`   
      using `TypeOK s'`  `sI1_Zero_Index_BOT s'`
      `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'`  `hI3_L0_E_Phase_Bounds s'` 
      `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'` `sI12_D3_Scanned_Prefix s'` `hI4_X_var_Lin_Sync s'`
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
      (* Case 2: successful dequeue (q_val \<noteq> BOT) *)
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
    (* hI4_X_var_Lin_Sync: consistency of the concrete/abstract correspondence (q_val \<noteq> BOT ) *)
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
        OF INV s'_is_update count_eq
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
    (* hI19: bidirectional synchronization between the logical state and the concrete PC (successful-dequeue branch - using only shared branch facts) *)
    (* ========================================================================= *)
    have "hI27_Pending_PC_Sync s'"
    proof (unfold hI27_Pending_PC_Sync_def, intro conjI allI impI)
      (* extract hI19 from the old state *)
      have hI19_s: "hI27_Pending_PC_Sync s" using INV unfolding system_invariant_def by blast
      (* 💡 follow the prem3_V pattern to prove the exact equality of s_var *)
      have s_var_eq: "s_var s' = s_var s"
        using s'_is_update unfolding Sys_D3_success_update_def Let_def
        by (simp add: s_var_def) 

      (* --------------------------------------------------------------------- *)
      (* Goal 1: dequeue side (PendingDeq implies a D-phase PC) *)
      (* --------------------------------------------------------------------- *)
      show "\<And>p'. HasPendingDeq s' p' \<Longrightarrow> program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof -
        fix p'
        assume pending_prime: "HasPendingDeq s' p'"
        
        (* 💥 Use Let_def together with his_seq_eq to discharge the blocked subgoal *)
        have pend_deq_eq: "HasPendingDeq s' p' = HasPendingDeq s p'"
          unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def 
          using his_seq_eq s_var_eq by simp
          
        have pending_s: "HasPendingDeq s p'"
          using pending_prime pend_deq_eq by simp

        show "program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
        proof (cases "p' = p")
          case True 
          (* pc_eq: if x = p then ''D4'' else ... *)
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
      (* Goal 2: enqueue side (PendingEnq implies an E-phase PC) *)
      (* --------------------------------------------------------------------- *)
      show "\<And>p'. HasPendingEnq s' p' (v_var s' p') \<Longrightarrow> program_counter s' p' \<in> {''E1'', ''E2'', ''E3''}"
      proof -
        fix p'
        assume pending_enq_prime: "HasPendingEnq s' p' (v_var s' p')"
        
        have s_var_eq: "s_var s' = s_var s"
          using s'_is_update unfolding Sys_D3_success_update_def Let_def
          by (simp add: s_var_def) 
        
        (* Extract the equality of v_var from other_vars_eq *)
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
    (* hI20: freshness of enqueue values (successful-dequeue branch - using only shared branch facts - ) *)
    (* ========================================================================= *)
    have "hI28_Fresh_Enq_Immunity s'"
    proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI)
      fix p_enq q_deq a sn
      
      (* Key revision: assume the full conjunctive premise in one shot \<and> , E3 *)
      assume prems: "program_counter s' p_enq \<in> {''E1'', ''E2''} \<and> 
                     v_var s' p_enq = a \<and> 
                     a \<noteq> BOT"
      
      (* 💡 Then split it into the three local facts needed later *)
      hence pc_e_prime: "program_counter s' p_enq \<in> {''E1'', ''E2''}"
        and v_eq_prime: "v_var s' p_enq = a"
        and a_not_bot: "a \<noteq> BOT" by auto

      have hI20_s: "hI28_Fresh_Enq_Immunity s" using INV unfolding system_invariant_def by blast

      (* prove the exact equality of s_var on the spot *)
      have s_var_eq: "s_var s' = s_var s"
        using s'_is_update unfolding Sys_D3_success_update_def Let_def 
        by (auto simp: bridge_defs s_var_def fun_eq_iff)

      show "\<not> DeqRetInHis s' q_deq a sn"
      proof (rule notI)
        assume his_prime: "DeqRetInHis s' q_deq a sn"

        (* Use his_seq_eq and the freshly proved s_var_eq to transport the history facts *)
        have his_eq: "DeqRetInHis s' q_deq a sn = DeqRetInHis s q_deq a sn"
          unfolding DeqRetInHis_def using his_seq_eq s_var_eq by simp
          
        have his_s: "DeqRetInHis s q_deq a sn"
          using his_prime his_eq by simp

        show False
        proof (cases "p_enq = p", goal_cases)
          case 1 
          (* Subcase 1: assume p_enq = p *)
          (* Use pc_eq to derive the new control state of p *)
          have "program_counter s' p = ''D4''"
            using pc_eq by auto
          with pc_e_prime 1 show False by auto
        next
          case 2 
          (* Subcase 2: assume p_enq \<noteq> p *)
          have old_pc: "program_counter s p_enq \<in> {''E1'', ''E2''}"
            using pc_e_prime 2 pc_eq by auto
            
          (* Extract the invariance of v_var from other_vars_eq *)
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
      (* 5. Proof of the linearization invariants *)
      (* ----------------------------------------------------------------- *)
      (* Prepare the basic facts about modify_lin *)
      have di_base: "data_independent base_lin"
        unfolding base_lin_def
        using di_lin_s modify_preserves_data_independent
        using current_lin_def by presburger

    (* ========================================================================= *)
    (* A. show data independence of the new linearization (using the freshness argument) *)
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
      (* B. prove lI2_Op_Cardinality (uniqueness/cardinality of the linearization) *)
      (* Use multiset preservation together with the established SetA/SetB transfer facts *)
      (* ================================================================= *)
      have "lI2_Op_Cardinality s'"
      proof -
        (* s_var s p *)
        let ?sn_deq = "s_var s p"
        let ?deq_act = "mk_op deq q_val p ?sn_deq"

        (* 1. Prepare the multiset relation using the stronger bridge facts *)
        have mset_eq: "mset (lin_seq s') = mset (lin_seq s) + {# ?deq_act #}"
        proof -
          (* Reuse the concrete bridge facts already used for lI1_Op_Sets_Equivalence *)
          have bridge: 
            "u_lin_seq (snd s) = current_lin" 
            "u_his_seq (snd s) = current_his"
            "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
            unfolding lin_seq_def his_seq_def current_lin_def current_his_def q_val_def jp_def 
            by (simp_all add: bridge_defs)
            
          (* prove multiset preservation for base_lin *)
          have "mset base_lin = mset (lin_seq s)"
            unfolding base_lin_def current_lin_def current_his_def
            using modify_preserves_mset q_not_bot by presburger
            
          (* combine the result with the append equation *)
          moreover have "lin_seq s' = base_lin @ [?deq_act]"
            using s'_is_update q_not_bot
            unfolding lin_seq_def Sys_D3_success_update_def base_lin_def Let_def s_var_def
            by (simp add: bridge bridge_defs)
            
          ultimately show ?thesis by simp
        qed

        (* 2. Apply the stepping lemma for lI2_Op_Cardinality directly *)
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
      (* C. prove lI3_HB_Ret_Lin_Sync (happens-before consistency) *)
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
      (* prove lI4_FIFO_Semantics s' (FIFO preservation), now packaged as an auxiliary lemma *)
      (* ----------------------------------------------------------------- *)
      have "lI4_FIFO_Semantics s'"
      proof -
        (* s_var s p *)
        let ?sn_deq = "s_var s p"

        (* 1. define the local base sequence *)
        define base where "base = (if should_modify (lin_seq s) (his_seq s) q_val 
                                   then modify_lin (lin_seq s) (his_seq s) q_val 
                                   else lin_seq s)"
        
        (* 2. prove the required equality facts with ?sn_deq instantiated *)
        have lin_eq: "lin_seq s' = base @ [mk_op deq q_val p ?sn_deq]"
          using D3_unfolded(2) q_not_bot base_def lin_s'_eq
          unfolding base_lin_def current_lin_def current_his_def s_var_def
          by auto

        (* 3. explicitly align the variables *)
        show ?thesis
        proof (rule lI4_FIFO_Semantics_deq_step_preservation[where s=s and q_val=q_val and s'=s' and p=p])
          (* Feed the premises manually so that Isabelle reports any mismatch explicitly *)
          show "system_invariant s" using INV .
          show "q_val \<in> SetB s" using q_in_SetB .
          show "q_val \<noteq> BOT" using q_not_bot . 
          
          show "base = (if should_modify (lin_seq s) (his_seq s) q_val then modify_lin (lin_seq s) (his_seq s) q_val else lin_seq s)"
            using base_def .
            
          (* The target equality must also be instantiated with ?sn_deq *)
          show "lin_seq s' = base @ [mk_op deq q_val p ?sn_deq]"
            using lin_eq .
        qed
      qed

      (* ----------------------------------------------------------------- *)
      (* prove lI5_SA_Prefix s' (preservation of the SetA prefix) *)
      (* ----------------------------------------------------------------- *)
      have "lI5_SA_Prefix s'"
      proof -
        (* s_var s p *)
        let ?sn_deq = "s_var s p"

        (* 1. align the base-sequence abbreviation *)
        define base where "base = (if should_modify (lin_seq s) (his_seq s) q_val 
                                   then modify_lin (lin_seq s) (his_seq s) q_val 
                                   else lin_seq s)"
        
        (* 2. align the append equation *)
        have lin_eq: "lin_seq s' = base @ [mk_op deq q_val p ?sn_deq]"
          using D3_unfolded(2) q_not_bot base_def lin_s'_eq
          unfolding base_lin_def current_lin_def current_his_def s_var_def
          by auto

        (* 3. close the goal in one line *)
        show ?thesis
          by (rule lI5_SA_Prefix_deq_step_preservation[where s=s and base_lin=base, OF INV q_in_SetB q_not_bot base_def lin_eq])
      qed

      (* ----------------------------------------------------------------- *)
      (* lI6_D4_Deq_Linearized: any D4-state must already have a matching linearized dequeue action (q_val \<noteq> BOT successful-dequeue branch) *)
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

      (* ----------------------------------------------------------------- *)
      (* prove Simulate_PC s' *)
      (* ----------------------------------------------------------------- *)
      have "Simulate_PC s'"
      proof -
        (* 1. recover the PC-mapping relation from the old state *)
        have old_refine: "Simulate_PC s" 
          using `system_invariant s` unfolding system_invariant_def by simp

        (* 2. unfold the premise and conclusion in sync and let auto finish *)
        show ?thesis
          using s'_is_update old_refine
          unfolding Simulate_PC_def Sys_D3_success_update_def Let_def
          by auto
      qed

      (* ----------------------------------------------------------------- *)
      (* 6. assemble the final conclusion *)
      (* ----------------------------------------------------------------- *)
    show ?thesis 
      unfolding system_invariant_def
      using `Simulate_PC s'` `TypeOK s'` `sI1_Zero_Index_BOT s'`
      `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'` `hI3_L0_E_Phase_Bounds s'` 
      `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'` `sI12_D3_Scanned_Prefix s'` `hI4_X_var_Lin_Sync s'`
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