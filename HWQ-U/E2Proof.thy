(* Main preservation proof for the E2 transition *)
theory E2Proof
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    E2Lemmas
begin

(* ========================================================== *)
(* Main preservation proof for the E2 transition *)
(* ========================================================== *)


lemma E2_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E2 p s s'"  
  shows "system_invariant s'"
proof -   
  (* ========================================================================= *)
  (* Step 0: bridge definitions and initial setup. *)
  (* ========================================================================= *)
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def 
                     x_var_def v_var_def s_var_def lin_seq_def his_seq_def

  (* Step 1: extract the full invariant package of the pre-state.*)
  have TypeOK_s: "TypeOK s" and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s" and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" 
   and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s" and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s" 
   and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s"  and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s" and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
   and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s" and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s" and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s" 
   and sI11_x_var_Scope_s: "sI11_x_var_Scope s" and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s" and hI4_X_var_Lin_Sync_s: "hI4_X_var_Lin_Sync s"
   and hI7_His_WF_s: "hI7_His_WF s" and hI8_Val_Unique_s: "hI8_Val_Unique s"
   and hI5_SSN_Unique_s: "hI5_SSN_Unique s" and hI6_SSN_Order_s: "hI6_SSN_Order s"
   and hI9_Deq_Ret_Unique_s: "hI9_Deq_Ret_Unique s" and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" and hI11_Enq_Ret_Existence_s: "hI11_Enq_Ret_Existence s" 
   and hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s" and hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s" and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" 
   and hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s" and hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s" and hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s" 
   and hI18_Idx_Order_No_Rev_HB_s: "hI18_Idx_Order_No_Rev_HB s" and hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s" and hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" 
   and hI21_Ret_Implies_Call_s: "hI21_Ret_Implies_Call s" and hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s" and hI23_Deq_Call_Ret_Balanced_s: "hI23_Deq_Call_Ret_Balanced s" 
   and hI24_HB_Implies_Idx_Order_s: "hI24_HB_Implies_Idx_Order s" and hI25_Enq_Call_Ret_Balanced_s: "hI25_Enq_Call_Ret_Balanced s" and hI26_DeqRet_D4_Mutex_s: "hI26_DeqRet_D4_Mutex s"
   and hI27_Pending_PC_Sync_s: "hI27_Pending_PC_Sync s" and hI28_Fresh_Enq_Immunity_s: "hI28_Fresh_Enq_Immunity s"
   and hI29_E2_Scanner_Immunity_s: "hI29_E2_Scanner_Immunity s" and hI30_Ticket_HB_Immunity_s: "hI30_Ticket_HB_Immunity s"
   and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" 
   and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" and lI5_SA_Prefix_s: "lI5_SA_Prefix s" and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" 
   and lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" and lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s" and lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s" 
   and lI10_D4_Enq_Deq_HB_s: "lI10_D4_Enq_Deq_HB s" and lI11_D4_Deq_Unique_s: "lI11_D4_Deq_Unique s" 
   and di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  (* Step 2: unfold Sys_E2 and extract the concrete updates.*)
  have step_facts [simp]:
    "program_counter s p = ''E2''"
    "program_counter s' = (program_counter s)(p := ''E3'')"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
    "X_var s' = X_var s" "V_var s' = V_var s"
    "i_var s' = i_var s" "v_var s' = v_var s" "s_var s' = s_var s"
    "lin_seq s' = lin_seq s"
    "his_seq s' = his_seq s"
  proof -
    show "program_counter s p = ''E2''" 
      using STEP unfolding Sys_E2_def C_E2_def program_counter_def by simp
      
    show "program_counter s' = (program_counter s)(p := ''E3'')" 
      using STEP unfolding Sys_E2_def C_E2_def program_counter_def Let_def
      by (auto simp: fun_eq_iff)
      
    show "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)" 
      using STEP unfolding Sys_E2_def C_E2_def Q_arr_def i_var_def v_var_def Let_def 
      by (auto simp: fun_eq_iff)
      
    show "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)" 
      using STEP unfolding Sys_E2_def C_E2_def Qback_arr_def i_var_def v_var_def Let_def 
      by (auto simp: fun_eq_iff)
      
    show "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s" 
         "X_var s' = X_var s" "V_var s' = V_var s"
         "i_var s' = i_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      using STEP 
      unfolding Sys_E2_def C_E2_def x_var_def j_var_def l_var_def 
                X_var_def V_var_def i_var_def v_var_def s_var_def Let_def 
      by auto
      
    show "lin_seq s' = lin_seq s" "his_seq s' = his_seq s" 
      using STEP unfolding Sys_E2_def lin_seq_def his_seq_def by auto
  qed

  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    using step_facts(2) by simp

  have pc_eqs [simp]:
    "\<And>q. (program_counter s' q = ''E2'') = 
         (program_counter s q = ''E2'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''E3'') = 
         (program_counter s q = ''E3'' \<or> q = p)"
    "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
    "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'')"
    "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'')"
    "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'')"
    "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
    "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    using step_facts(1) step_facts(2) by auto

(* ========================================================================= *)
  (* Step 3: Technical note for this proof step.*)
  (* ========================================================================= *)
  define ip where "ip = i_var s p"
  define val where "val = v_var s p"

  (* Step 1: Technical note for this proof step.*)
  have pending_s: "HasPendingEnq s p val" 
    using hI1_E_Phase_Pending_Enq_s step_facts(1) unfolding hI1_E_Phase_Pending_Enq_def val_def by blast
  have val_in_Val: "val \<in> Val"
    using pending_s hI20_Enq_Val_Valid_s unfolding HasPendingEnq_def EnqCallInHis_def hI20_Enq_Val_Valid_def val_def Let_def 
    by (metis in_set_conv_nth)
  have val_not_bot: "val \<noteq> BOT" 
    using val_in_Val unfolding Val_def BOT_def by simp

  (* Step 2: Technical note for this invariant-preservation argument.*)
  have not_in_qback_s: "\<not> InQBack s val"
  proof -
    have "\<not> (\<exists>k. Qback_arr s k = val \<and> k \<noteq> ip)"
      using hI14_Pending_Enq_Qback_Exclusivity_s pending_s step_facts(1) unfolding hI14_Pending_Enq_Qback_Exclusivity_def ip_def val_def by blast
    moreover have "Qback_arr s ip = BOT"
      using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def ip_def by blast
    ultimately show ?thesis 
      unfolding InQBack_def using val_not_bot by metis
  qed

  have qhas_s': "\<And>x. QHas s' x \<longleftrightarrow> QHas s x \<or> x = val"
  proof
    fix x assume "QHas s' x"
    then obtain k where "Q_arr s' k = x" unfolding QHas_def by auto
    thus "QHas s x \<or> x = val"
      using step_facts(3) unfolding ip_def val_def
      by (cases "k = i_var s p") (auto simp: fun_upd_def QHas_def)
  next
    fix x assume "QHas s x \<or> x = val"
    thus "QHas s' x"
    proof (elim disjE)
      assume "QHas s x"
      then obtain k where k_def: "Q_arr s k = x" unfolding QHas_def by auto
      show "QHas s' x"
      proof (cases "k = ip")
        case True
        (* Technical note for this proof step.*)
        hence "x = BOT" 
          using sI3_E2_Slot_Exclusive_s step_facts(1) k_def ip_def unfolding sI3_E2_Slot_Exclusive_def by auto
        have "ip \<noteq> 0" 
          using sI3_E2_Slot_Exclusive_s step_facts(1) ip_def unfolding sI3_E2_Slot_Exclusive_def Val_def by auto
        (* Technical note for this proof step.*)
        have "Q_arr s' 0 = BOT"
          using sI1_Zero_Index_BOT_s step_facts(3) `ip \<noteq> 0` ip_def val_def unfolding sI1_Zero_Index_BOT_def fun_upd_def by auto
        thus ?thesis unfolding QHas_def using `x = BOT` by blast
      next
        case False
        hence "Q_arr s' k = x" 
          using step_facts(3) k_def ip_def val_def by (simp add: fun_upd_def)
        thus ?thesis unfolding QHas_def by blast
      qed
    next
      assume "x = val"
      hence "Q_arr s' ip = x" 
        using step_facts(3) ip_def val_def by (simp add: fun_upd_def)
      thus "QHas s' x" unfolding QHas_def by blast
    qed
  qed

  have inqback_s': "\<And>x. InQBack s' x \<longleftrightarrow> InQBack s x \<or> x = val"
  proof
    fix x assume "InQBack s' x"
    then obtain k where "Qback_arr s' k = x" unfolding InQBack_def by auto
    thus "InQBack s x \<or> x = val"
      using step_facts(4) unfolding ip_def val_def
      by (cases "k = i_var s p") (auto simp: fun_upd_def InQBack_def)
  next
    fix x assume "InQBack s x \<or> x = val"
    thus "InQBack s' x"
    proof (elim disjE)
      assume "InQBack s x"
      then obtain k where k_def: "Qback_arr s k = x" unfolding InQBack_def by auto
      show "InQBack s' x"
      proof (cases "k = ip")
        case True
        (* Technical note for this proof step.*)
        hence "x = BOT" 
          using sI3_E2_Slot_Exclusive_s step_facts(1) k_def ip_def unfolding sI3_E2_Slot_Exclusive_def by auto
        have "ip \<noteq> 0" 
          using sI3_E2_Slot_Exclusive_s step_facts(1) ip_def unfolding sI3_E2_Slot_Exclusive_def Val_def by auto
        have "Qback_arr s' 0 = BOT"
          using sI1_Zero_Index_BOT_s step_facts(4) `ip \<noteq> 0` ip_def val_def unfolding sI1_Zero_Index_BOT_def fun_upd_def by auto
        thus ?thesis unfolding InQBack_def using `x = BOT` by blast
      next
        case False
        hence "Qback_arr s' k = x" 
          using step_facts(4) k_def ip_def val_def by (simp add: fun_upd_def)
        thus ?thesis unfolding InQBack_def by blast
      qed
    next
      assume "x = val"
      hence "Qback_arr s' ip = x" 
        using step_facts(4) ip_def val_def by (simp add: fun_upd_def)
      thus "InQBack s' x" unfolding InQBack_def by blast
    qed
  qed

  have typeb_eq: "\<And>x. TypeB s' x \<longleftrightarrow> TypeB s x"
  proof -
    fix x
    have pc_e2_s': "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow> 
                    (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x \<and> q \<noteq> p)"
      using pc_eqs step_facts other_facts by auto
    show "TypeB s' x \<longleftrightarrow> TypeB s x"
      unfolding TypeB_def pc_e2_s' val_def
      using qhas_s'[of x] step_facts(1)
      using val_def by blast 
  qed

  have typea_eq: "\<And>x. TypeA s' x \<longleftrightarrow> TypeA s x"
  proof -
    fix x
    show "TypeA s' x \<longleftrightarrow> TypeA s x"
      unfolding TypeA_def 
      using inqback_s'[of x] qhas_s'[of x] not_in_qback_s val_def by auto
  qed

  (* Step 5: Technical note for this invariant-preservation argument.*)
  have set_facts [simp]: 
    "SetA s' = SetA s" 
    "SetB s' = SetB s" 
  proof -
    show "SetA s' = SetA s" unfolding SetA_def using typea_eq by simp
    show "SetB s' = SetB s" unfolding SetB_def using typeb_eq by simp
  qed

  (* ========================================================================= *)
  (* Step 4: Technical note for this transition-specific proof step.*)
  (* ========================================================================= *)

  have STATE_rest:
    "TypeOK s' \<and>
     sI1_Zero_Index_BOT s' \<and>
     sI2_X_var_Upper_Bound s' \<and>
     sI3_E2_Slot_Exclusive s' \<and>
     sI4_E3_Qback_Written s' \<and>
     sI5_D2_Local_Bound s' \<and>
     sI6_D3_Scan_Pointers s' \<and>
     sI7_D4_Deq_Result s' \<and>
     hI3_L0_E_Phase_Bounds s' \<and>
     sI8_Q_Qback_Sync s' \<and>
     sI9_Qback_Discrepancy_E3 s' \<and>
     sI10_Qback_Unique_Vals s' \<and>
     hI2_SSN_Bounds s' \<and>
     sI11_x_var_Scope s' \<and>
     hI1_E_Phase_Pending_Enq s' \<and>
     sI12_D3_Scanned_Prefix s' \<and>
     hI4_X_var_Lin_Sync s'"
    using E2_preserves_state_invs_rest[OF INV STEP] .

  have HISTORY_rest:
    "hI7_His_WF s' \<and>
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
     hI30_Ticket_HB_Immunity s'"
    using E2_preserves_history_invs_rest[OF INV STEP] .

  have LIN_rest:
    "lI1_Op_Sets_Equivalence s' \<and>
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
     data_independent (lin_seq s') \<and>
     Simulate_PC s'"
    using E2_preserves_linearization_invs_rest[OF INV STEP] .

  (* ========================================================================= *)
  (* Step 5: Technical note for this proof step.*)
  (* ========================================================================= *)
  show ?thesis
    using STATE_rest HISTORY_rest LIN_rest
    unfolding system_invariant_def by blast
qed

end
