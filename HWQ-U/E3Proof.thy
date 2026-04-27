(* ========================================================== *)
(* Preservation of the system invariant for the E3 transition *)
(* ========================================================== *)
theory E3Proof
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    E3Lemmas
begin

lemma E3_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E3 p s s'"
  shows "system_invariant s'"
proof -
  (* ========================================================== *)
  (* 0. Bridge definitions and proof setup                     *)
  (* ========================================================== *)
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def 
                     x_var_def v_var_def s_var_def lin_seq_def his_seq_def

  (* ========== 1. Extract the pre-state invariant package ========== *)
  have TypeOK_s: "TypeOK s" and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s" and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" 
   and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s" and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s" 
   and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s" and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
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

  (* ========== 2. Analyze Sys_E3 and collect frame facts ========== *)
  have step_facts [simp]:
    "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
    "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
    "X_var s' = X_var s" "V_var s' = V_var s"
    "lin_seq s' = lin_seq s"
    "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    "program_counter s p = ''E3'' "
    "program_counter s' p = ''L0'' "
    "i_var s' p = BOT" "v_var s' p = BOT" 
    "s_var s' p = s_var s p + 1"
  proof -
    from STEP obtain us_mid where
      c_step: "C_E3 p (fst s) (fst s')"
      and u_step1: "U_E3 p (CState.v_var (fst s) p) (s_var s p) (snd s) us_mid"
      and u_step2: "U_E4 p us_mid (snd s')"
      unfolding Sys_E3_def
      by blast

    show "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
         "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
         "X_var s' = X_var s" "V_var s' = V_var s"
         "program_counter s p = ''E3'' " "program_counter s' p = ''L0'' "
         "i_var s' p = BOT" "v_var s' p = BOT"
    proof -
      from c_step show "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
           "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
           "X_var s' = X_var s" "V_var s' = V_var s"
           "program_counter s p = ''E3'' " "program_counter s' p = ''L0'' "
           "i_var s' p = BOT" "v_var s' p = BOT"
        unfolding C_E3_def bridge_defs
        by (auto simp: prod_eq_iff)
    qed

    show "s_var s' p = s_var s p + 1"
      using u_step1 u_step2
      unfolding U_E3_def U_E4_def bridge_defs s_var_def
      by (auto simp: prod_eq_iff)

    show "lin_seq s' = lin_seq s"
      using STEP
      unfolding Sys_E3_def C_E3_def U_E3_def U_E4_def bridge_defs
      by (auto simp: prod_eq_iff)

    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
      using STEP
      unfolding Sys_E3_def C_E3_def U_E3_def U_E4_def bridge_defs
      by (auto simp: prod_eq_iff)
  qed

  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> i_var s' q = i_var s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> v_var s' q = v_var s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  proof -
    fix q assume "q \<noteq> p"
    from STEP obtain us_mid where
      u_steps:
      "U_E3 p (CState.v_var (fst s) p) (s_var s p) (snd s) us_mid"
      "U_E4 p us_mid (snd s')"
      unfolding Sys_E3_def by blast
    thus "program_counter s' q = program_counter s q"
         "i_var s' q = i_var s q"
         "v_var s' q = v_var s q"
         "s_var s' q = s_var s q"
      using STEP \<open>q \<noteq> p\<close>
      unfolding Sys_E3_def C_E3_def U_E3_def U_E4_def bridge_defs
      by (auto simp: prod_eq_iff)
  qed

  have pc_eqs [simp]:
    "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'' \<or> q = p)"
    "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'' \<and> q \<noteq> p)"
  proof -
    fix q
    show "(program_counter s' q = ''L0'') = (program_counter s q = ''L0'' \<or> q = p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
    show "(program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
    show "(program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<and> q \<noteq> p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
    show "(program_counter s' q = ''E3'') = (program_counter s q = ''E3'' \<and> q \<noteq> p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
    show "(program_counter s' q = ''D1'') = (program_counter s q = ''D1'' \<and> q \<noteq> p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
    show "(program_counter s' q = ''D2'') = (program_counter s q = ''D2'' \<and> q \<noteq> p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
    show "(program_counter s' q = ''D3'') = (program_counter s q = ''D3'' \<and> q \<noteq> p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
    show "(program_counter s' q = ''D4'') = (program_counter s q = ''D4'' \<and> q \<noteq> p)"
      using step_facts other_facts(1)[of q] by (cases "q = p") auto
  qed

  (* ========== 3. Derived-set preservation under the E3 step ========== *)
  have typeb_eq: "\<And>x. TypeB s' x = TypeB s x"
  proof -
    fix x
    have "\<And>q. program_counter s q = ''E2'' \<Longrightarrow> q \<noteq> p"
      using step_facts by auto
    hence "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow>
           (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
      using pc_eqs step_facts other_facts by force
    thus "TypeB s' x = TypeB s x"
      unfolding TypeB_def using QHas_def by auto
  qed

  have typebt_eq: "\<And>x. TypeBT s' x = TypeBT s x"
  proof -
    fix x
    have idx_eq: "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def step_facts by simp
    have "(\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)) \<longleftrightarrow>
          (\<exists>q. program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT))"
      using pc_eqs step_facts other_facts idx_eq by auto
    thus "TypeBT s' x = TypeBT s x" unfolding TypeBT_def InQBack_def typeb_eq idx_eq step_facts by simp
  qed

  have typea_eq: "\<And>x. TypeA s' x = TypeA s x"
    unfolding TypeA_def QHas_def using step_facts by (simp add: InQBack_def)

  have typebo_eq: "\<And>x. TypeBO s' x = TypeBO s x"
    unfolding TypeBO_def QHas_def using pc_eqs step_facts typeb_eq typebt_eq by presburger

  have set_facts [simp]:
    "SetA s' = SetA s" "SetB s' = SetB s" "SetBT s' = SetBT s" "SetBO s' = SetBO s"
    "\<And>x. TypeB s' x = TypeB s x" "\<And>x. TypeBT s' x = TypeBT s x"
    "\<And>x. TypeA s' x = TypeA s x" "\<And>x. TypeBO s' x = TypeBO s x"
  proof -
    show "\<And>x. TypeA s' x = TypeA s x" by (rule typea_eq)
    show "\<And>x. TypeBO s' x = TypeBO s x" by (rule typebo_eq)
    show "\<And>x. TypeB s' x = TypeB s x" by (rule typeb_eq)
    show "\<And>x. TypeBT s' x = TypeBT s x" by (rule typebt_eq)
    show "SetA s' = SetA s" unfolding SetA_def using typea_eq by simp
    show "SetB s' = SetB s" unfolding SetB_def using typeb_eq by simp
    show "SetBT s' = SetBT s" unfolding SetBT_def using typebt_eq by simp
    show "SetBO s' = SetBO s" unfolding SetBO_def using typebo_eq by simp
  qed

  (* ========== 4. Reassemble the state, history, and linearization invariants ========== *)
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
    using E3_preserves_state_invs_rest[OF INV STEP] .

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
    using E3_preserves_history_invs_rest[OF INV STEP] .

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
    using E3_preserves_linearization_invs_rest[OF INV STEP] .

  (* ========== 5. Assemble the final invariant package ========== *)
  show ?thesis
    using STATE_rest HISTORY_rest LIN_rest
    unfolding system_invariant_def by blast
qed

end
