(* Preservation of the system invariant for the E1 transition *)
theory E1Proof
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    DeqLib
    EnqLib
    E1Lemmas
begin

lemma E1_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E1 p s s'"  
  shows "system_invariant s'"
proof -   
  (* ========================================================================= *)
  (* ========================================================================= *)
  (* 0. Bridge definitions and proof setup *)
  (* ========================================================================= *)
  (* ========================================================================= *)
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def 
                     x_var_def v_var_def s_var_def lin_seq_def his_seq_def

  (* Step 1: Extract all invariants of the pre-state (aligned with the current model) *)
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

  (* Step 2: Unfold Sys_E1 and extract the concrete update facts *)
  have step_facts [simp]:
    "program_counter s p = ''E1''"
    "program_counter s' = (program_counter s)(p := ''E2'')"
    "i_var s' = (i_var s)(p := X_var s)"
    "X_var s' = X_var s + 1"
    "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
    "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
    "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
    "his_seq s' = his_seq s"
  proof -
    show "program_counter s p = ''E1''" 
      using STEP unfolding Sys_E1_def C_E1_def program_counter_def by simp
      
    show "program_counter s' = (program_counter s)(p := ''E2'')" 
      using STEP unfolding Sys_E1_def C_E1_def program_counter_def Let_def by (auto simp: fun_eq_iff)
      
    show "i_var s' = (i_var s)(p := X_var s)" 
      using STEP unfolding Sys_E1_def C_E1_def i_var_def X_var_def Let_def by (auto simp: fun_eq_iff)
      
    show "X_var s' = X_var s + 1" 
      using STEP unfolding Sys_E1_def C_E1_def X_var_def Let_def by auto
      
    show "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
         "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s" 
         "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      using STEP 
      unfolding Sys_E1_def C_E1_def U_E2_def Q_arr_def Qback_arr_def x_var_def j_var_def 
                l_var_def V_var_def v_var_def s_var_def Let_def by auto
      
    show "his_seq s' = his_seq s" 
      using STEP unfolding Sys_E1_def his_seq_def
      using STEP Sys_E1_history_unchanged his_seq_def by auto 
  qed

  (* E1-specific append step: extract v and the newly appended SSN-tagged action *)
  define v where "v = v_var s p"
  define new_act where "new_act = mk_op enq v p (s_var s p)"
  have lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    using Sys_E1_lin_append[OF STEP] unfolding v_def new_act_def by simp

  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    using step_facts(2) by simp

  have pc_eqs [simp]:
    "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<or> q = p)"
    "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
    "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
    "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
    "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'')"
    "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'')"
    "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
    "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    using step_facts(1) step_facts(2) by auto

  (* ========================================================================= *)
  (* ========================================================================= *)
  (* 3. Core set reasoning: evolution of SetA / SetB                          *)
  (* ========================================================================= *)
  (* ========================================================================= *)

  (* Step 0: extract the initial program-counter state of the active process *)
  have pc_p_E1: "program_counter s p = ''E1''"
    using Sys_E1_pc_before[OF STEP] .

  (* Step 1: by hI1_E_Phase_Pending_Enq, a process in E1 must have a pending enqueue operation *)
  have pend_p: "HasPendingEnq s p v"
    using hI1_E_Phase_Pending_Enq_s pc_p_E1 unfolding hI1_E_Phase_Pending_Enq_def v_def by simp

  (* Step 2: turn the pending status into an explicit call record in the history *)
  have call_p: "EnqCallInHis s p v (s_var s p)"
    using HasPendingEnq_implies_EnqCallInHis[OF pend_p] .

  (* Step 3: show that v is a valid value, i.e. v \<in> Val *)
  have v_in_Val: "v \<in> Val"
  proof -
    from call_p obtain t where
      t_lt: "t < length (his_seq s)" and
      t_props: "act_val (his_seq s ! t) = v"
      unfolding EnqCallInHis_def Let_def
      by (metis in_set_conv_nth) 
    have "act_val (his_seq s ! t) \<in> Val"
      using hI20_Enq_Val_Valid_s t_lt unfolding hI20_Enq_Val_Valid_def
      using HasPendingEnq_imp_Val INV pend_p t_props by auto 
    then show ?thesis using t_props by simp
  qed

  (* Step 4: use hI14_Pending_Enq_Qback_Exclusivity to show that, since p is in E1 with a pending enqueue, its value cannot already appear in any Qback slot *)
  have not_InQBack_v: "\<not> InQBack s v"
    using hI14_Pending_Enq_Qback_Exclusivity_s pend_p pc_p_E1 unfolding hI14_Pending_Enq_Qback_Exclusivity_def InQBack_def v_def by blast

  (* Step 5: discharge the goalconclude that it is not in Qback and therefore cannot be of TypeBT *)
  have not_TypeBT_v: "\<not> TypeBT s v" 
    using not_InQBack_v unfolding TypeBT_def by simp

  (* Step 6: extract the validity facts for the global ticket variables from TypeOK *)
  have X_in_Val: "X_var s \<in> Val"
    using TypeOK_s unfolding TypeOK_def by simp
    
  have V_in_Val: "V_var s \<in> Val"
    using TypeOK_s unfolding TypeOK_def by simp

(* Record the fact that the history sequence is unchanged by the E1 step; this will be reused repeatedly below *)
  have his_eq: "his_seq s' = his_seq s"
    using step_facts by simp

  have setA_eq: "SetA s' = SetA s"
    using Sys_E1_SetA_eq[OF STEP] .

  have TypeBT_eq: "TypeBT s' a \<longleftrightarrow> TypeBT s a" for a
  proof (cases "a = v")
    case True
    have "\<not> TypeBT s a" using True not_TypeBT_v by simp
    moreover have "\<not> TypeBT s' a"
    proof
      assume bt': "TypeBT s' a"
      then have "InQBack s' a" unfolding TypeBT_def by simp
      then have "InQBack s a" using Sys_E1_InQBack_eq[OF STEP, of a] by simp
      with True not_InQBack_v show False by simp
    qed
    ultimately show ?thesis by simp
  next
    case False
    have a_ne_vvar: "a \<noteq> v_var s p" using False unfolding v_def by simp
    show ?thesis using Sys_E1_TypeBT_eq_other[OF STEP a_ne_vvar] by simp
  qed

  have SetBT_eq: "SetBT s' = SetBT s"
    unfolding SetBT_def using TypeBT_eq by blast

  have TypeBO_eq_other: "TypeBO s' a \<longleftrightarrow> TypeBO s a" if "a \<noteq> v" for a
  proof -
    have a_ne_vvar: "a \<noteq> v_var s p" using that unfolding v_def by simp
    show ?thesis using Sys_E1_TypeB_eq_other[OF STEP a_ne_vvar] TypeBT_eq[of a] unfolding TypeBO_def by blast
  qed

  have TypeB_s'_v: "TypeB s' v"
    using Sys_E1_TypeB_eq[OF STEP, of v] unfolding v_def by simp
  
  have TypeBO_s'_v: "TypeBO s' v"
    using TypeB_s'_v TypeBT_eq[of v] not_TypeBT_v unfolding TypeBO_def by simp

  have SetBO_new: "SetBO s' = insert v (SetBO s)"
  proof
    show "SetBO s' \<subseteq> insert v (SetBO s)"
    proof
      fix a assume a_in: "a \<in> SetBO s'"
      show "a \<in> insert v (SetBO s)"
      proof (cases "a = v")
        case True then show ?thesis by simp
      next
        case False
        then have "TypeBO s a" using a_in TypeBO_eq_other[OF False] unfolding SetBO_def by auto
        then show ?thesis using a_in False unfolding SetBO_def by auto
      qed
    qed
    show "insert v (SetBO s) \<subseteq> SetBO s'"
    proof
      fix a assume a_in: "a \<in> insert v (SetBO s)"
      show "a \<in> SetBO s'"
      proof (cases "a = v")
        case True then show ?thesis using v_in_Val TypeBO_s'_v unfolding SetBO_def by simp
      next
        case False
        then have "TypeBO s' a" using a_in TypeBO_eq_other[OF False] unfolding SetBO_def by auto
        then show ?thesis using a_in False unfolding SetBO_def by auto
      qed
    qed
  qed

  have setB_new: "SetB s' = insert v (SetB s)"
  proof
    show "SetB s' \<subseteq> insert v (SetB s)"
    proof
      fix a assume a_in: "a \<in> SetB s'"
      show "a \<in> insert v (SetB s)"
      proof (cases "a = v")
        case True then show ?thesis by simp
      next
        case False
        have a_ne_vvar: "a \<noteq> v_var s p" using False unfolding v_def by simp
        have a_val: "a \<in> Val" using a_in unfolding SetB_def by simp
        have a_type': "TypeB s' a" using a_in unfolding SetB_def by simp
        have a_type: "TypeB s a" using a_type' Sys_E1_TypeB_eq_other[OF STEP a_ne_vvar] by simp
        then show ?thesis using a_val a_type unfolding SetB_def by simp
      qed
    qed
    show "insert v (SetB s) \<subseteq> SetB s'"
    proof
      fix a assume a_in: "a \<in> insert v (SetB s)"
      show "a \<in> SetB s'"
      proof (cases "a = v")
        case True then show ?thesis using v_in_Val TypeB_s'_v unfolding SetB_def by simp
      next
        case False
        have a_ne_vvar: "a \<noteq> v_var s p" using False unfolding v_def by simp
        have a_old: "a \<in> SetB s" using a_in False by simp
        have "TypeB s a" using a_old unfolding SetB_def by simp
        then have "TypeB s' a" using Sys_E1_TypeB_eq_other[OF STEP a_ne_vvar] by simp
        then show ?thesis using a_in False unfolding SetB_def by auto
      qed
    qed
  qed

  (* ========================================================================= *)
  (* Step 4: Preservation of concrete-state invariants *)
  (* ========================================================================= *)

  have "TypeOK s'" 
    using TypeOK_s step_facts pc_eqs 
    unfolding TypeOK_def Val_def BOT_def 
    by auto
    
  have "sI1_Zero_Index_BOT s'" using sI1_Zero_Index_BOT_s step_facts unfolding sI1_Zero_Index_BOT_def by auto
  have "sI2_X_var_Upper_Bound s'" using sI2_X_var_Upper_Bound_s step_facts unfolding sI2_X_var_Upper_Bound_def
    using TypeOK_def \<open>TypeOK s'\<close> add_leD1 by presburger 
  
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_e2_slot_exclusive below, without changing the proof logic. *)
  have "sI3_E2_Slot_Exclusive s'"
    using E1_e2_slot_exclusive[
      OF sI3_E2_Slot_Exclusive_s sI4_E3_Qback_Written_s sI2_X_var_Upper_Bound_s X_in_Val step_facts pc_eqs
    ] .

  have "sI4_E3_Qback_Written s'"
  proof (unfold sI4_E3_Qback_Written_def, intro allI impI)
    fix q assume qE3': "program_counter s' q = ''E3''"
    have q_ne_p: "q \<noteq> p"
    proof
      assume qp: "q = p"
      have "program_counter s' p = ''E2''" using Sys_E1_pc_eq[OF STEP, of p] by simp
      with qE3' qp show False by simp
    qed
    have qE3: "program_counter s q = ''E3''" using qE3' q_ne_p Sys_E1_pc_eq[OF STEP, of q] by simp
    from sI4_E3_Qback_Written_s have sI4_E3_Qback_Written_q: "program_counter s q = ''E3'' \<longrightarrow> (i_var s q \<in> Val \<and> i_var s q < X_var s \<and> (Q_arr s (i_var s q) = v_var s q \<or> Q_arr s (i_var s q) = BOT) \<and> Qback_arr s (i_var s q) = v_var s q \<and> (\<forall>q'. q' \<noteq> q \<and> program_counter s q' \<in> {''E2'', ''E3''} \<longrightarrow> i_var s q \<noteq> i_var s q'))" unfolding sI4_E3_Qback_Written_def by simp
    from sI4_E3_Qback_Written_q qE3 have sI4_E3_Qback_Written_q_all: "i_var s q \<in> Val \<and> i_var s q < X_var s \<and> (Q_arr s (i_var s q) = v_var s q \<or> Q_arr s (i_var s q) = BOT) \<and> Qback_arr s (i_var s q) = v_var s q \<and> (\<forall>q'. q' \<noteq> q \<and> program_counter s q' \<in> {''E2'', ''E3''} \<longrightarrow> i_var s q \<noteq> i_var s q')" by simp
    have all_distinct: "\<forall>r. r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' q \<noteq> i_var s' r"
    proof (intro allI impI)
      fix r assume rq: "r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''}"
      show "i_var s' q \<noteq> i_var s' r"
      proof (cases "r = p")
        case True then show ?thesis using sI4_E3_Qback_Written_q_all q_ne_p True Sys_E1_i_eq[OF STEP, of q] Sys_E1_i_eq[OF STEP, of r] by simp
      next
        case False_r: False
        have r_old: "program_counter s r \<in> {''E2'', ''E3''}" using rq False_r Sys_E1_pc_eq[OF STEP, of r] by auto
        then show ?thesis using sI4_E3_Qback_Written_q_all rq(1) r_old q_ne_p False_r Sys_E1_i_eq[OF STEP, of q] Sys_E1_i_eq[OF STEP, of r] by simp
      qed
    qed
    show "i_var s' q \<in> Val \<and> i_var s' q < X_var s' \<and> (Q_arr s' (i_var s' q) = v_var s' q \<or> Q_arr s' (i_var s' q) = BOT) \<and> Qback_arr s' (i_var s' q) = v_var s' q \<and> (\<forall>r. r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' q \<noteq> i_var s' r)"
      using sI4_E3_Qback_Written_q_all q_ne_p Sys_E1_i_eq[OF STEP, of q] Sys_E1_X_eq[OF STEP] Sys_E1_qarr_eq[OF STEP, of "i_var s q"] Sys_E1_v_eq[OF STEP, of q] Sys_E1_qback_eq[OF STEP, of "i_var s q"] all_distinct by auto
  qed

  have "sI5_D2_Local_Bound s'" using sI5_D2_Local_Bound_s step_facts pc_eqs unfolding sI5_D2_Local_Bound_def by auto
  have "sI6_D3_Scan_Pointers s'" using sI6_D3_Scan_Pointers_s step_facts pc_eqs unfolding sI6_D3_Scan_Pointers_def by auto
  have "sI7_D4_Deq_Result s'" using sI7_D4_Deq_Result_s step_facts pc_eqs unfolding sI7_D4_Deq_Result_def by auto

  have "hI3_L0_E_Phase_Bounds s'"
    using hI3_L0_E_Phase_Bounds_E1_step[OF INV STEP] .

  have "sI8_Q_Qback_Sync s'" using sI8_Q_Qback_Sync_s step_facts unfolding sI8_Q_Qback_Sync_def by auto
  have "sI9_Qback_Discrepancy_E3 s'" using sI9_Qback_Discrepancy_E3_s step_facts pc_eqs unfolding sI9_Qback_Discrepancy_E3_def by auto
  have "sI10_Qback_Unique_Vals s'" using sI10_Qback_Unique_Vals_s step_facts unfolding sI10_Qback_Unique_Vals_def by auto
  have "hI2_SSN_Bounds s'" using hI2_SSN_Bounds_s step_facts pc_eqs unfolding hI2_SSN_Bounds_def by auto
  have "sI11_x_var_Scope s'" using sI11_x_var_Scope_s step_facts pc_eqs unfolding sI11_x_var_Scope_def by auto

  have "hI1_E_Phase_Pending_Enq s'"
  proof (unfold hI1_E_Phase_Pending_Enq_def, intro allI impI)
    fix q assume qpc': "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
    
    (* Step 1: derive that q also lies in {E1, E2, E3} in the pre-state *)
    have qpc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using qpc' pc_eqs by auto
      
    (* Step 2: extract the pending property of q from hI1_E_Phase_Pending_Enq in the pre-state *)
    have pend_old: "HasPendingEnq s q (v_var s q)"
      using hI1_E_Phase_Pending_Enq_s qpc unfolding hI1_E_Phase_Pending_Enq_def by blast
      
    (* Step 3: unfold Pending and transport the fact using the equalities of v_var, s_var, and his_seq *)
    show "HasPendingEnq s' q (v_var s' q)"
      using pend_old step_facts
      unfolding HasPendingEnq_def EnqCallInHis_def Let_def
      by auto
  qed

  have "sI12_D3_Scanned_Prefix s'"
  proof (unfold sI12_D3_Scanned_Prefix_def, intro allI impI)
    fix pa k
    assume pc_pa': "program_counter s' pa = ''D3''"
    assume k_lt': "k < j_var s' pa"

    (* Step 1: derive that pa is also in D3 in the pre-state and that j_var is unchanged *)
    have pc_pa: "program_counter s pa = ''D3''"
      using pc_pa' pc_eqs by auto
    have k_lt: "k < j_var s pa"
      using k_lt' step_facts by simp

    (* Step 2: use sI12_D3_Scanned_Prefix in the pre-state *)
    have old_sI12_D3_Scanned_Prefix: "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
      using sI12_D3_Scanned_Prefix_s pc_pa k_lt unfolding sI12_D3_Scanned_Prefix_def by blast

    (* Step 3: show inline that TypeB is monotone: any old TypeB fact is still valid in the new state *)
    have typeb_mono: "\<And>x. TypeB s x \<Longrightarrow> TypeB s' x"
      unfolding TypeB_def QHas_def
      using step_facts pc_eqs by auto

    (* Step 4: close the goal using the unchanged concrete arrays *)
    show "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
      using old_sI12_D3_Scanned_Prefix typeb_mono step_facts by auto
  qed
  
  have "hI4_X_var_Lin_Sync s'"
  proof -
    (* Step 1: the concrete fact is that X_var increases by exactly 1 in the E1 step *)
    have step_X: "X_var s' = X_var s + 1"
      using step_facts by simp
      
    (* Step 2: the appended action new_act is explicitly an enqueue action *)
    have act_is_enq: "op_name new_act = enq"
      unfolding new_act_def mk_op_def op_name_def by simp
      
    (* Step 3: unfold the counting definition so that simplification sees the matching +1 on both sides *)
    show ?thesis
      using hI4_X_var_Lin_Sync_s step_X lin_eq act_is_enq
      unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def new_act_def
      by (auto simp: op_name_def mk_op_def)
  qed

  (* ========================================================================= *)
  (* Step 5: Preservation of history and history-to-state consistency invariants *)
  (* ========================================================================= *)
  
  have "hI7_His_WF s'" using hI7_His_WF_s step_facts unfolding hI7_His_WF_def by simp
  have "hI8_Val_Unique s'" using hI8_Val_Unique_s step_facts unfolding hI8_Val_Unique_def by simp
  have "hI5_SSN_Unique s'" using hI5_SSN_Unique_s step_facts unfolding hI5_SSN_Unique_def by simp
  have "hI6_SSN_Order s'" using hI6_SSN_Order_s step_facts unfolding hI6_SSN_Order_def by simp
  have "hI9_Deq_Ret_Unique s'" using hI9_Deq_Ret_Unique_s step_facts unfolding hI9_Deq_Ret_Unique_def by simp
  
  have "hI10_Enq_Call_Existence s'"
  proof (unfold hI10_Enq_Call_Existence_def, intro conjI allI impI, goal_cases)
    case (1 q a)
    (* Step 1: use pc_eqs and step_facts to map the program counter and v_var back to the pre-state *)
    have qpc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" 
      using 1 pc_eqs pc_p_E1 by auto
    have qv: "v_var s q = a" 
      using 1 step_facts by simp
      
    (* Step 2: obtain the call record from the corresponding pre-state invariant *)
    have call_old: "EnqCallInHis s q a (s_var s q)" 
      using hI10_Enq_Call_Existence_s qpc qv unfolding hI10_Enq_Call_Existence_def by blast
      
    (* Step 3: unfold the definitions and close the goal using the unchanged history sequence and sequence number. *)
    show ?case 
      using call_old step_facts 
      unfolding EnqCallInHis_def Let_def 
      by auto
  next
    case (2 a)
    (* Step 1: E1 does not modify Qback_arr *)
    have inq: "\<exists>k. Qback_arr s k = a" 
      using 2 step_facts by simp
      
    (* Step 2: extract the required witness process q and sequence number sn from the pre-state *)
    then obtain q sn where call_old: "EnqCallInHis s q a sn" 
      using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def by blast
      
    (* Step 3: transport the result to the new state, carrying sn along *)
    show ?case 
      using call_old step_facts 
      unfolding EnqCallInHis_def Let_def
      by metis 
  qed

  have "hI11_Enq_Ret_Existence s'"
  proof (unfold hI11_Enq_Ret_Existence_def, intro allI impI, goal_cases)
    case (1 q a sn)
    
    (* Step 1: isolate the precondition and extract the full disjunction involving sn *)
    from 1 have pre1: "program_counter s' q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn" by blast
    from 1 have pre2: "\<exists>k. Qback_arr s' k = a" by blast
    from 1 have pre3: "EnqCallInHis s' q a sn" by blast

    (* Step 2: derive cond_old cleanly, again using a case split on the relevant goals *)
    have cond_old: "program_counter s q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s q \<noteq> a \<or> s_var s q \<noteq> sn"
    proof (cases "q = p", goal_cases)
      case 1 (* q = p *)
      (* If q = p, then its program counter in the new state is E2, hence it belongs to {E1, E2, E3} *)
      have "program_counter s' q = ''E2''" using 1 step_facts by simp
      then have "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}" by simp
      (* Hence the first disjunct in pre1 is false, so one of the value- or sequence-number conditions must hold *)
      with pre1 have "v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn" by blast
      then show ?case using step_facts 1 by simp
    next
      case 2 (* q \<noteq> p *)
      (* If q \<noteq> p, then its program counter, v_var, and s_var are unchanged and the property transports directly *)
      have "program_counter s' q = program_counter s q" using 2 step_facts by simp
      moreover have "v_var s' q = v_var s q" using 2 step_facts by simp
      moreover have "s_var s' q = s_var s q" using 2 step_facts by simp
      ultimately show ?case using pre1 by simp
    qed
      
    (* Step 3: separate and transport the remaining two concrete facts *)
    have inq_old: "\<exists>k. Qback_arr s k = a" 
      using pre2 step_facts by simp
      
    have call_old: "EnqCallInHis s q a sn" 
      using pre3 step_facts unfolding EnqCallInHis_def Let_def by auto
      
    (* Step 4: invoke the pre-state invariant to obtain the return record *)
    have ret_old: "EnqRetInHis s q a sn" 
      using hI11_Enq_Ret_Existence_s cond_old inq_old call_old unfolding hI11_Enq_Ret_Existence_def by blast
      
    (* Step 5: close the current case *)
    show ?case 
      using ret_old step_facts unfolding EnqRetInHis_def Let_def by auto
  qed

  have "hI12_D_Phase_Pending_Deq s'"
  proof (unfold hI12_D_Phase_Pending_Deq_def, intro allI impI)
    fix pa
    assume pc_pa': "program_counter s' pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    
    (* Step 1: derive that pa also lies in {D1, D2, D3, D4} in the pre-state *)
    have pc_pa: "program_counter s pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using pc_pa' pc_eqs by auto
      
    (* Step 2: extract the PendingDeq property from hI12_D_Phase_Pending_Deq in the pre-state *)
    have pend_old: "HasPendingDeq s pa"
      using hI12_D_Phase_Pending_Deq_s pc_pa unfolding hI12_D_Phase_Pending_Deq_def by auto
      
    (* Step 3: unfold HasPendingDeq and transport the property using the unchanged history and sequence number *)
    show "HasPendingDeq s' pa"
      using pend_old step_facts
      unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
      by auto
  qed
  
  have "hI13_Qback_Deq_Sync s'"
  proof (unfold hI13_Qback_Deq_Sync_def, intro allI impI)
    fix a
    assume a_ne: "a \<noteq> BOT"
    assume ex_gap': "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a"
    have ex_gap: "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a"
    proof -
      from ex_gap' obtain k where "Q_arr s' k = BOT" and "Qback_arr s' k = a" by blast
      then show ?thesis using Sys_E1_qarr_eq[OF STEP, of k] Sys_E1_qback_eq[OF STEP, of k]
        by auto
    qed
    from hI13_Qback_Deq_Sync_s a_ne ex_gap have old_wit: "\<exists>pa. (program_counter s pa = ''D4'' \<and> x_var s pa = a) \<or> (\<exists>sn. DeqRetInHis s pa a sn)" unfolding hI13_Qback_Deq_Sync_def by blast
    then obtain pa where pa_old: "(program_counter s pa = ''D4'' \<and> x_var s pa = a) \<or> (\<exists>sn. DeqRetInHis s pa a sn)" by blast
    have pa_new: "(program_counter s' pa = ''D4'' \<and> x_var s' pa = a) \<or> (\<exists>sn. DeqRetInHis s' pa a sn)"
    proof -
      from pa_old show ?thesis
      proof
        assume pa_d4: "program_counter s pa = ''D4'' \<and> x_var s pa = a"
        then have pa_D4: "program_counter s pa = ''D4''" and pa_x: "x_var s pa = a" by auto
        have pa_ne_p: "pa \<noteq> p"
        proof
          assume "pa = p" then have "program_counter s p = ''D4''" using pa_D4 by simp
          with pc_p_E1 show False by simp
        qed
        have "program_counter s' pa = ''D4''" using pa_D4 pa_ne_p Sys_E1_pc_eq[OF STEP, of pa] by simp
        moreover have "x_var s' pa = a" using pa_x Sys_E1_x_eq[OF STEP, of pa] by simp
        ultimately show ?thesis by blast
      next
        assume "\<exists>sn. DeqRetInHis s pa a sn"
        then show ?thesis using DeqRetInHis_his_eq[OF his_eq] by blast
      qed
    qed
    show "\<exists>p. (program_counter s' p = ''D4'' \<and> x_var s' p = a) \<or> (\<exists>sn. DeqRetInHis s' p a sn)" using pa_new by blast
  qed

  have "hI14_Pending_Enq_Qback_Exclusivity s'"
  proof (unfold hI14_Pending_Enq_Qback_Exclusivity_def, intro conjI allI impI)
    fix q a
    assume pre': "HasPendingEnq s' q a \<and> program_counter s' q \<in> {''E2'', ''E3''}"
    show "\<not> (\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q)"
    proof (cases "q = p")
      case True
      have pend_old: "HasPendingEnq s p a" using pre' True HasPendingEnq_his_eq[OF his_eq] step_facts by simp
      have no_qback_old: "\<not> (\<exists>k. Qback_arr s k = a)" using hI14_Pending_Enq_Qback_Exclusivity_s pend_old pc_p_E1 unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
      show ?thesis
      proof
        assume "\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q"
        then obtain k where "Qback_arr s' k = a" by blast
        then have "Qback_arr s k = a" using Sys_E1_qback_eq[OF STEP, of k] by simp
        then show False using no_qback_old by blast
      qed
    next
      case False
      have pend_old: "HasPendingEnq s q a" using pre' HasPendingEnq_his_eq[OF his_eq] step_facts by simp
      have qpc_old: "program_counter s q \<in> {''E2'', ''E3''}" using pre' False Sys_E1_pc_eq[OF STEP, of q] by auto
      have no_old: "\<not> (\<exists>k. Qback_arr s k = a \<and> k \<noteq> i_var s q)" using hI14_Pending_Enq_Qback_Exclusivity_s pend_old qpc_old unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
      show ?thesis
      proof
        assume "\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q"
        then obtain k where "Qback_arr s' k = a" and "k \<noteq> i_var s' q" by blast
        have "Qback_arr s k = a" using `Qback_arr s' k = a` Sys_E1_qback_eq[OF STEP, of k] by simp
        have "k \<noteq> i_var s q" using `k \<noteq> i_var s' q` False Sys_E1_i_eq[OF STEP, of q] by simp
        then show False using `Qback_arr s k = a` no_old by blast
      qed
    qed
  next
    fix q a
    assume pre': "HasPendingEnq s' q a \<and> program_counter s' q = ''E1''"
    have pend_old: "HasPendingEnq s q a" using pre' HasPendingEnq_his_eq[OF his_eq] step_facts by simp
    have q_ne_p: "q \<noteq> p"
    proof
      assume "q = p" then have "program_counter s' p = ''E1''" using pre' by simp
      moreover have "program_counter s' p = ''E2''" using Sys_E1_pc_eq[OF STEP, of p] by simp
      ultimately show False by simp
    qed
    have qpc_old: "program_counter s q = ''E1''" using pre' q_ne_p Sys_E1_pc_eq[OF STEP, of q] by simp
    have no_old: "\<not> (\<exists>k. Qback_arr s k = a)" using hI14_Pending_Enq_Qback_Exclusivity_s pend_old qpc_old unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
    show "\<not> (\<exists>k. Qback_arr s' k = a)"
    proof
      assume "\<exists>k. Qback_arr s' k = a"
      then obtain k where "Qback_arr s' k = a" by blast
      have "Qback_arr s k = a" using `Qback_arr s' k = a` Sys_E1_qback_eq[OF STEP, of k] by simp
      then show False using no_old by blast
    qed
  qed

  have "hI15_Deq_Result_Exclusivity s'"
  proof -
    (* Step 1: show that the low-level dequeue predicates are unchanged by the E1 step *)
    have eq_ret: "\<And>q a sn. DeqRetInHis s' q a sn = DeqRetInHis s q a sn"
      unfolding DeqRetInHis_def Let_def using step_facts by simp
      
    have eq_pend: "\<And>q. HasPendingDeq s' q = HasPendingDeq s q"
      unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def 
      using step_facts by simp
      
    have eq_pc_D4: "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
      using pc_eqs by simp

    show ?thesis
      using hI15_Deq_Result_Exclusivity_s
      unfolding hI15_Deq_Result_Exclusivity_def
      using eq_pc_D4 eq_pend eq_ret step_facts(5,7) by presburger

  qed
  
have "hI16_BO_BT_No_HB s'"
  proof (unfold hI16_BO_BT_No_HB_def, intro allI impI, goal_cases)
    case (1 a b)
    
    (* Step 1: extract the relevant set-membership facts from the goal *)
    have a_in': "a \<in> SetBO s'" using 1 by blast
    have b_in': "b \<in> SetBT s'" using 1 by blast
    
    (* Step 2: transport the happens-before relation using the unchanged history sequence *)
    have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq by auto
      
    (* Step 3: SetBT is preserved, so old members can be mapped directly *)
    have b_old: "b \<in> SetBT s" 
      using b_in' SetBT_eq by simp
      
    (* Step 4: split on whether a is the newly introduced value v *)
    show ?case
    proof (cases "a = v", goal_cases)
      case 1 (* a = v *)
      (* v is the fresh value allocated for the current process, so it cannot already have an enqueue return record. This is exactly the previously proved fact no_enq_ret_v: "\<forall>q sn. \<not> EnqRetInHis s q v sn" *)
      have no_ret_v: "\<not> (\<exists>k<length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v \<and> act_cr (his_seq s ! k) = ret)"
        using EnqRetInHis_def hI7_His_WF_s hI8_Val_Unique_s
          no_enq_ret_for_pending_value nth_mem pend_p by blast
        
      (* Without a return record, the corresponding happens-before relation is impossible *)
      have "\<not> HB_EnqRetCall s v b"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def mk_op_def op_name_def op_val_def
        using no_ret_v by auto
        
      then show ?case using 1 hb_eq by simp
    next
      case 2 (* a \<noteq> v *)
      (* a is an old element, so we use the previously proved equality SetBO_new: SetBO s' = insert v (SetBO s) *)
      have a_old: "a \<in> SetBO s" 
        using a_in' 2 SetBO_new by auto
        
      (* This matches the pre-state premises exactly, so we invoke hI16_BO_BT_No_HB_s *)
      have "\<not> HB_EnqRetCall s a b" 
        using hI16_BO_BT_No_HB_s a_old b_old unfolding hI16_BO_BT_No_HB_def by blast
        
      then show ?case using hb_eq by simp
    qed
  qed
  
  have "hI17_BT_BT_No_HB s'"
  proof (unfold hI17_BT_BT_No_HB_def, intro allI impI, goal_cases)
    case (1 a b)
    
    (* Step 1: extract the set-membership facts and map them back to the pre-state using preservation *)
    have a_old: "a \<in> SetBT s" using 1 SetBT_eq by simp
    have b_old: "b \<in> SetBT s" using 1 SetBT_eq by simp
    
    (* Step 2: transport the happens-before relation using the unchanged history sequence *)
    have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq by auto
      
    (* Step 3: since both elements are old, we can invoke hI17_BT_BT_No_HB_s from the pre-state directly *)
    have "\<not> HB_EnqRetCall s a b" 
      using hI17_BT_BT_No_HB_s a_old b_old unfolding hI17_BT_BT_No_HB_def by blast
      
    (* Step 4: close the goal *)
    then show ?case using hb_eq by simp
  qed
  
  have "hI18_Idx_Order_No_Rev_HB s'"
  proof (unfold hI18_Idx_Order_No_Rev_HB_def, intro allI impI, goal_cases)
    case (1 a b)
    
    (* Step 1: extract the preconditions in the new state *)
    have inqa': "InQBack s' a" using 1 by blast
    have inqb': "InQBack s' b" using 1 by blast
    have idx_lt': "Idx s' a < Idx s' b" using 1 by blast
    
    (* Step 2: E1 does not change Qback_arr, so membership and physical indices transport directly *)
    have inqa: "InQBack s a" 
      using inqa' step_facts unfolding InQBack_def by simp
      
    have inqb: "InQBack s b" 
      using inqb' step_facts unfolding InQBack_def by simp
      
    have idx_lt: "Idx s a < Idx s b" 
      using idx_lt' step_facts unfolding Idx_def AtIdx_def by simp
      
    (* Step 3: since his_seq is unchanged, the happens-before relation is equivalent in both states *)
    have hb_eq: "HB_EnqRetCall s' b a = HB_EnqRetCall s b a"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq by auto
      
    (* Step 4: the pre-state conditions are now available, so we invoke hI18_Idx_Order_No_Rev_HB_s *)
    have "\<not> HB_EnqRetCall s b a" 
      using hI18_Idx_Order_No_Rev_HB_s inqa inqb idx_lt unfolding hI18_Idx_Order_No_Rev_HB_def by blast
      
    (* Step 5: close the goal *)
    then show ?case using hb_eq by simp
  qed
  
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_scanner_catches_later_enq below, without changing the proof logic. *)
  have "hI19_Scanner_Catches_Later_Enq s'"
    using E1_scanner_catches_later_enq[
      OF hI19_Scanner_Catches_Later_Enq_s not_InQBack_v v_def step_facts pc_eqs his_eq
    ] .
  
  have "hI20_Enq_Val_Valid s'" using hI20_Enq_Val_Valid_s step_facts unfolding hI20_Enq_Val_Valid_def by simp

  have "hI21_Ret_Implies_Call s'"
  proof (unfold hI21_Ret_Implies_Call_def, intro allI impI, goal_cases)
    case (1 k)
    
    (* Step 1: the underlying history is unchanged *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by simp
    have k_len: "k < length (his_seq s)" using 1 his_eq by simp
    have k_ret: "act_cr (his_seq s ! k) = ret" using 1 his_eq by simp
    
    (* Step 2: invoke hI21_Ret_Implies_Call_s in the pre-state to obtain the corresponding call index tm *)
    from hI21_Ret_Implies_Call_s k_len k_ret obtain tm where tm_props:
      "tm < k"
      "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k)"
      "act_name (his_seq s ! tm) = act_name (his_seq s ! k)"
      "act_cr (his_seq s ! tm) = call"
      "(if act_name (his_seq s ! k) = enq then act_val (his_seq s ! tm) = act_val (his_seq s ! k) else act_val (his_seq s ! tm) = BOT)"
      unfolding hI21_Ret_Implies_Call_def by blast
      
    (* Step 3: split on the operation type of the current return record to resolve the nested conditional structure *)
    show ?case
    proof (cases "act_name (his_seq s ! k) = enq")
      case True
      (* In the enqueue case, unfold the corresponding condition *)
      have oper_enq: "act_name (his_seq s ! tm) = enq" using tm_props(3) True by simp
      have val_eq: "act_val (his_seq s ! tm) = act_val (his_seq s ! k)" using tm_props(5) True by simp
      
      show ?thesis 
        using tm_props True oper_enq val_eq his_eq 1 by auto
    next
      case False
      (* In the dequeue case, unfold the corresponding condition *)
      have val_bot: "act_val (his_seq s ! tm) = BOT" using tm_props(5) False by simp
      
      show ?thesis 
        using tm_props False val_bot his_eq 1 by auto
    qed
  qed

  have "hI22_Deq_Local_Pattern s'"
  proof (unfold hI22_Deq_Local_Pattern_def, intro allI impI, goal_cases)
    case (1 p a sn)
    
    (* Step 1: E1 only allocates a fresh ticket and does not touch dequeue-related arrays or history information *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by auto
    have q_eq: "Q_arr s' = Q_arr s" using step_facts by auto
    have qback_eq: "Qback_arr s' = Qback_arr s" using step_facts by auto
    have x_var_eq: "\<And>q. x_var s' q = x_var s q" using step_facts by auto
    
    (* Step 2: add the missing core equivalence showing that dequeue-return history is unchanged by E1 *)
    have deq_ret_eq: "DeqRetInHis s' p a sn \<longleftrightarrow> DeqRetInHis s p a sn"
      unfolding DeqRetInHis_def Let_def using his_eq by auto
      
    (* Step 3: extract the core premises of the goal and transport them back to the pre-state *)
    from 1 have cond_q': "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a \<and> (\<forall>q. x_var s' q \<noteq> a)" by blast
    from 1 have cond_ret': "DeqRetInHis s' p a sn" by blast
    
    have cond_q: "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a \<and> (\<forall>q. x_var s q \<noteq> a)"
      using cond_q' q_eq qback_eq x_var_eq by simp
    have cond_ret: "DeqRetInHis s p a sn"
      using cond_ret' deq_ret_eq by simp
      
    (* Step 4: invoke hI22_Deq_Local_Pattern_s in the pre-state to obtain the filtered-sequence property *)
    have "let p_his = filter (\<lambda>e. act_pid e = p) (his_seq s)
          in \<exists>i<length p_his. p_his ! i = mk_act deq a p sn ret \<and> 0 < i \<and> p_his ! (i - Suc 0) = mk_act deq BOT p sn call"
      using hI22_Deq_Local_Pattern_s cond_q cond_ret unfolding hI22_Deq_Local_Pattern_def
      by simp 
      
    (* Step 5: transport the obtained history-sequence conclusion back to the new state and close the goal *)
    then show ?case using his_eq by simp
  qed

  have "hI23_Deq_Call_Ret_Balanced s'" using hI23_Deq_Call_Ret_Balanced_s step_facts unfolding hI23_Deq_Call_Ret_Balanced_def by simp
  
  have "hI24_HB_Implies_Idx_Order s'"
  proof (unfold hI24_HB_Implies_Idx_Order_def, intro allI impI, goal_cases)
    case (1 u1 u2 v1 v2 idx1 idx2 sn1 sn2)
    
    (* Step 1: extract the three core premises in the new state s' *)
    from 1 have hb': "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)" by blast
    from 1 have q1': "CState.Q_arr (fst s') idx1 = v1" by blast
    from 1 have q2': "CState.Q_arr (fst s') idx2 = v2" by blast
    
    (* Step 2: E1 only changes the local ticket of p; the global queue and the history sequence stay unchanged *)
    (* From step_facts, simplification immediately sees fst s' = fst s and his_seq s' = his_seq s *)
    have hb: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
      using hb' step_facts unfolding HB_Act_def Let_def by auto
      
    have q1: "CState.Q_arr (fst s) idx1 = v1" 
      using q1' step_facts
      using Model.Q_arr_def by auto 
      
    have q2: "CState.Q_arr (fst s) idx2 = v2" 
      using q2' step_facts
      using Model.Q_arr_def by fastforce 
      
    (* Step 3: all pre-state premises are now available, so we invoke hI24_HB_Implies_Idx_Order_s *)
    show ?case
      using hI24_HB_Implies_Idx_Order_s hb q1 q2 unfolding hI24_HB_Implies_Idx_Order_def by blast
  qed
  
  have "hI25_Enq_Call_Ret_Balanced s'"
  proof (unfold hI25_Enq_Call_Ret_Balanced_def, intro allI impI, goal_cases)
    case (1 q k)
    
    (* Step 1: the history record is unchanged *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by simp
    
    (* Key fix: after introducing impI, the assumption becomes k \<le> length (his_seq s'), which is exactly what we need *)
    have k_le: "k \<le> length (his_seq s)" using 1 his_eq by simp
    
    (* Step 2: since the history is unchanged, extract the full pre-state property, including the three local let-bindings *)
    have hI25_Enq_Call_Ret_Balanced_old: "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s)) in
           let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
           let n_ret  = length (filter (\<lambda>e. act_cr e = ret) p_his) in
           n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
           (k = length (his_seq s) \<longrightarrow> (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1))"
      using hI25_Enq_Call_Ret_Balanced_s k_le unfolding hI25_Enq_Call_Ret_Balanced_def by blast
      
    (* Step 3: key observation: the E1 step only moves process p from E1 to E2. Since both E1 and E2 belong to {''E1'', ''E2'', ''E3''}, the truth of this membership test is unchanged. *)
    have pc_eq: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
    proof (cases "q = p")
      case True
      (* For process p, membership in the target set is preserved automatically *)
      have pc_s: "program_counter s p = ''E1''" using step_facts by simp
      have pc_s': "program_counter s' p = ''E2''" using step_facts by simp
      show ?thesis using True pc_s pc_s' by auto
    next
      case False
      (* For all other processes, the program counter is unchanged *)
      have "program_counter s' q = program_counter s q" using step_facts False pc_eqs by auto
      then show ?thesis by simp
    qed
    
    (* Step 4: transport all relevant properties from s to s' and finish the proof after unfolding the local let-bindings *)
    show ?case
      using hI25_Enq_Call_Ret_Balanced_old pc_eq his_eq unfolding Let_def by auto
  qed
  
  have "hI26_DeqRet_D4_Mutex s'"
  proof (unfold hI26_DeqRet_D4_Mutex_def, intro allI impI, goal_cases)
    case (1 q a)
    
    (* The goal is a negation, so we use a parameterless proof block to enter a contradiction argument via notI *)
    show ?case
    proof
      (* Step 1: assume there exists a process q that violates the invariant *)
      assume bad_cond: "(\<exists>sn. DeqRetInHis s' q a sn) \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a"
      
      (* Step 2: isolate the active process p: since p is in E2 after the E1 step, q cannot be p *)
      have q_neq_p: "q \<noteq> p"
      proof
        assume "q = p"
        with bad_cond have "program_counter s' p = ''D4''" by simp
        moreover have "program_counter s' p = ''E2''" using step_facts by simp
        ultimately show False by simp
      qed
      
      (* Step 3: transport the relevant facts: the history is unchanged globally, and for q \<noteq> p both the program counter and x_var stay unchanged *)
      obtain sn where sn_his: "DeqRetInHis s' q a sn" using bad_cond by blast
      
      have his_eq: "his_seq s' = his_seq s" using step_facts by auto
      have sn_his_s: "DeqRetInHis s q a sn" 
        using sn_his his_eq unfolding DeqRetInHis_def Let_def by simp
        
      have pc_q_s: "program_counter s q = ''D4''" 
        using bad_cond q_neq_p step_facts pc_eqs by auto
        
      (* E1 does not modify x_var at all, so this fact transports globally *)
      have x_var_eq: "\<And>x. x_var s' x = x_var s x" using step_facts by auto
      have x_q_s: "x_var s q = a" 
        using bad_cond x_var_eq by auto
        
      (* Step 4: reconstruct the violating condition in the pre-state and invoke hI26_DeqRet_D4_Mutex_s *)
      have "\<not> ((\<exists>sn. DeqRetInHis s q a sn) \<and> program_counter s q = ''D4'' \<and> x_var s q = a)"
        using hI26_DeqRet_D4_Mutex_s 1 unfolding hI26_DeqRet_D4_Mutex_def by blast
        
      (* Step 5: derive the contradiction and close the proof *)
      then show False using sn_his_s pc_q_s x_q_s by blast
    qed
  qed

  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_pending_pc_sync below, without changing the proof logic. *)
  have "hI27_Pending_PC_Sync s'"
    using E1_pending_pc_sync[OF hI27_Pending_PC_Sync_s step_facts pc_eqs] .

have "hI28_Fresh_Enq_Immunity s'"
  proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI, goal_cases)
    case (1 p' q a sn)
    
    (* Step 1: extract the core premises of the goal *)
    from 1 have pc_p': "program_counter s' p' \<in> {''E1'', ''E2''}" by blast
    from 1 have v_p': "v_var s' p' = a" by blast
    from 1 have a_not_bot: "a \<noteq> BOT" by blast
    
    (* Step 2: E1 leaves the global history sequence unchanged *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by simp
    have deq_eq: "DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
      unfolding DeqRetInHis_def Let_def using his_eq by simp
      
    (* Step 3: split on which process triggers the statement *)
    show ?case
      proof (cases "p' = p")
      case True
      (* Step 3: 1 handle the active process p, whose value is exactly the previously allocated v_var s p *)
      have a_is_v: "a = v_var s p" using True v_p' step_facts by auto
      
      (* extract the needed properties of the pre-state directly from step_facts, without relying on additional names *)
      have pc_s: "program_counter s p = ''E1''" using step_facts by auto
      have v_var_s: "v_var s p = a" using True v_p' step_facts by auto
      
      (* Since p is already in E1 in the pre-state and holds a non-BOT value a, hI28_Fresh_Enq_Immunity_s already tells us that it has no dequeue history. *)
      have "\<not> DeqRetInHis s q a sn" 
        using hI28_Fresh_Enq_Immunity_s pc_s v_var_s a_not_bot 
        unfolding hI28_Fresh_Enq_Immunity_def by blast
        
      then show ?thesis using deq_eq by simp
    next
      case False
      (* Step 3.2: handle any other process p': if it is not the active process, all its relevant fields are unchanged *)
      have pc_p'_s: "program_counter s p' = program_counter s' p'"
        using step_facts False pc_eqs by auto
      have v_p'_s: "v_var s p' = v_var s' p'"
        using step_facts False by auto
        
      (* transport the premises back to the pre-state s *)
      have pc_in_set: "program_counter s p' \<in> {''E1'', ''E2''}" 
        using pc_p' pc_p'_s by simp
      have v_val_eq: "v_var s p' = a" 
        using v_p' v_p'_s
        by blast 
        
      (* invoke hI28_Fresh_Enq_Immunity_s in the pre-state *)
      have "\<not> DeqRetInHis s q a sn"
        using hI28_Fresh_Enq_Immunity_s pc_in_set v_val_eq a_not_bot 
        unfolding hI28_Fresh_Enq_Immunity_def by blast
        
      (* transport the result back to the new state s' *)
      then show ?thesis using deq_eq by simp
    qed
  qed

  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_e2_scanner_immune below, without changing the proof logic. *)
  have "hI29_E2_Scanner_Immunity s'"
    using E1_e2_scanner_immune[OF INV not_InQBack_v v_def step_facts pc_eqs] .

(* ========================================================================= *)
    (* hI30_Ticket_HB_Immunity: preservation of ticket-order compatibility with happens-before across the E1 step *)
    (* Key idea: use sI2_X_var_Upper_Bound to show that the ticket of any old element is strictly smaller than the freshly allocated X_var *)
    (* ========================================================================= *)
    (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
    (* We only reuse the helper lemma E1_ticket_hb_immune below, without changing the proof logic. *)
    have "hI30_Ticket_HB_Immunity s'"
      using E1_ticket_hb_immune[OF INV TypeB_s'_v v_in_Val not_InQBack_v step_facts pc_eqs] .

  (* ========================================================================= *)
  (* Step 6: Preservation of linearization invariants *)
  (* Key point: E1 appends a new action, so OPLin, OP_A_enq, and OP_B_enq must be updated *)
  (* ========================================================================= *)

  have OPLin_new: "OPLin s' = insert new_act (OPLin s)"
    unfolding OPLin_def lin_eq by auto

  have OP_A_enq_eq: "OP_A_enq s' = OP_A_enq s"
    using his_eq setA_eq unfolding OP_A_enq_def by (auto simp: EnqCallInHis_his_eq[OF his_eq])

  have OP_A_deq_eq: "OP_A_deq s' = OP_A_deq s"
  proof
    show "OP_A_deq s' \<subseteq> OP_A_deq s"
    proof (intro subsetI)
      fix act assume act_in: "act \<in> OP_A_deq s'"
      
      (* Key fix: avoid using obtain here; extract the four required properties directly from the set characterization *)
      have act_lin: "act \<in> OPLin s'" 
       and act_deq: "op_name act = deq" 
       and act_setA: "op_val act \<in> SetA s'" 
       and act_call: "DeqCallInHis s' (op_pid act) (op_ssn act)"
        using act_in unfolding OP_A_deq_def by simp_all

      (* Identify act by unfolding new_act and showing that it is indeed an enqueue operation *)
      have "op_name new_act = enq" 
        unfolding new_act_def mk_op_def op_name_def by simp
        
      hence "act \<noteq> new_act" using act_deq
        by auto 
      
      (* Therefore act is not the freshly appended element; it must already belong to OPLin s *)
      hence old_lin: "act \<in> OPLin s" using act_lin OPLin_new by blast
      
      (* transport the claim using the unchanged concrete environment *)
      have old_setA: "op_val act \<in> SetA s" using act_setA setA_eq by simp
      have old_call: "DeqCallInHis s (op_pid act) (op_ssn act)" 
        using act_call his_eq unfolding DeqCallInHis_def Let_def by auto
        
      show "act \<in> OP_A_deq s" 
        unfolding OP_A_deq_def using old_lin act_deq old_setA old_call by simp
    qed

    show "OP_A_deq s \<subseteq> OP_A_deq s'"
    proof (intro subsetI)
      fix act assume act_in: "act \<in> OP_A_deq s"
      
      have act_lin: "act \<in> OPLin s" 
       and act_deq: "op_name act = deq" 
       and act_setA: "op_val act \<in> SetA s" 
       and act_call: "DeqCallInHis s (op_pid act) (op_ssn act)"
        using act_in unfolding OP_A_deq_def by simp_all

      (* finish by transporting the result to the new state *)
      have new_lin: "act \<in> OPLin s'" using act_lin OPLin_new by blast
      have new_setA: "op_val act \<in> SetA s'" using act_setA setA_eq by simp
      have new_call: "DeqCallInHis s' (op_pid act) (op_ssn act)" 
        using act_call his_eq unfolding DeqCallInHis_def Let_def by auto

      show "act \<in> OP_A_deq s'" 
        unfolding OP_A_deq_def using new_lin act_deq new_setA new_call by simp
    qed
  qed

  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_op_b_enq_new below, without changing the proof logic. *)
  have OP_B_enq_new: "OP_B_enq s' = insert new_act (OP_B_enq s)"
    using E1_op_b_enq_new[OF his_eq setB_new hI8_Val_Unique_s call_p v_in_Val TypeB_s'_v new_act_def] .

  have "lI1_Op_Sets_Equivalence s'"
    using lI1_Op_Sets_Equivalence_s OPLin_new OP_A_enq_eq OP_A_deq_eq OP_B_enq_new unfolding lI1_Op_Sets_Equivalence_def by blast

  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_op_cardinality below, without changing the proof logic. *)
  have lI2_Op_Cardinality_s': "lI2_Op_Cardinality s'"
    using E1_op_cardinality[OF INV setA_eq setB_new TypeB_s'_v v_in_Val not_InQBack_v pc_p_E1 hI1_E_Phase_Pending_Enq_s hI8_Val_Unique_s sI8_Q_Qback_Sync_s sI1_Zero_Index_BOT_s lI1_Op_Sets_Equivalence_s lI4_FIFO_Semantics_s di_lin_s call_p lin_eq new_act_def] .
  
  
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_hb_ret_lin_sync below, without changing the proof logic. *)
  have "lI3_HB_Ret_Lin_Sync s'"
    using E1_hb_ret_lin_sync[OF INV his_eq his_eq lin_eq pend_p new_act_def] .
  
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_fifo_semantics below, without changing the proof logic. *)
  have "lI4_FIFO_Semantics s'"
    using E1_fifo_semantics[OF INV lin_eq new_act_def] .

  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_sa_prefix below, without changing the proof logic. *)
  have "lI5_SA_Prefix s'"
    using E1_sa_prefix[OF INV lin_eq new_act_def TypeB_s'_v v_in_Val lI2_Op_Cardinality_s' \<open>lI1_Op_Sets_Equivalence s'\<close> lI1_Op_Sets_Equivalence_s lI2_Op_Cardinality_s setA_eq not_InQBack_v] .
  
(* ========================================================================= *)
  (* lI6_D4_Deq_Linearized: preservation of pending-dequeue membership in the linearization sequence *)
  (* Key idea: start with goal_cases and use process separation (q \<noteq> p) to transport the old membership fact directly *)
  (* ========================================================================= *)
  have "lI6_D4_Deq_Linearized s'"
  proof (unfold lI6_D4_Deq_Linearized_def, intro allI impI, goal_cases)
    (* Step 1: here q is an arbitrary process in state D4. *)
    case (1 q)
    then have pc_q: "program_counter s' q = ''D4''" by simp

    (* Step 2: show that q is not the active process p *)
    have "q \<noteq> p"
    proof
      assume "q = p"
      hence "program_counter s' p = ''D4''" using pc_q by simp
      moreover have "program_counter s' p = ''E2''" using step_facts by simp
      ultimately show False by simp
    qed

    (* Step 3: since q \<noteq> p, all relevant fields of q agree between s and s' *)
    have pc_q_s: "program_counter s q = ''D4''" 
      using pc_q \<open>q \<noteq> p\<close> step_facts by (auto simp: fun_upd_def)
    have x_q_s: "x_var s' q = x_var s q" using step_facts \<open>q \<noteq> p\<close> by simp
    have s_q_s: "s_var s' q = s_var s q" using step_facts \<open>q \<noteq> p\<close> by simp

    (* Step 4: invoke the pre-state invariant stating that q's action is already in the old sequence *)
    have lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" using INV unfolding system_invariant_def by blast
    hence "mk_op deq (x_var s q) q (s_var s q) \<in> set (lin_seq s)"
      using pc_q_s unfolding lI6_D4_Deq_Linearized_def by blast

    (* Step 5: conclude since the old sequence is a subset of the new one *)
    thus ?case
      using x_q_s s_q_s lin_eq by (auto simp: nth_append)
  qed
  
(* ========================================================================= *)
  (* lI7_D4_Deq_Deq_HB: preservation of the happens-before restriction for pending dequeue operations *)
  (* Key idea: use goal_cases to decompose the large conjunction early, and use q to avoid naming conflicts *)
  (* ========================================================================= *)
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_d4_deq_deq_hb below, without changing the proof logic. *)
  have "lI7_D4_Deq_Deq_HB s'"
    using E1_d4_deq_deq_hb[OF INV step_facts his_eq lin_eq new_act_def] .
  
(* ========================================================================= *)
  (* lI8_D3_Deq_Returned: a dequeue action in state D3 must have a corresponding return record in history *)
  (* Key idea: use goal_cases to distribute the quantifiers, and use the enqueue/dequeue type mismatch to force k into the old sequence *)
  (* ========================================================================= *)
  have "lI8_D3_Deq_Returned s'"
  proof (unfold lI8_D3_Deq_Returned_def, intro allI impI, goal_cases)
    case (1 q k)
    (* Step 1: extract the premises: q is in D3 and the k-th action of the sequence is q's dequeue action *)
    then have pc_q: "program_counter s' q = ''D3''"
          and k_lt: "k < length (lin_seq s')"
          and deq_k: "op_name (lin_seq s' ! k) = deq"
          and pid_k: "op_pid (lin_seq s' ! k) = q"
      by auto

    (* Step 2: show that q is not the active process p *)
    have "q \<noteq> p"
    proof
      assume "q = p"
      with pc_q have "program_counter s' p = ''D3''" by simp
      with step_facts show False by simp (* p is in E2 in s' *)
    qed

    (* Step 3: prove that k must already lie in the old sequence, since the new action is an enqueue while the k-th action is a dequeue *)
    have k_old: "k < length (lin_seq s)"
    proof (rule ccontr)
      assume "\<not> k < length (lin_seq s)"
      hence "k = length (lin_seq s)" using k_lt lin_eq by auto
      hence "lin_seq s' ! k = new_act" using lin_eq by (simp add: nth_append)
      hence "op_name (lin_seq s' ! k) = enq" 
        unfolding new_act_def mk_op_def op_name_def by simp
      with deq_k show False by simp
    qed

    (* Step 4: transport the properties of q and k back to the pre-state s *)
    have pc_q_s: "program_counter s q = ''D3''"
      using pc_q \<open>q \<noteq> p\<close> step_facts by (auto simp: fun_upd_def)
    
    have act_eq: "lin_seq s' ! k = lin_seq s ! k"
      using lin_eq k_old by (simp add: nth_append)

    have lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s" using INV unfolding system_invariant_def by blast

    (* Step 5: invoke the pre-state invariant and use the monotonicity of the history record (his_seq s' = his_seq s @ [call]) *)
    have "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
      using lI8_D3_Deq_Returned_s pc_q_s k_old act_eq deq_k pid_k
      unfolding lI8_D3_Deq_Returned_def by (auto simp: op_pid_def)

    thus ?case
      unfolding DeqRetInHis_def using his_eq act_eq by (auto simp: nth_append)
  qed
  
(* ========================================================================= *)
  (* lI9_D1_D2_Deq_Returned: a dequeue action in state D1 or D2 must have a corresponding return record in history *)
  (* Key idea: use goal_cases to expand the quantified statement and use the enqueue/dequeue type mismatch to determine the position of k *)
  (* ========================================================================= *)
  have "lI9_D1_D2_Deq_Returned s'"
  proof (unfold lI9_D1_D2_Deq_Returned_def, intro allI impI, goal_cases)
    case (1 q k)
    (* Step 1: extract the core premises *)
    then have pc_q: "program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2''"
          and k_lt: "k < length (lin_seq s')"
          and deq_k: "op_name (lin_seq s' ! k) = deq"
          and pid_k: "op_pid (lin_seq s' ! k) = q"
      by auto

    (* Step 2: isolate q and show that it cannot be the active process p *)
    have "q \<noteq> p"
    proof
      assume "q = p"
      with pc_q have "program_counter s' p = ''D1'' \<or> program_counter s' p = ''D2''" by simp
      with step_facts show False by simp (* p is in E2 in s' *)
    qed

    (* Step 3: show that k must lie in the old sequence, since the new action is an enqueue while the k-th action is a dequeue *)
    have k_old: "k < length (lin_seq s)"
    proof (rule ccontr)
      assume "\<not> k < length (lin_seq s)"
      hence "k = length (lin_seq s)" using k_lt lin_eq by auto
      hence "lin_seq s' ! k = new_act" using lin_eq by (simp add: nth_append)
      hence "op_name (lin_seq s' ! k) = enq" 
        unfolding new_act_def mk_op_def op_name_def by simp
      with deq_k show False by simp
    qed

    (* Step 4: transport the state facts and invoke the corresponding pre-state invariant *)
    have pc_q_s: "program_counter s q = ''D1'' \<or> program_counter s q = ''D2''"
      using pc_q \<open>q \<noteq> p\<close> step_facts by (auto simp: fun_upd_def)
    
    have act_eq: "lin_seq s' ! k = lin_seq s ! k"
      using lin_eq k_old by (simp add: nth_append)

    have lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s" using INV unfolding system_invariant_def by blast

    (* Step 5: transport the existence of the history record from s to s' *)
    have "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
      using lI9_D1_D2_Deq_Returned_s pc_q_s k_old act_eq deq_k pid_k
      unfolding lI9_D1_D2_Deq_Returned_def by (auto simp: op_pid_def)

    thus ?case
      unfolding DeqRetInHis_def using his_eq act_eq by (auto simp: nth_append)
  qed
  
(* ========================================================================= *)
  (* lI10_D4_Enq_Deq_HB: preservation of the enqueue/dequeue happens-before restriction for pending dequeue operations *)
  (* Key idea: k2 is ruled out by the action-type mismatch, and k1 is ruled out because without a return record it cannot serve as a happens-before predecessor *)
  (* ========================================================================= *)
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_d4_enq_deq_hb below, without changing the proof logic. *)
  have "lI10_D4_Enq_Deq_HB s'"
    using E1_d4_enq_deq_hb[OF INV step_facts his_eq lin_eq pend_p new_act_def] .
  
(* ========================================================================= *)
  (* lI11_D4_Deq_Unique: uniqueness and ordering constraints for pending dequeue actions *)
  (* Key idea: use goal_cases globally and unpack new_act manually to avoid simplifier blind spots *)
  (* ========================================================================= *)
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_d4_deq_unique below, without changing the proof logic. *)
  have "lI11_D4_Deq_Unique s'"
    using E1_d4_deq_unique[OF INV step_facts his_eq lin_eq new_act_def] .

(* ========================================================================= *)
  (* data_independent s': preservation of data independence for the linearization sequence *)
  (* Key idea: prove freshness of v by set-theoretic exclusion, then close the proof with the append lemma *)
  (* ========================================================================= *)
  (* This proof block has been moved from E1Proof.thy to E1Lemmas.thy. *)
  (* We only reuse the helper lemma E1_data_independent below, without changing the proof logic. *)
  have "data_independent (lin_seq s')"
    using E1_data_independent[OF not_InQBack_v sI8_Q_Qback_Sync_s sI1_Zero_Index_BOT_s pc_p_E1 hI1_E_Phase_Pending_Enq_s call_p hI8_Val_Unique_s lI1_Op_Sets_Equivalence_s di_lin_s TypeB_s'_v v_in_Val lin_eq new_act_def] .
  
  have "Simulate_PC s'" 
    using STEP unfolding Sys_E1_def by simp

  (* ========================================================================= *)
  (* ========================================================================= *)
  (* 7. Assemble the final invariant package *)
  (* ========================================================================= *)
  (* ========================================================================= *)
  show ?thesis 
    unfolding system_invariant_def
    using `Simulate_PC s'` `TypeOK s'` 
    using `sI1_Zero_Index_BOT s'` `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'` `hI3_L0_E_Phase_Bounds s'`
    using `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'` `sI12_D3_Scanned_Prefix s'` `hI4_X_var_Lin_Sync s'`
    using `hI7_His_WF s'` `hI8_Val_Unique s'` `hI5_SSN_Unique s'` `hI6_SSN_Order s'` 
    using `hI9_Deq_Ret_Unique s'` `hI10_Enq_Call_Existence s'` `hI11_Enq_Ret_Existence s'` `hI12_D_Phase_Pending_Deq s'` `hI13_Qback_Deq_Sync s'` `hI14_Pending_Enq_Qback_Exclusivity s'` `hI15_Deq_Result_Exclusivity s'` 
    using `hI16_BO_BT_No_HB s'` `hI17_BT_BT_No_HB s'` `hI18_Idx_Order_No_Rev_HB s'` `hI19_Scanner_Catches_Later_Enq s'` `hI20_Enq_Val_Valid s'` `hI21_Ret_Implies_Call s'` `hI22_Deq_Local_Pattern s'` 
    using `hI23_Deq_Call_Ret_Balanced s'` `hI24_HB_Implies_Idx_Order s'` `hI25_Enq_Call_Ret_Balanced s'` `hI26_DeqRet_D4_Mutex s'`
    using `hI27_Pending_PC_Sync s'` `hI28_Fresh_Enq_Immunity s'` `hI29_E2_Scanner_Immunity s'` `hI30_Ticket_HB_Immunity s'` 
    using `lI1_Op_Sets_Equivalence s'` `lI2_Op_Cardinality s'` `lI3_HB_Ret_Lin_Sync s'` `lI4_FIFO_Semantics s'` `lI5_SA_Prefix s'` `lI6_D4_Deq_Linearized s'` 
    using `lI7_D4_Deq_Deq_HB s'` `lI8_D3_Deq_Returned s'` `lI9_D1_D2_Deq_Returned s'` `lI10_D4_Enq_Deq_HB s'` `lI11_D4_Deq_Unique s'`
    using `data_independent (lin_seq s')`
    by blast
qed

end
