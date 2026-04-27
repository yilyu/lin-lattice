(* ========================================================== *)
(* Preservation of the system invariant for the D1 transition *)
(* ========================================================== *)
theory D1Proof
 imports 
    Main 
    "HOL-Library.Multiset" 
    Model
    DeqLib
begin

lemma D1_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_D1 p s s'"  
  shows "system_invariant s'"
proof -   
(* ========================================================== *)
  (* 0. Bridge definitions and proof setup                     *)
  (* ========================================================== *)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  (* ========== 1. Extract the complete pre-state invariant package ========== *)
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
   and hI19_s: "hI27_Pending_PC_Sync s" and hI20_s: "hI28_Fresh_Enq_Immunity s"
   and hI21_s: "hI29_E2_Scanner_Immunity s" and hI22_s: "hI30_Ticket_HB_Immunity s" 
   and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" 
   and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" and lI5_SA_Prefix_s: "lI5_SA_Prefix s" and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" 
   and lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" and lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s" and lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s" 
   and lI10_D4_Enq_Deq_HB_s: "lI10_D4_Enq_Deq_HB s" and lI11_D4_Deq_Unique_s: "lI11_D4_Deq_Unique s" 
   and di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  (* ========== 2. Collect the frame facts of the D1 step ========== *)
  have step_facts [simp]:
    "his_seq s' = his_seq s"
    "lin_seq s' = lin_seq s"
    "Q_arr s' = Q_arr s"
    "Qback_arr s' = Qback_arr s"
    "v_var s' = v_var s"
    "x_var s' = x_var s"
    "i_var s' = i_var s"
    "j_var s' = j_var s"
    "X_var s' = X_var s"
    "V_var s' = V_var s"
    "s_var s' = s_var s"
    "snd s' = snd s"
    "program_counter s p = ''D1''"
    "program_counter s' p = ''D2''"
    "l_var s' p = X_var s"
    using STEP unfolding Sys_D1_def C_D1_def bridge Let_def by (auto simp: prod_eq_iff)

  (* Step 1: isolate the frame properties for processes q \<noteq> p. *)
  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> l_var s' q = l_var s q"
    using STEP unfolding Sys_D1_def C_D1_def bridge Let_def by auto

  (* Step 2: record the PC-state equivalences needed later. *)
  have pc_eqs [simp]:
    "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
    "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'')"
    "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'')"
    "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
    "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
    "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    "\<And>q. (program_counter s' q \<in> {''E2'', ''E3''}) = (program_counter s q \<in> {''E2'', ''E3''})"
  proof -
    fix q
    show "(program_counter s' q = ''L0'') = (program_counter s q = ''L0'')" using step_facts(12,13) other_facts(1)[of q] by (cases "q = p", auto)
    show "(program_counter s' q = ''E1'') = (program_counter s q = ''E1'')" using step_facts(12,13) other_facts(1)[of q] by (cases "q = p", auto)
    show "(program_counter s' q = ''E2'') = (program_counter s q = ''E2'')" using step_facts(12,13) other_facts(1)[of q] by (cases "q = p", auto)
    show "(program_counter s' q = ''E3'') = (program_counter s q = ''E3'')" using step_facts(12,13) other_facts(1)[of q] by (cases "q = p", auto)
    show "(program_counter s' q = ''D3'') = (program_counter s q = ''D3'')" using step_facts(12,13) other_facts(1)[of q] by (cases "q = p", auto)
    show "(program_counter s' q = ''D4'') = (program_counter s q = ''D4'')" using step_facts(12,13) other_facts(1)[of q] by (cases "q = p", auto)
    show "(program_counter s' q \<in> {''E2'', ''E3''}) = (program_counter s q \<in> {''E2'', ''E3''})" using step_facts(12,13) other_facts(1)[of q] by (cases "q = p", auto)
  qed

  (* ========== 3. Prove preservation of the derived sets ========== *)
  have typeb_eq: "\<And>x. TypeB s' x = TypeB s x"
  proof -
    fix x
    have "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow> (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
    proof
      assume "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x"
      then obtain q where "program_counter s' q = ''E2''" "v_var s' q = x" by blast
      moreover have "q \<noteq> p" using `program_counter s' q = ''E2''` step_facts(13) by auto
      ultimately show "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x" using step_facts other_facts by auto
    next
      assume "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x"
      then obtain q where "program_counter s q = ''E2''" "v_var s q = x" by blast
      moreover have "q \<noteq> p" using `program_counter s q = ''E2''` step_facts(12) by auto
      ultimately show "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x" using step_facts other_facts by metis 
    qed
    thus "TypeB s' x = TypeB s x" unfolding TypeB_def QHas_def step_facts by simp
  qed

  have typebt_eq: "\<And>x. TypeBT s' x = TypeBT s x"
  proof -
    fix x
    have idx_eq: "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def step_facts by simp
    have "(\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)) \<longleftrightarrow>
          (\<exists>q. program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT))"
      (is "?LHS \<longleftrightarrow> ?RHS")
    proof
      assume "?LHS"
      then obtain q where "program_counter s' q = ''D3''" "j_var s' q \<le> Idx s' x" "Idx s' x < l_var s' q" "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT" by blast
      moreover have "q \<noteq> p" using `program_counter s' q = ''D3''` step_facts(13) by auto
      ultimately show "?RHS" using idx_eq step_facts other_facts by auto
    next
      assume "?RHS"
      then obtain q where "program_counter s q = ''D3''" "j_var s q \<le> Idx s x" "Idx s x < l_var s q" "\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT" by blast
      moreover have "q \<noteq> p" using `program_counter s q = ''D3''` step_facts(12) by auto
      ultimately show "?LHS" using idx_eq step_facts other_facts by metis 
    qed
    thus "TypeBT s' x = TypeBT s x" unfolding TypeBT_def InQBack_def typeb_eq idx_eq step_facts by simp
  qed

  have set_facts [simp]: 
    "SetA s' = SetA s" "SetB s' = SetB s" "SetBT s' = SetBT s" "SetBO s' = SetBO s"
    "\<And>x. TypeB s' x = TypeB s x" "\<And>x. TypeBT s' x = TypeBT s x"
    unfolding SetA_def SetB_def SetBT_def SetBO_def TypeA_def TypeBO_def InQBack_def QHas_def
    using typeb_eq typebt_eq step_facts by auto

  (* ========== 4. Reestablish the invariant clauses one by one ========== *)
  have "TypeOK s'"
  proof -
    have old_types: 
      "\<forall>q. program_counter s q \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
      "X_var s \<in> Val"
      "\<forall>q. l_var s q \<in> Val \<union> {BOT}"
      "\<forall>q. s_var s q \<in> Val"
      using TypeOK_s unfolding TypeOK_def by auto

    have pc_ok: "\<forall>q. program_counter s' q \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
    proof
      fix q show "program_counter s' q \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
        using old_types(1) by (cases "q = p", auto)
    qed

    have l_ok: "\<forall>q. l_var s' q \<in> Val \<union> {BOT}"
    proof
      fix q show "l_var s' q \<in> Val \<union> {BOT}"
        using old_types(2,3) by (cases "q = p", auto)
    qed

    (* Step 3: the SSN function is unchanged, so the goal closes directly. *)
    have sn_ok: "\<forall>q. s_var s' q \<in> Val"
      using old_types(4) by simp

    show ?thesis
      using TypeOK_s pc_ok l_ok sn_ok 
      unfolding TypeOK_def 
      by auto
  qed

  have "sI1_Zero_Index_BOT s'" using sI1_Zero_Index_BOT_s unfolding sI1_Zero_Index_BOT_def by simp
  have "sI2_X_var_Upper_Bound s'" using sI2_X_var_Upper_Bound_s unfolding sI2_X_var_Upper_Bound_def by simp
  have "sI3_E2_Slot_Exclusive s'" using sI3_E2_Slot_Exclusive_s unfolding sI3_E2_Slot_Exclusive_def by auto
  have "sI4_E3_Qback_Written s'" using sI4_E3_Qback_Written_s unfolding sI4_E3_Qback_Written_def by auto
  
  have "sI5_D2_Local_Bound s'"
  proof -
    have "X_var s \<in> Val" using TypeOK_s unfolding TypeOK_def by simp
    hence "1 \<le> X_var s" unfolding Val_def by auto
    show ?thesis
      unfolding sI5_D2_Local_Bound_def
    proof (intro allI impI)
      fix q assume "program_counter s' q = ''D2''"
      show "l_var s' q \<in> Val \<and> 1 \<le> l_var s' q \<and> l_var s' q \<le> X_var s'"
      proof (cases "q = p")
        case True
        thus ?thesis using step_facts \<open>X_var s \<in> Val\<close> \<open>1 \<le> X_var s\<close> by simp
      next
        case False
        have "program_counter s q = ''D2''" using False \<open>program_counter s' q = ''D2''\<close> other_facts by simp
        moreover have "l_var s' q = l_var s q" using False other_facts by simp
        ultimately show ?thesis using sI5_D2_Local_Bound_s step_facts unfolding sI5_D2_Local_Bound_def by simp
      qed
    qed
  qed

  have "sI6_D3_Scan_Pointers s'"
  proof -
    have "\<forall>q. program_counter s' q = ''D3'' \<longrightarrow> 
              j_var s' q \<in> Val \<and> l_var s' q \<in> Val \<and> 1 \<le> j_var s' q \<and> 
              j_var s' q < l_var s' q \<and> l_var s' q \<le> X_var s'"
    proof (intro allI impI)
      fix q assume "program_counter s' q = ''D3''"
      hence "q \<noteq> p" using step_facts(13) by auto
      hence "l_var s' q = l_var s q" using other_facts(2) by simp
      moreover have "program_counter s q = ''D3''" using `program_counter s' q = ''D3''` pc_eqs by simp
      ultimately show "j_var s' q \<in> Val \<and> l_var s' q \<in> Val \<and> 1 \<le> j_var s' q \<and> j_var s' q < l_var s' q \<and> l_var s' q \<le> X_var s'"
        using sI6_D3_Scan_Pointers_s unfolding sI6_D3_Scan_Pointers_def step_facts by auto
    qed
    thus ?thesis unfolding sI6_D3_Scan_Pointers_def by simp
  qed

  have "sI7_D4_Deq_Result s'" using sI7_D4_Deq_Result_s unfolding sI7_D4_Deq_Result_def by auto

  (* ========================================================== *)
  (* hI3_L0_E_Phase_Bounds under the D1 transition            *)
  (* ========================================================== *)
  have "hI3_L0_E_Phase_Bounds s'"
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    have q_ne_p: "q \<noteq> p" using 1 step_facts by auto
    have "program_counter s q = ''L0'' " using 1 q_ne_p other_facts by auto
    then show ?case 
      using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s] step_facts 
      by (simp add: HasPendingEnq_def HasPendingDeq_def Let_def s_var_def DeqCallInHis_def EnqCallInHis_def)
  next
    case (2 q)
    have q_ne_p: "q \<noteq> p" using 2 step_facts by auto
    have "program_counter s q = ''L0'' " using 2 q_ne_p other_facts by auto
    then show ?case using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s] step_facts by simp
  next
    case (3 q)
    have q_ne_p: "q \<noteq> p" using 3 step_facts by auto
    have "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" using 3 q_ne_p other_facts by auto
    then show ?case using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s] step_facts by auto
  next
    case (4 k)
    then show ?case using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s] step_facts by auto
  next
    case (5 k)
    then show ?case using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s] step_facts by auto
  qed

  have "sI8_Q_Qback_Sync s'" using sI8_Q_Qback_Sync_s unfolding sI8_Q_Qback_Sync_def by simp
  have "sI9_Qback_Discrepancy_E3 s'" using sI9_Qback_Discrepancy_E3_s unfolding sI9_Qback_Discrepancy_E3_def by auto
  have "sI10_Qback_Unique_Vals s'" using sI10_Qback_Unique_Vals_s unfolding sI10_Qback_Unique_Vals_def by simp
  have "hI2_SSN_Bounds s'" using hI2_SSN_Bounds_s unfolding hI2_SSN_Bounds_def s_var_def step_facts
    using s_var_def step_facts(11) by auto 

  (* ========================================================== *)
  (* sI11_x_var_Scope under the D1-to-D2 transition          *)
  (* ========================================================== *)
  have "sI11_x_var_Scope s'"
  proof (unfold sI11_x_var_Scope_def, intro allI impI, goal_cases)
    case (1 q)
    show ?case
    proof (cases "q = p")
      case True
      (* Step 1: in the pre-state, process p is at D1, hence x_var is BOT and remains unchanged. *)
      have "program_counter s p = ''D1'' " by simp
      hence "program_counter s p \<noteq> ''D4'' " by simp
      hence "x_var s p = BOT" using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def by blast
      then show ?thesis using True step_facts by simp
    next
      case False
      (* Step 2: transport the claim through the unchanged local variables. *)
      have "program_counter s q = program_counter s' q" using False other_facts(1) by simp
      with 1 have "program_counter s q \<noteq> ''D4'' "
        by presburger
      hence "x_var s q = BOT" using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def by blast
      then show ?thesis using False step_facts by simp
    qed
  qed

  have "hI1_E_Phase_Pending_Enq s'"
  proof -
    show ?thesis
      unfolding hI1_E_Phase_Pending_Enq_def
    proof (intro allI impI)
      fix q assume "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
      hence "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
        using pc_eqs by auto
      hence "HasPendingEnq s q (v_var s q)"
        using hI1_E_Phase_Pending_Enq_s unfolding hI1_E_Phase_Pending_Enq_def by blast
      moreover have "v_var s' q = v_var s q" "s_var s' q = s_var s q" "his_seq s' = his_seq s"
        using step_facts by (auto simp: fun_eq_iff)
      ultimately show "HasPendingEnq s' q (v_var s' q)"
        unfolding HasPendingEnq_def Let_def EnqCallInHis_def by simp
    qed
  qed

  have "sI12_D3_Scanned_Prefix s'" using sI12_D3_Scanned_Prefix_s unfolding sI12_D3_Scanned_Prefix_def by auto

  (* ========================================================== *)
  (* hI4_X_var_Lin_Sync under the D1 transition              *)
  (* ========================================================== *)
  have "hI4_X_var_Lin_Sync s'"
  proof -
    have X_var_eq: "X_var s' = X_var s" using step_facts(9) by simp
    have lin_seq_eq: "lin_seq s' = lin_seq s" using step_facts(2) by simp
    show ?thesis
      using hI4_X_var_Lin_Sync_s X_var_eq lin_seq_eq
      unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def
      by auto
  qed

  have "hI7_His_WF s'" using hI7_His_WF_s unfolding hI7_His_WF_def using step_facts(1) by presburger 
  have "hI8_Val_Unique s'" using hI8_Val_Unique_s unfolding hI8_Val_Unique_def by simp
  have "hI5_SSN_Unique s'" using hI5_SSN_Unique_s unfolding hI5_SSN_Unique_def step_facts by simp
  have "hI6_SSN_Order s'" using hI6_SSN_Order_s unfolding hI6_SSN_Order_def step_facts by simp

  have "hI9_Deq_Ret_Unique s'" using hI9_Deq_Ret_Unique_s unfolding hI9_Deq_Ret_Unique_def by simp

  have "hI10_Enq_Call_Existence s'"
  proof -
    show ?thesis
      unfolding hI10_Enq_Call_Existence_def
    proof (intro conjI)
      (* Step 1: show that every process in an enqueue phase has a matching call in the history. *)
      show "\<forall>q a. (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' q = a) \<longrightarrow> EnqCallInHis s' q a (s_var s' q)"
      proof (intro allI impI, elim conjE)
        fix q a
        assume pc': "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}" and v': "v_var s' q = a"
        (* Step 1a: reduce the claim to the pre-state using the PC equivalences. *)
        hence pc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" 
          using pc_eqs by auto
        (* Step 1b: invoke the corresponding pre-state invariant. *)
        hence "EnqCallInHis s q a (s_var s q)"
          using hI10_Enq_Call_Existence_s v' step_facts unfolding hI10_Enq_Call_Existence_def by auto
        (* Step 1c: map the conclusion back to the post-state. *)
        thus "EnqCallInHis s' q a (s_var s' q)"
          using step_facts unfolding EnqCallInHis_def by (auto simp: fun_eq_iff)
      qed
    next
      (* Step 2: show that each value in Qback still has a matching call action. *)
      show "\<forall>a. (\<exists>k. Qback_arr s' k = a) \<longrightarrow> (\<exists>q sn. EnqCallInHis s' q a sn)"
      proof (intro allI impI)
        fix a
        assume "\<exists>k. Qback_arr s' k = a"
        hence "\<exists>k. Qback_arr s k = a" using step_facts by simp
        hence "\<exists>q sn. EnqCallInHis s q a sn"
          using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def by blast
        thus "\<exists>q sn. EnqCallInHis s' q a sn"
          using step_facts unfolding EnqCallInHis_def by simp
      qed
    qed
  qed

  have "hI11_Enq_Ret_Existence s'"
  proof -
    show ?thesis
      unfolding hI11_Enq_Ret_Existence_def
    proof (intro allI impI, elim conjE)
      fix q a sn
      (* Step 2a: unfold the assumptions in the post-state. *)
      assume pre_s': "program_counter s' q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn"
         and qb_s':  "\<exists>k. Qback_arr s' k = a"
         and call_s': "EnqCallInHis s' q a sn"

      (* Step 2b: transport the premises back to the pre-state using the frame facts. *)
      have qb_s: "\<exists>k. Qback_arr s k = a" using qb_s' step_facts by simp
      have call_s: "EnqCallInHis s q a sn" 
        using call_s' step_facts unfolding EnqCallInHis_def by simp

      (* Step 2c: establish the corresponding pre-state premises. *)
      have pre_s: "program_counter s q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s q \<noteq> a \<or> s_var s q \<noteq> sn"
      proof -
        (* Step 2c(i): use the PC equivalences to preserve enqueue-phase membership. *)
        have pc_match: "(program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) = (program_counter s q \<in> {''E1'', ''E2'', ''E3''})"
          using pc_eqs by auto
        show ?thesis
          using pre_s' pc_match step_facts by (auto simp: fun_eq_iff)
      qed

      (* Step 2d: invoke the pre-state invariant clause. *)
      hence "EnqRetInHis s q a sn"
        using hI11_Enq_Ret_Existence_s qb_s call_s unfolding hI11_Enq_Ret_Existence_def by blast
      
      (* Step 2e: transport the result back to the post-state. *)
      thus "EnqRetInHis s' q a sn"
        using step_facts unfolding EnqRetInHis_def by simp
    qed
  qed

  have "hI12_D_Phase_Pending_Deq s'" 
  proof -
    (* Step 1: prove that HasPendingDeq is preserved by the D1 step. *)
    have pending_eq: "\<And>q. HasPendingDeq s' q = HasPendingDeq s q"
      using step_facts 
      unfolding HasPendingDeq_def DeqCallInHis_def Let_def 
      by (auto simp: fun_eq_iff)
    
    show ?thesis
      unfolding hI12_D_Phase_Pending_Deq_def
    proof (intro allI impI, goal_cases)
      case (1 q)
      hence pc_in': "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}" by simp
      
      (* Step 1a: split on q = p versus q \<noteq> p.
         The control states D1 and D2 are exactly the states changed by this step,
         so the dequeue-phase membership must be handled manually here. *)
      have pc_in: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof (cases "q = p")
        case True
        (* Case q = p: the old state is D1 and the new state is D2, both inside the dequeue phase set. *)
        thus ?thesis using step_facts by simp
      next
        case False
        (* Case q \<noteq> p: the PC is unchanged, so we map the claim back via the frame facts. *)
        thus ?thesis using pc_in' other_facts by auto
      qed
        
      (* Step 1b: use the pre-state invariant and transport the result back to the post-state. *)
      from hI12_D_Phase_Pending_Deq_s pc_in have "HasPendingDeq s q"
        unfolding hI12_D_Phase_Pending_Deq_def by blast
      thus "HasPendingDeq s' q" using pending_eq by simp
    qed
  qed

  have "hI13_Qback_Deq_Sync s'" using hI13_Qback_Deq_Sync_s unfolding hI13_Qback_Deq_Sync_def DeqRetInHis_def by auto

  (* ========================================================== *)
  (* hI14_Pending_Enq_Qback_Exclusivity under D1             *)
  (* ========================================================== *)
have "hI14_Pending_Enq_Qback_Exclusivity s'"
proof -
  show ?thesis
    unfolding hI14_Pending_Enq_Qback_Exclusivity_def
  proof (intro conjI allI impI)
    fix q a
    assume H': "HasPendingEnq s' q a \<and> program_counter s' q \<in> {''E2'', ''E3''}"
    show "\<not> (\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q)"
    proof
      assume ex': "\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q"
      then obtain k where
        qb': "Qback_arr s' k = a" and
        kneq': "k \<noteq> i_var s' q"
        by blast

      from H' have pend': "HasPendingEnq s' q a" and pc': "program_counter s' q \<in> {''E2'', ''E3''}"
        by blast+

      have q_ne_p: "q \<noteq> p"
        using pc' step_facts by auto
      have pc: "program_counter s q \<in> {''E2'', ''E3''}"
        using pc' q_ne_p other_facts by auto
      have qb: "Qback_arr s k = a"
        using qb' step_facts by simp
      have pend: "HasPendingEnq s q a"
        using pend' step_facts
        unfolding HasPendingEnq_def EnqCallInHis_def
        by auto

      have "k = i_var s q"
        using hI14_Pending_Enq_Qback_Exclusivity_s pc qb pend
        unfolding hI14_Pending_Enq_Qback_Exclusivity_def
        by blast
      hence "k = i_var s' q"
        using step_facts by simp
      with kneq' show False by simp
    qed
  next
    fix q a
    assume H': "HasPendingEnq s' q a \<and> program_counter s' q = ''E1''"
    show "\<not> (\<exists>k. Qback_arr s' k = a)"
    proof
      assume ex': "\<exists>k. Qback_arr s' k = a"
      then obtain k where qb': "Qback_arr s' k = a" by blast

      from H' have pend': "HasPendingEnq s' q a" and pc': "program_counter s' q = ''E1''"
        by blast+

      have q_ne_p: "q \<noteq> p"
        using pc' step_facts by auto
      have pc: "program_counter s q = ''E1''"
        using pc' q_ne_p other_facts by auto
      have qb: "Qback_arr s k = a"
        using qb' step_facts by simp
      have pend: "HasPendingEnq s q a"
        using pend' step_facts
        unfolding HasPendingEnq_def EnqCallInHis_def
        by auto

      show False
        using hI14_Pending_Enq_Qback_Exclusivity_s pc qb pend
        unfolding hI14_Pending_Enq_Qback_Exclusivity_def
        by blast
    qed
  qed
qed

  (* ========================================================== *)
  (* hI15_Deq_Result_Exclusivity under D1                    *)
  (* ========================================================== *)
  have "hI15_Deq_Result_Exclusivity s'"
  proof -
    have deqret_eq [simp]: "\<And>q a sn. DeqRetInHis s' q a sn = DeqRetInHis s q a sn"
      using step_facts
      unfolding DeqRetInHis_def
      by simp

    have pending_deq_eq [simp]: "\<And>q. HasPendingDeq s' q = HasPendingDeq s q"
      using step_facts
      unfolding HasPendingDeq_def DeqCallInHis_def Let_def
      by auto

    show ?thesis
      using hI15_Deq_Result_Exclusivity_s
      unfolding hI15_Deq_Result_Exclusivity_def
      using deqret_eq pc_eqs(6) pending_deq_eq step_facts(3,6)
      by presburger
  qed

  have "hI16_BO_BT_No_HB s'" using hI16_BO_BT_No_HB_s unfolding hI16_BO_BT_No_HB_def HB_EnqRetCall_def HB_Act_def by simp
  have "hI17_BT_BT_No_HB s'" using hI17_BT_BT_No_HB_s unfolding hI17_BT_BT_No_HB_def HB_EnqRetCall_def HB_Act_def by simp
  have "hI18_Idx_Order_No_Rev_HB s'" using hI18_Idx_Order_No_Rev_HB_s unfolding hI18_Idx_Order_No_Rev_HB_def HB_EnqRetCall_def HB_Act_def InQBack_def Idx_def AtIdx_def by simp
  
have "hI19_Scanner_Catches_Later_Enq s'"
  proof (unfold hI19_Scanner_Catches_Later_Enq_def, intro allI impI, goal_cases)
    case (1 a b)
    
    (* Step 1: unfold the six core premises of the post-state goal. *)
    from 1 have inqa': "InQBack s' a" by blast
    from 1 have inqb': "InQBack s' b" by blast
    from 1 have tba': "TypeB s' a" by blast
    from 1 have tbb': "TypeB s' b" by blast
    from 1 have idx_lt': "Idx s' a < Idx s' b" by blast
    from 1 have ex_q': "\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and> 
                            Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q" by blast
                            
    (* Step 2: restore InQBack and Idx through the unchanged physical state. *)
    have inqa: "InQBack s a" using inqa' step_facts unfolding InQBack_def by simp
    have inqb: "InQBack s b" using inqb' step_facts unfolding InQBack_def by simp
    have idx_lt: "Idx s a < Idx s b" using idx_lt' step_facts unfolding Idx_def AtIdx_def by simp
    
    (* Step 3: preserve TypeB, since D1 does not modify Q or introduce E2 processes. *)
    have tba: "TypeB s a" 
      using tba' step_facts pc_eqs unfolding TypeB_def QHas_def by auto
    have tbb: "TypeB s b" 
      using tbb' step_facts pc_eqs unfolding TypeB_def QHas_def by auto
    
    (* Step 4: transport the dequeue-side witness conditions. *)
    have deq_old: "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and> 
                       Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
    proof -
      from ex_q' obtain q where 
        q_pend': "HasPendingDeq s' q" and q_D3': "program_counter s' q = ''D3''" and
        q_idx1': "Idx s' a < j_var s' q" and q_idx2': "j_var s' q \<le> Idx s' b" and q_idx3': "Idx s' b < l_var s' q"
        by blast
        
      (* Since q is at D3, it cannot be the process p that just moved from D1 to D2. *)
      have q_ne_p: "q \<noteq> p"
      proof
        assume "q = p"
        with q_D3' have "program_counter s' p = ''D3''" by simp
        with step_facts show False by simp
      qed
      
      have q_pend: "HasPendingDeq s q" 
        using q_pend' step_facts unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
        by simp
      have q_D3: "program_counter s q = ''D3''" 
        using q_D3' q_ne_p step_facts by simp
      have q_idx1: "Idx s a < j_var s q" using q_idx1' q_ne_p step_facts unfolding Idx_def AtIdx_def by simp
      have q_idx2: "j_var s q \<le> Idx s b" using q_idx2' q_ne_p step_facts unfolding Idx_def AtIdx_def by simp
      have q_idx3: "Idx s b < l_var s q" using q_idx3' q_ne_p step_facts unfolding Idx_def AtIdx_def by simp
      
      show ?thesis using q_pend q_D3 q_idx1 q_idx2 q_idx3 by blast
    qed
    
    (* Step 5: the history is unchanged, hence the happens-before predicates are equivalent. *)
    have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using step_facts by auto
      
    (* Step 6: invoke the pre-state invariant with the transported premises. *)
    have "\<not> HB_EnqRetCall s a b" 
      using hI19_Scanner_Catches_Later_Enq_s inqa inqb tba tbb idx_lt deq_old unfolding hI19_Scanner_Catches_Later_Enq_def by blast
      
    (* Step 7: conclude the post-state goal. *)
    then show ?case using hb_eq by simp
  qed
  
  have "hI20_Enq_Val_Valid s'" using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def by simp
  have "hI21_Ret_Implies_Call s'"
  proof -
    have seq_eq: "his_seq s' = his_seq s" using step_facts by simp
    show "hI21_Ret_Implies_Call s'" using hI21_Ret_Implies_Call_s seq_eq unfolding hI21_Ret_Implies_Call_def by presburger
  qed
  have "hI22_Deq_Local_Pattern s'" using hI22_Deq_Local_Pattern_s unfolding hI22_Deq_Local_Pattern_def DeqRetInHis_def by simp
  have "hI23_Deq_Call_Ret_Balanced s'" using hI23_Deq_Call_Ret_Balanced_s unfolding hI23_Deq_Call_Ret_Balanced_def by simp
  
  have "hI24_HB_Implies_Idx_Order s'" 
  proof -
    have "CState.Q_arr (fst s') = CState.Q_arr (fst s)" using step_facts(3) unfolding Q_arr_def by simp
    thus ?thesis using hI24_HB_Implies_Idx_Order_s unfolding hI24_HB_Implies_Idx_Order_def HB_Act_def step_facts(1) by simp
  qed
  
  have "hI25_Enq_Call_Ret_Balanced s'" using hI25_Enq_Call_Ret_Balanced_s unfolding hI25_Enq_Call_Ret_Balanced_def by auto

  have "hI26_DeqRet_D4_Mutex s'"
  proof -
    have "\<forall>p' a sn. a \<in> Val \<longrightarrow> \<not> (DeqRetInHis s' p' a sn \<and> program_counter s' p' = ''D4'' \<and> x_var s' p' = a)"
    proof (intro allI impI)
      fix p' a sn assume a_val: "a \<in> Val"
      show "\<not> (DeqRetInHis s' p' a sn \<and> program_counter s' p' = ''D4'' \<and> x_var s' p' = a)"
      proof (cases "p' = p")
        case True
        have "program_counter s' p' = ''D2''" using True step_facts(13) by simp
        thus ?thesis by simp
      next
        case False
        have "program_counter s' p' = program_counter s p'" using False other_facts(1) by simp
        moreover have "x_var s' p' = x_var s p'" using step_facts(6) by simp
        moreover have "DeqRetInHis s' p' a sn = DeqRetInHis s p' a sn" unfolding DeqRetInHis_def using step_facts(1) by simp
        ultimately show ?thesis using hI26_DeqRet_D4_Mutex_s a_val False unfolding hI26_DeqRet_D4_Mutex_def by auto
      qed
    qed
    thus ?thesis unfolding hI26_DeqRet_D4_Mutex_def
      by auto 
  qed

  (* ========================================================== *)
  (* hI27_Pending_PC_Sync under the D1 transition           *)
  (* ========================================================== *)
  have "hI27_Pending_PC_Sync s'"
  proof -
    have pending_deq_eq [simp]: "\<And>q. HasPendingDeq s' q = HasPendingDeq s q"
      unfolding HasPendingDeq_def DeqCallInHis_def Let_def
      using step_facts
      by simp

    have pending_enq_eq [simp]:
      "\<And>q. HasPendingEnq s' q (v_var s' q) = HasPendingEnq s q (v_var s q)"
      unfolding HasPendingEnq_def EnqCallInHis_def Let_def
      using step_facts
      by simp

    show ?thesis
      unfolding hI27_Pending_PC_Sync_def
    proof (intro conjI allI impI)
      fix q
      assume pend': "HasPendingDeq s' q"
      hence pend: "HasPendingDeq s q" by simp

      show "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof (cases "q = p")
        case True
        then show ?thesis
          using step_facts(14)
          by simp
      next
        case False
        have "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
          using hI19_s pend
          unfolding hI27_Pending_PC_Sync_def
          by blast
        moreover have "program_counter s' q = program_counter s q"
          using False other_facts(1)
          by simp
        ultimately show ?thesis
          by simp
      qed
    next
      fix q
      assume pend': "HasPendingEnq s' q (v_var s' q)"
      hence pend: "HasPendingEnq s q (v_var s q)"
        using pending_enq_eq by auto 

      show "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
      proof (cases "q = p")
        case True
        have "program_counter s p \<in> {''E1'', ''E2'', ''E3''}"
          using hI19_s pend
          unfolding hI27_Pending_PC_Sync_def
          using True by auto
        moreover have "program_counter s p = ''D1''"
          using step_facts(13)
          by simp
        ultimately show ?thesis
          by simp
      next
        case False
        have "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
          using hI19_s pend
          unfolding hI27_Pending_PC_Sync_def
          by blast
        moreover have "program_counter s' q = program_counter s q"
          using False other_facts(1)
          by simp
        ultimately show ?thesis
          by simp
      qed
    qed
  qed

  (* ========================================================== *)
  (* hI28_Fresh_Enq_Immunity under the D1 transition        *)
  (* ========================================================== *)
  have "hI28_Fresh_Enq_Immunity s'"
  proof -
    have deqret_eq [simp]: "\<And>q a sn. DeqRetInHis s' q a sn = DeqRetInHis s q a sn"
      unfolding DeqRetInHis_def
      using step_facts
      by simp

    show ?thesis
      unfolding hI28_Fresh_Enq_Immunity_def
    proof (intro allI impI)
      fix p_enq q_deq a sn
      assume prems:
        "program_counter s' p_enq \<in> {''E1'', ''E2''} \<and>
         v_var s' p_enq = a \<and>
         a \<noteq> BOT"

      then have pc_e_prime: "program_counter s' p_enq \<in> {''E1'', ''E2''}"
        and v_eq_prime: "v_var s' p_enq = a"
        and a_not_bot: "a \<noteq> BOT"
        by auto

      show "\<not> DeqRetInHis s' q_deq a sn"
      proof
        assume his_prime: "DeqRetInHis s' q_deq a sn"

        show False
        proof (cases "p_enq = p")
          case True
          have "program_counter s' p = ''D2''"
            using step_facts(14)
            by simp
          with pc_e_prime True show False
            by simp
        next
          case False
          have old_pc: "program_counter s p_enq \<in> {''E1'', ''E2''}"
            using pc_e_prime False other_facts(1)
            by simp
          have old_v: "v_var s p_enq = a"
            using v_eq_prime step_facts(5)
            by simp
          have his_s: "DeqRetInHis s q_deq a sn"
            using his_prime
            by simp

          from hI20_s[unfolded hI28_Fresh_Enq_Immunity_def] old_pc old_v a_not_bot his_s
          show False
            by blast
        qed
      qed
    qed
  qed

    (* ========================================================== *)
    (* hI29_E2_Scanner_Immunity under the D1 transition      *)
    (* ========================================================== *)
    have "hI29_E2_Scanner_Immunity s'"
    proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI, goal_cases)
      case (1 p_enq a q_deq)
      
      (* Step 1: unfold the eight core premises of the target. *)
      from 1 have pc_e': "program_counter s' p_enq = ''E2''" by blast
      from 1 have inqa': "InQBack s' a" by blast
      from 1 have tba': "TypeB s' a" by blast
      from 1 have pend_q': "HasPendingDeq s' q_deq" by blast
      from 1 have pc_q_D3': "program_counter s' q_deq = ''D3''" by blast
      from 1 have idx1': "Idx s' a < j_var s' q_deq" by blast
      from 1 have idx2': "j_var s' q_deq \<le> i_var s' p_enq" by blast
      from 1 have idx3': "i_var s' p_enq < l_var s' q_deq" by blast

      (* Step 2: collect the preserved global-state facts. *)
      have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast
      
      (* Step 3: isolate process p, whose post-state is D2 rather than E2 or D3. *)
      have p_enq_neq_p: "p_enq \<noteq> p"
      proof
        assume "p_enq = p"
        with pc_e' have "program_counter s' p = ''E2''" by simp
        moreover have "program_counter s' p = ''D2''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed
      
      have q_deq_neq_p: "q_deq \<noteq> p"
      proof
        assume "q_deq = p"
        with pc_q_D3' have "program_counter s' p = ''D3''" by simp
        moreover have "program_counter s' p = ''D2''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed

      (* Step 4: transport all physical facts back to the pre-state. *)
      have pc_e_s: "program_counter s p_enq = ''E2''" using pc_e' p_enq_neq_p step_facts pc_eqs by auto
      have pc_q_s: "program_counter s q_deq = ''D3''" using pc_q_D3' q_deq_neq_p step_facts pc_eqs by auto
      
      have inqa_s: "InQBack s a" using inqa' step_facts unfolding InQBack_def by auto
      have tba_s: "TypeB s a" using tba' step_facts pc_eqs unfolding TypeB_def QHas_def by auto
      
      (* Step 4a: the D1 step only appends the dequeue call of p, so it does not affect pending facts for q_deq \<noteq> p. *)
      have s_var_eq: "s_var s' = s_var s" unfolding s_var_def using step_facts
        by (simp add: s_var_def) 
      have pend_q_s: "HasPendingDeq s q_deq"
      proof -
        have "HasPendingDeq s' q_deq = HasPendingDeq s q_deq"
          unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
          using step_facts s_var_eq q_deq_neq_p by (auto simp: mk_act_def act_pid_def)
        thus ?thesis using pend_q' by simp
      qed
      
      (* Step 4b: transport all index and bound constraints. *)
      have idx_eq: "\<And>x. Idx s' x = Idx s x" using step_facts unfolding Idx_def AtIdx_def by auto
      have j_var_eq: "j_var s' q_deq = j_var s q_deq" using q_deq_neq_p step_facts by auto
      have l_var_eq: "l_var s' q_deq = l_var s q_deq" using q_deq_neq_p step_facts by auto
      have i_var_eq: "i_var s' p_enq = i_var s p_enq" using p_enq_neq_p step_facts by auto
      have v_var_eq: "v_var s' p_enq = v_var s p_enq" using p_enq_neq_p step_facts by auto

      have bound1: "Idx s a < j_var s q_deq" using idx1' idx_eq j_var_eq by simp
      have bound2: "j_var s q_deq \<le> i_var s p_enq" using idx2' j_var_eq i_var_eq by simp
      have bound3: "i_var s p_enq < l_var s q_deq" using idx3' i_var_eq l_var_eq by simp

      (* Step 5: invoke the pre-state invariant with the transported premises. *)
      have no_hb_old: "\<not> HB_EnqRetCall s a (v_var s p_enq)"
        using hI21_s pc_e_s inqa_s tba_s pend_q_s pc_q_s bound1 bound2 bound3
        unfolding hI29_E2_Scanner_Immunity_def by blast

      (* Step 6: discharge the HB obligations using the appended-call characterization. *)
      show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
      proof -
        have hb_stable: "HB_EnqRetCall s' a (v_var s' p_enq) = HB_EnqRetCall s a (v_var s p_enq)"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
          using step_facts v_var_eq by auto
        thus ?thesis using no_hb_old by simp
      qed
    qed

    (* ========================================================== *)
    (* hI30_Ticket_HB_Immunity under the D1 transition       *)
    (* D1 is an internal step: the history and ticket structure remain unchanged. *)
    (* ========================================================== *)
    have "hI30_Ticket_HB_Immunity s'"
    proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI, goal_cases)
      case (1 b q)
      
      (* Step 1: unfold the five core premises of the target. *)
      from 1 have pc_q': "program_counter s' q \<in> {''E2'', ''E3''}" by blast
      from 1 have inqb': "InQBack s' b" by blast
      from 1 have b_not_bot': "b \<noteq> BOT" by blast
      from 1 have b_neq_v': "b \<noteq> v_var s' q" by blast
      from 1 have hb': "HB_EnqRetCall s' b (v_var s' q)" by blast

      (* Step 2: collect the corresponding pre-state invariant facts. *)
      have hI22_s: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast

      (* Step 3: isolate process p, which moves to D2 and hence cannot witness E2/E3-side premises. *)
      have q_neq_p: "q \<noteq> p"
      proof
        assume "q = p"
        with pc_q' have "program_counter s' p \<in> {''E2'', ''E3''}" by simp
        moreover have "program_counter s' p = ''D2''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed

      (* Step 4: transport all physical facts back to the pre-state. *)
      (* Use q \<noteq> p to isolate the unchanged local state. *)
      have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}" 
        using pc_q' q_neq_p step_facts pc_eqs by auto

      have inqb_s: "InQBack s b" using inqb' step_facts unfolding InQBack_def by auto
      
      have v_var_eq: "v_var s' q = v_var s q" using q_neq_p step_facts by auto
      have i_var_eq: "i_var s' q = i_var s q" using q_neq_p step_facts by auto
      
      have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_var_eq by simp

      (* The D1 step is internal, so the global history sequence is unchanged. *)
      have seq_eq: "his_seq s' = his_seq s" using step_facts by simp

      (* Hence the relevant HB predicates are preserved. *)
      have hb_eq: "HB_EnqRetCall s' b (v_var s' q) = HB_EnqRetCall s b (v_var s q)"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
        using seq_eq v_var_eq by simp
      have hb_s: "HB_EnqRetCall s b (v_var s q)" using hb' hb_eq by simp

      have idx_eq: "Idx s' b = Idx s b" unfolding Idx_def AtIdx_def using step_facts by simp

      (* Step 5: invoke the pre-state invariant in its simplified form. *)
      have "Idx s b < i_var s q"
        using hI22_s pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
        unfolding hI30_Ticket_HB_Immunity_def by blast

      (* Step 6: transport the conclusion back to the post-state. *)
      thus "Idx s' b < i_var s' q" using idx_eq i_var_eq by simp
    qed

  have "lI1_Op_Sets_Equivalence s'" using lI1_Op_Sets_Equivalence_s unfolding lI1_Op_Sets_Equivalence_def OPLin_def OP_A_enq_def OP_A_deq_def OP_B_enq_def EnqCallInHis_def DeqCallInHis_def by simp
  have "lI2_Op_Cardinality s'" using lI2_Op_Cardinality_s unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def by simp
  have "lI3_HB_Ret_Lin_Sync s'" using lI3_HB_Ret_Lin_Sync_s unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def EnqRetInHis_def DeqRetInHis_def by simp
  have "lI4_FIFO_Semantics s'" using lI4_FIFO_Semantics_s unfolding lI4_FIFO_Semantics_def by simp
  have "lI5_SA_Prefix s'" using lI5_SA_Prefix_s unfolding lI5_SA_Prefix_def by simp

  have "lI6_D4_Deq_Linearized s'"
  proof (unfold lI6_D4_Deq_Linearized_def, intro allI impI)
    fix q
    assume pc': "program_counter s' q = ''D4''"

    have pc: "program_counter s q = ''D4''"
      using pc'
      by simp

    have "mk_op deq (x_var s q) q (s_var s q) \<in> set (lin_seq s)"
      using lI6_D4_Deq_Linearized_s pc
      unfolding lI6_D4_Deq_Linearized_def
      by blast

    thus "mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s')"
      by simp
  qed
  
    (* ========================================================== *)
    (* lI7_D4_Deq_Deq_HB under the D1 transition              *)
    (* ========================================================== *)
    have "lI7_D4_Deq_Deq_HB s'"
    proof -
      (* Step 1: establish the key PC mapping facts. *)
      have pc_map: "\<And>q. (program_counter s' q = ''D4'') \<longleftrightarrow> (program_counter s q = ''D4'')"
        using step_facts(13) other_facts(1) by (auto simp: ext)
      
      (* Step 2: unfold the relevant definitions and let SMT align the indices. *)
      show ?thesis
        using lI7_D4_Deq_Deq_HB_s pc_map step_facts
        unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def HB_consistent_def HB_def s_var_def
        by (smt (verit) fun_upd_other)
    qed


  (* ========================================================== *)
  (* lI8_D3_Deq_Returned under the D1 transition            *)
  (* ========================================================== *)
  have "lI8_D3_Deq_Returned s'"
    unfolding lI8_D3_Deq_Returned_def
  proof (intro allI impI)
    fix q k
    assume q_D3: "program_counter s' q = ''D3''"
       and k_bound: "k < length (lin_seq s')"
       and act_match: "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
       
    have "q \<noteq> p"
    proof
      assume "q = p"
      with q_D3 step_facts(13) show False by simp
    qed
    hence pc_q: "program_counter s q = ''D3''" using q_D3 pc_eqs by simp
    
    have old_inv: "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
      using lI8_D3_Deq_Returned_s pc_q k_bound act_match unfolding step_facts
      by (simp add: lI8_D3_Deq_Returned_def) 
      
    thus "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
      unfolding DeqRetInHis_def using step_facts by simp
  qed

  (* ========================================================== *)
  (* lI9_D1_D2_Deq_Returned under the D1 transition         *)
  (* ========================================================== *)
  have "lI9_D1_D2_Deq_Returned s'"
    unfolding lI9_D1_D2_Deq_Returned_def
  proof (intro allI impI)
    fix q k
    assume q_D12: "program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2''"
       and k_bound: "k < length (lin_seq s')"
       and act_match: "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
       
    have pc_q: "program_counter s q = ''D1'' \<or> program_counter s q = ''D2''"
    proof (cases "q = p")
      case True thus ?thesis using step_facts(12) by simp
    next
      case False thus ?thesis using q_D12 pc_eqs by simp
    qed
    
    have old_inv: "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
      using lI9_D1_D2_Deq_Returned_s pc_q k_bound act_match unfolding step_facts
      using lI9_D1_D2_Deq_Returned_def by blast 
      
    thus "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
      unfolding DeqRetInHis_def using step_facts by simp
  qed

    (* ========================================================== *)
    (* lI10_D4_Enq_Deq_HB and lI11_D4_Deq_Unique under D1    *)
    (* ========================================================== *)
    have "lI10_D4_Enq_Deq_HB s'"
      using lI10_D4_Enq_Deq_HB_s step_facts other_facts unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def s_var_def
      using HB_Act_def \<open>lI3_HB_Ret_Lin_Sync s'\<close> lI3_HB_Ret_Lin_Sync_def by blast

have "lI11_D4_Deq_Unique s'"
proof -
  have deqret_eq [simp]: "\<And>q a sn. DeqRetInHis s' q a sn = DeqRetInHis s q a sn"
    unfolding DeqRetInHis_def
    using step_facts
    by simp

  show ?thesis
    unfolding lI11_D4_Deq_Unique_def
  proof (intro allI impI)
    fix q
    assume pc_q_s': "program_counter s' q = ''D4''"

    have pc_q_s: "program_counter s q = ''D4''"
      using pc_q_s'
      by simp

    from lI11_D4_Deq_Unique_s[unfolded lI11_D4_Deq_Unique_def] pc_q_s
    show "\<exists>k2 < length (lin_seq s').
            lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
            (\<forall>k3 < length (lin_seq s').
               op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2
               \<longrightarrow> k3 < k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3)))"
      by simp
  qed
qed


  have "data_independent (lin_seq s')" using di_lin_s step_facts(2) by simp
  have "Simulate_PC s'" using STEP unfolding Sys_D1_def by simp

  (* ========== 5. Assemble the final invariant package ========== *)
  show ?thesis 
    unfolding system_invariant_def
    using `Simulate_PC s'` `TypeOK s'` `sI1_Zero_Index_BOT s'`
    `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'` `hI3_L0_E_Phase_Bounds s'`
    `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'` `sI12_D3_Scanned_Prefix s'` `hI4_X_var_Lin_Sync s'`
    `hI7_His_WF s'` `hI8_Val_Unique s'` `hI5_SSN_Unique s'` `hI6_SSN_Order s'` 
    `hI9_Deq_Ret_Unique s'` `hI10_Enq_Call_Existence s'` `hI11_Enq_Ret_Existence s'` `hI12_D_Phase_Pending_Deq s'` `hI13_Qback_Deq_Sync s'` `hI14_Pending_Enq_Qback_Exclusivity s'` `hI15_Deq_Result_Exclusivity s'` `hI16_BO_BT_No_HB s'` `hI17_BT_BT_No_HB s'` `hI18_Idx_Order_No_Rev_HB s'` `hI19_Scanner_Catches_Later_Enq s'` `hI20_Enq_Val_Valid s'` `hI21_Ret_Implies_Call s'` `hI22_Deq_Local_Pattern s'` `hI23_Deq_Call_Ret_Balanced s'` `hI24_HB_Implies_Idx_Order s'` `hI25_Enq_Call_Ret_Balanced s'`  `hI26_DeqRet_D4_Mutex s'`
    `hI27_Pending_PC_Sync s'` `hI28_Fresh_Enq_Immunity s'` `hI29_E2_Scanner_Immunity s'` `hI30_Ticket_HB_Immunity s'` 
    `lI1_Op_Sets_Equivalence s'` `lI2_Op_Cardinality s'` `lI3_HB_Ret_Lin_Sync s'` `lI4_FIFO_Semantics s'` `lI5_SA_Prefix s'` `lI6_D4_Deq_Linearized s'` `lI7_D4_Deq_Deq_HB s'` `lI8_D3_Deq_Returned s'` `lI9_D1_D2_Deq_Returned s'` `lI10_D4_Enq_Deq_HB s'` `lI11_D4_Deq_Unique s'`
    `data_independent (lin_seq s')`
    by blast
qed


end