(* ========================================================== *)
(* Preservation of the system invariant for the D4 transition *)
(* ========================================================== *)
theory D4Proof
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    Termination
    DeqLib
    D4Lemmas
begin

lemma D4_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_D4 p s s'"  
  shows "system_invariant s'"
proof -   
  (* Step 0: keep the bridge definitions available for local rewriting. *)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  (* Step 1: extract the full invariant package from the pre-state. *)
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
   and hI24_HB_Implies_Idx_Order_s: "hI24_HB_Implies_Idx_Order s" and hI25_Enq_Call_Ret_Balanced_s: "hI25_Enq_Call_Ret_Balanced s"  and hI26_DeqRet_D4_Mutex_s: "hI26_DeqRet_D4_Mutex s"
   and hI19_s: "hI27_Pending_PC_Sync s" and hI20_s: "hI28_Fresh_Enq_Immunity s"
   and hI21_s: "hI29_E2_Scanner_Immunity s" and hI22_s: "hI30_Ticket_HB_Immunity s" (* Extract the ticket-order invariant explicitly. *)
   and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" 
   and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" and lI5_SA_Prefix_s: "lI5_SA_Prefix s" and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" 
   and lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" and lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s" and lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s" 
   and lI10_D4_Enq_Deq_HB_s: "lI10_D4_Enq_Deq_HB s" and lI11_D4_Deq_Unique_s: "lI11_D4_Deq_Unique s" 
   and di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  (* Step 2: unfold Sys_D4 and derive the frame facts of the transition. *)
  have step_facts [simp]:
    "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
    "v_var s' = v_var s" "i_var s' = i_var s"
    "X_var s' = X_var s" "V_var s' = V_var s"
    "lin_seq s' = lin_seq s"
    "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    "program_counter s p = ''D4'' "
    "program_counter s' p = ''L0'' "
    "j_var s' p = BOT" "l_var s' p = BOT" "x_var s' p = BOT" 
    "s_var s' p = s_var s p + 1"  
  proof -
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast

    show "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s" "v_var s' = v_var s" "i_var s' = i_var s" 
         "X_var s' = X_var s" "V_var s' = V_var s" "program_counter s p = ''D4'' " 
         "program_counter s' p = ''L0'' " "j_var s' p = BOT" "l_var s' p = BOT" 
         "x_var s' p = BOT" "s_var s' p = s_var s p + 1"
      using STEP u_steps
      unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
      
    show "lin_seq s' = lin_seq s"
      using u_steps unfolding U_D3_def U_D4_def bridge by auto

    show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
      using u_steps unfolding U_D3_def U_D4_def bridge by auto
  qed

  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> j_var s' q = j_var s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> l_var s' q = l_var s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q" 
  proof -
    fix q assume "q \<noteq> p"
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    thus "program_counter s' q = program_counter s q"
         "j_var s' q = j_var s q"
         "l_var s' q = l_var s q"
         "x_var s' q = x_var s q"
         "s_var s' q = s_var s q"
      using STEP \<open>q \<noteq> p\<close>
      unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
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

  (* Step 3: show that the derived classification sets are preserved. *)
  have typeb_eq: "\<And>x. TypeB s' x = TypeB s x"
  proof -
    fix x
    have "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow> (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
      using pc_eqs step_facts by auto
    thus "TypeB s' x = TypeB s x" unfolding TypeB_def QHas_def step_facts by simp
  qed

  have typebt_eq: "\<And>x. TypeBT s' x = TypeBT s x"
  proof -
    fix x
    have idx_eq: "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def step_facts by simp
    have "(\<exists>q. program_counter s' q = ''D3'' \<and> 
             j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> 
             (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)) \<longleftrightarrow>
        (\<exists>q. program_counter s q = ''D3'' \<and> 
             j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> 
             (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT))"
      (is "(\<exists>q. ?P' q) \<longleftrightarrow> (\<exists>q. ?P q)")
    proof
    assume "\<exists>q. ?P' q"
    then obtain q where q_prop: "?P' q" by blast
    have "q \<noteq> p" using q_prop step_facts(10) by auto
    with q_prop other_facts step_facts idx_eq show "\<exists>q. ?P q"
      by (metis (no_types, lifting))
    next
    assume "\<exists>q. ?P q"
    then obtain q where q_prop: "?P q" by blast
    have "q \<noteq> p" using q_prop step_facts(9) by auto
    with q_prop other_facts step_facts idx_eq show "\<exists>q. ?P' q"
      by (metis (no_types, lifting))
    qed
    thus "TypeBT s' x = TypeBT s x" unfolding TypeBT_def InQBack_def typeb_eq idx_eq step_facts by simp
  qed

  have typea_eq: "\<And>x. TypeA s' x = TypeA s x"
    unfolding TypeA_def QHas_def using step_facts
    by (simp add: InQBack_def) 

  have typebo_eq: "\<And>x. TypeBO s' x = TypeBO s x"
    unfolding TypeBO_def QHas_def using pc_eqs step_facts
    using typeb_eq typebt_eq by presburger

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


  (* ------------------------------------------------------------------------- *)
  (* Step 4: preserve the concrete-state invariants. *)
  (* ------------------------------------------------------------------------- *)
  have "TypeOK s'"
  proof -
    have pc_ok: "\<forall>q. program_counter s' q \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
      using TypeOK_s pc_eqs unfolding TypeOK_def by auto

    have vars_ok: "\<forall>q. (j_var s' q = BOT \<or> j_var s' q \<in> Val) \<and> 
                       (l_var s' q = BOT \<or> l_var s' q \<in> Val) \<and> 
                       (x_var s' q = BOT \<or> x_var s' q \<in> Val) \<and>
                       (v_var s' q = BOT \<or> v_var s' q \<in> Val)"
      using TypeOK_s step_facts other_facts unfolding TypeOK_def
      by (metis Un_iff empty_iff insert_iff) 

    have s_ok: "\<forall>q. s_var s' q \<in> Val"
    proof
      fix q
      show "s_var s' q \<in> Val"
      proof (cases "q = p")
        case True
        from TypeOK_s have "s_var s p \<in> Val" unfolding TypeOK_def by auto
        hence "s_var s p > 0" unfolding Val_def by simp
        hence "s_var s p + 1 > 0" by simp
        with True step_facts(14) show ?thesis unfolding Val_def by simp
      next
        case False
        then show ?thesis using other_facts TypeOK_s unfolding TypeOK_def by auto
      qed
    qed

    show ?thesis 
      using TypeOK_s pc_ok vars_ok s_ok step_facts 
      unfolding TypeOK_def by auto
  qed

  have "sI1_Zero_Index_BOT s'" using sI1_Zero_Index_BOT_s unfolding sI1_Zero_Index_BOT_def by simp
  have "sI2_X_var_Upper_Bound s'" using sI2_X_var_Upper_Bound_s unfolding sI2_X_var_Upper_Bound_def using step_facts by auto
  have "sI3_E2_Slot_Exclusive s'" using sI3_E2_Slot_Exclusive_s unfolding sI3_E2_Slot_Exclusive_def using pc_eqs step_facts other_facts by auto
  have "sI4_E3_Qback_Written s'" using sI4_E3_Qback_Written_s unfolding sI4_E3_Qback_Written_def using pc_eqs step_facts other_facts by auto
  have "sI5_D2_Local_Bound s'" using sI5_D2_Local_Bound_s unfolding sI5_D2_Local_Bound_def using pc_eqs step_facts other_facts by auto
  have "sI6_D3_Scan_Pointers s'" using sI6_D3_Scan_Pointers_s unfolding sI6_D3_Scan_Pointers_def using pc_eqs step_facts other_facts by auto
  have "sI7_D4_Deq_Result s'" using sI7_D4_Deq_Result_s unfolding sI7_D4_Deq_Result_def using pc_eqs step_facts other_facts by auto
  have "sI8_Q_Qback_Sync s'" using sI8_Q_Qback_Sync_s unfolding sI8_Q_Qback_Sync_def using step_facts by simp
  have "sI9_Qback_Discrepancy_E3 s'" using sI9_Qback_Discrepancy_E3_s unfolding sI9_Qback_Discrepancy_E3_def using pc_eqs step_facts other_facts by auto
  have "sI10_Qback_Unique_Vals s'" using sI10_Qback_Unique_Vals_s unfolding sI10_Qback_Unique_Vals_def using step_facts by simp


  (* Preserve the global SSN bound invariant. *)
  have hI2_SSN_Bounds_s': "hI2_SSN_Bounds s'"
    using hI2_SSN_Bounds_D4_step[OF INV STEP] .

  have "hI3_L0_E_Phase_Bounds s'" 
    using hI3_L0_E_Phase_Bounds_D4_step[OF INV STEP hI2_SSN_Bounds_s'] .

  (* ========================================================================= *)
  (* Preserve sI11_x_var_Scope across the D4 transition.                     *)
  (* ========================================================================= *)
  have "sI11_x_var_Scope s'"
    using sI11_x_var_Scope_D4_step[OF sI11_x_var_Scope_s STEP] .

(* Pending enqueue operations remain pending after the appended dequeue return. *)
  have "hI1_E_Phase_Pending_Enq s'"
    using hI1_E_Phase_Pending_Enq_D4_step[OF hI1_E_Phase_Pending_Enq_s STEP] .

  have "sI12_D3_Scanned_Prefix s'" using sI12_D3_Scanned_Prefix_s unfolding sI12_D3_Scanned_Prefix_def using pc_eqs step_facts other_facts by auto

  (* ========================================================================= *)
  (* Preserve hI4_X_var_Lin_Sync across the D4 transition.                  *)
  (* ========================================================================= *)
  have "hI4_X_var_Lin_Sync s'"
    using hI4_X_var_Lin_Sync_D4_step[OF hI4_X_var_Lin_Sync_s STEP] .

  (* ------------------------------------------------------------------------- *)
  (* Step 5: preserve the history and linearization invariants after list append. *)
  (* ------------------------------------------------------------------------- *)

  have "hI7_His_WF s'"
    unfolding hI7_His_WF_def Let_def
  proof (intro allI impI)
    fix k
    assume k_lt: "k < length (his_seq s')"
    assume ret_cond: "act_cr (his_seq s' ! k) = ret"
    
    have len_eq: "length (his_seq s') = length (his_seq s) + 1" 
      using step_facts by simp
      
    consider (old) "k < length (his_seq s)" | (new) "k = length (his_seq s)"
      using k_lt len_eq by linarith
      
    thus "\<exists>j<k. act_pid (his_seq s' ! j) = act_pid (his_seq s' ! k) \<and>
                act_ssn (his_seq s' ! j) = act_ssn (his_seq s' ! k) \<and>
                act_name (his_seq s' ! j) = act_name (his_seq s' ! k) \<and>
                act_cr (his_seq s' ! j) = call \<and>
                (if act_name (his_seq s' ! k) = enq 
                 then act_val (his_seq s' ! j) = act_val (his_seq s' ! k) 
                 else act_val (his_seq s' ! j) = BOT)"
    proof cases
      case old
      have k_old: "k < length (his_seq s)" by fact
      have ret_old: "act_cr (his_seq s ! k) = ret"
        using old ret_cond step_facts by (simp add: nth_append)
        
      from hI7_His_WF_s[unfolded hI7_His_WF_def Let_def, rule_format, OF k_old ret_old]
      obtain j where j_props:
        "j < k"
        "act_pid (his_seq s ! j) = act_pid (his_seq s ! k)"
        "act_ssn (his_seq s ! j) = act_ssn (his_seq s ! k)"
        "act_name (his_seq s ! j) = act_name (his_seq s ! k)"
        "act_cr (his_seq s ! j) = call"
        "(if act_name (his_seq s ! k) = enq then act_val (his_seq s ! j) = act_val (his_seq s ! k) else act_val (his_seq s ! j) = BOT)"
        by auto
        
      show ?thesis
        apply (intro exI[where x=j])
        using j_props old step_facts 
        by (auto simp: nth_append)
        
    next
      case new
      have e_k: "his_seq s' ! k = mk_act deq (x_var s p) p (s_var s p) ret"
        using new step_facts by (simp add: nth_append)
        
      have "HasPendingDeq s p"
        using hI12_D_Phase_Pending_Deq_s step_facts pc_eqs unfolding hI12_D_Phase_Pending_Deq_def by auto
      then obtain call_e where call_in: "call_e \<in> set (his_seq s)"
        and call_def: "call_e = mk_act deq BOT p (s_var s p) call"
        unfolding HasPendingDeq_def DeqCallInHis_def Let_def 
        by (force simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

      from call_in obtain j where j_props:
        "j < length (his_seq s)" "his_seq s ! j = call_e"
        by (meson in_set_conv_nth)

      have p1: "j < k" using j_props(1) new by simp

      have e_j: "his_seq s' ! j = mk_act deq BOT p (s_var s p) call"
        using j_props step_facts call_def by (simp add: nth_append)
      
      show ?thesis
        apply (intro exI[where x=j])
        using p1 e_k e_j
        by (simp add: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    qed
  qed

  have "hI8_Val_Unique s'" 
    using hI8_Val_Unique_s unfolding hI8_Val_Unique_def 
    using step_facts(8) by (auto simp: nth_append mk_act_def act_name_def act_cr_def)

  have "hI6_SSN_Order s'"
    unfolding hI6_SSN_Order_def
  proof (intro allI impI)
    fix i j
    assume bounds: "i < length (his_seq s')" "j < length (his_seq s')"
    assume props_raw: "i < j \<and> act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
    
    have props: "i < j" "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
      using props_raw by auto

    have len_eq: "length (his_seq s') = length (his_seq s) + 1" 
      using step_facts(8) by simp

    consider (both_old) "j < length (his_seq s)" 
           | (i_old_j_new) "i < length (his_seq s)" "j = length (his_seq s)"
      using bounds props(1) len_eq by linarith

    thus "act_ssn (his_seq s' ! i) < act_ssn (his_seq s' ! j) \<or>
          (act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j) \<and> 
           act_cr (his_seq s' ! i) = call \<and> act_cr (his_seq s' ! j) = ret)"
    proof cases
      case both_old
      thus ?thesis using hI6_SSN_Order_s unfolding hI6_SSN_Order_def 
        using bounds props step_facts(8) by (auto simp: nth_append)
    next
      case i_old_j_new
      have j_is_new: "his_seq s' ! j = mk_act deq (x_var s p) p (s_var s p) ret"
        using i_old_j_new step_facts(8) by (simp add: nth_append)
      hence pid_j: "act_pid (his_seq s' ! j) = p"
        and ssn_j: "act_ssn (his_seq s' ! j) = s_var s p"
        and cr_j:  "act_cr (his_seq s' ! j) = ret"
        by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)

      from props(2) pid_j have pid_i: "act_pid (his_seq s' ! i) = p" by simp
      have i_is_old: "his_seq s' ! i = his_seq s ! i"
        using i_old_j_new step_facts(8) by (simp add: nth_append)

      have ssn_bound: "act_ssn (his_seq s ! i) \<le> s_var s p"
        using hI2_SSN_Bounds_s i_old_j_new(1) pid_i i_is_old unfolding hI2_SSN_Bounds_def by auto

      have "act_ssn (his_seq s' ! i) < s_var s p \<or> 
            (act_ssn (his_seq s' ! i) = s_var s p \<and> act_cr (his_seq s' ! i) = call)"
      proof (cases "act_ssn (his_seq s ! i) = s_var s p")
        case False
        thus ?thesis using ssn_bound i_is_old by simp
      next
        case True
        have "act_cr (his_seq s' ! i) = call"
        proof (rule ccontr)
          assume "act_cr (his_seq s' ! i) \<noteq> call"
          hence "act_cr (his_seq s ! i) = ret" 
            using i_is_old by (cases "act_cr (his_seq s ! i)") auto

          from hI12_D_Phase_Pending_Deq_s step_facts(9) have pending: "HasPendingDeq s p"
            unfolding hI12_D_Phase_Pending_Deq_def by blast
            
          from pending have no_ret: "\<forall>e \<in> set (his_seq s). act_pid e = p \<and> act_ssn e = s_var s p \<longrightarrow> act_cr e \<noteq> ret"
            unfolding HasPendingDeq_def DeqRetInHis_def Let_def by auto

          have "his_seq s ! i \<in> set (his_seq s)" using i_old_j_new(1) by simp
          with pid_i i_is_old True have "act_pid (his_seq s ! i) = p" "act_ssn (his_seq s ! i) = s_var s p" by auto
          with no_ret have "act_cr (his_seq s ! i) \<noteq> ret"
            by (simp add: \<open>his_seq s ! i \<in> set (his_seq s)\<close>)
          thus False using \<open>act_cr (his_seq s ! i) = ret\<close> by contradiction
        qed
        thus ?thesis using True i_is_old by simp
      qed
      thus ?thesis using ssn_j cr_j by auto
    qed
  qed

  have "hI5_SSN_Unique s'"
    unfolding hI5_SSN_Unique_def
  proof (intro allI impI)
    fix i j
    assume bounds: "i < length (his_seq s')" "j < length (his_seq s')"
    
    assume props_raw: "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j) \<and>
                       act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j) \<and>
                       act_cr (his_seq s' ! i) = act_cr (his_seq s' ! j)"
    
    have props: "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
                "act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j)"
                "act_cr (his_seq s' ! i) = act_cr (his_seq s' ! j)"
      using props_raw by auto

    have len_eq: "length (his_seq s') = length (his_seq s) + 1" 
      using step_facts(8) by simp

    let ?L = "length (his_seq s)"
    consider (both_old) "i < ?L" "j < ?L"
           | (i_old_j_new) "i < ?L" "j = ?L"
           | (i_new_j_old) "i = ?L" "j < ?L"
           | (both_new) "i = ?L" "j = ?L"
      using bounds len_eq by linarith

    thus "i = j"
    proof cases
      case both_old
      thus ?thesis using hI5_SSN_Unique_s props bounds step_facts(8) 
        unfolding hI5_SSN_Unique_def by (auto simp: nth_append)
    next
      case i_old_j_new
      have j_is_new: "his_seq s' ! j = mk_act deq (x_var s p) p (s_var s p) ret"
        using i_old_j_new step_facts(8) by (simp add: nth_append)
      hence pid_j: "act_pid (his_seq s' ! j) = p"
        and ssn_j: "act_ssn (his_seq s' ! j) = s_var s p"
        and cr_j:  "act_cr (his_seq s' ! j) = ret"
        by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)
      
      from props pid_j ssn_j cr_j have i_props:
        "act_pid (his_seq s' ! i) = p"
        "act_ssn (his_seq s' ! i) = s_var s p"
        "act_cr (his_seq s' ! i) = ret"
        by simp_all

      have i_is_old: "his_seq s' ! i = his_seq s ! i"
        using i_old_j_new step_facts(8) by (simp add: nth_append)
      have i_in_set: "his_seq s ! i \<in> set (his_seq s)"
        using i_old_j_new by simp

      from hI12_D_Phase_Pending_Deq_s step_facts(9) have pending: "HasPendingDeq s p"
        unfolding hI12_D_Phase_Pending_Deq_def by blast
      from pending have no_ret: "\<forall>e \<in> set (his_seq s). act_pid e = p \<and> act_ssn e = s_var s p \<longrightarrow> act_cr e \<noteq> ret"
        unfolding HasPendingDeq_def DeqRetInHis_def Let_def by auto

      have "act_cr (his_seq s ! i) \<noteq> ret"
        using no_ret i_in_set i_props(1) i_props(2) i_is_old by simp
      thus ?thesis using i_props(3) i_is_old
        by simp 
    next
      case i_new_j_old
      have i_is_new: "his_seq s' ! i = mk_act deq (x_var s p) p (s_var s p) ret"
        using i_new_j_old step_facts(8) by (simp add: nth_append)
      hence pid_i: "act_pid (his_seq s' ! i) = p"
        and ssn_i: "act_ssn (his_seq s' ! i) = s_var s p"
        and cr_i:  "act_cr (his_seq s' ! i) = ret"
        by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)
      
      from props pid_i ssn_i cr_i have j_props:
        "act_pid (his_seq s' ! j) = p"
        "act_ssn (his_seq s' ! j) = s_var s p"
        "act_cr (his_seq s' ! j) = ret"
        by simp_all

      have j_is_old: "his_seq s' ! j = his_seq s ! j"
        using i_new_j_old step_facts(8) by (simp add: nth_append)
      have j_in_set: "his_seq s ! j \<in> set (his_seq s)"
        using i_new_j_old by simp

      from hI12_D_Phase_Pending_Deq_s step_facts(9) have pending: "HasPendingDeq s p"
        unfolding hI12_D_Phase_Pending_Deq_def by blast
      from pending have no_ret: "\<forall>e \<in> set (his_seq s). act_pid e = p \<and> act_ssn e = s_var s p \<longrightarrow> act_cr e \<noteq> ret"
        unfolding HasPendingDeq_def DeqRetInHis_def Let_def by auto

      have "act_cr (his_seq s ! j) \<noteq> ret"
        using no_ret j_in_set j_props(1) j_props(2) j_is_old by simp
      thus ?thesis using j_props(3) j_is_old by simp
    next
      case both_new
      thus ?thesis by simp
    qed
  qed

  have "hI9_Deq_Ret_Unique s'"
    unfolding hI9_Deq_Ret_Unique_def
  proof (intro allI impI)
    fix i j
    assume bounds: "i < length (his_seq s')" "j < length (his_seq s')"
    
    assume props_raw: "act_name (his_seq s' ! i) = deq \<and>
                       act_name (his_seq s' ! j) = deq \<and>
                       act_cr (his_seq s' ! i) = ret \<and>
                       act_cr (his_seq s' ! j) = ret \<and>
                       act_val (his_seq s' ! i) \<noteq> BOT \<and>
                       act_val (his_seq s' ! i) = act_val (his_seq s' ! j)"
                       
    have props: "act_name (his_seq s' ! i) = deq"
                "act_name (his_seq s' ! j) = deq"
                "act_cr (his_seq s' ! i) = ret"
                "act_cr (his_seq s' ! j) = ret"
                "act_val (his_seq s' ! i) \<noteq> BOT"
                "act_val (his_seq s' ! i) = act_val (his_seq s' ! j)"
      using props_raw by auto

    have len_eq: "length (his_seq s') = length (his_seq s) + 1" 
      using step_facts(8) by simp

    let ?L = "length (his_seq s)"
    consider (both_old) "i < ?L" "j < ?L" | (i_new_j_old) "i = ?L" "j < ?L"
           | (i_old_j_new) "i < ?L" "j = ?L" | (both_new) "i = ?L" "j = ?L"
      using bounds len_eq by linarith

    thus "i = j"
    proof cases
      case both_old
      thus ?thesis using hI9_Deq_Ret_Unique_s props bounds step_facts(8) unfolding hI9_Deq_Ret_Unique_def 
        by (auto simp: nth_append)
    next
      case i_new_j_old
      have val_i: "act_val (his_seq s' ! i) = x_var s p"
        using i_new_j_old step_facts(8) by (simp add: nth_append mk_act_def act_val_def)
      
      have old_j_props: "act_name (his_seq s ! j) = deq \<and> act_cr (his_seq s ! j) = ret"
        using props i_new_j_old step_facts(8) by (auto simp: nth_append)
        
      have "act_val (his_seq s ! j) \<noteq> x_var s p"
        using x_var_not_in_old_deq_ret[OF INV step_facts(9) i_new_j_old(2)] old_j_props by simp
        
      have "act_val (his_seq s' ! j) = act_val (his_seq s ! j)"
        using i_new_j_old step_facts(8) by (simp add: nth_append)
        
      thus ?thesis using val_i props(6) \<open>act_val (his_seq s ! j) \<noteq> x_var s p\<close> by simp
    next
      case i_old_j_new
      have val_j: "act_val (his_seq s' ! j) = x_var s p"
        using i_old_j_new step_facts(8) by (simp add: nth_append mk_act_def act_val_def)
        
      have old_i_props: "act_name (his_seq s ! i) = deq \<and> act_cr (his_seq s ! i) = ret"
        using props i_old_j_new step_facts(8) by (auto simp: nth_append)
        
      have "act_val (his_seq s ! i) \<noteq> x_var s p"
        using x_var_not_in_old_deq_ret[OF INV step_facts(9) i_old_j_new(1)] old_i_props by simp
        
      have "act_val (his_seq s' ! i) = act_val (his_seq s ! i)"
        using i_old_j_new step_facts(8) by (simp add: nth_append)
        
      thus ?thesis using val_j props(6) \<open>act_val (his_seq s ! i) \<noteq> x_var s p\<close> by simp
    next
      case both_new
      thus ?thesis by simp
    qed
  qed
    
  have "hI10_Enq_Call_Existence s'"
    unfolding hI10_Enq_Call_Existence_def
  proof (intro conjI)
    show "\<forall>q a. (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' q = a) \<longrightarrow> EnqCallInHis s' q a (s_var s' q)"
    proof (intro allI impI)
      fix q a assume prems: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' q = a"
      
      have "q \<noteq> p" using prems step_facts pc_eqs by auto
      
      have "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
        using prems \<open>q \<noteq> p\<close> step_facts pc_eqs by auto
      moreover have "v_var s q = a"
        using prems \<open>q \<noteq> p\<close> step_facts other_facts by auto
      ultimately have "EnqCallInHis s q a (s_var s q)"
        using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def by blast
        
      moreover have "s_var s q = s_var s' q"
        using \<open>q \<noteq> p\<close> step_facts other_facts by auto
      ultimately show "EnqCallInHis s' q a (s_var s' q)"
        using EnqCall_mono[OF _ step_facts(8)] by auto
    qed

    show "\<forall>a. (\<exists>k. Qback_arr s' k = a) \<longrightarrow> (\<exists>q sn. EnqCallInHis s' q a sn)"
    proof (intro allI impI)
      fix a assume "\<exists>k. Qback_arr s' k = a"
      hence "\<exists>k. Qback_arr s k = a" 
        using step_facts other_facts by auto
      then obtain q sn where old_call: "EnqCallInHis s q a sn"
        using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def
        by blast 
        
      have "EnqCallInHis s' q a sn"
        using EnqCall_mono[OF old_call step_facts(8)] by simp
      thus "\<exists>q sn. EnqCallInHis s' q a sn" by blast
    qed
  qed
    
  have "hI11_Enq_Ret_Existence s'"
    unfolding hI11_Enq_Ret_Existence_def
  proof (intro allI impI)
    fix q a sn
    assume prems_raw: "(program_counter s' q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn) \<and>
                       (\<exists>k. Qback_arr s' k = a) \<and> EnqCallInHis s' q a sn"

    have pc_cond_s': "program_counter s' q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn"
      and qback_s': "\<exists>k. Qback_arr s' k = a"
      and call_s': "EnqCallInHis s' q a sn"
      using prems_raw by auto

    have call_in_s: "EnqCallInHis s q a sn"
    proof -
      have "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts(8) by simp
      thus ?thesis using call_s'
        unfolding EnqCallInHis_def Let_def
        by (auto simp: mk_act_def act_name_def)
    qed

    have qback_s: "\<exists>k. Qback_arr s k = a"
      using qback_s' step_facts other_facts by simp

    have pc_cond_s: "program_counter s q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s q \<noteq> a \<or> s_var s q \<noteq> sn"
    proof (cases "q = p")
      case True
      have "program_counter s p = ''D4''" using pc_eqs by auto
      thus ?thesis using True by auto
    next
      case False
      have "program_counter s q = program_counter s' q" using False step_facts pc_eqs by auto
      moreover have "v_var s q = v_var s' q" using False step_facts other_facts by auto
      moreover have "s_var s q = s_var s' q" using False step_facts other_facts by auto
      ultimately show ?thesis using pc_cond_s'
        by metis
    qed

    have "EnqRetInHis s q a sn"
      using hI11_Enq_Ret_Existence_s pc_cond_s qback_s call_in_s unfolding hI11_Enq_Ret_Existence_def by blast

    thus "EnqRetInHis s' q a sn"
    proof -
      have "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts(8) by simp
      thus ?thesis using \<open>EnqRetInHis s q a sn\<close>
        unfolding EnqRetInHis_def Let_def
        by auto
    qed
  qed

  have "hI12_D_Phase_Pending_Deq s'"
    unfolding hI12_D_Phase_Pending_Deq_def Let_def
  proof (intro allI impI)
    fix q
    assume pc_q_s': "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"

    have q_neq_p: "q \<noteq> p"
    proof
      assume "q = p"
      have "program_counter s' p = ''L0''" using step_facts pc_eqs by simp
      with pc_q_s' `q = p` show False by simp
    qed

    have pc_q_s: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using q_neq_p pc_q_s' step_facts pc_eqs by auto
    
    have pending_old: "HasPendingDeq s q"
      using hI12_D_Phase_Pending_Deq_s pc_q_s unfolding hI12_D_Phase_Pending_Deq_def by blast

    show "HasPendingDeq s' q"
      unfolding HasPendingDeq_def Let_def
    proof (intro conjI)
      have s_var_eq: "s_var s' q = s_var s q" 
        using q_neq_p step_facts other_facts by auto
      
      have "DeqCallInHis s q (s_var s q)"
        using pending_old unfolding HasPendingDeq_def Let_def by auto
        
      then obtain call_e where call_in: "call_e \<in> set (his_seq s)"
        and call_def: "call_e = mk_act deq BOT q (s_var s q) call"
        unfolding DeqCallInHis_def Let_def
        by (force simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
        
      hence "call_e \<in> set (his_seq s')"
        using step_facts(8) by auto
        
      show "DeqCallInHis s' q (s_var s' q)"
        using s_var_eq call_def call_in step_facts(8)
        unfolding DeqCallInHis_def Let_def
        by (auto intro: bexI[of _ call_e] 
                 simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

      show "\<forall>e\<in>set (his_seq s'). \<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)"
      proof
        fix e assume "e \<in> set (his_seq s')"
        hence "e \<in> set (his_seq s) \<or> e = mk_act deq (x_var s p) p (s_var s p) ret"
          using step_facts(8) by auto
        thus "\<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)"
        proof
          assume old_e: "e \<in> set (his_seq s)"
          have "\<forall>x\<in>set (his_seq s). \<not> (act_pid x = q \<and> act_ssn x = s_var s q \<and> act_cr x = ret)"
            using pending_old unfolding HasPendingDeq_def DeqRetInHis_def Let_def by auto
          thus ?thesis using old_e s_var_eq by auto
        next
          assume new_e: "e = mk_act deq (x_var s p) p (s_var s p) ret"
          have "act_pid e = p" using new_e by (simp add: mk_act_def act_pid_def)
          thus ?thesis using q_neq_p by simp
        qed
      qed
    qed
  qed

    have "hI13_Qback_Deq_Sync s'"
    proof (rule hI13_Qback_Deq_Sync_D4_step)
      show "hI13_Qback_Deq_Sync s" using hI13_Qback_Deq_Sync_s by simp      
      show "Q_arr s' = Q_arr s" using step_facts by simp      
      show "Qback_arr s' = Qback_arr s" using step_facts by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "program_counter s' = (program_counter s)(p := ''L0'')" 
        using pc_eqs by (auto simp: fun_upd_def)        
      show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q" 
        using other_facts by simp        
      show "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q" 
        using other_facts by simp
    qed

    have "hI14_Pending_Enq_Qback_Exclusivity s'"
    proof (rule hI14_Pending_Enq_Qback_Exclusivity_D4_step)
      show "hI14_Pending_Enq_Qback_Exclusivity s" using hI14_Pending_Enq_Qback_Exclusivity_s by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "program_counter s' = (program_counter s)(p := ''L0'')" 
        using pc_eqs by (auto simp: fun_upd_def)        
      show "Qback_arr s' = Qback_arr s" 
        using step_facts by simp        
      show "\<And>q. q \<noteq> p \<Longrightarrow> i_var s' q = i_var s q" 
        using other_facts by simp        
      show "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q" 
        using other_facts by simp
    qed

    have "hI15_Deq_Result_Exclusivity s'"
    proof (rule hI15_Deq_Result_Exclusivity_D4_step)
      show "hI15_Deq_Result_Exclusivity s" using hI15_Deq_Result_Exclusivity_s by simp      
      show "system_invariant s" using INV by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "program_counter s' = (program_counter s)(p := ''L0'')" 
        using pc_eqs by (auto simp: fun_upd_def)        
      show "Q_arr s' = Q_arr s" 
        using step_facts by simp        
      show "x_var s' p = BOT" 
        using step_facts by simp        
      show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q" 
        using other_facts by simp        
      show "program_counter s p = ''D4''" 
        using step_facts by simp
      show "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q" 
        using other_facts by simp
    qed

    have "hI16_BO_BT_No_HB s'"
    proof (rule hI16_BO_BT_No_HB_D4_step)
      show "hI16_BO_BT_No_HB s" using hI16_BO_BT_No_HB_s by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "SetBO s' = SetBO s"
        using step_facts set_facts 
        unfolding SetBO_def TypeBO_def TypeB_def QHas_def
        by (auto simp: InQBack_def)        
      show "SetBT s' = SetBT s"
        using step_facts set_facts 
        unfolding SetBT_def TypeBT_def TypeB_def QHas_def
        by (auto simp: InQBack_def)
    qed

    have "hI17_BT_BT_No_HB s'"
    proof (rule hI17_BT_BT_No_HB_D4_step)
      show "hI17_BT_BT_No_HB s" using hI17_BT_BT_No_HB_s by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "SetBT s' = SetBT s"
        using step_facts set_facts 
        unfolding SetBT_def TypeBT_def TypeB_def QHas_def
        by (auto simp: InQBack_def)
    qed

    have "hI18_Idx_Order_No_Rev_HB s'"
    proof (rule hI18_Idx_Order_No_Rev_HB_D4_step)
      show "hI18_Idx_Order_No_Rev_HB s" using hI18_Idx_Order_No_Rev_HB_s by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "\<And>x. Idx s' x = Idx s x" 
        using step_facts unfolding Idx_def
        using AtIdx_def by presburger         
      show "\<And>x. InQBack s' x = InQBack s x" 
        using step_facts unfolding InQBack_def by auto        
      show "\<And>i. AtIdx s' i = AtIdx s i" 
        using step_facts unfolding AtIdx_def by auto
    qed
  
    have "hI19_Scanner_Catches_Later_Enq s'"
    proof (rule hI19_Scanner_Catches_Later_Enq_D4_step)
      show "hI19_Scanner_Catches_Later_Enq s" using hI19_Scanner_Catches_Later_Enq_s by simp
      show "system_invariant s" using INV by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "program_counter s' = (program_counter s)(p := ''L0'')" 
        using pc_eqs by (auto simp: fun_upd_def)        
      show "\<And>q. q \<noteq> p \<Longrightarrow> 
        program_counter s' q = program_counter s q \<and> 
        j_var s' q = j_var s q \<and> 
        l_var s' q = l_var s q \<and> 
        s_var s' q = s_var s q"
        using other_facts pc_eqs by auto
      show "\<And>x. Idx s' x = Idx s x" 
        using step_facts 
        unfolding Idx_def AtIdx_def 
        by simp
      show "\<And>x. TypeB s' x = TypeB s x" 
        using set_facts 
        unfolding TypeB_def TypeBT_def TypeBO_def QHas_def 
        by (auto simp: InQBack_def)
        
      (* Align the proof obligations with the updated InQBack stability argument. *)
      show "\<And>x. InQBack s' x = InQBack s x"
        using step_facts unfolding InQBack_def by auto
        
      show "\<And>a b. HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
      proof -
        fix a b
        have seq_eq: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
          using step_facts by simp          
        show "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
          unfolding HB_EnqRetCall_def HB_Act_def
          using seq_eq HB_enq_stable_deq_append
          by meson 
      qed
    qed
  
  have "hI20_Enq_Val_Valid s'" using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def using step_facts(8) by (auto simp: nth_append mk_act_def act_name_def act_val_def)

    have "hI21_Ret_Implies_Call s'"
    proof (rule hI21_Ret_Implies_Call_D4_step)
      show "hI21_Ret_Implies_Call s" using hI21_Ret_Implies_Call_s by simp      
      show "hI12_D_Phase_Pending_Deq s" using hI12_D_Phase_Pending_Deq_s by simp      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp        
      show "program_counter s p = ''D4''" 
        using step_facts by simp
    qed

    have "hI22_Deq_Local_Pattern s'"
    proof (rule hI22_Deq_Local_Pattern_D4_step)
      show "hI22_Deq_Local_Pattern s" using hI22_Deq_Local_Pattern_s by simp
      show "hI12_D_Phase_Pending_Deq s" using hI12_D_Phase_Pending_Deq_s by simp
      show "hI15_Deq_Result_Exclusivity s" using hI15_Deq_Result_Exclusivity_s by simp
      show "hI26_DeqRet_D4_Mutex s" using hI26_DeqRet_D4_Mutex_s by simp
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
      show "program_counter s p = ''D4''" 
        using step_facts by simp
        
      show "last (filter (\<lambda>e. act_pid e = p) (his_seq s)) = mk_act deq BOT p (s_var s p) call"
      proof (rule pending_call_is_last)
        show "HasPendingDeq s p" using hI12_D_Phase_Pending_Deq_s step_facts unfolding hI12_D_Phase_Pending_Deq_def by blast
        show "hI2_SSN_Bounds s" using hI2_SSN_Bounds_s by simp
        show "hI6_SSN_Order s" using INV unfolding system_invariant_def by simp
      qed
        
      show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q" using other_facts by auto
      show "x_var s' p = BOT" using step_facts by auto
      show "\<And>k. Q_arr s' k = Q_arr s k" using step_facts by auto
      show "\<And>k. Qback_arr s' k = Qback_arr s k" using step_facts by auto
      show "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q" using other_facts by auto
    qed

    have "hI23_Deq_Call_Ret_Balanced s'"
    proof (rule hI23_Deq_Call_Ret_Balanced_D4_step)
      show "hI23_Deq_Call_Ret_Balanced s" using hI23_Deq_Call_Ret_Balanced_s by simp
      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by auto
        
      show "act_pid (mk_act deq (x_var s p) p (s_var s p) ret) = p" 
        by (simp add: mk_act_def act_pid_def)
      show "act_name (mk_act deq (x_var s p) p (s_var s p) ret) = deq" 
        by (simp add: mk_act_def act_name_def)
      show "act_cr (mk_act deq (x_var s p) p (s_var s p) ret) = ret" 
        by (simp add: mk_act_def act_cr_def)
        
      show "filter (\<lambda>e. act_pid e = p) (his_seq s) \<noteq> []"
      proof -
        have "HasPendingDeq s p" 
          using hI12_D_Phase_Pending_Deq_s step_facts unfolding hI12_D_Phase_Pending_Deq_def by blast
          
        then obtain e where "e \<in> set (his_seq s)" "act_pid e = p"
          unfolding HasPendingDeq_def Let_def DeqCallInHis_def by blast
          
        thus ?thesis 
          by (auto simp: filter_empty_conv)
      qed
      
      have local_last_fact: "last (filter (\<lambda>e. act_pid e = p) (his_seq s)) = mk_act deq BOT p (s_var s p) call"
      proof (rule pending_call_is_last)
        show "HasPendingDeq s p" using hI12_D_Phase_Pending_Deq_s step_facts unfolding hI12_D_Phase_Pending_Deq_def by blast
        show "hI2_SSN_Bounds s" using hI2_SSN_Bounds_s by simp
        show "hI6_SSN_Order s" using INV unfolding system_invariant_def by simp
      qed
        
      show "act_name (last (filter (\<lambda>e. act_pid e = p) (his_seq s))) = deq"
        using local_last_fact by (simp add: mk_act_def act_name_def)
        
      show "act_cr (last (filter (\<lambda>e. act_pid e = p) (his_seq s))) = call"
        using local_last_fact by (simp add: mk_act_def act_cr_def)
    qed
  
    have "hI24_HB_Implies_Idx_Order s'"
    proof (rule hI24_HB_Implies_Idx_Order_D4_step)
      show "hI24_HB_Implies_Idx_Order s" using hI24_HB_Implies_Idx_Order_s by simp
      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]" 
        using step_facts by simp
        
      show "act_name (mk_act deq (x_var s p) p (s_var s p) ret) = deq" 
        by (simp add: mk_act_def act_name_def)
        
      show "CState.Q_arr (fst s') = CState.Q_arr (fst s)"
        using step_facts unfolding Q_arr_def by auto
    qed
  
    have "hI25_Enq_Call_Ret_Balanced s'"
    proof (rule hI25_Enq_Call_Ret_Balanced_D4_step)
      show "hI25_Enq_Call_Ret_Balanced s" using hI25_Enq_Call_Ret_Balanced_s by simp
      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
        
      show "act_name (mk_act deq (x_var s p) p (s_var s p) ret) = deq"
        by (simp add: mk_act_def act_name_def)
        
      show "program_counter s p = ''D4''" using step_facts by simp
      show "program_counter s' p = ''L0''" using step_facts by simp
      show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
        using other_facts by auto
    qed

    have "hI26_DeqRet_D4_Mutex s'"
    proof (rule hI26_DeqRet_D4_Mutex_D4_step)
      show "hI26_DeqRet_D4_Mutex s" using hI26_DeqRet_D4_Mutex_s by simp
      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
        
      show "act_pid (mk_act deq (x_var s p) p (s_var s p) ret) = p"
        by (simp add: mk_act_def act_pid_def)
        
      show "program_counter s' p = ''L0''" using step_facts by simp
      show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
        using other_facts step_facts by auto
      show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
        using other_facts step_facts by auto
    qed

  (* ========================================================================= *)
  (* Preserve hI27_Pending_PC_Sync across the D4 transition.                *)
  (* ========================================================================= *)
  have "hI27_Pending_PC_Sync s'"
  proof (unfold hI27_Pending_PC_Sync_def, intro conjI allI impI)
    (* Dequeue side *)
    show "\<And>p'. HasPendingDeq s' p' \<Longrightarrow> program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    proof -
      fix p' assume pending_prime: "HasPendingDeq s' p'"
      show "program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof (cases "p' = p")
        case True
        have "program_counter s' p = ''L0''" using step_facts by simp
        with \<open>hI2_SSN_Bounds s'\<close> have "\<forall>e\<in>set (his_seq s'). act_pid e = p \<longrightarrow> act_ssn e < s_var s' p"
          unfolding hI2_SSN_Bounds_def by auto
        hence "\<not> DeqCallInHis s' p (s_var s' p)"
          unfolding DeqCallInHis_def Let_def by fastforce
        hence "\<not> HasPendingDeq s' p"
          unfolding HasPendingDeq_def Let_def by simp
        with pending_prime True show ?thesis by simp
      next
        case False
        have "HasPendingDeq s' p' = HasPendingDeq s p'"
          unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
          using step_facts(8) other_facts False by (auto simp: mk_act_def act_pid_def)
        with pending_prime have "HasPendingDeq s p'" by simp
        with hI19_s have "program_counter s p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
          unfolding hI27_Pending_PC_Sync_def by blast
        thus ?thesis using False other_facts by simp
      qed
    qed

    (* Enqueue side *)
    show "\<And>p'. HasPendingEnq s' p' (v_var s' p') \<Longrightarrow> program_counter s' p' \<in> {''E1'', ''E2'', ''E3''}"
    proof -
      fix p' assume pending_prime: "HasPendingEnq s' p' (v_var s' p')"
      show "program_counter s' p' \<in> {''E1'', ''E2'', ''E3''}"
      proof (cases "p' = p")
        case True
        have "program_counter s' p = ''L0''" using step_facts by simp
        with \<open>hI2_SSN_Bounds s'\<close> have "\<forall>e\<in>set (his_seq s'). act_pid e = p \<longrightarrow> act_ssn e < s_var s' p"
          unfolding hI2_SSN_Bounds_def by auto
        hence "\<not> EnqCallInHis s' p (v_var s' p) (s_var s' p)"
          unfolding EnqCallInHis_def Let_def by fastforce
        hence "\<not> HasPendingEnq s' p (v_var s' p)"
          unfolding HasPendingEnq_def Let_def by simp
        with pending_prime True show ?thesis by simp
      next
        case False
        have "HasPendingEnq s' p' (v_var s' p') = HasPendingEnq s p' (v_var s p')"
          unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def Let_def
          using step_facts(8) other_facts False by (auto simp: mk_act_def act_pid_def)
        with pending_prime have "HasPendingEnq s p' (v_var s p')" by simp
        with hI19_s have "program_counter s p' \<in> {''E1'', ''E2'', ''E3''}"
          unfolding hI27_Pending_PC_Sync_def by blast
        thus ?thesis using False other_facts by simp
      qed
    qed
  qed

  (* ========================================================================= *)
  (* Preserve hI28_Fresh_Enq_Immunity across the D4 transition.             *)
  (* ========================================================================= *)
  have "hI28_Fresh_Enq_Immunity s'"
  proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI)
    fix p_enq q_deq a sn
    assume prems: "program_counter s' p_enq \<in> {''E1'', ''E2''} \<and> 
                   v_var s' p_enq = a \<and> 
                   a \<noteq> BOT"
    hence pc_e_prime: "program_counter s' p_enq \<in> {''E1'', ''E2''}"
      and v_eq_prime: "v_var s' p_enq = a"
      and a_not_bot: "a \<noteq> BOT" by auto

    show "\<not> DeqRetInHis s' q_deq a sn"
    proof (rule notI)
      assume his_prime: "DeqRetInHis s' q_deq a sn"
      
      have p_enq_neq_p: "p_enq \<noteq> p"
      proof
        assume "p_enq = p"
        have "program_counter s' p = ''L0''" using step_facts by simp
        with pc_e_prime \<open>p_enq = p\<close> show False by simp
      qed

      have pc_e_old: "program_counter s p_enq \<in> {''E1'', ''E2''}"
        using pc_e_prime p_enq_neq_p other_facts by simp
      have v_eq_old: "v_var s p_enq = a"
        using v_eq_prime p_enq_neq_p other_facts by simp

      have "DeqRetInHis s' q_deq a sn \<longleftrightarrow> DeqRetInHis s q_deq a sn \<or> (q_deq = p \<and> a = x_var s p \<and> sn = s_var s p)"
        unfolding DeqRetInHis_def Let_def using step_facts(8) 
        by (auto simp: mk_act_def act_pid_def act_val_def act_ssn_def act_name_def act_cr_def)
      with his_prime consider (old_his) "DeqRetInHis s q_deq a sn" | (new_his) "q_deq = p" "a = x_var s p" "sn = s_var s p" by auto

      thus False
      proof cases
        case old_his
        from hI20_s[unfolded hI28_Fresh_Enq_Immunity_def] pc_e_old v_eq_old a_not_bot old_his show False by blast
      next
        case new_his
        have "x_var s p = a" using new_his by simp
        
        have "Qback_arr s (j_var s p) = a"
          using sI7_D4_Deq_Result_s \<open>program_counter s p = ''D4''\<close> \<open>x_var s p = a\<close> unfolding sI7_D4_Deq_Result_def by auto

        have pend_enq: "HasPendingEnq s p_enq a"
          using hI1_E_Phase_Pending_Enq_s pc_e_old v_eq_old unfolding hI1_E_Phase_Pending_Enq_def by auto

        show False
        proof (cases "program_counter s p_enq = ''E1''")
          case True
          have "\<not> (\<exists>k. Qback_arr s k = a)"
            using hI14_Pending_Enq_Qback_Exclusivity_s pend_enq True unfolding hI14_Pending_Enq_Qback_Exclusivity_def by auto
          with \<open>Qback_arr s (j_var s p) = a\<close> show False by blast
        next
          case False
          have "program_counter s p_enq = ''E2''" using pc_e_old False by simp
          have "\<forall>k. Qback_arr s k = a \<longrightarrow> k = i_var s p_enq"
            using hI14_Pending_Enq_Qback_Exclusivity_s pend_enq \<open>program_counter s p_enq = ''E2''\<close> unfolding hI14_Pending_Enq_Qback_Exclusivity_def by auto
          hence "j_var s p = i_var s p_enq"
            using \<open>Qback_arr s (j_var s p) = a\<close> by simp

          have "Qback_arr s (i_var s p_enq) = BOT"
            using sI3_E2_Slot_Exclusive_s \<open>program_counter s p_enq = ''E2''\<close> unfolding sI3_E2_Slot_Exclusive_def by auto

          with \<open>Qback_arr s (j_var s p) = a\<close> \<open>j_var s p = i_var s p_enq\<close> have "a = BOT" by simp
          with a_not_bot show False by simp
        qed
      qed
    qed
  qed

    (* ========================================================================= *)
    (* Preserve hI29_E2_Scanner_Immunity across the D4 transition.          *)
    (* ========================================================================= *)
    have "hI29_E2_Scanner_Immunity s'"
    proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI, goal_cases)
      case (1 p_enq a q_deq)
      
      (* Step 1: extract the core assumptions of the target goal. *)
      from 1 have pc_e': "program_counter s' p_enq = ''E2''" by blast
      from 1 have inqa': "InQBack s' a" by blast
      from 1 have tba': "TypeB s' a" by blast
      from 1 have pend_q': "HasPendingDeq s' q_deq" by blast
      from 1 have pc_q_D3': "program_counter s' q_deq = ''D3''" by blast
      from 1 have idx1': "Idx s' a < j_var s' q_deq" by blast
      from 1 have idx2': "j_var s' q_deq \<le> i_var s' p_enq" by blast
      from 1 have idx3': "i_var s' p_enq < l_var s' q_deq" by blast

      (* Step 2: import the relevant invariant from the pre-state. *)
      have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast
      
      (* Step 3: isolate the active process p, which returns to L0 after D4. *)
      have p_enq_neq_p: "p_enq \<noteq> p" 
      proof
        assume "p_enq = p"
        with pc_e' have "program_counter s' p = ''E2''" by simp
        moreover have "program_counter s' p = ''L0''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed
      
      have q_deq_neq_p: "q_deq \<noteq> p"
      proof
        assume "q_deq = p"
        with pc_q_D3' have "program_counter s' p = ''D3''" by simp
        moreover have "program_counter s' p = ''L0''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed

      (* Step 4: transport the concrete facts back to the pre-state. *)
      have pc_e_s: "program_counter s p_enq = ''E2''" using pc_e' p_enq_neq_p step_facts pc_eqs by auto
      have pc_q_s: "program_counter s q_deq = ''D3''" using pc_q_D3' q_deq_neq_p step_facts pc_eqs by auto
      
      have inqa_s: "InQBack s a" using inqa' step_facts unfolding InQBack_def by auto
      have tba_s: "TypeB s a" using tba' step_facts pc_eqs unfolding TypeB_def QHas_def by auto
      
      (* The appended dequeue return does not affect pending status for q_deq \<noteq> p. *)
      have pend_q_s: "HasPendingDeq s q_deq"
      proof -
        have "HasPendingDeq s' q_deq = HasPendingDeq s q_deq"
          unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
          using step_facts q_deq_neq_p by (auto simp: mk_act_def act_pid_def)
        thus ?thesis using pend_q' by simp
      qed
      
      (* Transport all index and pointer facts back to the pre-state. *)
      have idx_eq: "\<And>x. Idx s' x = Idx s x" using step_facts unfolding Idx_def AtIdx_def by auto
      have j_var_eq: "j_var s' q_deq = j_var s q_deq" using q_deq_neq_p step_facts by auto
      have l_var_eq: "l_var s' q_deq = l_var s q_deq" using q_deq_neq_p step_facts by auto
      have i_var_eq: "i_var s' p_enq = i_var s p_enq" using p_enq_neq_p step_facts by auto
      have v_var_eq: "v_var s' p_enq = v_var s p_enq" using p_enq_neq_p step_facts by auto

      have bound1: "Idx s a < j_var s q_deq" using idx1' idx_eq j_var_eq by simp
      have bound2: "j_var s q_deq \<le> i_var s p_enq" using idx2' j_var_eq i_var_eq by simp
      have bound3: "i_var s p_enq < l_var s q_deq" using idx3' i_var_eq l_var_eq by simp

      (* Step 5: apply the corresponding pre-state invariant. *)
      have no_hb_old: "\<not> HB_EnqRetCall s a (v_var s p_enq)"
        using hI21_s pc_e_s inqa_s tba_s pend_q_s pc_q_s bound1 bound2 bound3
        unfolding hI29_E2_Scanner_Immunity_def by blast

      (* Step 6: show that the relevant happens-before relation is stable under the append. *)
      show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
      proof -
        (* Use the prepared append-stability lemma HB_enq_stable_deq_append. *)
        have hb_stable: "HB_EnqRetCall s' a (v_var s' p_enq) = HB_EnqRetCall s a (v_var s p_enq)"
          unfolding HB_EnqRetCall_def HB_Act_def
          using step_facts HB_enq_stable_deq_append v_var_eq
          by metis 
        thus ?thesis using no_hb_old by simp
      qed
    qed

(* ========================================================================= *)
    (* Preserve hI30_Ticket_HB_Immunity across the D4 transition.            *)
    (* The proof relies on append stability of the relevant HB relation.      *)
    (* ========================================================================= *)
    have "hI30_Ticket_HB_Immunity s'"
    proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI, goal_cases)
      case (1 b q)
      
      (* Step 1: extract the core assumptions of the target goal. *)
      from 1 have pc_q': "program_counter s' q \<in> {''E2'', ''E3''}" by blast
      from 1 have inqb': "InQBack s' b" by blast
      from 1 have b_not_bot': "b \<noteq> BOT" by blast
      from 1 have b_neq_v': "b \<noteq> v_var s' q" by blast
      from 1 have hb': "HB_EnqRetCall s' b (v_var s' q)" by blast

      (* Step 2: import the corresponding pre-state invariant. *)
      have hI22_s: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast

      (* Step 3: isolate the active process p, which cannot remain in E2 or E3 after D4. *)
      have q_neq_p: "q \<noteq> p"
      proof
        assume "q = p"
        with pc_q' have "program_counter s' p \<in> {''E2'', ''E3''}" by simp
        moreover have "program_counter s' p = ''L0''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed

      (* Step 4: transport all relevant concrete facts back to the pre-state. *)
      have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}" 
        using pc_q' q_neq_p step_facts pc_eqs by auto

      have inqb_s: "InQBack s b" using inqb' step_facts unfolding InQBack_def by auto
      
      have v_var_eq: "v_var s' q = v_var s q" using q_neq_p step_facts by auto
      have i_var_eq: "i_var s' q = i_var s q" using q_neq_p step_facts by auto
      
      have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_var_eq by simp

      (* The appended dequeue return does not change the enqueue-related HB relation. *)
      have seq_eq: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp

      (* Invoke the append lemma directly to keep the proof stable. *)
      have hb_eq: "HB_EnqRetCall s' b (v_var s' q) = HB_EnqRetCall s b (v_var s q)"
        unfolding HB_EnqRetCall_def HB_Act_def
        using HB_enq_stable_deq_append[OF seq_eq] v_var_eq
        by fastforce
      have hb_s: "HB_EnqRetCall s b (v_var s q)" using hb' hb_eq by simp

      have idx_eq: "Idx s' b = Idx s b" unfolding Idx_def AtIdx_def using step_facts by simp

      (* Step 5: apply the simplified pre-state invariant. *)
      have "Idx s b < i_var s q"
        using hI22_s pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
        unfolding hI30_Ticket_HB_Immunity_def by blast

      (* Step 6: transport the conclusion back to the post-state. *)
      thus "Idx s' b < i_var s' q" using idx_eq i_var_eq by simp
    qed

    have "lI1_Op_Sets_Equivalence s'"
    proof (rule lI1_Op_Sets_Equivalence_D4_step)
      show "lI1_Op_Sets_Equivalence s" using lI1_Op_Sets_Equivalence_s by simp
      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
      show "act_cr (mk_act deq (x_var s p) p (s_var s p) ret) = ret"
        by (simp add: mk_act_def act_cr_def)
        
      show "OPLin s' = OPLin s" using step_facts unfolding OPLin_def by auto
      show "SetA s' = SetA s" using step_facts unfolding SetA_def by auto
      show "SetB s' = SetB s" using step_facts unfolding SetB_def by auto
    qed

  have "lI2_Op_Cardinality s'" using lI2_Op_Cardinality_s step_facts unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def by auto

    have "lI3_HB_Ret_Lin_Sync s'"
    proof (rule lI3_HB_Ret_Lin_Sync_D4_step)
      show "lI3_HB_Ret_Lin_Sync s" using lI3_HB_Ret_Lin_Sync_s by simp
      show "lI6_D4_Deq_Linearized s" using lI6_D4_Deq_Linearized_s by simp
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
      show "act_name (mk_act deq (x_var s p) p (s_var s p) ret) = deq"
        by (simp add: mk_act_def act_name_def)
      show "act_cr (mk_act deq (x_var s p) p (s_var s p) ret) = ret"
        by (simp add: mk_act_def act_cr_def)
      show "act_pid (mk_act deq (x_var s p) p (s_var s p) ret) = p" by (simp add: mk_act_def act_pid_def)
      show "act_val (mk_act deq (x_var s p) p (s_var s p) ret) = x_var s p" by (simp add: mk_act_def act_val_def)
      show "act_ssn (mk_act deq (x_var s p) p (s_var s p) ret) = s_var s p" by (simp add: mk_act_def act_ssn_def)
      
      show "program_counter s p = ''D4''" using step_facts by simp
      show "x_var s p = x_var s p" by simp
      show "s_var s p = s_var s p" by simp
      show "lin_seq s' = lin_seq s" using step_facts by simp
    qed

  have "lI4_FIFO_Semantics s'" using lI4_FIFO_Semantics_s step_facts unfolding lI4_FIFO_Semantics_def by simp
  have "lI5_SA_Prefix s'" using lI5_SA_Prefix_s step_facts unfolding lI5_SA_Prefix_def by simp


    have "lI6_D4_Deq_Linearized s'"
      unfolding lI6_D4_Deq_Linearized_def
    proof (intro allI impI)
      fix q
      assume pc_q: "program_counter s' q = ''D4''"
      show "mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s')"
      proof (cases "q = p")
        case True
        have "program_counter s' p = ''L0''" using step_facts by simp
        with pc_q True have False by simp
        thus ?thesis ..
      next
        case False
        have "program_counter s q = ''D4''" using pc_q False other_facts step_facts by auto
        moreover have "x_var s' q = x_var s q" "s_var s' q = s_var s q" "lin_seq s' = lin_seq s" 
          using step_facts other_facts False by auto
        ultimately show ?thesis using lI6_D4_Deq_Linearized_s unfolding lI6_D4_Deq_Linearized_def by auto
      qed
    qed

    have "lI7_D4_Deq_Deq_HB s'"
    proof (rule lI7_D4_Deq_Deq_HB_D4_step)
      show "lI7_D4_Deq_Deq_HB s" using lI7_D4_Deq_Deq_HB_s by simp
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
      
      let ?e = "mk_act deq (x_var s p) p (s_var s p) ret"
      show "act_name ?e = deq" "act_cr ?e = ret" "act_pid ?e = p"
        by (simp_all add: mk_act_def act_name_def act_cr_def act_pid_def)
      
      show "program_counter s' p = ''L0'' " using step_facts by simp
      show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
        using other_facts by auto
      show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q"
        using other_facts by auto
      show "lin_seq s' = lin_seq s" using step_facts by simp
    qed

    have "lI8_D3_Deq_Returned s'"
    proof (rule lI8_D3_Deq_Returned_D4_step)
      show "lI8_D3_Deq_Returned s" using lI8_D3_Deq_Returned_s by simp
      
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
        
      show "act_pid (mk_act deq (x_var s p) p (s_var s p) ret) = p"
        by (simp add: mk_act_def act_pid_def)
        
      show "program_counter s' p = ''L0'' " using step_facts by simp
      show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
        using other_facts by auto
      show "lin_seq s' = lin_seq s" using step_facts by simp
    qed

    have "lI9_D1_D2_Deq_Returned s'"
    proof (rule lI9_D1_D2_Deq_Returned_D4_step)
      show "lI9_D1_D2_Deq_Returned s" using lI9_D1_D2_Deq_Returned_s by simp
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
      show "act_pid (mk_act deq (x_var s p) p (s_var s p) ret) = p"
        by (simp add: mk_act_def act_pid_def)
      show "program_counter s' p = ''L0'' " using step_facts by simp
      show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
        using other_facts by auto
      show "lin_seq s' = lin_seq s" using step_facts by simp
    qed


    have "lI10_D4_Enq_Deq_HB s'"
    proof (rule lI10_D4_Enq_Deq_HB_D4_step)
      show "lI10_D4_Enq_Deq_HB s" using lI10_D4_Enq_Deq_HB_s by simp
      show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
        using step_facts by simp
      
      let ?e = "mk_act deq (x_var s p) p (s_var s p) ret"
      show "act_name ?e = deq" "act_cr ?e = ret" "act_pid ?e = p"
        by (simp_all add: mk_act_def act_name_def act_cr_def act_pid_def)
      
      show "program_counter s' p = ''L0'' " using step_facts by simp
      show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
        using other_facts by auto
      show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q"
        using other_facts by auto
      show "lin_seq s' = lin_seq s" using step_facts by simp
    qed

    have "lI11_D4_Deq_Unique s'"
      unfolding lI11_D4_Deq_Unique_def
    proof (intro allI impI)
      fix q
      assume pc_q: "program_counter s' q = ''D4''"
      show "\<exists>k2<length (lin_seq s').
             lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
             (\<forall>k3<length (lin_seq s').
                 op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
                 k3 < k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3)))"
      proof (cases "q = p")
        case True
        have "program_counter s' p = ''L0''" using step_facts by simp
        with pc_q True have False by simp
        thus ?thesis ..
      next
        case False
        have old_pc: "program_counter s q = ''D4''" using pc_q False other_facts step_facts by auto
        have vars_eq: "x_var s' q = x_var s q" "s_var s' q = s_var s q" "lin_seq s' = lin_seq s" 
          using step_facts other_facts False by auto
          
        from lI11_D4_Deq_Unique_s[unfolded lI11_D4_Deq_Unique_def, rule_format, OF old_pc]
        obtain k2 where k2_props: 
          "k2 < length (lin_seq s)"
          "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
          "\<forall>k3<length (lin_seq s).
              op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
              k3 < k2 \<and> DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
          by blast
          
        have his_eq: "\<And>val sn. DeqRetInHis s' q val sn \<longleftrightarrow> DeqRetInHis s q val sn"
        proof -
          fix val sn
          have "set (his_seq s') = set (his_seq s) \<union> {mk_act deq (x_var s p) p (s_var s p) ret}"
            using step_facts by simp
          thus "DeqRetInHis s' q val sn \<longleftrightarrow> DeqRetInHis s q val sn"
            unfolding DeqRetInHis_def Let_def using False
            by (auto simp: mk_act_def act_pid_def)
        qed
        
        show ?thesis
          unfolding vars_eq
          using k2_props his_eq by auto
      qed
    qed

  have "data_independent (lin_seq s')" using di_lin_s step_facts by simp

  have "Simulate_PC s'" using STEP unfolding Sys_D4_def by simp

  (* Step 6: assemble the final invariant package. *)
  show ?thesis 
    unfolding system_invariant_def
    using `Simulate_PC s'` `TypeOK s'` `sI1_Zero_Index_BOT s'`
    `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'` `hI3_L0_E_Phase_Bounds s'` 
    `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'``sI12_D3_Scanned_Prefix s'` `hI4_X_var_Lin_Sync s'` 
    `hI7_His_WF s'` `hI8_Val_Unique s'` `hI5_SSN_Unique s'` `hI6_SSN_Order s'` 
    `hI9_Deq_Ret_Unique s'` `hI10_Enq_Call_Existence s'` `hI11_Enq_Ret_Existence s'` `hI12_D_Phase_Pending_Deq s'` `hI13_Qback_Deq_Sync s'` `hI14_Pending_Enq_Qback_Exclusivity s'` `hI15_Deq_Result_Exclusivity s'` `hI16_BO_BT_No_HB s'` `hI17_BT_BT_No_HB s'` `hI18_Idx_Order_No_Rev_HB s'` `hI19_Scanner_Catches_Later_Enq s'` `hI20_Enq_Val_Valid s'` `hI21_Ret_Implies_Call s'` `hI22_Deq_Local_Pattern s'` `hI23_Deq_Call_Ret_Balanced s'` `hI24_HB_Implies_Idx_Order s'` `hI25_Enq_Call_Ret_Balanced s'`  `hI26_DeqRet_D4_Mutex s'`
    `hI27_Pending_PC_Sync s'` `hI28_Fresh_Enq_Immunity s'` `hI29_E2_Scanner_Immunity s'` `hI30_Ticket_HB_Immunity s'` (* Final assembly of the invariant package. *)
    `lI1_Op_Sets_Equivalence s'` `lI2_Op_Cardinality s'` `lI3_HB_Ret_Lin_Sync s'` `lI4_FIFO_Semantics s'` `lI5_SA_Prefix s'`
    `lI6_D4_Deq_Linearized s'` `lI7_D4_Deq_Deq_HB s'` `lI8_D3_Deq_Returned s'` `lI9_D1_D2_Deq_Returned s'` `lI10_D4_Enq_Deq_HB s'` `lI11_D4_Deq_Unique s'`
    `data_independent (lin_seq s')`
    by blast
qed

end