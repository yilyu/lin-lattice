theory E2Lemmas
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    DeqLib
    EnqLib
begin

(* ========================================================== *)
(* Auxiliary preservation lemmas for the E2 transition *)
(* ========================================================== *)



(* ========================================================================= *)
(* E2-specific helper lemmas for concrete updates and invariant preservation *)
(* ========================================================================= *)
(* ========== Basic concrete facts for the E2 step ========== *)

lemma E2_Idx_v_var_eq_i_var:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "Idx s' (v_var s p) = i_var s p"
proof -
  note bridge = program_counter_def Qback_arr_def i_var_def v_var_def
  
  have pc_p_E2: "program_counter s p = ''E2''" 
    using STEP unfolding Sys_E2_def C_E2_def bridge by auto
  
  have step_qback: "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge by auto

  have hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" using INV unfolding system_invariant_def by blast
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast
  
  have pend_p: "HasPendingEnq s p (v_var s p)" 
    using hI1_E_Phase_Pending_Enq_s pc_p_E2 unfolding hI1_E_Phase_Pending_Enq_def by blast
    
  have no_other_v: "\<forall>k. k \<noteq> i_var s p \<longrightarrow> Qback_arr s k \<noteq> v_var s p"
    using hI14_Pending_Enq_Qback_Exclusivity_s pend_p pc_p_E2 unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
    
  have "\<forall>k. Qback_arr s' k = v_var s p \<longleftrightarrow> k = i_var s p"
  proof
    fix k show "Qback_arr s' k = v_var s p \<longleftrightarrow> k = i_var s p"
    proof (cases "k = i_var s p")
      case True thus ?thesis using step_qback by simp
    next
      case False
      hence "Qback_arr s' k = Qback_arr s k" using step_qback by simp
      moreover have "Qback_arr s k \<noteq> v_var s p" using no_other_v False by simp
      ultimately show ?thesis using False by simp
    qed
  qed
  thus ?thesis unfolding Idx_def AtIdx_def by (metis (mono_tags, lifting) someI_ex)
qed




(* ========== History-existence and exclusivity lemmas ========== *)

lemma hI10_Enq_Call_Existence_E2_step:
  fixes s s' :: SysState and p :: nat and a :: nat
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
      and EX_K: "\<exists>k. Qback_arr s' k = a"
  shows "\<exists>q sn. EnqCallInHis s' q a sn"
proof (goal_cases)
  case 1
  (* Step 1: Technical note for this proof step.*)
  have TypeOK_s: "TypeOK s" and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s"
    using INV unfolding system_invariant_def by auto
    
  have step_facts:
    "program_counter s p = ''E2'' "
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    "his_seq s' = his_seq s"
    "v_var s' = v_var s"
    using STEP unfolding Sys_E2_def C_E2_def program_counter_def Qback_arr_def 
                           his_seq_def i_var_def v_var_def Let_def
    by (auto simp: fun_eq_iff)

  (* Step 2: instantiate the existential witness k.*)
  from EX_K obtain k where k_def: "Qback_arr s' k = a" by auto

  (* Step 3: Technical note for this proof step.*)
  show ?case
  proof (cases "k = i_var s p")
    case True
    (* Case A: Technical note for this proof step.*)
    hence "a = v_var s p" 
      using step_facts k_def by (simp add: fun_upd_def)
    
    (* Technical note for this invariant-preservation argument.*)
    have "HasPendingEnq s p (v_var s p)"
      using hI1_E_Phase_Pending_Enq_s step_facts(1) unfolding hI1_E_Phase_Pending_Enq_def by blast
    hence "\<exists>sn. EnqCallInHis s p (v_var s p) sn"
      unfolding HasPendingEnq_def Let_def by auto
      
    (* Technical note for this proof step.*)
    thus ?thesis 
      using `a = v_var s p` step_facts unfolding EnqCallInHis_def by auto
      
  next
    case False
    (* Case B: Technical note for this proof step.*)
    hence "Qback_arr s' k = Qback_arr s k" 
      using step_facts by (simp add: fun_upd_def)
    hence "a = Qback_arr s k" 
      using k_def by simp
    
    (* Technical note for this invariant-preservation argument.*)
    hence "\<exists>k0. Qback_arr s k0 = a" by blast
    
    thus ?thesis 
      using hI10_Enq_Call_Existence_s step_facts unfolding hI10_Enq_Call_Existence_def EnqCallInHis_def by auto
  qed
qed

lemma deq_x_var_neq_enq_v_var:
  assumes INV: "system_invariant s"
      and PC_p: "program_counter s p = ''E2''"
  shows "\<forall>q. HasPendingDeq s q \<longrightarrow> x_var s q \<noteq> v_var s p"
proof (intro allI impI notI)
  fix q
  assume pending_q: "HasPendingDeq s q"
  assume x_eq: "x_var s q = v_var s p"

  (* Technical note for this invariant-preservation argument.*)
  from INV have sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and sI11_x_var_Scope_s: "sI11_x_var_Scope s" 
            and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" 
            and hI19_s: "hI27_Pending_PC_Sync s" 
            and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" and hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s"
    unfolding system_invariant_def by auto

  (* Step 0: Technical note for this proof step.*)
  have val_not_bot: "v_var s p \<noteq> BOT"
  proof -
    from hI10_Enq_Call_Existence_s PC_p have "EnqCallInHis s p (v_var s p) (s_var s p)"
      unfolding hI10_Enq_Call_Existence_def by auto
    moreover have "\<forall>k<length (his_seq s). act_name (his_seq s ! k) = enq \<longrightarrow> act_val (his_seq s ! k) \<in> Val"
      using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def by blast
    ultimately have "v_var s p \<in> Val" 
      unfolding EnqCallInHis_def Let_def
      by (metis in_set_conv_nth) 
    thus ?thesis unfolding Val_def BOT_def by auto
  qed

  (* Step 1: Technical note for this invariant-preservation argument.*)
  have pc_in_D_range: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using hI19_s pending_q unfolding hI27_Pending_PC_Sync_def by blast

  (* Step 2: Technical note for this transition-specific proof step.*)
  have not_D123: "program_counter s q \<noteq> ''D1'' \<and> program_counter s q \<noteq> ''D2'' \<and> program_counter s q \<noteq> ''D3''"
  proof (intro conjI)
    show "program_counter s q \<noteq> ''D1''" using sI11_x_var_Scope_s x_eq val_not_bot unfolding sI11_x_var_Scope_def by auto
    show "program_counter s q \<noteq> ''D2''" using sI11_x_var_Scope_s x_eq val_not_bot unfolding sI11_x_var_Scope_def by auto
    show "program_counter s q \<noteq> ''D3''" using sI11_x_var_Scope_s x_eq val_not_bot unfolding sI11_x_var_Scope_def by auto
  qed

  (* Step 3: Technical note for this transition-specific proof step.*)
  with pc_in_D_range have pc_d4: "program_counter s q = ''D4''" by auto

  (* Step 4: Technical note for this transition-specific proof step.*)
  have k_props: "Qback_arr s (j_var s q) = v_var s p"
    using sI7_D4_Deq_Result_s pc_d4 x_eq unfolding sI7_D4_Deq_Result_def by auto

  (* Step 5: Technical note for this invariant-preservation argument.*)
  have p_pending: "HasPendingEnq s p (v_var s p)"
    using hI1_E_Phase_Pending_Enq_s PC_p unfolding hI1_E_Phase_Pending_Enq_def by blast

  (* Step 6: Technical note for this invariant-preservation argument.*)
  have "j_var s q = i_var s p"
    using hI14_Pending_Enq_Qback_Exclusivity_s PC_p p_pending k_props unfolding hI14_Pending_Enq_Qback_Exclusivity_def by auto

  (* Step 7: Technical note for this transition-specific proof step.*)
  hence "Qback_arr s (i_var s p) = v_var s p" using k_props by simp
  with sI3_E2_Slot_Exclusive_s PC_p val_not_bot show False unfolding sI3_E2_Slot_Exclusive_def
    by metis
qed

(* ========================================================================= *)
(* Technical note for this proof step.*)
(* ========================================================================= *)

(* ========== Happens-before separation for the fresh enqueue ========== *)

lemma fresh_enq_no_HB_with_old:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
      and a_not_new: "a \<noteq> v_var s p"
      and tb_a_s': "TypeB s' a"
      and idx_a_lt_b: "Idx s' a < Idx s' (v_var s p)"
      and scanner_cond: "\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and> 
                             Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' (v_var s p) \<and> 
                             Idx s' (v_var s p) < l_var s' q"
  shows "\<not> HB_EnqRetCall s' a (v_var s p)"
proof -
  (* unfold the basic concrete facts of the E2 step*)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def 
                i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def 
                lin_seq_def his_seq_def

  have pc_p_E2: "program_counter s p = ''E2''" 
    using STEP unfolding Sys_E2_def C_E2_def bridge by auto
  
  have step_facts:
    "his_seq s' = his_seq s"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "v_var s' = v_var s"
    "s_var s' = s_var s"
    "i_var s' = i_var s"
    "j_var s' = j_var s"
    "l_var s' = l_var s"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    "program_counter s' p = ''E3''"
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge
    by (auto simp: fun_eq_iff)

  show ?thesis
  proof (cases "a = BOT")
    case True
    (* ===================================================================== *)
    (* Branch 1: Technical note for this invariant-preservation argument.*)
    (* ===================================================================== *)
    have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast
    show ?thesis
    proof
      assume hb: "HB_EnqRetCall s' a (v_var s p)"
      
      (* Technical note for this proof step.*)
      from hb obtain p1 p2 sn1 sn2 k1 k2 :: nat where hb_ret:
        "k1 < length (his_seq s)"
        "act_name (his_seq s ! k1) = enq" 
        "act_val (his_seq s ! k1) = a"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
        using step_facts(1) by (auto simp: op_name_def op_val_def)
        
      (* Technical note for this invariant-preservation argument.*)
      have "act_val (his_seq s ! k1) \<in> Val" 
        using hI20_Enq_Val_Valid_s hb_ret(1) hb_ret(2) unfolding hI20_Enq_Val_Valid_def by blast
      
      (* Technical note for this proof step.*)
      with hb_ret(3) True show False
        by (simp add: BOT_def Val_def)
    qed

  next
    case False
    (* ===================================================================== *)
    (* Branch 2: Technical note for this proof step.*)
    (* ===================================================================== *)
    hence a_not_bot: "a \<noteq> BOT" by simp

    have hI21_s: "hI29_E2_Scanner_Immunity s" 
      using INV unfolding system_invariant_def by auto

    have tb_a_s: "TypeB s a"
    proof -
      from tb_a_s' have "QHas s' a \<or> (\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = a)" 
        unfolding TypeB_def by simp
      thus ?thesis 
      proof (elim disjE)
        assume "QHas s' a"
        then obtain k where "Q_arr s' k = a" unfolding QHas_def by blast
        hence "Q_arr s k = a" 
          using step_facts(2) a_not_new by (auto simp: fun_upd_def split: if_splits)
        thus ?thesis unfolding TypeB_def QHas_def by blast
      next
        assume "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = a"
        then obtain q where q_props: "program_counter s' q = ''E2''" "v_var s' q = a" by blast
        have "q \<noteq> p" using q_props(1) step_facts(9) by auto
        hence "program_counter s q = ''E2''" "v_var s q = a"
          using q_props step_facts(3,10) by (auto simp: fun_eq_iff)
        thus ?thesis unfolding TypeB_def by blast
      qed
    qed

    have qback_i_bot: "Qback_arr s (i_var s p) = BOT"
    proof -
      have "sI3_E2_Slot_Exclusive s" using INV unfolding system_invariant_def by blast
      thus ?thesis using pc_p_E2 unfolding sI3_E2_Slot_Exclusive_def by blast
    qed

    have idx_b_is_i: "Idx s' (v_var s p) = i_var s p" 
    proof -
      have hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" using INV unfolding system_invariant_def by blast
      have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast
      
      have pend_p: "HasPendingEnq s p (v_var s p)" 
        using hI1_E_Phase_Pending_Enq_s pc_p_E2 unfolding hI1_E_Phase_Pending_Enq_def by blast
        
      have no_other_b: "\<forall>k. k \<noteq> i_var s p \<longrightarrow> Qback_arr s k \<noteq> v_var s p"
        using hI14_Pending_Enq_Qback_Exclusivity_s pend_p pc_p_E2 unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
        
      have "\<forall>k. Qback_arr s' k = v_var s p \<longleftrightarrow> k = i_var s p"
      proof
        fix k show "Qback_arr s' k = v_var s p \<longleftrightarrow> k = i_var s p"
        proof (cases "k = i_var s p")
          case True thus ?thesis using step_facts(8) by simp
        next
          case False
          hence "Qback_arr s' k = Qback_arr s k" using step_facts(8) by simp
          moreover have "Qback_arr s k \<noteq> v_var s p" using no_other_b False by simp
          ultimately show ?thesis using False by simp
        qed
      qed
      thus ?thesis unfolding Idx_def AtIdx_def by (metis (mono_tags, lifting) someI_ex)
    qed
      
    have idx_a_s: "Idx s' a = Idx s a"
    proof -
      have "(\<lambda>k. Qback_arr s' k = a) = (\<lambda>k. Qback_arr s k = a)"
      proof (rule ext)
        fix k show "(Qback_arr s' k = a) = (Qback_arr s k = a)"
        proof (cases "k = i_var s p")
          case True
          have "Qback_arr s' k = v_var s p" using step_facts(8) True by simp
          moreover have "Qback_arr s k = BOT" using qback_i_bot True by simp
          ultimately show ?thesis using a_not_new a_not_bot by simp
        next
          case False
          thus ?thesis using step_facts(8) by simp
        qed
      qed
      thus ?thesis unfolding Idx_def AtIdx_def by simp
    qed

    from scanner_cond obtain q where q_props_s':
      "HasPendingDeq s' q" "program_counter s' q = ''D3''"
      "Idx s' a < j_var s' q" "j_var s' q \<le> Idx s' (v_var s p)" "Idx s' (v_var s p) < l_var s' q" 
      by blast

    have q_neq_p: "q \<noteq> p"
    proof
      assume "q = p"
      with q_props_s'(2) step_facts(9) show False by simp
    qed

    have pend_q_s: "HasPendingDeq s q" 
    proof -
      have "HasPendingDeq s' q = HasPendingDeq s q"
        unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
        using step_facts(1,4) by simp
      thus ?thesis using q_props_s'(1) by simp
    qed
    
    have pc_q_s: "program_counter s q = ''D3''" 
      using q_props_s'(2) q_neq_p step_facts(10) by simp
    
    have "Idx s a < j_var s q" using q_props_s'(3) idx_a_s step_facts(6) by simp
    moreover have "j_var s q \<le> i_var s p" using q_props_s'(4) idx_b_is_i step_facts(6) by simp
    moreover have "i_var s p < l_var s q" using q_props_s'(5) idx_b_is_i step_facts(7) by simp
    ultimately have index_chain: "Idx s a < j_var s q \<and> j_var s q \<le> i_var s p \<and> i_var s p < l_var s q" by simp

    have no_hb_s: "\<not> HB_EnqRetCall s a (v_var s p)" 
      using hI21_s[unfolded hI29_E2_Scanner_Immunity_def, rule_format, of p a q]
      using pc_p_E2 tb_a_s pend_q_s pc_q_s index_chain
      using HB_implies_InQBack INV by blast 

    have "HB_EnqRetCall s' a (v_var s p) = HB_EnqRetCall s a (v_var s p)"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def match_ret_def match_call_def Let_def
      using step_facts(1) by auto

    thus ?thesis using no_hb_s by simp
  qed
qed


lemma hI11_Enq_Ret_Existence_E2_step:
  assumes INV: "system_invariant s" 
      and STEP: "Sys_E2 p s s'"
  shows "hI11_Enq_Ret_Existence s'"
proof (unfold hI11_Enq_Ret_Existence_def, intro allI impI)
  (* Step 1: fix the variables and assumptions.*)
  fix pa a sn
  assume assm: "(program_counter s' pa \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' pa \<noteq> a \<or> s_var s' pa \<noteq> sn) \<and> 
                (\<exists>k. Qback_arr s' k = a) \<and> 
                EnqCallInHis s' pa a sn"

  (* Step 2: Technical note for this proof step.*)
  have step_facts: 
    "his_seq s' = his_seq s" 
    "v_var s' = v_var s" "s_var s' = s_var s"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    "program_counter s' = (program_counter s)(p := ''E3'')"
    using STEP unfolding Sys_E2_def C_E2_def Let_def
              program_counter_def v_var_def s_var_def i_var_def Qback_arr_def his_seq_def
    by (auto simp: fun_eq_iff)

  (* Technical note for this proof step.*)
  from INV have hI11_Enq_Ret_Existence_s: "hI11_Enq_Ret_Existence s" 
            and val_uni: "hI8_Val_Unique s" 
            and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s"
            and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s"
            unfolding system_invariant_def by auto

  from assm obtain k_val where k_def: "Qback_arr s' k_val = a" by auto

  (* Step 3: Main case split.*)
  show "EnqRetInHis s' pa a sn"
  proof (cases "k_val = i_var s p")
    case True
    (* Case A: freshly written value (k = i_var)*)
    hence a_val: "a = v_var s p" using k_def step_facts by simp
    
    show ?thesis
    proof (cases "pa = p \<and> sn = s_var s p")
      case True
      (* Case A1: Technical note for this proof step.*)
      hence is_p: "pa = p" by simp
      have "program_counter s' p = ''E3'' " using step_facts by simp
      with is_p a_val True assm step_facts show ?thesis by auto
    next
      case False
      (* Case A2: Technical note for this proof step.*)
      have curr_call: "EnqCallInHis s p (v_var s p) (s_var s p)"
        using hI10_Enq_Call_Existence_s STEP unfolding hI10_Enq_Call_Existence_def Sys_E2_def C_E2_def program_counter_def by auto
      from assm curr_call a_val val_uni False step_facts
      show ?thesis unfolding hI8_Val_Unique_def EnqCallInHis_def
        by (metis in_set_conv_nth) 
    qed

  next
    case False
    (* Case B: Technical note for this proof step.*)
    hence a_in_old: "a = Qback_arr s k_val" using k_def step_facts by simp
    
    show ?thesis
    proof (cases "pa = p")
      case True
      (* Case B1: pa = p, old value (use hI14_Pending_Enq_Qback_Exclusivity rule out v_var = a)*)
      hence is_p: "pa = p" by simp
      from hI14_Pending_Enq_Qback_Exclusivity_s have "v_var s p \<noteq> a"
        using STEP False a_in_old unfolding hI14_Pending_Enq_Qback_Exclusivity_def HasPendingEnq_def Sys_E2_def C_E2_def program_counter_def
        by (metis (no_types, lifting) hI1_E_Phase_Pending_Enq_def HasPendingEnq_def insertCI
            program_counter_def system_invariant_def)
      with is_p a_in_old hI11_Enq_Ret_Existence_s assm step_facts show ?thesis
        unfolding hI11_Enq_Ret_Existence_def EnqRetInHis_def EnqCallInHis_def by (metis (no_types, lifting))
    next
      case False_pa: False
      (* Case B2: Technical note for this proof step.*)
      hence pa_stable: "v_var s pa = v_var s' pa" "s_var s pa = s_var s' pa" "program_counter s pa = program_counter s' pa"
        using step_facts by  auto
      with False_pa a_in_old hI11_Enq_Ret_Existence_s assm step_facts show ?thesis
        unfolding hI11_Enq_Ret_Existence_def EnqRetInHis_def EnqCallInHis_def by (metis (no_types, lifting))
    qed
  qed
qed

lemma hI14_Pending_Enq_Qback_Exclusivity_E2_step:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "hI14_Pending_Enq_Qback_Exclusivity s'"
proof (unfold hI14_Pending_Enq_Qback_Exclusivity_def, intro conjI)
(* Step 0: Technical note for this proof step.*)
  have step_facts: 
    "his_seq s' = his_seq s" 
    "v_var s' = v_var s" 
    "s_var s' = s_var s"  (* Technical note for this proof step.*)
    "i_var s' = i_var s"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    "program_counter s' = (program_counter s)(p := ''E3'')"
    "program_counter s p = ''E2'' "
    using STEP unfolding Sys_E2_def C_E2_def Let_def
              program_counter_def v_var_def s_var_def i_var_def Qback_arr_def his_seq_def
    by (auto simp: fun_eq_iff)

  from INV have hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" 
            and val_uni: "hI8_Val_Unique s" 
            and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s"
    unfolding system_invariant_def by auto

  (* Technical note for this proof step.*)
  have hpd_eq: "\<And>pa a. HasPendingEnq s' pa a = HasPendingEnq s pa a"
    using step_facts unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def
    by (simp add: fun_eq_iff)

  (* Step 1: Technical note for this transition-specific proof step.*)
  show "\<forall>pa a. HasPendingEnq s' pa a \<and> program_counter s' pa \<in> {''E2'', ''E3''} \<longrightarrow> 
               \<not> (\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' pa)"
  proof (intro allI impI notI, elim exE conjE)
    fix pa a k
    assume pnd: "HasPendingEnq s' pa a" and pc_new: "program_counter s' pa \<in> {''E2'', ''E3''}"
    assume k_val: "Qback_arr s' k = a" and k_not_i: "k \<noteq> i_var s' pa"

    show False
    proof (cases "pa = p")
      case True
      (* Case A: Technical note for this proof step.*)
      hence is_p: "pa = p" by simp
      (* Step 1: Technical note for this proof step.*)
      from pnd hpd_eq is_p have call_a: "EnqCallInHis s p a (s_var s p)"
        unfolding HasPendingEnq_def
        by metis 
      
      from hI10_Enq_Call_Existence_s step_facts(6) have call_v: "EnqCallInHis s p (v_var s p) (s_var s p)"
        unfolding hI10_Enq_Call_Existence_def
        using step_facts(7) by blast 

      (* Step 2: usevalue uniquenessprove a = v_var s p.*)
      have a_val: "a = v_var s p"
      proof -
        (* Technical note for this invariant-preservation argument.*)
        from call_a obtain i where i_props: 
          "i < length (his_seq s)" 
          "act_pid (his_seq s ! i) = p" 
          "act_ssn (his_seq s ! i) = s_var s p" 
          "act_val (his_seq s ! i) = a"
          "act_name (his_seq s ! i) = enq" 
          "act_cr (his_seq s ! i) = call"
          unfolding EnqCallInHis_def
          by (metis in_set_conv_nth)
          
        from call_v obtain j where j_props: 
          "j < length (his_seq s)" 
          "act_pid (his_seq s ! j) = p" 
          "act_ssn (his_seq s ! j) = s_var s p" 
          "act_val (his_seq s ! j) = v_var s p"
          "act_name (his_seq s ! j) = enq" 
          "act_cr (his_seq s ! j) = call"
          unfolding EnqCallInHis_def
          by (metis in_set_conv_nth) 
           
        (* Technical note for this invariant-preservation argument.*)
        with val_uni show "a = v_var s p"
          unfolding hI8_Val_Unique_def
          by (metis INV hI5_SSN_Unique_def i_props(1,2,3,4,6)
              system_invariant_def)
      qed

      show False
      proof (cases "k = i_var s p")
        case True_k: True
        (* Technical note for this proof step.*)
        with is_p step_facts(3) k_not_i show False
          by (simp add: step_facts(4)) 
      next
        case False_k: False
        (* Technical note for this proof step.*)
        hence "Qback_arr s k = a" using k_val step_facts(4)
          by (simp add: step_facts(5)) 
        (* Technical note for this invariant-preservation argument.*)
        with hI14_Pending_Enq_Qback_Exclusivity_s is_p a_val pnd hpd_eq False_k step_facts(6) show False
          unfolding hI14_Pending_Enq_Qback_Exclusivity_def by (auto simp: step_facts)
      qed

    next
      case False_pa: False
      (* Case B: Technical note for this proof step.*)
      hence pa_old_pc: "program_counter s pa \<in> {''E2'', ''E3''}"
        using pc_new step_facts(5)
        by (simp add: step_facts(6))
      
      show False
      proof (cases "k = i_var s p")
        case True_k: True
        (* Technical note for this proof step.*)
        hence "a = v_var s p" using k_val step_facts(4)
          using step_facts(5) by auto 
        (* Step 1: Technical note for this proof step.*)
        from pnd hpd_eq have call_pa: "EnqCallInHis s pa a (s_var s pa)"
          unfolding HasPendingEnq_def
          by meson 
        
        from hI10_Enq_Call_Existence_s step_facts(6) have call_p: "EnqCallInHis s p (v_var s p) (s_var s p)"
          unfolding hI10_Enq_Call_Existence_def
          using step_facts(7) by blast 

        (* Step 2: Technical note for this proof step.*)
        have "pa = p"
        proof -
          from call_pa obtain i where i_props: 
            "i < length (his_seq s)" "act_val (his_seq s ! i) = a"
            "act_pid (his_seq s ! i) = pa" "act_name (his_seq s ! i) = enq" "act_cr (his_seq s ! i) = call"
            unfolding EnqCallInHis_def
            by (metis in_set_conv_nth) 
            
          from call_p obtain j where j_props: 
            "j < length (his_seq s)" "act_val (his_seq s ! j) = v_var s p"
            "act_pid (his_seq s ! j) = p" "act_name (his_seq s ! j) = enq" "act_cr (his_seq s ! j) = call"
            unfolding EnqCallInHis_def
            by (metis in_set_conv_nth) 

          (* Technical note for this proof step.*)
          have "i = j"
            using \<open>a = v_var s p\<close> val_uni
                  i_props(1,2,4,5) j_props(1,2,4,5)
            unfolding hI8_Val_Unique_def
            by metis
          
          (* Technical note for this proof step.*)
          with i_props j_props show ?thesis by simp
        qed

        (* Step 3: Technical note for this proof step.*)
        with False_pa show False by contradiction
      next
        case False_k: False
        (* Technical note for this invariant-preservation argument.*)
        hence "Qback_arr s k = a" using k_val step_facts(4)
          by (simp add: step_facts(5))
        with hI14_Pending_Enq_Qback_Exclusivity_s False_pa pa_old_pc pnd hpd_eq k_not_i show False
          unfolding hI14_Pending_Enq_Qback_Exclusivity_def using step_facts(3)
          by (simp add: step_facts(4)) 
      qed
    qed
  qed

  (* Step 2: Technical note for this proof step.*)
  show "\<forall>pa a. HasPendingEnq s' pa a \<and> program_counter s' pa = ''E1'' \<longrightarrow> 
               \<not> (\<exists>k. Qback_arr s' k = a)"
  proof (intro allI impI notI, elim exE conjE)
    fix pa a k
    assume pnd: "HasPendingEnq s' pa a" and pc_e1: "program_counter s' pa = ''E1'' "
    assume k_val: "Qback_arr s' k = a"

    (* Technical note for this transition-specific proof step.*)
    have is_not_p: "pa \<noteq> p" using pc_e1 step_facts(5)
      using step_facts(6) by auto 
    
    show False
    proof (cases "k = i_var s p")
      case True_k: True
      (* Technical note for this proof step.*)
      hence "a = v_var s p" using k_val step_facts(4)
        using step_facts(5) by fastforce 
      (* Step 1: Technical note for this proof step.*)
      from pnd hpd_eq have call_pa: "EnqCallInHis s pa a (s_var s pa)"
        unfolding HasPendingEnq_def
        by meson

        from hI10_Enq_Call_Existence_s step_facts(6) have call_p: "EnqCallInHis s p (v_var s p) (s_var s p)"
          unfolding hI10_Enq_Call_Existence_def
          using step_facts(7) by blast 

        (* Step 2: Technical note for this proof step.*)
        have "pa = p"
        proof -
          from call_pa obtain i where i_props: 
            "i < length (his_seq s)" "act_val (his_seq s ! i) = a"
            "act_pid (his_seq s ! i) = pa" "act_name (his_seq s ! i) = enq" "act_cr (his_seq s ! i) = call"
            unfolding EnqCallInHis_def
            by (metis in_set_conv_nth) 
            
          from call_p obtain j where j_props: 
            "j < length (his_seq s)" "act_val (his_seq s ! j) = v_var s p"
            "act_pid (his_seq s ! j) = p" "act_name (his_seq s ! j) = enq" "act_cr (his_seq s ! j) = call"
            unfolding EnqCallInHis_def
            by (metis in_set_conv_nth) 

          (* Technical note for this proof step.*)
        have "i = j"
          using \<open>a = v_var s p\<close> val_uni
                i_props(1,2,4,5) j_props(1,2,4,5)
          unfolding hI8_Val_Unique_def
          by metis
          
          (* Technical note for this proof step.*)
          with i_props j_props show ?thesis by simp
        qed

      (* Step 4: Technical note for this proof step.*)
      with is_not_p show False by contradiction
    next
      case False_k: False
      (* Technical note for this invariant-preservation argument.*)
      hence "Qback_arr s k = a" using k_val step_facts(4)
        by (simp add: step_facts(5)) 
      with hI14_Pending_Enq_Qback_Exclusivity_s is_not_p pnd hpd_eq pc_e1 show False
        unfolding hI14_Pending_Enq_Qback_Exclusivity_def using step_facts(5)
        using step_facts(6) by auto
    qed
  qed
qed


lemma hI15_Deq_Result_Exclusivity_E2_step:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "hI15_Deq_Result_Exclusivity s'"
proof -
  (* Step 1: Technical note for this proof step.*)
  have hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s" using INV unfolding system_invariant_def by blast
  have hI20_s: "hI28_Fresh_Enq_Immunity s" using INV unfolding system_invariant_def by blast
  have pc_p_E2: "program_counter s p = ''E2''" using STEP unfolding Sys_E2_def
    by (simp add: C_E2_def program_counter_def) 

  (* Step 2: Technical note for this transition-specific proof step.*)
  have step_facts:
    "his_seq s' = his_seq s"
    "x_var s' = x_var s"
    "s_var s' = s_var s"
    "v_var s' = v_var s"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def 
    by (auto simp: his_seq_def x_var_def s_var_def v_var_def Q_arr_def i_var_def fun_eq_iff)

  have pc_eqs: "\<And>q. program_counter s' q = (if q = p then ''E3'' else program_counter s q)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def by (auto simp: program_counter_def)

  (* Technical note for this proof step.*)
  have deq_ret_eq: "\<And>q a sn. DeqRetInHis s' q a sn = DeqRetInHis s q a sn"
    unfolding DeqRetInHis_def using step_facts by simp
    
  have pending_deq_eq: "\<And>q. HasPendingDeq s' q = HasPendingDeq s q"
    unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def using step_facts by simp

  (* Step 3: Technical note for this invariant-preservation argument.*)
  show ?thesis
    unfolding hI15_Deq_Result_Exclusivity_def
  proof (intro conjI allI impI, goal_cases)
    
    (* ================================================================= *)
    (* Case 1: Technical note for this transition-specific proof step.*)
    (* ================================================================= *)
    case (1 a p1 p2)
    (* Technical note for this proof step.*)
    (* Technical note for this proof step.*)
    show "\<not> (((\<exists>sn1. DeqRetInHis s' p1 a sn1) \<or> (program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a)) \<and> 
             ((\<exists>sn2. DeqRetInHis s' p2 a sn2) \<or> (program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a)))"
    proof -
      have "program_counter s' p1 = ''D4'' \<longleftrightarrow> program_counter s p1 = ''D4''" using pc_eqs
        by (simp add: pc_p_E2) 
      moreover have "program_counter s' p2 = ''D4'' \<longleftrightarrow> program_counter s p2 = ''D4''" using pc_eqs
        using pc_p_E2 by auto 
      ultimately show ?thesis
        using hI15_Deq_Result_Exclusivity_s 1 deq_ret_eq step_facts(2) unfolding hI15_Deq_Result_Exclusivity_def by auto
    qed

  next
    (* ================================================================= *)
    (* Case 2: Technical note for this proof step.*)
    (* ================================================================= *)
    case (2 q a k)
    (* Technical note for this proof step.*)
    
    (* Technical note for this proof step.*)
    show "\<not> (x_var s' q = a \<and> Q_arr s' k = a)"
    proof (rule notI, elim conjE)
      assume x_eq_a: "x_var s' q = a"
      assume q_eq_a: "Q_arr s' k = a"
      
      have pending_s: "HasPendingDeq s q" using 2(2) pending_deq_eq by simp
      have x_s_a: "x_var s q = a" using x_eq_a step_facts(2) by simp

      show False
      proof (cases "k = i_var s p")
        case False
        hence "Q_arr s' k = Q_arr s k" using step_facts(5) by simp
        with q_eq_a have "Q_arr s k = a" by simp
        thus False using hI15_Deq_Result_Exclusivity_s 2(1) pending_s x_s_a unfolding hI15_Deq_Result_Exclusivity_def by blast
      next
        case True
        hence "Q_arr s' k = v_var s p" using step_facts(5) by simp
        with q_eq_a have a_is_v: "a = v_var s p" by simp
        
        have "x_var s q \<noteq> v_var s p" 
          using deq_x_var_neq_enq_v_var[OF INV pc_p_E2] pending_s by blast
        thus False using x_s_a a_is_v by simp
      qed
    qed

  next
    (* ================================================================= *)
    (* Case 3: Technical note for this proof step.*)
    (* ================================================================= *)
    case (3 q a k)
    (* Technical note for this proof step.*)
    
    (* Technical note for this proof step.*)
    show "Q_arr s' k \<noteq> a"
    proof (rule notI)
      assume q_eq_a: "Q_arr s' k = a"
      
      (* Technical note for this proof step.*)
      from 3(2) obtain sn where ret_s': "DeqRetInHis s' q a sn" by blast
      have ret_s: "DeqRetInHis s q a sn" using ret_s' deq_ret_eq by simp

      show False
      proof (cases "k = i_var s p")
        case False
        hence "Q_arr s' k = Q_arr s k" using step_facts(5) by simp
        with q_eq_a have "Q_arr s k = a" by simp
        thus False using hI15_Deq_Result_Exclusivity_s 3(1) ret_s unfolding hI15_Deq_Result_Exclusivity_def by blast
      next
        case True
        hence "Q_arr s' k = v_var s p" using step_facts(5) by simp
        with q_eq_a have v_eq_a: "v_var s p = a" by simp
        
        have a_not_bot: "a \<noteq> BOT" using 3(1) unfolding Val_def BOT_def by auto
        
        (* Technical note for this invariant-preservation argument.*)
        from hI20_s[unfolded hI28_Fresh_Enq_Immunity_def, rule_format] pc_p_E2 v_eq_a a_not_bot 
        have "\<not> DeqRetInHis s q a sn" by blast
        
        thus False using ret_s by contradiction
      qed
    qed
  qed
qed


lemma hI16_BO_BT_No_HB_E2_step:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "hI16_BO_BT_No_HB s'"
proof -
  (* Step 1: extract the required invariant package.*)
  have hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s" using INV unfolding system_invariant_def by blast
  have hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s" using INV unfolding system_invariant_def by blast
  have sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" using INV unfolding system_invariant_def by blast
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast
  have hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" using INV unfolding system_invariant_def by blast
  have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast
  have lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" using INV unfolding system_invariant_def by blast
  have lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" using INV unfolding system_invariant_def by blast

  (* Step 2: Technical note for this transition-specific proof step.*)
  have pc_p_E2: "program_counter s p = ''E2''" using STEP unfolding Sys_E2_def by (simp add: C_E2_def program_counter_def)
  
  (* Technical note for this proof step.*)
  have step_facts:
    "his_seq s' = his_seq s"
    "x_var s' = x_var s"
    "s_var s' = s_var s"
    "v_var s' = v_var s"
    "i_var s' = i_var s"
    "j_var s' = j_var s"
    "l_var s' = l_var s"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def
    by (auto simp: his_seq_def x_var_def s_var_def v_var_def Q_arr_def i_var_def Qback_arr_def j_var_def l_var_def fun_eq_iff)

  have pc_eqs: "\<And>q. program_counter s' q = (if q = p then ''E3'' else program_counter s q)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def by (auto simp: program_counter_def)

  (* Step 3: Technical note for this proof step.*)
  have val_not_bot: "v_var s p \<noteq> BOT"
    using hI10_Enq_Call_Existence_s hI20_Enq_Val_Valid_s pc_p_E2 unfolding hI10_Enq_Call_Existence_def hI20_Enq_Val_Valid_def EnqCallInHis_def Let_def Val_def BOT_def
    using E2_implies_HasPendingEnq HasPendingEnq_imp_Val INV Val_def
    by blast 

  (* Step 4: invokeStandalone lemma, dischargevalue uniqueness.*)
  have v_var_unique: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<Longrightarrow> v_var s q \<noteq> v_var s p"
    using enq_v_var_unique[OF INV _ _] pc_p_E2 by fastforce

  (* Step 5: Technical note for this proof step.*)
  have idx_eq: "\<And>x. x \<noteq> v_var s p \<Longrightarrow> x \<noteq> BOT \<Longrightarrow> Idx s' x = Idx s x"
  proof -
    fix x assume "x \<noteq> v_var s p" "x \<noteq> BOT"
    have "(\<lambda>k. Qback_arr s' k = x) = (\<lambda>k. Qback_arr s k = x)"
    proof (rule ext)
      fix k
      show "(Qback_arr s' k = x) = (Qback_arr s k = x)"
      proof (cases "k = i_var s p")
        case True
        hence "Qback_arr s' k = v_var s p" using step_facts by simp
        hence left: "Qback_arr s' k \<noteq> x" using `x \<noteq> v_var s p` by simp
        have "Qback_arr s k = BOT" using sI3_E2_Slot_Exclusive_s pc_p_E2 True unfolding sI3_E2_Slot_Exclusive_def by auto
        hence right: "Qback_arr s k \<noteq> x" using `x \<noteq> BOT` by simp
        show ?thesis using left right by simp
      next
        case False
        thus ?thesis using step_facts by simp
      qed
    qed
    thus "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def by simp
  qed

  (* Step 6: Technical note for this invariant-preservation argument.*)
  have typeb_cases: "\<And>x. TypeB s' x \<Longrightarrow> x = v_var s p \<or> TypeB s x"
  proof -
    fix x assume "TypeB s' x"
    hence "QHas s' x \<or> (\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x)" unfolding TypeB_def by simp
    thus "x = v_var s p \<or> TypeB s x"
    proof (elim disjE, goal_cases)
      case 1
      then obtain k where "Q_arr s' k = x" unfolding QHas_def by blast
      thus ?case using step_facts pc_p_E2 unfolding TypeB_def QHas_def by (cases "k = i_var s p") auto
    next
      case 2
      then obtain q where "program_counter s' q = ''E2''" "v_var s' q = x" by blast
      have "q \<noteq> p" using `program_counter s' q = ''E2''` pc_eqs by auto
      thus ?case using `program_counter s' q = ''E2''` `v_var s' q = x` pc_eqs step_facts unfolding TypeB_def by auto
    qed
  qed

  (* Step 7: Technical note for this invariant-preservation argument.*)
  have typebt_subset: "\<And>x. TypeBT s' x \<Longrightarrow> x \<noteq> v_var s p \<Longrightarrow> x \<noteq> BOT \<Longrightarrow> TypeBT s x"
  proof -
    fix x assume tb_s': "TypeBT s' x" and "x \<noteq> v_var s p" and "x \<noteq> BOT"
    hence tb: "TypeB s' x" and inqb: "InQBack s' x" 
      and cond: "(\<forall>k<Idx s' x. Q_arr s' k = BOT) \<or> (\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT))"
      unfolding TypeBT_def by auto
    
    have tb_s: "TypeB s x" using typeb_cases[OF tb] `x \<noteq> v_var s p` by simp
    have idx_x: "Idx s' x = Idx s x" using idx_eq `x \<noteq> v_var s p` `x \<noteq> BOT` by simp
    
    have inqb_s: "InQBack s x"
    proof -
      from inqb obtain k where "Qback_arr s' k = x" unfolding InQBack_def by auto
      hence "Qback_arr s k = x" using step_facts `x \<noteq> v_var s p` by (cases "k = i_var s p") auto
      thus ?thesis unfolding InQBack_def by blast
    qed
    
    (* Technical note for this transition-specific proof step.*)
    have bot_imp: "\<And>k. Q_arr s' k = BOT \<Longrightarrow> Q_arr s k = BOT"
    proof -
      fix k assume "Q_arr s' k = BOT"
      show "Q_arr s k = BOT"
      proof (cases "k = i_var s p")
        case True
        hence "Q_arr s' k = v_var s p" using step_facts by simp
        with `Q_arr s' k = BOT` have "v_var s p = BOT" by simp
        with val_not_bot show ?thesis by contradiction
      next
        case False
        thus ?thesis using `Q_arr s' k = BOT` step_facts by simp
      qed
    qed
    
    have cond_s: "(\<forall>k<Idx s x. Q_arr s k = BOT) \<or> (\<exists>q. program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT))"
    proof -
      from cond show ?thesis
      proof (elim disjE)
        assume "\<forall>k<Idx s' x. Q_arr s' k = BOT"
        hence "\<forall>k<Idx s x. Q_arr s k = BOT" using bot_imp idx_x by simp
        thus ?thesis by blast
      next
        assume "\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)"
        then obtain q where q_props: "program_counter s' q = ''D3''" "j_var s' q \<le> Idx s' x" "Idx s' x < l_var s' q" "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT" by blast
        have "q \<noteq> p" using q_props(1) pc_eqs by auto
        hence "program_counter s q = ''D3''" "j_var s q = j_var s' q" "l_var s q = l_var s' q"
          using step_facts pc_eqs q_props(1) by auto
        have "\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT"
          using q_props(4) bot_imp idx_x `j_var s q = j_var s' q` by simp
        with `program_counter s q = ''D3''` `j_var s q = j_var s' q` `l_var s q = l_var s' q` q_props(2,3) idx_x
        have "program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT)" by simp
        thus ?thesis by blast
      qed
    qed
    thus "TypeBT s x" unfolding TypeBT_def using tb_s inqb_s cond_s by simp
  qed

(* Step 8: Technical note for this invariant-preservation argument.*)
  show ?thesis
    unfolding hI16_BO_BT_No_HB_def
  proof (intro allI impI, goal_cases)
    case (1 a b)
    (* ========================================================================= *)
    (* Technical note for this invariant-preservation argument.*)
    (* ========================================================================= *)
    show "\<not> HB_EnqRetCall s' a b"
    proof
      assume hb: "HB_EnqRetCall s' a b"

      have "a \<in> Val \<and> b \<in> Val"
      proof -
        from hb obtain p1 p2 sn1 sn2 k1 k2 :: nat where evs:
          "k1 < length (his_seq s')" "act_name (his_seq s' ! k1) = enq" "act_val (his_seq s' ! k1) = a"
          "k2 < length (his_seq s')" "act_name (his_seq s' ! k2) = enq" "act_val (his_seq s' ! k2) = b"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
          by (auto simp: op_name_def op_val_def)
        
        have evs_s: 
          "k1 < length (his_seq s)" "act_name (his_seq s ! k1) = enq" "act_val (his_seq s ! k1) = a"
          "k2 < length (his_seq s)" "act_name (his_seq s ! k2) = enq" "act_val (his_seq s ! k2) = b"
          using evs step_facts(1) by auto
          
        have "a \<in> Val" using hI20_Enq_Val_Valid_s evs_s(1,2,3) unfolding hI20_Enq_Val_Valid_def by blast
        moreover have "b \<in> Val" using hI20_Enq_Val_Valid_s evs_s(4,5,6) unfolding hI20_Enq_Val_Valid_def by blast
        ultimately show ?thesis by simp
      qed
      hence a_not_bot: "a \<noteq> BOT" and b_not_bot: "b \<noteq> BOT" by (auto simp: Val_def BOT_def)

      have hb_s: "HB_EnqRetCall s a b"
        using hb unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def match_ret_def match_call_def Let_def using step_facts by simp

      have a_BO_s': "a \<in> SetBO s'" and b_BT_s': "b \<in> SetBT s'" using 1 by auto

      consider (a_new) "a = v_var s p" 
             | (b_new_a_old) "a \<noteq> v_var s p" "b = v_var s p" 
             | (both_old) "a \<noteq> v_var s p" "b \<noteq> v_var s p"
        by blast

      thus False
      proof (cases, goal_cases)
        case 1
        (* Technical note for this invariant-preservation argument.*)
        hence True_a: "a = v_var s p" by simp
        
        have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = a \<and> act_cr (his_seq s ! k_ret) = ret"
          using hb_s unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def op_name_def op_val_def by force
        then obtain k_ret where k_ret_len: "k_ret < length (his_seq s)"
                            and k_ret_op: "act_name (his_seq s ! k_ret) = enq"
                            and k_ret_val: "act_val (his_seq s ! k_ret) = a"
                            and k_ret_cr: "act_cr (his_seq s ! k_ret) = ret" by blast
        
        from INV have hI7_His_WF_s: "hI7_His_WF s" unfolding system_invariant_def by blast
        have "\<exists>k_call < k_ret. act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret) \<and>
                               act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret) \<and>
                               act_name (his_seq s ! k_call) = enq \<and>
                               act_cr (his_seq s ! k_call) = call \<and>
                               act_val (his_seq s ! k_call) = a"
          using hI7_His_WF_s k_ret_len k_ret_op k_ret_val k_ret_cr unfolding hI7_His_WF_def Let_def by force
        then obtain k_call where k_call_len: "k_call < length (his_seq s)"
                             and k_call_op: "act_name (his_seq s ! k_call) = enq"
                             and k_call_val: "act_val (his_seq s ! k_call) = a"
                             and k_call_cr: "act_cr (his_seq s ! k_call) = call"
                             and k_call_pid: "act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret)"
                             and k_call_ssn: "act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret)"
          using k_ret_len using dual_order.strict_trans by auto
          
        have pending_p: "HasPendingEnq s p a" using hI1_E_Phase_Pending_Enq_s pc_p_E2 True_a unfolding hI1_E_Phase_Pending_Enq_def by blast
        have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and> 
                                            act_val (his_seq s ! j_call) = a \<and> 
                                            act_cr (his_seq s ! j_call) = call \<and> 
                                            act_pid (his_seq s ! j_call) = p \<and> 
                                            act_ssn (his_seq s ! j_call) = s_var s p"
          using pending_p unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by (metis in_set_conv_nth) 
        then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                             and j_call_op: "act_name (his_seq s ! j_call) = enq"
                             and j_call_val: "act_val (his_seq s ! j_call) = a"
                             and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                             and j_call_pid: "act_pid (his_seq s ! j_call) = p"
                             and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s p" by blast
                             
        from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
        have "k_call = j_call"
          using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
          unfolding hI8_Val_Unique_def by blast
          
        hence "act_pid (his_seq s ! k_ret) = p" and "act_ssn (his_seq s ! k_ret) = s_var s p"
          using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all
          
        moreover have "\<not> (\<exists>k < length (his_seq s). act_pid (his_seq s ! k) = p \<and> act_ssn (his_seq s ! k) = s_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_p unfolding HasPendingEnq_def EnqRetInHis_def Let_def match_ret_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by force
          
        ultimately show False using k_ret_len k_ret_cr by blast

      next
        case 2
        (* Technical note for this proof step.*)
        hence False_a: "a \<noteq> v_var s p" and True_b: "b = v_var s p" by simp_all
        
        have idx_b_s': "Idx s' b = i_var s p" 
          using True_b E2_Idx_v_var_eq_i_var by (simp add: INV STEP) 
        have idx_a_s': "Idx s' a = Idx s a" 
          using idx_eq False_a a_not_bot by simp
          
        (* Technical note for this invariant-preservation argument.*)
        have inqb_a_s: "InQBack s a"
        proof (rule ccontr)
          assume not_inq: "\<not> InQBack s a"
          
          have tb_a: "TypeB s a" using a_BO_s' False_a typeb_cases unfolding SetBO_def TypeBO_def by blast
          have "\<not> QHas s a"
            using HB_implies_InQBack INV hb_s not_inq by auto 
          then obtain q where q_E2: "program_counter s q = ''E2''" and q_v: "v_var s q = a"
            using tb_a unfolding TypeB_def by blast
            
          have pend_q: "HasPendingEnq s q a" using hI1_E_Phase_Pending_Enq_s q_E2 q_v unfolding hI1_E_Phase_Pending_Enq_def by blast
          
          have "\<exists>k<length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = a \<and> act_cr (his_seq s ! k) = ret"
            using hb_s unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def op_name_def op_val_def by force
          then obtain k_ret where k_ret_len: "k_ret < length (his_seq s)"
                              and k_ret_op: "act_name (his_seq s ! k_ret) = enq"
                              and k_ret_val: "act_val (his_seq s ! k_ret) = a"
                              and k_ret_cr: "act_cr (his_seq s ! k_ret) = ret" by blast
                              
          from INV have hI7_His_WF_s: "hI7_His_WF s" unfolding system_invariant_def by blast
          have "\<exists>k_call < k_ret. act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret) \<and>
                                 act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret) \<and>
                                 act_name (his_seq s ! k_call) = enq \<and>
                                 act_cr (his_seq s ! k_call) = call \<and>
                                 act_val (his_seq s ! k_call) = a"
            using hI7_His_WF_s k_ret_len k_ret_op k_ret_val k_ret_cr unfolding hI7_His_WF_def Let_def by force
          then obtain k_call where k_call_len: "k_call < length (his_seq s)"
                               and k_call_op: "act_name (his_seq s ! k_call) = enq"
                               and k_call_val: "act_val (his_seq s ! k_call) = a"
                               and k_call_cr: "act_cr (his_seq s ! k_call) = call"
                               and k_call_pid: "act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret)"
                               and k_call_ssn: "act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret)"
            using k_ret_len using dual_order.strict_trans by auto
            
          have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and> 
                                              act_val (his_seq s ! j_call) = a \<and> 
                                              act_cr (his_seq s ! j_call) = call \<and> 
                                              act_pid (his_seq s ! j_call) = q \<and> 
                                              act_ssn (his_seq s ! j_call) = s_var s q"
            using pend_q unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
            by (metis in_set_conv_nth) 
          then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                               and j_call_op: "act_name (his_seq s ! j_call) = enq"
                               and j_call_val: "act_val (his_seq s ! j_call) = a"
                               and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                               and j_call_pid: "act_pid (his_seq s ! j_call) = q"
                               and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s q" by blast
                               
          from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
          have "k_call = j_call"
            using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
            unfolding hI8_Val_Unique_def by blast
            
          hence "act_pid (his_seq s ! k_ret) = q" and "act_ssn (his_seq s ! k_ret) = s_var s q"
            using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all
            
          moreover have "\<not> (\<exists>k < length (his_seq s). act_pid (his_seq s ! k) = q \<and> act_ssn (his_seq s ! k) = s_var s q \<and> act_cr (his_seq s ! k) = ret)"
            using pend_q unfolding HasPendingEnq_def EnqRetInHis_def Let_def match_ret_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
            by force
            
          ultimately show False using k_ret_len k_ret_cr by blast
        qed

        have inq_a_s': "InQBack s' a" using inqb_a_s False_a step_facts(8) unfolding InQBack_def
          by (metis sI3_E2_Slot_Exclusive_def sI3_E2_Slot_Exclusive_s a_not_bot fun_upd_other pc_p_E2
              step_facts(9))
          
        (* Technical note for this invariant-preservation argument.*)
        have hb_target: "HB_EnqRetCall s a (v_var s p)" using hb_s True_b by simp
        have hI22_s: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast
        have "Idx s a < i_var s p"
          using hI22_s[unfolded hI30_Ticket_HB_Immunity_def, rule_format, of a p]
          using pc_p_E2 inqb_a_s False_a hb_target
          using INV hb_implies_idx_lt_i_var by auto
          
        have idx_lt: "Idx s' a < Idx s' b" 
          using `Idx s a < i_var s p` idx_a_s' idx_b_s' by simp

        (* Technical note for this invariant-preservation argument.*)
        have "TypeBT s' b" using b_BT_s' unfolding SetBT_def by auto
        hence bt_b_def: "(\<forall>k<Idx s' b. Q_arr s' k = BOT) \<or> 
                         (\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' b \<longrightarrow> Q_arr s' k = BOT))"
          unfolding TypeBT_def by auto
          
        show False
        proof (cases "\<forall>k<Idx s' b. Q_arr s' k = BOT")
          case True
          (* Technical note for this proof step.*)
          have "\<forall>k<Idx s' a. Q_arr s' k = BOT" using True idx_lt by simp
          (* Technical note for this invariant-preservation argument.*)
          hence "TypeBT s' a" 
            unfolding TypeBT_def using a_BO_s' unfolding SetBO_def TypeBO_def
            using inq_a_s' by auto 
          with a_BO_s' show False unfolding SetBO_def TypeBO_def by simp
        next
          case False
          (* Technical note for this transition-specific proof step.*)
          then obtain q where q_props:
            "program_counter s' q = ''D3''"
            "j_var s' q \<le> Idx s' b"
            "Idx s' b < l_var s' q"
            "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' b \<longrightarrow> Q_arr s' k = BOT"
            using bt_b_def by blast
            
          (* Technical note for this proof step.*)
          have "Idx s' a < j_var s' q"
          proof (rule ccontr)
            assume "\<not> (Idx s' a < j_var s' q)"
            hence "j_var s' q \<le> Idx s' a" by simp
            have "Idx s' a < l_var s' q" using idx_lt q_props(3) by simp
            have "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT" using q_props(4) idx_lt by simp
            have "TypeBT s' a"
              unfolding TypeBT_def
              using a_BO_s' inq_a_s' q_props(1) `j_var s' q \<le> Idx s' a` 
                    `Idx s' a < l_var s' q` `\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT`
              unfolding SetBO_def TypeBO_def by blast
            with a_BO_s' show False unfolding SetBO_def TypeBO_def by simp
          qed
            
          (* Technical note for this invariant-preservation argument.*)
          have q_neq_p: "q \<noteq> p" using q_props(1) pc_eqs by auto
          have pc_q_s: "program_counter s q = ''D3''" using q_props(1) q_neq_p pc_eqs by simp
          have idx_a_s: "Idx s a < j_var s q" using `Idx s' a < j_var s' q` idx_a_s' step_facts by simp
          have j_le_i: "j_var s q \<le> i_var s p" using q_props(2) step_facts idx_b_s' by simp
          have i_lt_l: "i_var s p < l_var s q" using q_props(3) step_facts idx_b_s' by simp
          
          have hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s" using INV unfolding system_invariant_def by blast
          have pend_q_s: "HasPendingDeq s q" using hI12_D_Phase_Pending_Deq_s pc_q_s unfolding hI12_D_Phase_Pending_Deq_def by blast

          have tb_a_s: "TypeB s a" using a_BO_s' False_a typeb_cases unfolding SetBO_def TypeBO_def by blast

          (* Technical note for this invariant-preservation argument.*)
          have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast
          have "\<not> HB_EnqRetCall s a (v_var s p)"
            using hI21_s[unfolded hI29_E2_Scanner_Immunity_def, rule_format, of p a q]
            using pc_p_E2 tb_a_s pend_q_s pc_q_s idx_a_s j_le_i i_lt_l
            using inqb_a_s by auto 
            
          thus False using hb_target by simp
        qed

      next
        case 3
        (* Technical note for this invariant-preservation argument.*)
        hence False_a: "a \<noteq> v_var s p" and False_b: "b \<noteq> v_var s p" by simp_all
        
        have a_BO_s: "a \<in> SetBO s \<or> a \<in> SetBT s"
          using typeb_cases a_BO_s' False_a unfolding SetBO_def SetBT_def TypeBO_def SetB_def by blast
          
        have b_BT_s: "b \<in> SetBT s" using typebt_subset b_BT_s' False_b b_not_bot unfolding SetBT_def by blast
        
        from a_BO_s show False
        proof
          assume "a \<in> SetBO s"
          with hI16_BO_BT_No_HB_s b_BT_s hb_s show False unfolding hI16_BO_BT_No_HB_def by blast
        next
          assume "a \<in> SetBT s"
          with hI17_BT_BT_No_HB_s b_BT_s hb_s show False unfolding hI17_BT_BT_No_HB_def by blast
        qed
      qed
    qed
  qed
qed


(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma hI17_BT_BT_No_HB_E2_step:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "hI17_BT_BT_No_HB s'"
proof -
  (* Step 1: extract the required invariant package.*)
  have hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s" using INV unfolding system_invariant_def by blast
  have sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" using INV unfolding system_invariant_def by blast
  have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" using INV unfolding system_invariant_def by blast
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast
  have sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s" using INV unfolding system_invariant_def by blast
  have hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" using INV unfolding system_invariant_def by blast
  have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast

  (* Step 2: Technical note for this transition-specific proof step.*)
  have pc_p_E2: "program_counter s p = ''E2''" using STEP unfolding Sys_E2_def by (simp add: C_E2_def program_counter_def)
  
  have step_facts:
    "his_seq s' = his_seq s"
    "x_var s' = x_var s"
    "s_var s' = s_var s"
    "v_var s' = v_var s"
    "i_var s' = i_var s"
    "j_var s' = j_var s"
    "l_var s' = l_var s"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def
    by (auto simp: his_seq_def x_var_def s_var_def v_var_def Q_arr_def i_var_def Qback_arr_def j_var_def l_var_def fun_eq_iff)

  have pc_eqs: "\<And>q. program_counter s' q = (if q = p then ''E3'' else program_counter s q)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def by (auto simp: program_counter_def)

  (* Step 3: Technical note for this proof step.*)
  have val_not_bot: "v_var s p \<noteq> BOT"
  proof -
    (* Step 1: Technical note for this invariant-preservation argument.*)
    have "EnqCallInHis s p (v_var s p) (s_var s p)"
      using hI10_Enq_Call_Existence_s pc_p_E2 unfolding hI10_Enq_Call_Existence_def by blast
      
    (* Step 2: Technical note for this proof step.*)
    then obtain k where k_len: "k < length (his_seq s)"
                    and k_op: "act_name (his_seq s ! k) = enq"
                    and k_val: "act_val (his_seq s ! k) = v_var s p"
      unfolding EnqCallInHis_def Let_def by (metis in_set_conv_nth)
      
    (* Step 3: Technical note for this invariant-preservation argument.*)
    moreover have "act_val (his_seq s ! k) \<in> Val"
      using hI20_Enq_Val_Valid_s k_len k_op unfolding hI20_Enq_Val_Valid_def by simp
      
    (* Step 4: Technical note for this proof step.*)
    ultimately have "v_var s p \<in> Val" by simp
    thus ?thesis unfolding Val_def BOT_def by auto
  qed

  (* Step 4: Technical note for this proof step.*)
  have idx_v_is_i: "Idx s' (v_var s p) = i_var s p"
    using E2_Idx_v_var_eq_i_var[OF INV STEP] .

  (* Step 5: Technical note for this proof step.*)
  have idx_eq: "\<And>x. x \<noteq> v_var s p \<Longrightarrow> x \<noteq> BOT \<Longrightarrow> Idx s' x = Idx s x"
  proof -
    fix x assume "x \<noteq> v_var s p" "x \<noteq> BOT"
    have "(\<lambda>k. Qback_arr s' k = x) = (\<lambda>k. Qback_arr s k = x)"
    proof (rule ext)
      fix k
      show "(Qback_arr s' k = x) = (Qback_arr s k = x)"
      proof (cases "k = i_var s p")
        case True
        hence "Qback_arr s' k = v_var s p" using step_facts by simp
        hence left: "Qback_arr s' k \<noteq> x" using `x \<noteq> v_var s p` by simp
        have "Qback_arr s k = BOT" using sI3_E2_Slot_Exclusive_s pc_p_E2 True unfolding sI3_E2_Slot_Exclusive_def by auto
        hence right: "Qback_arr s k \<noteq> x" using `x \<noteq> BOT` by simp
        show ?thesis using left right by simp
      next
        case False
        thus ?thesis using step_facts by simp
      qed
    qed
    thus "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def by simp
  qed

  (* Step 6: Technical note for this invariant-preservation argument.*)
  have typeb_cases: "\<And>x. TypeB s' x \<Longrightarrow> x = v_var s p \<or> TypeB s x"
  proof -
    fix x assume "TypeB s' x"
    hence "QHas s' x \<or> (\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x)" unfolding TypeB_def by simp
    thus "x = v_var s p \<or> TypeB s x"
    proof (elim disjE, goal_cases)
      case 1
      then obtain k where "Q_arr s' k = x" unfolding QHas_def by blast
      thus ?case using step_facts pc_p_E2 unfolding TypeB_def QHas_def by (cases "k = i_var s p") auto
    next
      case 2
      then obtain q where "program_counter s' q = ''E2''" "v_var s' q = x" by blast
      have "q \<noteq> p" using `program_counter s' q = ''E2''` pc_eqs by auto
      thus ?case using `program_counter s' q = ''E2''` `v_var s' q = x` pc_eqs step_facts unfolding TypeB_def by auto
    qed
  qed

  (* Step 7: Technical note for this invariant-preservation argument.*)
  have typebt_subset: "\<And>x. TypeBT s' x \<Longrightarrow> x \<noteq> v_var s p \<Longrightarrow> x \<noteq> BOT \<Longrightarrow> TypeBT s x"
  proof -
    fix x assume tb_s': "TypeBT s' x" and "x \<noteq> v_var s p" and "x \<noteq> BOT"
    hence tb: "TypeB s' x" and inqb: "InQBack s' x" 
      and cond: "(\<forall>k<Idx s' x. Q_arr s' k = BOT) \<or> (\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT))"
      unfolding TypeBT_def by auto
    
    have tb_s: "TypeB s x" using typeb_cases[OF tb] `x \<noteq> v_var s p` by simp
    have idx_x: "Idx s' x = Idx s x" using idx_eq `x \<noteq> v_var s p` `x \<noteq> BOT` by simp
    
    have inqb_s: "InQBack s x"
    proof -
      from inqb obtain k where "Qback_arr s' k = x" unfolding InQBack_def by auto
      hence "Qback_arr s k = x" using step_facts `x \<noteq> v_var s p` by (cases "k = i_var s p") auto
      thus ?thesis unfolding InQBack_def by blast
    qed
    
    have bot_imp: "\<And>k. Q_arr s' k = BOT \<Longrightarrow> Q_arr s k = BOT"
    proof -
      fix k assume "Q_arr s' k = BOT"
      show "Q_arr s k = BOT"
      proof (cases "k = i_var s p")
        case True
        hence "Q_arr s' k = v_var s p" using step_facts by simp
        with `Q_arr s' k = BOT` have "v_var s p = BOT" by simp
        with val_not_bot show ?thesis by contradiction
      next
        case False
        thus ?thesis using `Q_arr s' k = BOT` step_facts by simp
      qed
    qed
    
    have cond_s: "(\<forall>k<Idx s x. Q_arr s k = BOT) \<or> (\<exists>q. program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT))"
    proof -
      from cond show ?thesis
      proof (elim disjE)
        assume "\<forall>k<Idx s' x. Q_arr s' k = BOT"
        hence "\<forall>k<Idx s x. Q_arr s k = BOT" using bot_imp idx_x by simp
        thus ?thesis by blast
      next
        assume "\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)"
        then obtain q where q_props: "program_counter s' q = ''D3''" "j_var s' q \<le> Idx s' x" "Idx s' x < l_var s' q" "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT" by blast
        have "q \<noteq> p" using q_props(1) pc_eqs by auto
        hence "program_counter s q = ''D3''" "j_var s q = j_var s' q" "l_var s q = l_var s' q"
          using step_facts pc_eqs q_props(1) by auto
        have "\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT"
          using q_props(4) bot_imp idx_x `j_var s q = j_var s' q` by simp
        with `program_counter s q = ''D3''` `j_var s q = j_var s' q` `l_var s q = l_var s' q` q_props(2,3) idx_x
        have "program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT)" by simp
        thus ?thesis by blast
      qed
    qed
    thus "TypeBT s x" unfolding TypeBT_def using tb_s inqb_s cond_s by simp
  qed

  (* Step 8: Technical note for this invariant-preservation argument.*)
  show ?thesis
    unfolding hI17_BT_BT_No_HB_def
  proof (intro allI impI, goal_cases)
    case (1 a b)
    (* Technical note for this invariant-preservation argument.*)
    assume prems_raw: "a \<in> SetBT s' \<and> b \<in> SetBT s'"
    hence prems: "a \<in> SetBT s'" "b \<in> SetBT s'" by auto
    
    show "\<not> HB_EnqRetCall s' a b"
    proof
      (* Technical note for this proof step.*)
      assume hb: "HB_EnqRetCall s' a b"

      have "a \<in> Val \<and> b \<in> Val"
      proof -
        from hb obtain p1 p2 sn1 sn2 k1 k2 :: nat where evs:
          "k1 < length (his_seq s')" "act_name (his_seq s' ! k1) = enq" "act_val (his_seq s' ! k1) = a"
          "k2 < length (his_seq s')" "act_name (his_seq s' ! k2) = enq" "act_val (his_seq s' ! k2) = b"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
          by (auto simp: op_name_def op_val_def)
        
        have evs_s: 
          "k1 < length (his_seq s)" "act_name (his_seq s ! k1) = enq" "act_val (his_seq s ! k1) = a"
          "k2 < length (his_seq s)" "act_name (his_seq s ! k2) = enq" "act_val (his_seq s ! k2) = b"
          using evs step_facts(1) by auto
          
        have "a \<in> Val" using hI20_Enq_Val_Valid_s evs_s(1,2,3) unfolding hI20_Enq_Val_Valid_def by blast
        moreover have "b \<in> Val" using hI20_Enq_Val_Valid_s evs_s(4,5,6) unfolding hI20_Enq_Val_Valid_def by blast
        ultimately show ?thesis by simp
      qed
      hence a_not_bot: "a \<noteq> BOT" and b_not_bot: "b \<noteq> BOT" by (auto simp: Val_def BOT_def)

      have hb_s: "HB_EnqRetCall s a b"
        using hb unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def match_ret_def match_call_def Let_def using step_facts by simp

      have a_BT_s': "a \<in> SetBT s'" and b_BT_s': "b \<in> SetBT s'" using 1 by auto
      have tb_a_s': "TypeB s' a" using a_BT_s' unfolding SetBT_def TypeBT_def by auto

      consider (a_new) "a = v_var s p" 
             | (b_new_a_old) "a \<noteq> v_var s p" "b = v_var s p" 
             | (both_old) "a \<noteq> v_var s p" "b \<noteq> v_var s p"
        by blast

      thus False
      proof (cases, goal_cases)
        case 1
        (* ===================================================================== *)
        (* Technical note for this invariant-preservation argument.
           Technical note for this transition-specific proof step.*)
        (* ===================================================================== *)
        hence True_a: "a = v_var s p" by simp
        
        have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = a \<and> act_cr (his_seq s ! k_ret) = ret"
          using hb_s unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def op_name_def op_val_def by force
        then obtain k_ret where k_ret_len: "k_ret < length (his_seq s)"
                            and k_ret_op: "act_name (his_seq s ! k_ret) = enq"
                            and k_ret_val: "act_val (his_seq s ! k_ret) = a"
                            and k_ret_cr: "act_cr (his_seq s ! k_ret) = ret" by blast
        
        from INV have hI7_His_WF_s: "hI7_His_WF s" unfolding system_invariant_def by blast
        have "\<exists>k_call < k_ret. act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret) \<and>
                               act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret) \<and>
                               act_name (his_seq s ! k_call) = enq \<and>
                               act_cr (his_seq s ! k_call) = call \<and>
                               act_val (his_seq s ! k_call) = a"
          using hI7_His_WF_s k_ret_len k_ret_op k_ret_val k_ret_cr unfolding hI7_His_WF_def Let_def by force
        then obtain k_call where k_call_len: "k_call < length (his_seq s)"
                             and k_call_op: "act_name (his_seq s ! k_call) = enq"
                             and k_call_val: "act_val (his_seq s ! k_call) = a"
                             and k_call_cr: "act_cr (his_seq s ! k_call) = call"
                             and k_call_pid: "act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret)"
                             and k_call_ssn: "act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret)"
          using k_ret_len using dual_order.strict_trans by auto
          
        have pending_p: "HasPendingEnq s p a" using hI1_E_Phase_Pending_Enq_s pc_p_E2 True_a unfolding hI1_E_Phase_Pending_Enq_def by blast
        have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and> 
                                            act_val (his_seq s ! j_call) = a \<and> 
                                            act_cr (his_seq s ! j_call) = call \<and> 
                                            act_pid (his_seq s ! j_call) = p \<and> 
                                            act_ssn (his_seq s ! j_call) = s_var s p"
          using pending_p unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by (metis in_set_conv_nth) 
        then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                             and j_call_op: "act_name (his_seq s ! j_call) = enq"
                             and j_call_val: "act_val (his_seq s ! j_call) = a"
                             and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                             and j_call_pid: "act_pid (his_seq s ! j_call) = p"
                             and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s p" by blast
                             
        from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
        have "k_call = j_call"
          using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
          unfolding hI8_Val_Unique_def by blast
          
        hence "act_pid (his_seq s ! k_ret) = p" and "act_ssn (his_seq s ! k_ret) = s_var s p"
          using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all
          
        moreover have "\<not> (\<exists>k < length (his_seq s). act_pid (his_seq s ! k) = p \<and> act_ssn (his_seq s ! k) = s_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_p unfolding HasPendingEnq_def EnqRetInHis_def Let_def match_ret_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by force
          
        ultimately show False using k_ret_len k_ret_cr by blast

      next
        case 2
        (* ===================================================================== *)
        (* Technical note for this proof step.
           Technical note for this proof step.
           Technical note for this invariant-preservation argument.
           Technical note for this proof step.*)
        (* ===================================================================== *)
        hence False_a: "a \<noteq> v_var s p" and True_b: "b = v_var s p" by simp_all
        
        have idx_b_s': "Idx s' b = i_var s p" using True_b idx_v_is_i by simp
        have idx_a_s': "Idx s' a = Idx s a" using idx_eq False_a a_not_bot by simp
        
        (* Technical note for this proof step.*)
        have inqb_a_s: "InQBack s a" 
          using a_BT_s' False_a step_facts(8) unfolding SetBT_def TypeBT_def InQBack_def
          using step_facts(9) by auto 
          
        have hb_target: "HB_EnqRetCall s a (v_var s p)" using hb_s True_b by simp
        
        (* invoke hI22*)
        have hI22_s: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast
        have "Idx s a < i_var s p"
          using hI22_s[unfolded hI30_Ticket_HB_Immunity_def, rule_format, of a p]
          using pc_p_E2 inqb_a_s False_a hb_target
          using INV hb_implies_idx_lt_i_var by auto 
          
        have idx_lt: "Idx s' a < Idx s' b" using `Idx s a < i_var s p` idx_a_s' idx_b_s' by simp

        have "TypeBT s' b" using b_BT_s' unfolding SetBT_def by auto
        hence bt_b_def: "(\<forall>k<Idx s' b. Q_arr s' k = BOT) \<or> 
                         (\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' b \<longrightarrow> Q_arr s' k = BOT))"
          unfolding TypeBT_def by auto
          
        show False
        proof (cases "\<forall>k<Idx s' b. Q_arr s' k = BOT")
          case True
          (* Technical note for this proof step.*)
          have q_arr_a_bot: "Q_arr s' (Idx s' a) = BOT" using True idx_lt by simp
          
          (* Technical note for this proof step.*)
          have not_qhas_a: "\<not> QHas s' a"
          proof
            assume "QHas s' a"
            then obtain k_a where ka_prop: "Q_arr s' k_a = a" unfolding QHas_def by blast
            
            (* Technical note for this proof step.*)
            have "Qback_arr s' k_a = a"
            proof (cases "k_a = i_var s p")
              case True
              hence "Q_arr s' k_a = v_var s p" using step_facts(8) by simp
              with ka_prop have "a = v_var s p" by simp
              with False_a show ?thesis by contradiction
            next
              case False
              hence "Q_arr s k_a = a" using ka_prop step_facts(8) by simp
              have "Q_arr s k_a \<noteq> BOT" using a_not_bot `Q_arr s k_a = a` by simp
              hence "Qback_arr s k_a = Q_arr s k_a" using sI8_Q_Qback_Sync_s unfolding sI8_Q_Qback_Sync_def
                by metis 
              hence "Qback_arr s k_a = a" using `Q_arr s k_a = a` by simp
              thus ?thesis using False step_facts(9) by simp
            qed
            
            (* Technical note for this transition-specific proof step.*)
            have "k_a = Idx s a"
              using sI12_D3_Scanned_Prefix_s `Qback_arr s' k_a = a` inqb_a_s a_not_bot False_a step_facts(9)
              unfolding sI12_D3_Scanned_Prefix_def Idx_def AtIdx_def InQBack_def
              by (metis INV Idx_eq_j_and_Q_BOT_implies_not_TypeB fun_upd_apply
                  idx_a_s' inqb_a_s q_arr_a_bot step_facts(8) tb_a_s' typeb_cases
                  val_not_bot)
              
            hence "k_a = Idx s' a" using idx_a_s' by simp
            hence "Q_arr s' (Idx s' a) = a" using ka_prop by simp
            with q_arr_a_bot a_not_bot show False by simp
          qed
          
          (* Technical note for this invariant-preservation argument.*)
          have "\<exists>q_old. program_counter s' q_old = ''E2'' \<and> v_var s' q_old = a" 
            using tb_a_s' not_qhas_a unfolding TypeB_def by blast
          then obtain q_old where q_old_E2: "program_counter s' q_old = ''E2''" and q_old_v: "v_var s' q_old = a" by blast
          
          have q_old_neq_p: "q_old \<noteq> p" using q_old_v False_a step_facts(4) by auto
          hence pc_q_old_s: "program_counter s q_old = ''E2''" using q_old_E2 pc_eqs by simp
          have v_q_old_s: "v_var s q_old = a" using q_old_v q_old_neq_p step_facts(4) by simp
          
          (* Technical note for this invariant-preservation argument.*)
          have "HasPendingEnq s q_old a" using hI1_E_Phase_Pending_Enq_s pc_q_old_s v_q_old_s unfolding hI1_E_Phase_Pending_Enq_def by blast
          hence no_ret_a: "\<forall>e\<in>set (his_seq s). \<not> (act_pid e = q_old \<and> act_ssn e = s_var s q_old \<and> act_cr e = ret)"
            unfolding HasPendingEnq_def EnqRetInHis_def Let_def by auto
            
          (* Technical note for this invariant-preservation argument.*)
          have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = a \<and> act_cr (his_seq s ! k_ret) = ret"
            using hb_s unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def op_name_def op_val_def by force
          then obtain k_ret where k_ret_len: "k_ret < length (his_seq s)"
                              and k_ret_val: "act_val (his_seq s ! k_ret) = a"
                              and k_ret_cr: "act_cr (his_seq s ! k_ret) = ret" 
                              and k_ret_op: "act_name (his_seq s ! k_ret) = enq" by blast
                              
          from INV have hI7_His_WF_s: "hI7_His_WF s" unfolding system_invariant_def by blast
          have "\<exists>k_call < k_ret. act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret) \<and>
                                 act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret) \<and>
                                 act_name (his_seq s ! k_call) = enq \<and>
                                 act_cr (his_seq s ! k_call) = call \<and>
                                 act_val (his_seq s ! k_call) = a"
            using hI7_His_WF_s k_ret_len k_ret_op k_ret_val k_ret_cr unfolding hI7_His_WF_def Let_def by force
          then obtain k_call where k_call_len: "k_call < length (his_seq s)"
                               and k_call_op: "act_name (his_seq s ! k_call) = enq"
                               and k_call_val: "act_val (his_seq s ! k_call) = a"
                               and k_call_cr: "act_cr (his_seq s ! k_call) = call"
                               and k_call_pid: "act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret)"
                               and k_call_ssn: "act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret)"
            using k_ret_len using dual_order.strict_trans by auto
            
          have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and> 
                                              act_val (his_seq s ! j_call) = a \<and> 
                                              act_cr (his_seq s ! j_call) = call \<and> 
                                              act_pid (his_seq s ! j_call) = q_old \<and> 
                                              act_ssn (his_seq s ! j_call) = s_var s q_old"
            using `HasPendingEnq s q_old a` unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
            by (metis in_set_conv_nth) 
          then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                               and j_call_op: "act_name (his_seq s ! j_call) = enq"
                               and j_call_val: "act_val (his_seq s ! j_call) = a"
                               and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                               and j_call_pid: "act_pid (his_seq s ! j_call) = q_old"
                               and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s q_old" by blast
                               
          from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
          have "k_call = j_call"
            using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
            unfolding hI8_Val_Unique_def by blast
            
          hence "act_pid (his_seq s ! k_ret) = q_old" and "act_ssn (his_seq s ! k_ret) = s_var s q_old"
            using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all
            
          with no_ret_a k_ret_len k_ret_cr show False by force
          
        next
          case False
          (* Reasoning branch 3: scannerinvariant.*)
          then obtain q where q_props:
            "program_counter s' q = ''D3''"
            "j_var s' q \<le> Idx s' b"
            "Idx s' b < l_var s' q"
            "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' b \<longrightarrow> Q_arr s' k = BOT"
            using bt_b_def by blast
            
          have "Idx s' a < j_var s' q"
          proof (rule ccontr)
            assume "\<not> (Idx s' a < j_var s' q)"
            hence "j_var s' q \<le> Idx s' a" by simp
            have "Idx s' a < l_var s' q" using idx_lt q_props(3) by simp
            have "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT" using q_props(4) idx_lt by simp
            have "TypeBT s' a"
              unfolding TypeBT_def
              using tb_a_s' q_props(1) `j_var s' q \<le> Idx s' a` 
                    `Idx s' a < l_var s' q` `\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT`
              unfolding SetBO_def TypeBO_def
              by (metis INV Idx_eq_j_and_Q_BOT_implies_not_TypeB True_b
                  \<open>Model.j_var s' q \<le> Idx s' a\<close> a_not_bot fun_upd_other idx_a_s'
                  idx_lt idx_v_is_i inqb_a_s linorder_neq_iff q_props(4) step_facts(8)
                  tb_a_s' typeb_cases) 
            with a_BT_s' show False unfolding SetBT_def TypeBT_def
              by (metis (lifting) INV Idx_eq_j_and_Q_BOT_implies_not_TypeB True_b
                  \<open>Model.j_var s' q \<le> Idx s' a\<close> a_not_bot b_not_bot fun_upd_other
                  fun_upd_same idx_a_s' idx_lt idx_v_is_i inqb_a_s q_props(4)
                  step_facts(8) typeb_cases) 

          qed
          (* Technical note for this invariant-preservation argument.*)
          
          have q_neq_p: "q \<noteq> p" using q_props(1) pc_eqs by auto
          have pc_q_s: "program_counter s q = ''D3''" using q_props(1) q_neq_p pc_eqs by simp
          have idx_a_s: "Idx s a < j_var s q" using `Idx s' a < j_var s' q` idx_a_s' step_facts by simp
          have j_le_i: "j_var s q \<le> i_var s p" using q_props(2) step_facts idx_b_s' by simp
          have i_lt_l: "i_var s p < l_var s q" using q_props(3) step_facts idx_b_s' by simp
          
          have hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s" using INV unfolding system_invariant_def by blast
          have pend_q_s: "HasPendingDeq s q" using hI12_D_Phase_Pending_Deq_s pc_q_s unfolding hI12_D_Phase_Pending_Deq_def by blast

          have tb_a_s: "TypeB s a" using a_BT_s' False_a typeb_cases unfolding SetBT_def TypeBT_def by blast

          have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast
          have "\<not> HB_EnqRetCall s a (v_var s p)"
            using hI21_s[unfolded hI29_E2_Scanner_Immunity_def, rule_format, of p a q]
            using pc_p_E2 tb_a_s pend_q_s pc_q_s idx_a_s j_le_i i_lt_l
            using inqb_a_s by fastforce 
            
          thus False using hb_target by simp
        qed

      next
        case 3
        (* Technical note for this invariant-preservation argument.*)
        hence False_a: "a \<noteq> v_var s p" and False_b: "b \<noteq> v_var s p" by simp_all
        
        have a_BT_s: "a \<in> SetBT s" using typebt_subset a_BT_s' False_a a_not_bot unfolding SetBT_def by blast
        have b_BT_s: "b \<in> SetBT s" using typebt_subset b_BT_s' False_b b_not_bot unfolding SetBT_def by blast
        
        with hI17_BT_BT_No_HB_s hb_s show False unfolding hI17_BT_BT_No_HB_def
          by (simp add: a_BT_s)
      qed
    qed
  qed
qed


(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma hI18_Idx_Order_No_Rev_HB_E2_step:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "hI18_Idx_Order_No_Rev_HB s'"
proof -
  (* Step 1: Technical note for this proof step.*)
  have hI18_Idx_Order_No_Rev_HB_s: "hI18_Idx_Order_No_Rev_HB s" using INV unfolding system_invariant_def by blast
  have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast
  have sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" using INV unfolding system_invariant_def by blast
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast
  
  (* Step 2: unfold the basic concrete facts of the E2 step.*)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def 
                i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def 
                lin_seq_def his_seq_def

  have pc_p_E2: "program_counter s p = ''E2''" 
    using STEP unfolding Sys_E2_def C_E2_def bridge by auto
  
  have step_facts:
    "his_seq s' = his_seq s"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "v_var s' = v_var s"
    "s_var s' = s_var s"
    "i_var s' = i_var s"
    "j_var s' = j_var s"
    "l_var s' = l_var s"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge
    by (auto simp: fun_eq_iff)

  (* Step 3: Technical note for this invariant-preservation argument.*)
  have idx_v_is_i: "Idx s' (v_var s p) = i_var s p" 
  proof -
    have hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" using INV unfolding system_invariant_def by blast
    have pend_p: "HasPendingEnq s p (v_var s p)" 
      using hI1_E_Phase_Pending_Enq_s pc_p_E2 unfolding hI1_E_Phase_Pending_Enq_def by blast
      
    have no_other_v: "\<forall>k. k \<noteq> i_var s p \<longrightarrow> Qback_arr s k \<noteq> v_var s p"
      using hI14_Pending_Enq_Qback_Exclusivity_s pend_p pc_p_E2 unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
      
    have "\<forall>k. Qback_arr s' k = v_var s p \<longleftrightarrow> k = i_var s p"
    proof
      fix k show "Qback_arr s' k = v_var s p \<longleftrightarrow> k = i_var s p"
      proof (cases "k = i_var s p")
        case True thus ?thesis using step_facts(8) by simp
      next
        case False
        hence "Qback_arr s' k = Qback_arr s k" using step_facts(8) by simp
        moreover have "Qback_arr s k \<noteq> v_var s p" using no_other_v False by simp
        ultimately show ?thesis using False by simp
      qed
    qed
    thus ?thesis unfolding Idx_def AtIdx_def by (metis (mono_tags, lifting) someI_ex)
  qed

  (* Step 4: Technical note for this proof step.*)
  have idx_eq: "\<And>x. x \<noteq> v_var s p \<Longrightarrow> x \<noteq> BOT \<Longrightarrow> Idx s' x = Idx s x"
  proof -
    fix x assume "x \<noteq> v_var s p" "x \<noteq> BOT"
    have qback_i_bot: "Qback_arr s (i_var s p) = BOT"
      using sI3_E2_Slot_Exclusive_s pc_p_E2 unfolding sI3_E2_Slot_Exclusive_def by blast

    have "(\<lambda>k. Qback_arr s' k = x) = (\<lambda>k. Qback_arr s k = x)"
    proof (rule ext)
      fix k show "(Qback_arr s' k = x) = (Qback_arr s k = x)"
      proof (cases "k = i_var s p")
        case True
        have "Qback_arr s' k = v_var s p" using step_facts(8) True by simp
        moreover have "Qback_arr s k = BOT" using qback_i_bot True by simp
        ultimately show ?thesis using \<open>x \<noteq> v_var s p\<close> \<open>x \<noteq> BOT\<close> by simp
      next
        case False
        thus ?thesis using step_facts(8) by simp
      qed
    qed
    thus "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def by simp
  qed

(* ========================================================================= *)
  (* Step 5: Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  show ?thesis
    unfolding hI18_Idx_Order_No_Rev_HB_def
  proof (intro allI impI)
    fix a b
    (* Technical note for this proof step.*)
    assume prems_raw: "InQBack s' a \<and> InQBack s' b \<and> Idx s' a < Idx s' b"
    hence prems: "InQBack s' a" "InQBack s' b" "Idx s' a < Idx s' b" by auto
    
    show "\<not> HB_EnqRetCall s' b a"
    proof
      assume hb: "HB_EnqRetCall s' b a"
      
      have "a \<in> Val \<and> b \<in> Val"
      proof -
        from hb obtain p1 p2 sn1 sn2 k1 k2 :: nat where evs:
          "k1 < length (his_seq s')" "act_name (his_seq s' ! k1) = enq" "act_val (his_seq s' ! k1) = b"
          "k2 < length (his_seq s')" "act_name (his_seq s' ! k2) = enq" "act_val (his_seq s' ! k2) = a"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
          by (auto simp: op_name_def op_val_def)
        
        have evs_s: 
          "k1 < length (his_seq s)" "act_name (his_seq s ! k1) = enq" "act_val (his_seq s ! k1) = b"
          "k2 < length (his_seq s)" "act_name (his_seq s ! k2) = enq" "act_val (his_seq s ! k2) = a"
          using evs step_facts(1) by auto
          
        have "b \<in> Val" using hI20_Enq_Val_Valid_s evs_s(1,2,3) unfolding hI20_Enq_Val_Valid_def by blast
        moreover have "a \<in> Val" using hI20_Enq_Val_Valid_s evs_s(4,5,6) unfolding hI20_Enq_Val_Valid_def by blast
        ultimately show ?thesis by simp
      qed
      hence a_not_bot: "a \<noteq> BOT" and b_not_bot: "b \<noteq> BOT" by (auto simp: Val_def BOT_def)

      have hb_s: "HB_EnqRetCall s b a"
        using hb unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def match_ret_def match_call_def Let_def 
        using step_facts(1) by simp

      (* Technical note for this proof step.*)
      consider (b_new) "b = v_var s p" 
             | (a_new_b_old) "b \<noteq> v_var s p" "a = v_var s p" 
             | (both_old) "b \<noteq> v_var s p" "a \<noteq> v_var s p"
        by blast
        
      thus False
      proof (cases, goal_cases)
        case 1
        (* ===================================================================== *)
        (* Branch 1: Technical note for this invariant-preservation argument.
           Technical note for this proof step.*)
        (* ===================================================================== *)
        hence True_b: "b = v_var s p" by simp
        
        from hb_s obtain p1 p2 sn1 sn2 k1 k2 :: nat where hb_ret:
          "k1 < length (his_seq s)"
          "act_name (his_seq s ! k1) = enq" 
          "act_val (his_seq s ! k1) = b"
          "act_cr (his_seq s ! k1) = ret"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
          using step_facts(1) by (auto simp: op_name_def op_val_def)
        
        from INV have hI7_His_WF_s: "hI7_His_WF s" unfolding system_invariant_def by blast
        have "\<exists>k_call < k1. act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k1) \<and>
                            act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k1) \<and>
                            act_name (his_seq s ! k_call) = enq \<and>
                            act_cr (his_seq s ! k_call) = call \<and>
                            act_val (his_seq s ! k_call) = b"
          using hI7_His_WF_s hb_ret(1) hb_ret(2) hb_ret(3) hb_ret(4) unfolding hI7_His_WF_def Let_def by force
        then obtain k_call where k_call_len: "k_call < length (his_seq s)"
                             and k_call_op: "act_name (his_seq s ! k_call) = enq"
                             and k_call_val: "act_val (his_seq s ! k_call) = b"
                             and k_call_cr: "act_cr (his_seq s ! k_call) = call"
                             and k_call_pid: "act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k1)"
                             and k_call_ssn: "act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k1)"
          using hb_ret(1) using dual_order.strict_trans by auto
          
        have pending_p: "HasPendingEnq s p b" using hI1_E_Phase_Pending_Enq_s pc_p_E2 True_b unfolding hI1_E_Phase_Pending_Enq_def by blast
        have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and> 
                                            act_val (his_seq s ! j_call) = b \<and> 
                                            act_cr (his_seq s ! j_call) = call \<and> 
                                            act_pid (his_seq s ! j_call) = p \<and> 
                                            act_ssn (his_seq s ! j_call) = s_var s p"
          using pending_p unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by (metis in_set_conv_nth) 
        then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                             and j_call_op: "act_name (his_seq s ! j_call) = enq"
                             and j_call_val: "act_val (his_seq s ! j_call) = b"
                             and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                             and j_call_pid: "act_pid (his_seq s ! j_call) = p"
                             and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s p" by blast
                             
        from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
        have "k_call = j_call"
          using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
          unfolding hI8_Val_Unique_def by blast
          
        hence "act_pid (his_seq s ! k1) = p" and "act_ssn (his_seq s ! k1) = s_var s p"
          using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all
          
        moreover have "\<not> (\<exists>k < length (his_seq s). act_pid (his_seq s ! k) = p \<and> act_ssn (his_seq s ! k) = s_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_p unfolding HasPendingEnq_def EnqRetInHis_def Let_def match_ret_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by force
          
        ultimately show False using hb_ret(1) hb_ret(4) by blast

      next
        case 2
        (* ===================================================================== *)
        (* Branch 2: Technical note for this proof step.*)
        (* ===================================================================== *)
        hence False_b: "b \<noteq> v_var s p" and True_a: "a = v_var s p" by simp_all
        
        have inqb_b_s: "InQBack s b" 
          using prems(2) step_facts(8) False_b unfolding InQBack_def by (auto split: if_splits)
        have idx_b_s: "Idx s' b = Idx s b" using idx_eq False_b b_not_bot by simp

        have idx_lt: "i_var s p < Idx s b" using prems(3) True_a idx_b_s idx_v_is_i by simp
        have hb_target: "HB_EnqRetCall s b (v_var s p)" using hb_s True_a by simp
        
        (* Technical note for this invariant-preservation argument.*)
        have "Idx s b < i_var s p"
          using hb_implies_idx_lt_i_var[OF INV pc_p_E2 inqb_b_s False_b hb_target] .
          
        with idx_lt show False by simp

      next
        case 3
        (* ===================================================================== *)
        (* Technical note for this invariant-preservation argument.*)
        (* ===================================================================== *)
        hence False_b: "b \<noteq> v_var s p" and False_a: "a \<noteq> v_var s p" by simp_all
        
        have inqb_b_s: "InQBack s b" 
          using prems(2) step_facts(8) False_b unfolding InQBack_def by (auto split: if_splits)
        have idx_b_s: "Idx s' b = Idx s b" using idx_eq False_b b_not_bot by simp
        
        have inqb_a_s: "InQBack s a" 
          using prems(1) step_facts(8) False_a unfolding InQBack_def by (auto split: if_splits)
        have idx_a_s: "Idx s' a = Idx s a" using idx_eq False_a a_not_bot by simp
        
        have "Idx s a < Idx s b" using prems(3) idx_a_s idx_b_s by simp
        thus False using hI18_Idx_Order_No_Rev_HB_s inqb_a_s inqb_b_s hb_s unfolding hI18_Idx_Order_No_Rev_HB_def by blast
      qed
    qed
  qed
qed


lemma hI19_Scanner_Catches_Later_Enq_E2_step:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "hI19_Scanner_Catches_Later_Enq s'"
proof -
  (* Step 1: extract the required invariant package.*)
  have hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s" using INV unfolding system_invariant_def by blast
  have sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" using INV unfolding system_invariant_def by blast
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast
  have hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" using INV unfolding system_invariant_def by blast
  have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast

  (* Step 2: Technical note for this transition-specific proof step.*)
  have pc_p_E2: "program_counter s p = ''E2''" using STEP unfolding Sys_E2_def by (simp add: C_E2_def program_counter_def)
  
  have step_facts:
    "his_seq s' = his_seq s"
    "x_var s' = x_var s"
    "s_var s' = s_var s"
    "v_var s' = v_var s"
    "i_var s' = i_var s"
    "j_var s' = j_var s"
    "l_var s' = l_var s"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def
    by (auto simp: his_seq_def x_var_def s_var_def v_var_def Q_arr_def i_var_def Qback_arr_def j_var_def l_var_def fun_eq_iff)

  have pc_eqs: "\<And>q. program_counter s' q = (if q = p then ''E3'' else program_counter s q)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def by (auto simp: program_counter_def)

  (* Step 3: Technical note for this proof step.*)
  have val_not_bot: "v_var s p \<noteq> BOT"
    using hI10_Enq_Call_Existence_s hI20_Enq_Val_Valid_s pc_p_E2 unfolding hI10_Enq_Call_Existence_def hI20_Enq_Val_Valid_def EnqCallInHis_def Let_def Val_def BOT_def
    by (metis ex_least_nat_le in_set_conv_nth insertCI
        mem_Collect_eq) 

  (* Step 4: Technical note for this invariant-preservation argument.*)
  have typeb_cases: "\<And>x. TypeB s' x \<Longrightarrow> x = v_var s p \<or> TypeB s x"
  proof -
    fix x assume "TypeB s' x"
    hence "QHas s' x \<or> (\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x)" unfolding TypeB_def by simp
    thus "x = v_var s p \<or> TypeB s x"
    proof (elim disjE, goal_cases)
      case 1
      then obtain k where "Q_arr s' k = x" unfolding QHas_def by blast
      thus ?case using step_facts pc_p_E2 unfolding TypeB_def QHas_def by (cases "k = i_var s p") auto
    next
      case 2
      then obtain q where "program_counter s' q = ''E2''" "v_var s' q = x" by blast
      have "q \<noteq> p" using 2(1) pc_eqs
        using \<open>program_counter s' q = ''E2''\<close> by auto 
      thus ?case using 2 pc_eqs step_facts unfolding TypeB_def
        by metis 
    qed
  qed

  (* Step 5: Technical note for this proof step.*)
  have idx_eq: "\<And>x. x \<noteq> v_var s p \<Longrightarrow> x \<noteq> BOT \<Longrightarrow> Idx s' x = Idx s x"
  proof -
    fix x assume "x \<noteq> v_var s p" "x \<noteq> BOT"
    have "(\<lambda>k. Qback_arr s' k = x) = (\<lambda>k. Qback_arr s k = x)"
    proof (rule ext)
      fix k
      show "(Qback_arr s' k = x) = (Qback_arr s k = x)"
      proof (cases "k = i_var s p")
        case True
        hence "Qback_arr s' k = v_var s p" using step_facts by simp
        hence left: "Qback_arr s' k \<noteq> x" using \<open>x \<noteq> v_var s p\<close> by simp
        have "Qback_arr s k = BOT" using sI3_E2_Slot_Exclusive_s pc_p_E2 True unfolding sI3_E2_Slot_Exclusive_def by auto
        hence right: "Qback_arr s k \<noteq> x" using \<open>x \<noteq> BOT\<close> by simp
        show ?thesis using left right by simp
      next
        case False
        thus ?thesis using step_facts by simp
      qed
    qed
    thus "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def by simp
  qed

  (* Step 6: Technical note for this invariant-preservation argument.*)
  show ?thesis
    unfolding hI19_Scanner_Catches_Later_Enq_def
  proof (intro allI impI, goal_cases)
    case (1 a b)
    (* Technical note for this proof step.*)
    show "\<not> HB_EnqRetCall s' a b"
    proof
      assume hb: "HB_EnqRetCall s' a b"
      
      (* Technical note for this invariant-preservation argument.*)
      have "a \<in> Val \<and> b \<in> Val"
      proof -
        from hb obtain p1 p2 sn1 sn2 k1 k2 :: nat where evs:
          "k1 < length (his_seq s')" "act_name (his_seq s' ! k1) = enq" "act_val (his_seq s' ! k1) = a"
          "k2 < length (his_seq s')" "act_name (his_seq s' ! k2) = enq" "act_val (his_seq s' ! k2) = b"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
          by (auto simp: op_name_def op_val_def)
        
        have evs_s: 
          "k1 < length (his_seq s)" "act_name (his_seq s ! k1) = enq" "act_val (his_seq s ! k1) = a"
          "k2 < length (his_seq s)" "act_name (his_seq s ! k2) = enq" "act_val (his_seq s ! k2) = b"
          using evs step_facts(1) by auto
          
        have "a \<in> Val" using hI20_Enq_Val_Valid_s evs_s(1,2,3) unfolding hI20_Enq_Val_Valid_def by blast
        moreover have "b \<in> Val" using hI20_Enq_Val_Valid_s evs_s(4,5,6) unfolding hI20_Enq_Val_Valid_def by blast
        ultimately show ?thesis by simp
      qed
      hence a_not_bot: "a \<noteq> BOT" and b_not_bot: "b \<noteq> BOT" by (auto simp: Val_def BOT_def)

      (* Technical note for this proof step.*)
      have hb_s: "HB_EnqRetCall s a b"
        using hb unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def match_ret_def match_call_def Let_def using step_facts by simp

      (* Technical note for this proof step.*)
      have tb_a_s': "TypeB s' a" and tb_b_s': "TypeB s' b" using 1 by auto
      have idx_lt_s': "Idx s' a < Idx s' b" using 1 by auto
      
      (* extractscanner q*)
      obtain q where q_props:
        "HasPendingDeq s' q"
        "program_counter s' q = ''D3''"
        "Idx s' a < j_var s' q"
        "j_var s' q \<le> Idx s' b"
        "Idx s' b < l_var s' q"
        using "1" by auto 

      (* Technical note for this proof step.*)
      have q_neq_p: "q \<noteq> p" using q_props(2) pc_eqs by auto
      have q_old_props: "program_counter s q = ''D3''" "j_var s q = j_var s' q" "l_var s q = l_var s' q"
        using q_props q_neq_p pc_eqs step_facts by auto
      have pend_deq_q: "HasPendingDeq s q" 
        using q_props(1) q_neq_p step_facts 
        unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def by (auto simp: mk_act_def act_pid_def)

      (* Technical note for this proof step.*)
      have False
      proof (cases "a = v_var s p")
        case True
        (* Technical note for this proof step.*)
        
        have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = a \<and> act_cr (his_seq s ! k_ret) = ret"
          using hb_s unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def op_name_def op_val_def by force
        then obtain k_ret where k_ret_len: "k_ret < length (his_seq s)"
                            and k_ret_op: "act_name (his_seq s ! k_ret) = enq"
                            and k_ret_val: "act_val (his_seq s ! k_ret) = a"
                            and k_ret_cr: "act_cr (his_seq s ! k_ret) = ret" by blast
        
        from INV have hI7_His_WF_s: "hI7_His_WF s" unfolding system_invariant_def by blast
        have "\<exists>k_call < k_ret. act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret) \<and>
                               act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret) \<and>
                               act_name (his_seq s ! k_call) = enq \<and>
                               act_cr (his_seq s ! k_call) = call \<and>
                               act_val (his_seq s ! k_call) = a"
          using hI7_His_WF_s k_ret_len k_ret_op k_ret_val k_ret_cr unfolding hI7_His_WF_def Let_def by force
        then obtain k_call where k_call_len: "k_call < length (his_seq s)"
                             and k_call_op: "act_name (his_seq s ! k_call) = enq"
                             and k_call_val: "act_val (his_seq s ! k_call) = a"
                             and k_call_cr: "act_cr (his_seq s ! k_call) = call"
                             and k_call_pid: "act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret)"
                             and k_call_ssn: "act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret)"
          using k_ret_len using dual_order.strict_trans by auto
          
        have pending_p: "HasPendingEnq s p a" using hI1_E_Phase_Pending_Enq_s pc_p_E2 True unfolding hI1_E_Phase_Pending_Enq_def by blast
        have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and> 
                                            act_val (his_seq s ! j_call) = a \<and> 
                                            act_cr (his_seq s ! j_call) = call \<and> 
                                            act_pid (his_seq s ! j_call) = p \<and> 
                                            act_ssn (his_seq s ! j_call) = s_var s p"
          using pending_p unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by (metis in_set_conv_nth) 
        then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                             and j_call_op: "act_name (his_seq s ! j_call) = enq"
                             and j_call_val: "act_val (his_seq s ! j_call) = a"
                             and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                             and j_call_pid: "act_pid (his_seq s ! j_call) = p"
                             and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s p" by blast
                             
        from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
        have "k_call = j_call"
          using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
          unfolding hI8_Val_Unique_def by blast
          
        hence "act_pid (his_seq s ! k_ret) = p" and "act_ssn (his_seq s ! k_ret) = s_var s p"
          using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all
          
        moreover have "\<not> (\<exists>k < length (his_seq s). act_pid (his_seq s ! k) = p \<and> act_ssn (his_seq s ! k) = s_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_p unfolding HasPendingEnq_def EnqRetInHis_def Let_def match_ret_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
          by force
          
        ultimately show False using k_ret_len k_ret_cr by blast
        
      next
        case False_a: False
        have tb_a_s: "TypeB s a" using typeb_cases tb_a_s' False_a
          by auto 
        have idx_a_s: "Idx s' a = Idx s a" using idx_eq False_a a_not_bot by simp

        show False
        proof (cases "b = v_var s p")
          case False_b: False
          (* Technical note for this invariant-preservation argument.*)
          have tb_b_s: "TypeB s b" using typeb_cases tb_b_s' False_b
            by auto 
          have idx_b_s: "Idx s' b = Idx s b" using idx_eq False_b b_not_bot by simp
          
          have "Idx s a < Idx s b" using idx_lt_s' idx_a_s idx_b_s by simp
          moreover have "Idx s a < j_var s q" and "j_var s q \<le> Idx s b" and "Idx s b < l_var s q"
            using q_props q_old_props idx_a_s idx_b_s by auto
          ultimately have "\<not> HB_EnqRetCall s a b"
            using hI19_Scanner_Catches_Later_Enq_s tb_a_s tb_b_s pend_deq_q q_old_props(1) unfolding hI19_Scanner_Catches_Later_Enq_def
            by (metis "1" False_b HB_implies_InQBack INV InQBack_def fun_upd_apply
                step_facts(9)) 
          thus False using hb_s by contradiction

        next
          case True_b: True
          (* Technical note for this proof step.*)
          have idx_lt_v: "Idx s' a < Idx s' (v_var s p)" 
            using idx_lt_s' True_b by simp
          
          have scan_cond: "\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and> 
                               Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' (v_var s p) \<and> 
                               Idx s' (v_var s p) < l_var s' q"
            using q_props True_b by blast

          have "\<not> HB_EnqRetCall s' a (v_var s p)"
            using fresh_enq_no_HB_with_old[OF INV STEP False_a tb_a_s' idx_lt_v scan_cond] .
            
          thus False using hb True_b by simp
        qed
      qed
      thus False by simp
    qed
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma hI24_HB_Implies_Idx_Order_E2_step:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows "hI24_HB_Implies_Idx_Order s'"
proof -
  (* Step 1: Technical note for this proof step.*)
  have hI24_HB_Implies_Idx_Order_s: "hI24_HB_Implies_Idx_Order s" using INV unfolding system_invariant_def by blast
  have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast
  have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" using INV unfolding system_invariant_def by blast
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast
  have sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s" using INV unfolding system_invariant_def by blast
  
  (* Step 2: Technical note for this transition-specific proof step.*)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def 
                i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def 
                lin_seq_def his_seq_def

  have pc_p_E2: "program_counter s p = ''E2''" 
    using STEP unfolding Sys_E2_def C_E2_def bridge by auto
  
  have step_facts:
    "his_seq s' = his_seq s"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "v_var s' = v_var s"
    "i_var s' = i_var s"
    "s_var s' = s_var s"
    "CState.Q_arr (fst s') = (CState.Q_arr (fst s))(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge
    by (auto simp: fun_eq_iff)

  (* Step 3: Technical note for this invariant-preservation argument.*)
  show ?thesis
    unfolding hI24_HB_Implies_Idx_Order_def
  proof (intro allI impI, goal_cases)
    case (1 u1 u2 v1 v2 idx1 idx2 sn1 sn2)
    (* Technical note for this proof step.*)
    assume prems_raw: "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1) \<and> 
                       CState.Q_arr (fst s') idx1 = v1 \<and> 
                       CState.Q_arr (fst s') idx2 = v2"
    hence hb_s': "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
      and q_idx1: "CState.Q_arr (fst s') idx1 = v1"
      and q_idx2: "CState.Q_arr (fst s') idx2 = v2" by auto

    have hb_s: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
      using hb_s' step_facts(1) unfolding HB_Act_def HB_def Let_def match_ret_def match_call_def by simp

    (* Technical note for this proof step.*)
    have "v1 \<in> Val \<and> v2 \<in> Val"
    proof -
      from hb_s obtain h1 h2 where "h1 < length (his_seq s)" "act_val (his_seq s ! h1) = v2" "act_name (his_seq s ! h1) = enq"
                                   "h2 < length (his_seq s)" "act_val (his_seq s ! h2) = v1" "act_name (his_seq s ! h2) = enq"
        unfolding HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
        by auto
      thus ?thesis using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def by blast
    qed
    hence v1_not_bot: "v1 \<noteq> BOT" and v2_not_bot: "v2 \<noteq> BOT" by (auto simp: Val_def BOT_def)

    (* Technical note for this proof step.*)
    consider (v2_new) "idx2 = i_var s p" 
           | (v1_new_v2_old) "idx2 \<noteq> i_var s p" "idx1 = i_var s p" 
           | (both_old) "idx2 \<noteq> i_var s p" "idx1 \<noteq> i_var s p"
      by blast

    thus "idx2 < idx1"
    proof (cases, goal_cases)
      case 1
      (* ===================================================================== *)
      (* Technical note for this proof step.
         Technical note for this invariant-preservation argument.*)
      (* ===================================================================== *)
      hence "v2 = v_var s p" using q_idx2 step_facts(6) by simp
      
      have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = v2 \<and> act_cr (his_seq s ! k_ret) = ret"
        using hb_s unfolding HB_Act_def HB_def Let_def match_ret_def mk_op_def op_name_def op_val_def by force
        
      moreover have "\<not> (\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v_var s p \<and> act_cr (his_seq s ! k) = ret)"
        using pending_enq_val_has_no_ret[OF INV] pc_p_E2
        by blast 
        
      ultimately show ?case using `v2 = v_var s p` by simp

    next
      case 2
      (* ===================================================================== *)
      (* Technical note for this proof step.
         Technical note for this proof step.
         Technical note for this proof step.*)
      (* ===================================================================== *)
      hence idx1_is_i: "idx1 = i_var s p" and idx2_neq_i: "idx2 \<noteq> i_var s p" by simp_all
      hence "v1 = v_var s p" using q_idx1 step_facts(6) by simp
      
      have q_idx2_s: "CState.Q_arr (fst s) idx2 = v2" 
        using q_idx2 idx2_neq_i step_facts(6) by simp
        
      have qback_idx2_s: "Qback_arr s idx2 = v2"
        using sI8_Q_Qback_Sync_s q_idx2_s v2_not_bot unfolding sI8_Q_Qback_Sync_def Q_arr_def Qback_arr_def
        by force 
        
      have inqb_v2: "InQBack s v2" 
        using qback_idx2_s unfolding InQBack_def by auto
        
      have v2_neq_v_p: "v2 \<noteq> v_var s p"
      proof
        assume "v2 = v_var s p"
        (* Technical note for this proof step.*)
        have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = v2 \<and> act_cr (his_seq s ! k_ret) = ret"
          using hb_s unfolding HB_Act_def HB_def Let_def match_ret_def mk_op_def op_name_def op_val_def by force
        moreover have "\<not> (\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_enq_val_has_no_ret[OF INV] pc_p_E2
          by blast 
        ultimately show False using `v2 = v_var s p` by simp
      qed
      
      have hb_target: "HB_EnqRetCall s v2 (v_var s p)"
      proof -
        (* Technical note for this invariant-preservation argument.*)
        have "HB (his_seq s) (mk_op enq v2 u2 sn2) (mk_op enq (v_var s p) u1 sn1)"
          using hb_s `v1 = v_var s p` unfolding HB_Act_def by auto
        thus ?thesis unfolding HB_EnqRetCall_def HB_Act_def by blast
      qed

      (* invoke hI22 direct proof*)
      have "Idx s v2 < i_var s p"
        using hb_implies_idx_lt_i_var[OF INV pc_p_E2 inqb_v2 v2_neq_v_p hb_target] .
        
      (* Technical note for this transition-specific proof step.*)
      have "Idx s v2 = idx2"
        using sI12_D3_Scanned_Prefix_s qback_idx2_s inqb_v2 v2_not_bot unfolding sI12_D3_Scanned_Prefix_def
        by (metis sI10_Qback_Unique_Vals_def AtIdx_def INV Idx_implies_AtIdx
            system_invariant_def) 
        
      thus ?case using `Idx s v2 < i_var s p` idx1_is_i by simp

    next
      case 3
      (* ===================================================================== *)
      (* Technical note for this invariant-preservation argument.*)
      (* ===================================================================== *)
      hence "idx1 \<noteq> i_var s p" and "idx2 \<noteq> i_var s p" by simp_all
      hence q_idx1_s: "CState.Q_arr (fst s) idx1 = v1" 
        and q_idx2_s: "CState.Q_arr (fst s) idx2 = v2"
        using q_idx1 q_idx2 step_facts(6) by simp_all
        
      show ?case 
        using hI24_HB_Implies_Idx_Order_s hb_s q_idx1_s q_idx2_s unfolding hI24_HB_Implies_Idx_Order_def by blast
    qed
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI3_L0_E_Phase_Bounds_E2_step:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E2 p s s'"
  shows "hI3_L0_E_Phase_Bounds s'"
proof -
  (* Step 0: Technical note for this proof step.*)
  have hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s" 
    using INV unfolding system_invariant_def by auto

  (* Step 1: Technical note for this transition-specific proof step.*)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  have pc_p_old: "program_counter s p = ''E2'' "
    using STEP unfolding Sys_E2_def C_E2_def bridge by auto
  have pc_p_new: "program_counter s' p = ''E3'' "
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge by (auto simp: fun_eq_iff)
    
  have his_eq: "his_seq s' = his_seq s"
    using STEP unfolding Sys_E2_def bridge by auto
  have s_var_eq: "s_var s' = s_var s"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge by auto
  have V_eq: "V_var s' = V_var s"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge by auto
  have qback_eq: "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    using STEP unfolding Sys_E2_def C_E2_def Qback_arr_def i_var_def v_var_def Let_def bridge by (auto simp: fun_eq_iff)

  have pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge by (auto simp: fun_eq_iff)
  have v_var_eq: "v_var s' = v_var s"
    using STEP unfolding Sys_E2_def C_E2_def Let_def bridge by auto

  (* Step 2: Technical note for this invariant-preservation argument.*)
  show ?thesis
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    (* Technical note for this transition-specific proof step.*)
    have q_ne_p: "q \<noteq> p" using 1 pc_p_new by auto
    have old_L0: "program_counter s q = ''L0'' " 
      using 1 q_ne_p pc_other by auto
      
    have pend_enq_eq: "HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a" for a
      using his_eq s_var_eq unfolding HasPendingEnq_def Let_def Model.EnqCallInHis_def
      by (auto simp: mk_act_def act_pid_def)
      
    have pend_deq_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
      using his_eq s_var_eq unfolding HasPendingDeq_def Let_def Model.DeqCallInHis_def
      by (auto simp: mk_act_def act_pid_def)
      
    show ?case
      using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s old_L0] pend_enq_eq pend_deq_eq by simp

  next
    case (2 q)
    (* Technical note for this transition-specific proof step.*)
    have q_ne_p: "q \<noteq> p" using 2 pc_p_new by auto
    have old_L0: "program_counter s q = ''L0'' " 
      using 2 q_ne_p pc_other by auto
      
    have "length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
          length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
      using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s old_L0] by simp
    then show ?case
      using his_eq by (simp add: mk_act_def act_pid_def act_name_def act_cr_def)

  next
    case (3 q)
    (* Technical note for this proof step.*)
    show ?case
    proof (cases "q = p")
      case True
      have old_E: "program_counter s p \<in> {''E1'', ''E2'', ''E3''}"
        using pc_p_old by simp
      show ?thesis
        using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s old_E] True v_var_eq V_eq by simp
    next
      case False
      have old_E: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
        using 3 False pc_other by auto
      show ?thesis
        using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s old_E] False v_var_eq V_eq by simp
    qed

  next
    case (4 k)
    (* Technical note for this proof step.*)
    have old_k: "k < length (his_seq s)"
      using 4 his_eq by simp
    show ?case
      using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s old_k] 4 his_eq V_eq by auto

  next
    case (5 k)
    (* Technical note for this proof step.*)
    show ?case
    proof (cases "k = i_var s p")
      case True
      (* Technical note for this proof step.
         Technical note for this transition-specific proof step.*)
      have "Qback_arr s' k = v_var s p"
        using True qback_eq by simp
      moreover have "v_var s p < V_var s"
        using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s] pc_p_old by auto
      ultimately show ?thesis
        using 5 V_eq by (cases "v_var s p = BOT") (auto simp: Val_def BOT_def)
    next
      case False
      (* Technical note for this proof step.*)
      have "Qback_arr s' k = Qback_arr s k"
        using False qback_eq by simp
      thus ?thesis
        using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s, of k] 5 V_eq by auto
    qed
  qed
qed


(* ========================================================================= *)
(* Technical note for this transition-specific proof step.*)
(* ========================================================================= *)
lemma E2_preserves_invariant_core:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E2 p s s'"  
  shows "system_invariant s'"
proof -   
  (* ========================================================================= *)
  (* Step 0: bridge definitionsandsetup.*)
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
  (* Step 4: Technical note for this proof step.*)
  (* ========================================================================= *)

  have "TypeOK s'" 
    using TypeOK_s pc_eqs step_facts unfolding TypeOK_def by auto
    
  have "sI1_Zero_Index_BOT s'"
  proof -
    (* Technical note for this transition-specific proof step.*)
    have "i_var s p \<noteq> 0" 
      using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def Val_def by auto
      
    (* Technical note for this proof step.*)
    thus ?thesis
      using sI1_Zero_Index_BOT_s step_facts(3) step_facts(4)
      by (auto simp: fun_upd_def sI1_Zero_Index_BOT_def)
  qed

  have "sI2_X_var_Upper_Bound s'"
  proof -
    (* Technical note for this transition-specific proof step.*)
    have "i_var s p < X_var s" 
      using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def by auto
      
    (* Technical note for this proof step.*)
    thus ?thesis
      using sI2_X_var_Upper_Bound_s step_facts
      unfolding sI2_X_var_Upper_Bound_def 
      by (auto simp: fun_upd_def)
  qed


  have "sI3_E2_Slot_Exclusive s'"
    unfolding sI3_E2_Slot_Exclusive_def
  proof (intro allI impI)
    fix p0 assume pc_p0: "program_counter s' p0 = ''E2''"
    
    (* Step 1: Technical note for this transition-specific proof step.*)
    hence "program_counter s p0 = ''E2''" and "p0 \<noteq> p"
      using pc_eqs by auto
      
    (* Step 2: Technical note for this transition-specific proof step.*)
    have p0_props: 
      "i_var s p0 \<in> Val \<and>
       i_var s p0 < X_var s \<and>
       Q_arr s (i_var s p0) = BOT \<and>
       Qback_arr s (i_var s p0) = BOT \<and>
       (\<forall>q. q \<noteq> p0 \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p0 \<noteq> i_var s q)"
      using sI3_E2_Slot_Exclusive_s `program_counter s p0 = ''E2''` unfolding sI3_E2_Slot_Exclusive_def by auto
      
    (* Step 3: Technical note for this proof step.*)
    have "i_var s p0 \<noteq> i_var s p" 
      using p0_props `p0 \<noteq> p` step_facts(1) by auto
      
    (* Step 4: Technical note for this proof step.*)
    thus "i_var s' p0 \<in> Val \<and>
          i_var s' p0 < X_var s' \<and>
          Q_arr s' (i_var s' p0) = BOT \<and>
          Qback_arr s' (i_var s' p0) = BOT \<and>
          (\<forall>q. q \<noteq> p0 \<and> program_counter s' q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' p0 \<noteq> i_var s' q)"
      using p0_props step_facts pc_eqs by (auto simp: fun_upd_def)
  qed

  have "sI4_E3_Qback_Written s'"
    unfolding sI4_E3_Qback_Written_def
  proof (intro allI impI)
    fix p0 assume pc_p0: "program_counter s' p0 = ''E3''"
    
    (* Technical note for this transition-specific proof step.*)
    consider (is_p) "p0 = p" | (not_p) "p0 \<noteq> p" by blast
    then show "i_var s' p0 \<in> Val \<and>
               i_var s' p0 < X_var s' \<and>
               (Q_arr s' (i_var s' p0) = v_var s' p0 \<or> Q_arr s' (i_var s' p0) = BOT) \<and>
               Qback_arr s' (i_var s' p0) = v_var s' p0 \<and>
               (\<forall>q. q \<noteq> p0 \<and> program_counter s' q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' p0 \<noteq> i_var s' q)"
    proof cases
      case is_p
      (* Technical note for this transition-specific proof step.*)
      have p_props:
        "i_var s p \<in> Val"
        "i_var s p < X_var s"
        "(\<forall>q. q \<noteq> p \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p \<noteq> i_var s q)"
        using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def by auto

      (* Technical note for this transition-specific proof step.*)
      show ?thesis
        using is_p p_props step_facts pc_eqs
        by (auto simp: fun_upd_def)
        
    next
      case not_p
      (* Technical note for this transition-specific proof step.*)
      hence "program_counter s p0 = ''E3''" using pc_p0 pc_eqs by auto
      
      have p0_props:
        "i_var s p0 \<in> Val"
        "i_var s p0 < X_var s"
        "Q_arr s (i_var s p0) = v_var s p0 \<or> Q_arr s (i_var s p0) = BOT"
        "Qback_arr s (i_var s p0) = v_var s p0"
        "(\<forall>q. q \<noteq> p0 \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p0 \<noteq> i_var s q)"
        using sI4_E3_Qback_Written_s `program_counter s p0 = ''E3''` unfolding sI4_E3_Qback_Written_def by auto

      (* Technical note for this proof step.*)
      have "i_var s p0 \<noteq> i_var s p"
        using p0_props(5) step_facts(1) not_p by auto

      (* Technical note for this proof step.*)
      show ?thesis
        using not_p p0_props `i_var s p0 \<noteq> i_var s p` step_facts pc_eqs
        by (auto simp: fun_upd_def)
    qed
  qed
  
  have "sI5_D2_Local_Bound s'" 
    using sI5_D2_Local_Bound_s unfolding sI5_D2_Local_Bound_def using pc_eqs step_facts by auto
    
  have "sI6_D3_Scan_Pointers s'" 
    using sI6_D3_Scan_Pointers_s unfolding sI6_D3_Scan_Pointers_def using pc_eqs step_facts by auto
    
  have "sI7_D4_Deq_Result s'"
  proof -
    (* Technical note for this transition-specific proof step.*)
    have no_conflict: "\<And>pa. program_counter s pa = ''D4'' \<Longrightarrow> j_var s pa \<noteq> i_var s p"
    proof -
      fix pa assume "program_counter s pa = ''D4''"
      (* Technical note for this transition-specific proof step.*)
      hence "Qback_arr s (j_var s pa) \<noteq> BOT" 
        using sI7_D4_Deq_Result_s unfolding sI7_D4_Deq_Result_def by auto
      (* Technical note for this transition-specific proof step.*)
      moreover have "Qback_arr s (i_var s p) = BOT"
        using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def by auto
      ultimately show "j_var s pa \<noteq> i_var s p" by metis
    qed

    (* Technical note for this proof step.*)
    thus ?thesis
      using sI7_D4_Deq_Result_s step_facts pc_eqs
      unfolding sI7_D4_Deq_Result_def
      by (auto simp: fun_upd_def)
  qed

  have "hI3_L0_E_Phase_Bounds s'"
  using hI3_L0_E_Phase_Bounds_E2_step[OF INV STEP] .

  have "sI8_Q_Qback_Sync s'"
    using sI8_Q_Qback_Sync_s step_facts(3) step_facts(4)
    unfolding sI8_Q_Qback_Sync_def
    by (auto simp: fun_upd_def)

  have "sI9_Qback_Discrepancy_E3 s'"
    unfolding sI9_Qback_Discrepancy_E3_def
  proof (intro allI impI)
    fix k q
    assume cond1: "Q_arr s' k = BOT \<and> Qback_arr s' k \<noteq> BOT"
    assume cond2: "program_counter s' q \<in> {''E3''} \<and> i_var s' q = k"
    
    (* Step 1: Technical note for this proof step.*)
    have pending: "HasPendingEnq s p (v_var s p)" 
      using hI1_E_Phase_Pending_Enq_s step_facts(1) unfolding hI1_E_Phase_Pending_Enq_def by auto
    have "v_var s p \<in> Val" 
      using pending hI20_Enq_Val_Valid_s unfolding HasPendingEnq_def EnqCallInHis_def hI20_Enq_Val_Valid_def Let_def 
      by (metis in_set_conv_nth)
    hence val_not_bot: "v_var s p \<noteq> BOT" unfolding Val_def BOT_def by auto

    (* Step 2: Technical note for this proof step.*)
    have k_neq_ip: "k \<noteq> i_var s p"
    proof
      assume "k = i_var s p"
      hence "Q_arr s' k = v_var s p" using step_facts(3) by (simp add: fun_upd_def)
      with cond1 val_not_bot show False by simp
    qed

    (* Step 3: Technical note for this proof step.*)
    have q_neq_p: "q \<noteq> p"
    proof
      assume "q = p"
      hence "i_var s' q = i_var s p" using step_facts by simp
      with cond2 k_neq_ip show False by simp
    qed

    (* Step 4: Technical note for this proof step.*)
    have "program_counter s q \<in> {''E3''}" "i_var s q = k" 
      using cond2 q_neq_p pc_eqs step_facts by auto
    moreover have "Q_arr s k = BOT" "Qback_arr s k \<noteq> BOT" 
      using cond1 k_neq_ip step_facts(3) step_facts(4) by (auto simp: fun_upd_def)
      
    (* Step 5: Technical note for this transition-specific proof step.*)
    ultimately have "v_var s q = Qback_arr s k" 
      using sI9_Qback_Discrepancy_E3_s unfolding sI9_Qback_Discrepancy_E3_def by blast
      
    thus "v_var s' q = Qback_arr s' k"
      using q_neq_p k_neq_ip step_facts by (simp add: fun_upd_def)
  qed

  have "sI10_Qback_Unique_Vals s'"
  proof -
    (* Technical note for this proof step.*)
    have val_is_new: "\<forall>k. Qback_arr s k \<noteq> v_var s p"
      using not_in_qback_s unfolding InQBack_def val_def by auto

    (* Technical note for this proof step.*)
    thus ?thesis
      using sI10_Qback_Unique_Vals_s step_facts(4)
      unfolding sI10_Qback_Unique_Vals_def
      by (auto simp: fun_upd_def)
  qed

  have "hI2_SSN_Bounds s'"
  proof -
    (* Step 1: Technical note for this transition-specific proof step.*)
    have pc_L0: "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
      using pc_eqs by simp

    (* Step 2: Technical note for this proof step.*)
    show ?thesis
      using hI2_SSN_Bounds_s step_facts pc_L0
      unfolding hI2_SSN_Bounds_def
      by auto
  qed
  
  have "sI11_x_var_Scope s'" 
    using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def using pc_eqs step_facts by auto
    
  have "hI1_E_Phase_Pending_Enq s'"
    unfolding hI1_E_Phase_Pending_Enq_def
  proof (intro allI impI)
    fix q assume pc_q: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
    
    (* Step 1: Technical note for this proof step.
          Technical note for this transition-specific proof step.
          Technical note for this transition-specific proof step.*)
    have old_pc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using pc_q pc_eqs step_facts(1) by auto
      
    (* Step 2: Technical note for this invariant-preservation argument.*)
    have "HasPendingEnq s q (v_var s q)"
      using hI1_E_Phase_Pending_Enq_s old_pc unfolding hI1_E_Phase_Pending_Enq_def by blast
      
    (* Step 3: Technical note for this proof step.*)
    thus "HasPendingEnq s' q (v_var s' q)"
      unfolding HasPendingEnq_def EnqCallInHis_def Let_def
      using step_facts by auto
  qed

  have "sI12_D3_Scanned_Prefix s'"
    unfolding sI12_D3_Scanned_Prefix_def
  proof (intro allI impI)
    fix pa k
    assume pa_pc: "program_counter s' pa = ''D3'' "
    assume k_lt: "k < j_var s' pa"

    (* Step 1: Technical note for this proof step.*)
    have pc_s: "program_counter s pa = ''D3'' " using pa_pc pc_eqs by auto
    have j_s: "j_var s' pa = j_var s pa" using step_facts by auto

    show "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
    proof (cases "k = i_var s p")
      case True
      (* Technical note for this proof step.*)
      (* Technical note for this proof step.*)
      have val_new: "Q_arr s' k = v_var s p" 
        using True step_facts by simp
      
      (* Technical note for this invariant-preservation argument.*)
      have "TypeB s' (v_var s p)"
      proof -
        (* Step 1: Technical note for this proof step.*)
        have "QHas s' (v_var s p)"
          unfolding QHas_def
          using True val_new by blast
          
        (* Step 2: Technical note for this invariant-preservation argument.*)
        thus ?thesis
          unfolding TypeB_def by blast
      qed
      thus ?thesis using val_new by simp

    next
      case False
      (* Technical note for this proof step.*)
      (* Technical note for this proof step.*)
      have q_stable: "Q_arr s' k = Q_arr s k" 
        using False step_facts by auto
      
      (* Technical note for this transition-specific proof step.*)
      have "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
        using sI12_D3_Scanned_Prefix_s pc_s k_lt j_s unfolding sI12_D3_Scanned_Prefix_def
        by simp 
      
      (* Technical note for this invariant-preservation argument.*)
      thus ?thesis using q_stable typeb_eq by auto
    qed
  qed

(* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI4_X_var_Lin_Sync s'"
  proof -
    (* Technical note for this transition-specific proof step.*)
    have "X_var s' = X_var s" 
      using STEP unfolding Sys_E2_def C_E2_def Let_def X_var_def by (auto simp: fun_eq_iff)
    
    have "lin_seq s' = lin_seq s" 
      using STEP unfolding Sys_E2_def C_E2_def Let_def lin_seq_def by (auto simp: fun_eq_iff)
      
    thus ?thesis
      using hI4_X_var_Lin_Sync_s \<open>X_var s' = X_var s\<close> unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def by simp
  qed

  (* ========================================================================= *)
  (* Step 5: Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  
  have "hI7_His_WF s'" 
    using hI7_His_WF_s step_facts unfolding hI7_His_WF_def by simp
  have "hI8_Val_Unique s'" 
    using hI8_Val_Unique_s step_facts unfolding hI8_Val_Unique_def by simp
  have "hI5_SSN_Unique s'" 
    using hI5_SSN_Unique_s step_facts unfolding hI5_SSN_Unique_def by simp
  have "hI6_SSN_Order s'" 
    using hI6_SSN_Order_s step_facts unfolding hI6_SSN_Order_def by simp
  have "hI9_Deq_Ret_Unique s'" 
    using hI9_Deq_Ret_Unique_s step_facts unfolding hI9_Deq_Ret_Unique_def by simp
  
  (* Technical note for this invariant-preservation argument.*)
  have "hI10_Enq_Call_Existence s'"
    unfolding hI10_Enq_Call_Existence_def
  proof (intro conjI)
    (* Part 1: Technical note for this transition-specific proof step.*)
    (* Technical note for this invariant-preservation argument.*)
    show "\<forall>p a. program_counter s' p \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' p = a \<longrightarrow> 
                EnqCallInHis s' p a (s_var s' p)"
      using `hI1_E_Phase_Pending_Enq s'` unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def
      by metis 

  next
    (* Part 2: Technical note for this proof step.*)
    show "\<forall>a. (\<exists>k. Qback_arr s' k = a) \<longrightarrow> (\<exists>q. Ex (EnqCallInHis s' q a))"
    proof (intro allI impI)
      fix a assume "\<exists>k. Qback_arr s' k = a"
      
      (* invokeAuxiliary lemma hI10_Enq_Call_Existence_E2_step*)
      (* Technical note for this proof step.*)
      show "\<exists>q. Ex (EnqCallInHis s' q a)"
        using hI10_Enq_Call_Existence_E2_step [OF INV STEP \<open>\<exists>k. Qback_arr s' k = a\<close>] 
        by auto
    qed
  qed

  (* Technical note for this invariant-preservation argument.*)
  have "hI11_Enq_Ret_Existence s'"
    by (rule hI11_Enq_Ret_Existence_E2_step [OF INV STEP])
  
(* Step 1: Technical note for this proof step.*)
  have hpd_eq: "\<And>pa. HasPendingDeq s' pa = HasPendingDeq s pa"
  proof -
    fix pa
    (* Technical note for this proof step.*)
    from STEP have his_eq: "his_seq s' = his_seq s" 
      unfolding Sys_E2_def C_E2_def his_seq_def by auto
    
    show "HasPendingDeq s' pa = HasPendingDeq s pa"
      unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def
      using his_eq by simp
  qed

  have "hI12_D_Phase_Pending_Deq s'"
    unfolding hI12_D_Phase_Pending_Deq_def
  proof (intro allI impI)
    fix pa
    (* Technical note for this transition-specific proof step.*)
    assume "program_counter s' pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    
    (* Technical note for this transition-specific proof step.*)
    hence pc_old: "program_counter s pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using pc_eqs by auto
    
    (* Technical note for this invariant-preservation argument.*)
    from hI12_D_Phase_Pending_Deq_s pc_old hpd_eq show "HasPendingDeq s' pa"
      unfolding hI12_D_Phase_Pending_Deq_def by auto
  qed
    
  have "hI13_Qback_Deq_Sync s'"
  proof (unfold hI13_Qback_Deq_Sync_def, intro allI impI)
    fix a
    assume a_nz: "a \<noteq> BOT"
    assume gap_new: "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a"

    (* Step 1: Technical note for this proof step.*)
    from INV have hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s" unfolding system_invariant_def by auto
    from gap_new obtain k where k_gap: "Q_arr s' k = BOT" "Qback_arr s' k = a" by blast

    (* Step 2: Technical note for this proof step.*)
    have k_not_p: "k \<noteq> i_var s p"
    proof
      assume "k = i_var s p"
      (* Technical note for this transition-specific proof step.*)
      (* Technical note for this proof step.*)
      hence "Q_arr s' k = v_var s p" using step_facts by simp
      with k_gap(1) have "v_var s p = BOT" by simp
      (* Technical note for this proof step.*)
      moreover from INV have "v_var s p \<noteq> BOT" 
        unfolding system_invariant_def hI20_Enq_Val_Valid_def (* Technical note for this invariant-preservation argument.*)
        using step_facts
        using val_def val_not_bot by blast 
      ultimately show False by contradiction
    qed

    (* Step 3: Technical note for this proof step.*)
    hence gap_old: "Q_arr s k = BOT \<and> Qback_arr s k = a"
      using k_gap step_facts by auto

    (* Step 4: Technical note for this invariant-preservation argument.*)
    with hI13_Qback_Deq_Sync_s a_nz have "\<exists>p. (program_counter s p = ''D4'' \<and> x_var s p = a) \<or> (\<exists>sn. DeqRetInHis s p a sn)"
      unfolding hI13_Qback_Deq_Sync_def by blast
    
    (* Step 5: Technical note for this proof step.*)
    thus "\<exists>p. (program_counter s' p = ''D4'' \<and> x_var s' p = a) \<or> (\<exists>sn. DeqRetInHis s' p a sn)"
    proof (elim exE disjE, goal_cases)
      case (1 pa) (* Technical note for this transition-specific proof step.*)
      (* Technical note for this transition-specific proof step.*)
      hence "pa \<noteq> p" using step_facts(1) by auto
      hence "program_counter s' pa = ''D4'' " "x_var s' pa = a"
        using 1 step_facts by auto
      thus ?case by blast
    next
      case (2 pa sn) (* Technical note for this proof step.*)
      hence "DeqRetInHis s' pa a sn"
        using step_facts(12) unfolding DeqRetInHis_def by simp
      thus ?case by blast
    qed
  qed

(* Technical note for this invariant-preservation argument.*)
  have "hI14_Pending_Enq_Qback_Exclusivity s'"
    by (rule hI14_Pending_Enq_Qback_Exclusivity_E2_step [OF INV STEP])

(* Technical note for this invariant-preservation argument.*)
  have "hI15_Deq_Result_Exclusivity s'"
    by (rule hI15_Deq_Result_Exclusivity_E2_step [OF INV STEP])
  
(* Technical note for this invariant-preservation argument.*)
  have "hI16_BO_BT_No_HB s'" using hI16_BO_BT_No_HB_E2_step[OF INV STEP] .
  
  have "hI17_BT_BT_No_HB s'" using hI17_BT_BT_No_HB_E2_step[OF INV STEP] .
  
  have "hI18_Idx_Order_No_Rev_HB s'" using hI18_Idx_Order_No_Rev_HB_E2_step[OF INV STEP] .
  
  have "hI19_Scanner_Catches_Later_Enq s'" using hI19_Scanner_Catches_Later_Enq_E2_step[OF INV STEP] .
  
  have "hI20_Enq_Val_Valid s'" 
    using hI20_Enq_Val_Valid_s step_facts unfolding hI20_Enq_Val_Valid_def by simp

  have "hI21_Ret_Implies_Call s'"
  proof -
    (* Technical note for this proof step.*)
    have seq_eq: "his_seq s' = his_seq s" using step_facts(1) by simp
    
    (* Technical note for this proof step.*)
    show ?thesis 
      using hI21_Ret_Implies_Call_s seq_eq 
      unfolding hI21_Ret_Implies_Call_def 
      by (auto split: if_splits)
  qed
    
(* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI22_Deq_Local_Pattern s'"
    unfolding hI22_Deq_Local_Pattern_def
  proof (intro allI impI, goal_cases)
    case (1 p_deq a sn)
    (* Step 1: Technical note for this proof step.*)
    then obtain k where k_props:
      "Q_arr s' k = BOT"
      "Qback_arr s' k = a"
      "\<forall>q. x_var s' q \<noteq> a"
      "DeqRetInHis s' p_deq a sn"
      by blast

    (* Step 2: Technical note for this invariant-preservation argument.*)
    have hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s" using INV unfolding system_invariant_def by blast

    (* Step 3: Technical note for this proof step.*)
    have "k \<noteq> i_var s p"
    proof
      assume "k = i_var s p"
      (* Technical note for this transition-specific proof step.*)
      hence "Q_arr s' k = v_var s p" using step_facts(8) by simp
      with k_props(1) have "v_var s p = BOT" by simp
      (* Technical note for this proof step.*)
      with val_not_bot show False
        by (simp add: val_def) 
    qed

    (* Step 4: map back topre-state.*)
    hence old_Q: "Q_arr s k = BOT" and old_Qback: "Qback_arr s k = a"
      using k_props(1,2) step_facts(8,9) by auto
      
    have old_x: "\<forall>q. x_var s q \<noteq> a" 
      using k_props(3) step_facts(2) by auto
      
    have old_his: "DeqRetInHis s p_deq a sn" 
      using k_props(4) step_facts(1) unfolding DeqRetInHis_def Let_def by auto

    (* Step 5: Technical note for this proof step.*)
    have old_antecedent: "((\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a \<and> (\<forall>q. x_var s q \<noteq> a)) \<and> DeqRetInHis s p_deq a sn)"
      using old_Q old_Qback old_x old_his by blast

    from hI22_Deq_Local_Pattern_s[unfolded hI22_Deq_Local_Pattern_def, rule_format, OF old_antecedent]
    have old_consequent: "let p_his = filter (\<lambda>e. act_pid e = p_deq) (his_seq s) in
      \<exists>i < length p_his. 
          p_his ! i = mk_act deq a p_deq sn ret \<and>        
         (i > 0 \<and> p_his ! (i - 1) = mk_act deq BOT p_deq sn call)" .

    (* Step 6: Technical note for this proof step.*)
    thus ?case using step_facts(1) by simp
  qed
  
  have "hI23_Deq_Call_Ret_Balanced s'" 
    using hI23_Deq_Call_Ret_Balanced_s step_facts unfolding hI23_Deq_Call_Ret_Balanced_def by simp
    
  have "hI24_HB_Implies_Idx_Order s'"
    by (rule hI24_HB_Implies_Idx_Order_E2_step [OF INV STEP])
  
  have "hI25_Enq_Call_Ret_Balanced s'"
  proof -
    (* Technical note for this transition-specific proof step.*)
    have pc_stable: "\<And>q. (program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) = (program_counter s q \<in> {''E1'', ''E2'', ''E3''})"
    proof -
      fix q
      show "(program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) = (program_counter s q \<in> {''E1'', ''E2'', ''E3''})"
      proof (cases "q = p")
        case True
        (* Technical note for this transition-specific proof step.*)
        hence "program_counter s' q = ''E3''" using pc_eqs by simp
        moreover have "program_counter s q = ''E2''"
          by (simp add: True)
        ultimately show ?thesis by simp
      next
        case False
        (* Technical note for this proof step.*)
        thus ?thesis using pc_eqs by simp
      qed
    qed
    
    (* Technical note for this invariant-preservation argument.*)
    show ?thesis
      using hI25_Enq_Call_Ret_Balanced_s step_facts(1) pc_stable
      unfolding hI25_Enq_Call_Ret_Balanced_def
      by simp
  qed
    
  (* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI26_DeqRet_D4_Mutex s'"
    unfolding hI26_DeqRet_D4_Mutex_def
  proof (intro allI impI, goal_cases)
    case (1 q a)
    (* Technical note for this proof step.*)
    show ?case
    proof (rule notI)
      (* Technical note for this transition-specific proof step.*)
      assume bad: "(\<exists>sn. DeqRetInHis s' q a sn) \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a"
      then obtain sn where ret_s': "DeqRetInHis s' q a sn" 
                       and pc_q_s': "program_counter s' q = ''D4''" 
                       and x_q_s': "x_var s' q = a" by blast
      
      have hI26_DeqRet_D4_Mutex_s: "hI26_DeqRet_D4_Mutex s" using INV unfolding system_invariant_def by blast

      show False
      proof (cases "q = p", goal_cases)
        case 1
        (* Technical note for this transition-specific proof step.*)
        have "program_counter s' p = ''E3''" using pc_eqs by simp
        with pc_q_s' 1 show False by simp
      next
        case 2
        (* Technical note for this transition-specific proof step.*)
        have "program_counter s q = ''D4''" using pc_q_s' 2 pc_eqs by simp
        
        (* Technical note for this transition-specific proof step.*)
        have "x_var s q = a" using x_q_s' step_facts by simp
        
        (* Technical note for this transition-specific proof step.*)
        have "DeqRetInHis s q a sn"
          using ret_s' step_facts unfolding DeqRetInHis_def Let_def by simp
          
        (* Technical note for this proof step.*)
        from hI26_DeqRet_D4_Mutex_s 1(1) `program_counter s q = ''D4''` `x_var s q = a` `DeqRetInHis s q a sn`
        show False unfolding hI26_DeqRet_D4_Mutex_def by blast
      qed
    qed
  qed

(* ========================================================================= *)
  (* Technical note for this transition-specific proof step.*)
  (* ========================================================================= *)
  
  (* Technical note for this proof step.*)
  have pc_p_E2: "program_counter s p = ''E2'' " 
    using STEP unfolding Sys_E2_def C_E2_def by (simp add: program_counter_def)

  (* Technical note for this invariant-preservation argument.*)
  have typeb_cases: "\<And>x. TypeB s' x \<Longrightarrow> x = v_var s p \<or> TypeB s x"
  proof -
    fix x assume "TypeB s' x"
    hence "QHas s' x \<or> (\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x)" unfolding TypeB_def by simp
    thus "x = v_var s p \<or> TypeB s x"
    proof (elim disjE, goal_cases)
      case 1
      then obtain k where "Q_arr s' k = x" unfolding QHas_def by blast
      thus ?case using step_facts pc_p_E2 unfolding TypeB_def QHas_def by (cases "k = i_var s p") auto
    next
      case 2
      then obtain q where "program_counter s' q = ''E2'' " "v_var s' q = x" by blast
      have "q \<noteq> p" using `program_counter s' q = ''E2''` pc_eqs by auto
      thus ?case using `program_counter s' q = ''E2''` `v_var s' q = x` pc_eqs step_facts unfolding TypeB_def by auto
    qed
  qed

  (* Technical note for this transition-specific proof step.*)
  have idx_eq: "\<And>x. x \<noteq> v_var s p \<Longrightarrow> x \<noteq> BOT \<Longrightarrow> Idx s' x = Idx s x"
  proof -
    fix x assume "x \<noteq> v_var s p" "x \<noteq> BOT"
    have qback_i_bot: "Qback_arr s (i_var s p) = BOT"
      using sI3_E2_Slot_Exclusive_s pc_p_E2 unfolding sI3_E2_Slot_Exclusive_def by blast

    have "(\<lambda>k. Qback_arr s' k = x) = (\<lambda>k. Qback_arr s k = x)"
    proof (rule ext)
      fix k show "(Qback_arr s' k = x) = (Qback_arr s k = x)"
      proof (cases "k = i_var s p")
        case True
        have "Qback_arr s' k = v_var s p" using step_facts(9) True by simp
        hence left: "Qback_arr s' k \<noteq> x" using `x \<noteq> v_var s p` by simp
        have "Qback_arr s k = BOT" using qback_i_bot True by simp
        hence right: "Qback_arr s k \<noteq> x" using `x \<noteq> BOT` by simp
        show ?thesis using left right by simp
      next
        case False
        thus ?thesis using step_facts(9) by simp
      qed
    qed
    thus "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def by simp
  qed

(* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI27_Pending_PC_Sync s'"
    unfolding hI27_Pending_PC_Sync_def
  proof (intro conjI allI impI, goal_cases)
    case (1 q)
    have "HasPendingDeq s q" 
      using 1 step_facts unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def by simp
    with hI27_Pending_PC_Sync_s have "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}" 
      unfolding hI27_Pending_PC_Sync_def by blast
    moreover have "q \<noteq> p" using 1 pc_p_E2
      using calculation by force 
    ultimately show ?case using pc_eqs by simp
  next
    case (2 q)
    have "HasPendingEnq s q (v_var s q)" 
      using 2 step_facts unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def Let_def by simp
    with hI27_Pending_PC_Sync_s have "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" 
      unfolding hI27_Pending_PC_Sync_def by blast
    thus ?case using pc_eqs by (cases "q = p") auto
  qed

  (* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI28_Fresh_Enq_Immunity s'"
    unfolding hI28_Fresh_Enq_Immunity_def
  proof (intro allI impI, goal_cases)
    case (1 q_enq q_deq a sn)
    have pc_q: "program_counter s' q_enq \<in> {''E1'', ''E2''}" and "v_var s' q_enq = a" and "a \<noteq> BOT" 
      using 1 by auto
    have "q_enq \<noteq> p" using pc_q pc_eqs by auto
    hence "program_counter s q_enq \<in> {''E1'', ''E2''}" using pc_q pc_eqs by simp
    moreover have "v_var s q_enq = a" using 1 \<open>q_enq \<noteq> p\<close> step_facts by simp
    ultimately have "\<not> DeqRetInHis s q_deq a sn" 
      using hI28_Fresh_Enq_Immunity_s 1(1) unfolding hI28_Fresh_Enq_Immunity_def by blast
    thus ?case using step_facts unfolding DeqRetInHis_def Let_def
      by presburger 
  qed

  (* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI29_E2_Scanner_Immunity s'"
    unfolding hI29_E2_Scanner_Immunity_def
  proof (intro allI impI, goal_cases)
    case (1 p_enq a q)
    show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
    proof
      assume hb: "HB_EnqRetCall s' a (v_var s' p_enq)"
      (* extract a \<in> Val*)
      have "a \<in> Val" 
      proof -
        from hb obtain p1 p2 sn1 sn2 k1 k2 :: nat where evs:
          "k1 < length (his_seq s')" "act_name (his_seq s' ! k1) = enq" "act_val (his_seq s' ! k1) = a"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def by (auto simp: op_name_def op_val_def)
        have "k1 < length (his_seq s)" using evs(1) step_facts(1) by simp
        thus ?thesis using hI20_Enq_Val_Valid_s evs(2,3) step_facts(1) unfolding hI20_Enq_Val_Valid_def by force
      qed
      hence a_not_bot: "a \<noteq> BOT" by (simp add: Val_def BOT_def)

      have "p_enq \<noteq> p" using 1 pc_eqs by auto
      have "q \<noteq> p" using 1 pc_eqs by auto
      
      have pc_p_enq_s: "program_counter s p_enq = ''E2''" using 1 \<open>p_enq \<noteq> p\<close> pc_eqs by simp
      have pc_q_s: "program_counter s q = ''D3''" using 1 \<open>q \<noteq> p\<close> pc_eqs by simp
      have pend_q_s: "HasPendingDeq s q" 
        using 1 \<open>q \<noteq> p\<close> step_facts unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def by simp
      
      have hb_s: "HB_EnqRetCall s a (v_var s p_enq)" 
        using hb step_facts \<open>p_enq \<noteq> p\<close> unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
        by metis 

      show False
      proof (cases "a = v_var s p")
        case True
        (* Technical note for this invariant-preservation argument.*)
        have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = v_var s p \<and> act_cr (his_seq s ! k_ret) = ret"
          using hb_s True unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def mk_op_def op_name_def op_val_def by force
          
        (* Technical note for this proof step.*)
        have pc_p_active: "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" using pc_p_E2 by simp
        moreover have "\<not> (\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_enq_val_has_no_ret[OF INV pc_p_active] by simp
          
        ultimately show False
          by (simp add:
              \<open>\<exists>k_ret<length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = Model.v_var s p \<and> act_cr (his_seq s ! k_ret) = ret\<close>)
      next
        case False
        (* Technical note for this invariant-preservation argument.*)
        have tb_a_s: "TypeB s a" using 1 typeb_cases False by blast
        have idx_a_s: "Idx s' a = Idx s a" using idx_eq False a_not_bot by simp
        
        have "Idx s a < j_var s q" using 1(1) idx_a_s step_facts \<open>q \<noteq> p\<close> by auto
        moreover have "j_var s q \<le> i_var s p_enq" using 1(1) step_facts \<open>p_enq \<noteq> p\<close> \<open>q \<noteq> p\<close> by auto
        moreover have "i_var s p_enq < l_var s q" using 1(1) step_facts \<open>p_enq \<noteq> p\<close> \<open>q \<noteq> p\<close> by auto
        
        ultimately show False 
          using hI29_E2_Scanner_Immunity_s[unfolded hI29_E2_Scanner_Immunity_def, rule_format, of p_enq a q]
          using pc_p_enq_s tb_a_s pend_q_s pc_q_s hb_s
          using "1" False inqback_s' val_def by blast 
      qed
    qed
  qed

(* ========================================================================= *)
    (* Technical note for this invariant-preservation argument.*)
    (* Technical note for this proof step.*)
    (* ========================================================================= *)
    have "hI30_Ticket_HB_Immunity s'"
    proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI, goal_cases)
      case (1 b q)
      
      (* Step 1: Technical note for this proof step.*)
      from 1 have pc_q': "program_counter s' q \<in> {''E2'', ''E3''}" by blast
      from 1 have inqb': "InQBack s' b" by blast
      from 1 have b_not_bot': "b \<noteq> BOT" by blast
      from 1 have b_neq_v': "b \<noteq> v_var s' q" by blast
      from 1 have hb': "HB_EnqRetCall s' b (v_var s' q)" by blast

      (* Step 2: Technical note for this transition-specific proof step.*)
      have inv_hI22: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast
      
      have his_eq: "his_seq s' = his_seq s" using step_facts by simp
      have v_var_eq_all: "v_var s' = v_var s" using step_facts by auto
      have i_var_eq_all: "i_var s' = i_var s" using step_facts by auto
      
      (* Technical note for this proof step.*)
      have pc_p_s: "program_counter s p = ''E2''" using step_facts pc_eqs by auto
      
      (* Technical note for this proof step.*)
      have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}"
      proof (cases "q = p")
        case True thus ?thesis using pc_p_s by simp
      next
        case False thus ?thesis using pc_q' step_facts pc_eqs by auto
      qed

      (* Technical note for this proof step.*)
      have hb_s: "HB_EnqRetCall s b (v_var s q)"
        using hb' his_eq v_var_eq_all
        unfolding HB_EnqRetCall_def HB_Act_def HB_def match_ret_def match_call_def Let_def mk_op_def op_name_def op_val_def
        by simp

      (* Step 3: Technical note for this proof step.*)
      show "Idx s' b < i_var s' q"
      proof (cases "b = v_var s p")
        case True
        (* ==================================================================== *)
        (* Technical note for this proof step.*)
        (* ==================================================================== *)
        
        (* Technical note for this transition-specific proof step.*)
        have pc_p_E123: "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" using pc_p_s by simp
        have no_ret: "\<not> (\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_enq_val_has_no_ret[OF INV pc_p_E123] by simp
          
        (* Technical note for this proof step.*)
        (* Technical note for this invariant-preservation argument.*)
        have "\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = b \<and> act_cr (his_seq s ! k) = ret"
          using hb_s unfolding HB_EnqRetCall_def HB_Act_def HB_def match_ret_def match_call_def Let_def mk_op_def op_name_def op_val_def
          by auto
          
        (* Technical note for this proof step.*)
        with no_ret True show ?thesis
          by auto 

      next
        case False
        (* ==================================================================== *)
        (* Technical note for this proof step.*)
        (* ==================================================================== *)
        
        (* Technical note for this proof step.
           Technical note for this transition-specific proof step.*)
        have idx_eq: "Idx s' b = Idx s b"
          using False step_facts 
          unfolding Idx_def AtIdx_def
          by (metis sI3_E2_Slot_Exclusive_def sI3_E2_Slot_Exclusive_s b_not_bot' fun_upd_def)
          
        have inqb_s: "InQBack s b"
          using inqb' False step_facts unfolding InQBack_def by auto
          
        have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_var_eq_all by simp

        (* Technical note for this proof step.*)
        have "Idx s b < i_var s q"
          using inv_hI22 pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
          unfolding hI30_Ticket_HB_Immunity_def by blast

        (* Technical note for this proof step.*)
        thus ?thesis using idx_eq i_var_eq_all by simp
      qed
    qed

  (* ========================================================================= *)
  (* Step 6: Technical note for this proof step.*)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  
  have "lI1_Op_Sets_Equivalence s'"
  proof -
    have "OPLin s' = OPLin s" 
      unfolding OPLin_def step_facts by simp
      
    moreover have "OP_A_enq s' = OP_A_enq s" 
      unfolding OP_A_enq_def EnqCallInHis_def 
      using set_facts step_facts by simp
      
    moreover have "OP_A_deq s' = OP_A_deq s" 
      unfolding OP_A_deq_def DeqCallInHis_def OPLin_def 
      using set_facts step_facts by simp
      
    moreover have "OP_B_enq s' = OP_B_enq s" 
      unfolding OP_B_enq_def EnqCallInHis_def 
      using set_facts step_facts by simp
      
    ultimately show ?thesis 
      using lI1_Op_Sets_Equivalence_s unfolding lI1_Op_Sets_Equivalence_def by simp
  qed
  
  have "lI2_Op_Cardinality s'" 
    using lI2_Op_Cardinality_s unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def 
    using set_facts step_facts by simp
    
(* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "lI3_HB_Ret_Lin_Sync s'"
  proof -
    (* Step 1: Technical note for this proof step.*)
    have seq_eq: "lin_seq s' = lin_seq s" "his_seq s' = his_seq s"
      using step_facts by simp_all
    
    (* Step 2: Technical note for this proof step.*)
    (* Technical note for this invariant-preservation argument.*)
    show ?thesis
      using lI3_HB_Ret_Lin_Sync_s seq_eq 
      unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def EnqRetInHis_def DeqRetInHis_def 
      by simp
  qed
    
  have "lI4_FIFO_Semantics s'" 
    using lI4_FIFO_Semantics_s unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def 
    using step_facts by simp
    
(* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "lI5_SA_Prefix s'"
  proof -
    (* Step 1: Technical note for this proof step.*)
    have seq_eq: "lin_seq s' = lin_seq s" 
      using step_facts by simp
      
    (* Step 2: Technical note for this invariant-preservation argument.
       Technical note for this invariant-preservation argument.
       Technical note for this invariant-preservation argument.
       Technical note for this invariant-preservation argument.*)
    show ?thesis
      using lI5_SA_Prefix_s seq_eq unfolding lI5_SA_Prefix_def by simp
  qed
  
  have "lI6_D4_Deq_Linearized s'" 
    using lI6_D4_Deq_Linearized_s unfolding lI6_D4_Deq_Linearized_def 
    using pc_eqs step_facts by simp
    
(* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "lI7_D4_Deq_Deq_HB s'"
  proof -
    (* Step 1: Technical note for this proof step.*)
    have seq_vars_eq: 
      "lin_seq s' = lin_seq s" "his_seq s' = his_seq s"
      "x_var s' = x_var s" "s_var s' = s_var s"
      using step_facts by simp_all

    (* Step 2: Technical note for this transition-specific proof step.*)
    have pc_d4_stable: "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    proof -
      fix q show "(program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
        using pc_eqs pc_p_E2 by (cases "q = p") auto
    qed

    (* Step 3: Technical note for this proof step.*)
    show ?thesis
      using lI7_D4_Deq_Deq_HB_s seq_vars_eq pc_d4_stable
      unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
      by metis
  qed
    
  have "lI8_D3_Deq_Returned s'" 
    using lI8_D3_Deq_Returned_s unfolding lI8_D3_Deq_Returned_def DeqRetInHis_def 
    using pc_eqs step_facts by simp
    
  have "lI9_D1_D2_Deq_Returned s'" 
    using lI9_D1_D2_Deq_Returned_s unfolding lI9_D1_D2_Deq_Returned_def DeqRetInHis_def 
    using pc_eqs step_facts by simp
    
(* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "lI10_D4_Enq_Deq_HB s'"
  proof -
    (* Step 1: Technical note for this transition-specific proof step.*)
    have seq_vars_eq: 
      "lin_seq s' = lin_seq s" "his_seq s' = his_seq s"
      "x_var s' = x_var s" "s_var s' = s_var s"
      using step_facts by simp_all

    (* Step 2: Technical note for this transition-specific proof step.*)
    have pc_d4_stable: "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
      using pc_eqs pc_p_E2 by (cases "q = p") auto

    (* Step 3: Technical note for this invariant-preservation argument.*)
    show ?thesis
      using lI10_D4_Enq_Deq_HB_s seq_vars_eq pc_d4_stable
      unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def HB_Act_def
      by metis
  qed
    
  have "lI11_D4_Deq_Unique s'" 
    using lI11_D4_Deq_Unique_s unfolding lI11_D4_Deq_Unique_def DeqRetInHis_def 
    using pc_eqs step_facts by simp

  have "data_independent (lin_seq s')" 
    using di_lin_s step_facts by simp
    
  have "Simulate_PC s'" 
    using STEP unfolding Sys_E2_def by simp

  (* ========================================================================= *)
  (* Step 7: Technical note for this proof step.*)
  (* ========================================================================= *)
  show ?thesis 
    unfolding system_invariant_def
    using `Simulate_PC s'` `TypeOK s'` 
    using `sI1_Zero_Index_BOT s'` `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'`  `hI3_L0_E_Phase_Bounds s'` 
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


(* ========================================================================= *)
(* Technical note for this transition-specific proof step.*)
(* ========================================================================= *)

lemma E2_preserves_state_invs_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows
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
  using E2_preserves_invariant_core[OF INV STEP]
  unfolding system_invariant_def by auto

lemma E2_preserves_history_invs_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows
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
  using E2_preserves_invariant_core[OF INV STEP]
  unfolding system_invariant_def by auto

lemma E2_preserves_linearization_invs_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows
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
  using E2_preserves_invariant_core[OF INV STEP]
  unfolding system_invariant_def by auto


end
