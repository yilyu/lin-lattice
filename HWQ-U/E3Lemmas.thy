(* E3-specific helper lemmas for history-side and linearization-side preservation *)
theory E3Lemmas
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    D4Lemmas
    DeqLib
    EnqLib
begin

(* ========================================================== *)
(* Auxiliary preservation lemmas for the E3 transition *)
(* ========================================================== *)




(* ========================================================================= *)
(* Preservation of hI13_Qback_Deq_Sync across the E3 step *)
(* ========================================================================= *)
lemma hI13_Qback_Deq_Sync_E3_step:
  assumes inv_hI13_Qback_Deq_Sync: "hI13_Qback_Deq_Sync s"
    and Q_arr_eq: "Q_arr s' = Q_arr s"
    and Qback_arr_eq: "Qback_arr s' = Qback_arr s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and x_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
    and s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
    and pc_p: "program_counter s p = ''E3''"  (* Technical note for this transition-specific proof step.*)
  shows "hI13_Qback_Deq_Sync s'"
  unfolding hI13_Qback_Deq_Sync_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 a)
  (* Technical note for this proof step.*)
  have a_val: "a \<noteq> BOT" using 1 by simp
  have "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a" using 1 by simp
  
  (* Technical note for this transition-specific proof step.*)
  hence "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a" 
    using Q_arr_eq Qback_arr_eq by simp
  
  (* Technical note for this proof step.*)
  then obtain q sn where old_prop:
    "(program_counter s q = ''D4'' \<and> x_var s q = a \<and> s_var s q = sn) \<or> DeqRetInHis s q a sn"
    using inv_hI13_Qback_Deq_Sync a_val unfolding hI13_Qback_Deq_Sync_def by blast
    
  (* Technical note for this proof step.*)
  show ?case
  proof (cases "q = p")
    case True
    (* Technical note for this proof step.*)
    have "program_counter s q = ''E3''" using True pc_p by simp
    hence "program_counter s q \<noteq> ''D4''" by simp
    
    (* Technical note for this transition-specific proof step.*)
    hence "DeqRetInHis s q a sn" using old_prop by auto
    
    (* Technical note for this proof step.*)
    hence "DeqRetInHis s' q a sn" 
      using his_append unfolding DeqRetInHis_def Let_def by (auto simp: nth_append)
      
    thus ?thesis by blast
  next
    case False
    (* Technical note for this proof step.*)
    have "program_counter s q = ''D4'' \<and> x_var s q = a \<and> s_var s q = sn \<Longrightarrow> 
          program_counter s' q = ''D4'' \<and> x_var s' q = a \<and> s_var s' q = sn"
      using False pc_eq x_var_other s_var_other by (auto simp: fun_upd_def)
      
    moreover have "DeqRetInHis s q a sn \<Longrightarrow> DeqRetInHis s' q a sn"
      using his_append unfolding DeqRetInHis_def Let_def by (auto simp: nth_append)
      
    ultimately show ?thesis using old_prop by blast
  qed
qed

(* ========================================================================= *)
(* Preservation of pending-enqueue exclusivity across the E3 step *)
(* ========================================================================= *)

(* ========== Preservation of history-side exclusivity invariants ========== *)

lemma hI14_Pending_Enq_Qback_Exclusivity_E3_step:
  assumes inv_hI14_Pending_Enq_Qback_Exclusivity: "hI14_Pending_Enq_Qback_Exclusivity s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and Qback_arr_eq: "Qback_arr s' = Qback_arr s"
    and i_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> i_var s' q = i_var s q"
    and s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  shows "hI14_Pending_Enq_Qback_Exclusivity s'"
  unfolding hI14_Pending_Enq_Qback_Exclusivity_def
  apply (intro conjI allI impI)
proof (goal_cases)
  (* ======================================================================= *)
  (* Part 1: Technical note for this transition-specific proof step.*)
  (* ======================================================================= *)
  case (1 q a)
  have pc_cond_s': "program_counter s' q \<in> {''E2'', ''E3''}" using 1 by simp
  have pending_s': "HasPendingEnq s' q a" using 1 by simp

  have q_not_p: "q \<noteq> p"
  proof
    assume "q = p"
    hence "program_counter s' q = ''L0''" using pc_eq by (simp add: fun_upd_def)
    with pc_cond_s' show False by simp
  qed

  have pending_s: "HasPendingEnq s q a"
  proof -
    have enq_call: "EnqCallInHis s' q a (s_var s' q)"
      and no_ret: "\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
      using pending_s' unfolding HasPendingEnq_def Let_def by blast+

    have sn_eq: "s_var s' q = s_var s q" using q_not_p s_var_other by simp
    have set_s': "set (his_seq s') = insert (mk_act enq (v_var s p) p (s_var s p) ret) (set (his_seq s))"
      using his_append by auto

    have "EnqCallInHis s q a (s_var s q)"
      using enq_call sn_eq set_s' q_not_p
      unfolding EnqCallInHis_def mk_act_def act_pid_def by auto
    moreover have "\<forall>e\<in>set (his_seq s). act_ssn e = s_var s q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
      using no_ret sn_eq set_s' by auto
    ultimately show ?thesis unfolding HasPendingEnq_def Let_def by blast
  qed

  (* Technical note for this proof step.*)
  have pc_s: "program_counter s q \<in> {''E2'', ''E3''}"
    using pc_cond_s' q_not_p pc_eq by (auto simp: fun_upd_def)

  have "\<not> (\<exists>k. Qback_arr s k = a \<and> k \<noteq> i_var s q)"
    using inv_hI14_Pending_Enq_Qback_Exclusivity pc_s pending_s unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
    
  thus ?case
    using Qback_arr_eq i_var_other[OF q_not_p] by auto

next
  (* ======================================================================= *)
  (* Part 2: Technical note for this proof step.*)
  (* ======================================================================= *)
  case (2 q a)
  have pc_cond_s': "program_counter s' q = ''E1''" using 2 by simp
  have pending_s': "HasPendingEnq s' q a" using 2 by simp

  have q_not_p: "q \<noteq> p"
  proof
    assume "q = p"
    hence "program_counter s' q = ''L0''" using pc_eq by (simp add: fun_upd_def)
    with pc_cond_s' show False by simp
  qed

  have pending_s: "HasPendingEnq s q a"
  proof -
    have enq_call: "EnqCallInHis s' q a (s_var s' q)"
      and no_ret: "\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
      using pending_s' unfolding HasPendingEnq_def Let_def by blast+

    have sn_eq: "s_var s' q = s_var s q" using q_not_p s_var_other by simp
    have set_s': "set (his_seq s') = insert (mk_act enq (v_var s p) p (s_var s p) ret) (set (his_seq s))"
      using his_append by auto

    have "EnqCallInHis s q a (s_var s q)"
      using enq_call sn_eq set_s' q_not_p
      unfolding EnqCallInHis_def mk_act_def act_pid_def by auto
    moreover have "\<forall>e\<in>set (his_seq s). act_ssn e = s_var s q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
      using no_ret sn_eq set_s' by auto
    ultimately show ?thesis unfolding HasPendingEnq_def Let_def by blast
  qed

  (* Technical note for this proof step.*)
  have pc_s: "program_counter s q = ''E1''"
    using pc_cond_s' q_not_p pc_eq by (auto simp: fun_upd_def)

  have "\<not> (\<exists>k. Qback_arr s k = a)"
    using inv_hI14_Pending_Enq_Qback_Exclusivity pc_s pending_s unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast

  thus ?case
    using Qback_arr_eq by auto
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)

(* ========== Preservation of dequeue-side exclusivity invariants ========== *)

lemma hI15_Deq_Result_Exclusivity_E3_step:
  assumes inv_hI15_Deq_Result_Exclusivity: "hI15_Deq_Result_Exclusivity s"
    and inv_sys: "system_invariant s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and pc_p: "program_counter s p = ''E3''"
    and s_var_p: "s_var s' p = s_var s p + 1"  
    and Q_arr_eq: "Q_arr s' = Q_arr s"
    and x_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
    and s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  shows "hI15_Deq_Result_Exclusivity s'"
  unfolding hI15_Deq_Result_Exclusivity_def
  apply (intro conjI allI impI)
proof (goal_cases)
  (* ======================================================================= *)
  (* Part 1: Technical note for this proof step.*)
  (* ======================================================================= *)
  case (1 a p1 p2)
  have a_val: "a \<in> Val" using 1 by simp
  have p1_neq_p2: "p1 \<noteq> p2" using 1 by simp

  (* Technical note for this proof step.*)
  show ?case
  proof
    assume conflict_s': "((\<exists>sn1. DeqRetInHis s' p1 a sn1) \<or> (program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a)) \<and>
                         ((\<exists>sn2. DeqRetInHis s' p2 a sn2) \<or> (program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a))"

    have deq_ret_equiv: "\<And>q sn. DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
    proof (intro iffI)
      fix q sn assume "DeqRetInHis s' q a sn"
      
      (* Technical note for this proof step.*)
      have e_not_deq: "act_name (mk_act enq (v_var s p) p (s_var s p) ret) \<noteq> deq \<or> 
                       act_cr (mk_act enq (v_var s p) p (s_var s p) ret) \<noteq> ret"
        by (simp add: mk_act_def act_name_def)
        
      (* Technical note for this proof step.*)
      show "DeqRetInHis s q a sn"
        using DeqRet_rev[OF \<open>DeqRetInHis s' q a sn\<close> his_append e_not_deq] by simp
    next
      fix q sn assume "DeqRetInHis s q a sn"
      
      (* Technical note for this proof step.*)
      show "DeqRetInHis s' q a sn"
        using DeqRet_mono[OF \<open>DeqRetInHis s q a sn\<close> his_append] by simp
    qed

    have pc_x_equiv: "\<And>q. program_counter s' q = ''D4'' \<and> x_var s' q = a \<longleftrightarrow> 
                          program_counter s q = ''D4'' \<and> x_var s q = a"
    proof -
      fix q
      show "program_counter s' q = ''D4'' \<and> x_var s' q = a \<longleftrightarrow> program_counter s q = ''D4'' \<and> x_var s q = a"
      proof (cases "q = p")
        case True
        have "program_counter s' p = ''L0''" using pc_eq by (simp add: fun_upd_def)
        moreover from pc_p have "program_counter s p = ''E3''" by simp
        hence "program_counter s p \<noteq> ''D4''" by simp
        ultimately show ?thesis using True by simp
      next
        case False
        have "program_counter s' q = program_counter s q" using False pc_eq by (simp add: fun_upd_def)
        moreover have "x_var s' q = x_var s q" using False x_var_other by simp
        ultimately show ?thesis by simp
      qed
    qed

    have conflict_s: "((\<exists>sn1. DeqRetInHis s p1 a sn1) \<or> (program_counter s p1 = ''D4'' \<and> x_var s p1 = a)) \<and>
                      ((\<exists>sn2. DeqRetInHis s p2 a sn2) \<or> (program_counter s p2 = ''D4'' \<and> x_var s p2 = a))"
      using conflict_s' deq_ret_equiv pc_x_equiv by auto

    (* usepre-statederive a contradiction, directly show False.*)
    show False 
      using inv_hI15_Deq_Result_Exclusivity a_val p1_neq_p2 conflict_s unfolding hI15_Deq_Result_Exclusivity_def by blast
  qed

next
  (* ======================================================================= *)
  (* Part 2: Technical note for this transition-specific proof step.*)
  (* ======================================================================= *)
  case (2 q a k)
  have a_val: "a \<in> Val" using 2 by simp
  have pending_s': "HasPendingDeq s' q" using 2 by simp

  show ?case
  proof
    (* Technical note for this proof step.*)
    assume bad_s': "x_var s' q = a \<and> Q_arr s' k = a"

    have q_not_p: "q \<noteq> p"
    proof
      assume "q = p"
      have "HasPendingDeq s' p" using pending_s' \<open>q = p\<close> by simp
      then obtain e where e_in: "e \<in> set (his_seq s')"
        and e_props: "act_pid e = p" "act_ssn e = s_var s' p" "act_cr e = call"
        unfolding HasPendingDeq_def Let_def DeqCallInHis_def by blast

      have "set (his_seq s') = set (his_seq s) \<union> {mk_act enq (v_var s p) p (s_var s p) ret}"
        using his_append by auto
      hence "e \<in> set (his_seq s)"
        using e_in e_props(3) by (auto simp: mk_act_def act_cr_def)

      from inv_sys have "hI2_SSN_Bounds s" unfolding system_invariant_def by auto
      hence "act_ssn e \<le> s_var s p" 
        using \<open>e \<in> set (his_seq s)\<close> e_props(1) unfolding hI2_SSN_Bounds_def by blast
        
      moreover have "act_ssn e = s_var s p + 1" 
        using e_props(2) s_var_p by simp
      ultimately show False by simp
    qed

    have pending_s: "HasPendingDeq s q"
    proof -
      from pending_s' obtain call_s': "DeqCallInHis s' q (s_var s' q)"
        and no_ret_s': "\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
        unfolding HasPendingDeq_def Let_def by blast
        
      have sn_eq: "s_var s' q = s_var s q" using q_not_p s_var_other by simp
      have call_s: "DeqCallInHis s q (s_var s q)"
        using DeqCall_rev[OF _ his_append] call_s' sn_eq 
        by (auto simp: mk_act_def act_name_def act_cr_def)
        
      have set_s': "set (his_seq s') = set (his_seq s) \<union> {mk_act enq (v_var s p) p (s_var s p) ret}"
        using his_append by auto
      have no_ret_s: "\<forall>e\<in>set (his_seq s). act_ssn e = s_var s q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
        using no_ret_s' sn_eq set_s' by auto
        
      show ?thesis unfolding HasPendingDeq_def Let_def using call_s no_ret_s by blast
    qed

    have x_eq: "x_var s q = a" using bad_s' q_not_p x_var_other by simp
    have qarr_eq: "Q_arr s k = a" using bad_s' Q_arr_eq by simp
    
    show False 
      using inv_hI15_Deq_Result_Exclusivity a_val pending_s x_eq qarr_eq unfolding hI15_Deq_Result_Exclusivity_def by blast
  qed

next
  (* ======================================================================= *)
  (* Part 3: Technical note for this proof step.*)
  (* ======================================================================= *)
  case (3 q a k)
  have a_val: "a \<in> Val" using 3 by simp
  
  (* Technical note for this proof step.*)
  have ret_s': "\<exists>sn. DeqRetInHis s' q a sn" using 3 by simp
  
  show ?case
  proof
    (* Technical note for this proof step.*)
    assume qarr_s': "Q_arr s' k = a"
    
    (* Technical note for this proof step.*)
    from ret_s' obtain sn where "DeqRetInHis s' q a sn" by blast
    
    (* invokebackward monotonicitylemma*)
    hence ret_s: "DeqRetInHis s q a sn"
      using DeqRet_rev[OF _ his_append] 
      by (auto simp: mk_act_def act_name_def act_cr_def)
      
    have qarr_s: "Q_arr s k = a" using qarr_s' Q_arr_eq by simp
    
    (* invokepre-state hI15_Deq_Result_Exclusivity derive a contradiction.*)
    show False 
      using inv_hI15_Deq_Result_Exclusivity a_val ret_s qarr_s unfolding hI15_Deq_Result_Exclusivity_def by blast
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI16_BO_BT_No_HB_E3_step:
  assumes inv_hI16_BO_BT_No_HB: "hI16_BO_BT_No_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and set_bo_stable: "SetBO s' = SetBO s"
    and set_bt_stable: "SetBT s' = SetBT s"
  shows "hI16_BO_BT_No_HB s'"
  unfolding hI16_BO_BT_No_HB_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 a b)
  have a_bo_s: "a \<in> SetBO s" using 1 set_bo_stable by simp
  have b_bt_s: "b \<in> SetBT s" using 1 set_bt_stable by simp

(* Key derivation: show that appending a return event does not change HB.*)
  have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
  proof
    (* Technical note for this proof step.*)
    assume "HB_EnqRetCall s' a b"
    then obtain p1 sn1 p2 sn2 where hb_s': "HB (his_seq s') (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_EnqRetCall_def HB_Act_def by auto

    (* Step 1: Technical note for this invariant-preservation argument.*)
    from hb_s'[unfolded HB_def] obtain k1 k2 where k_order: "k1 < k2"
      and m_ret: "match_ret (his_seq s') k1 (mk_op enq a p1 sn1)"
      and m_call: "match_call (his_seq s') k2 (mk_op enq b p2 sn2)"
      by blast

    have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp

    (* Step 2: Technical note for this proof step.*)
    have k2_len: "k2 < length (his_seq s')" 
      using m_call unfolding match_call_def Let_def by simp

    have k2_old: "k2 < length (his_seq s)"
    proof (rule ccontr)
      assume "\<not> k2 < length (his_seq s)"
      hence "k2 = length (his_seq s)" using k2_len len_s' by linarith
      hence "his_seq s' ! k2 = mk_act enq (v_var s p) p (s_var s p) ret" using his_append by (simp add: nth_append)
      hence "act_cr (his_seq s' ! k2) = ret" by (simp add: mk_act_def act_cr_def)
      thus False using m_call unfolding match_call_def Let_def by auto
    qed

    (* Step 3: useindex monotonicity.*)
    have k1_old: "k1 < length (his_seq s)" using k_order k2_old by linarith

    (* Step 4: Technical note for this proof step.*)
    have m1: "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
      using k1_old his_append m_ret unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
      using k2_old his_append m_call unfolding match_call_def Let_def by (auto simp: nth_append)

    have "HB (his_seq s) (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_def using k_order m1 m2 by blast
    thus "HB_EnqRetCall s a b" unfolding HB_EnqRetCall_def HB_Act_def by blast
  next
    (* Technical note for this proof step.*)
    assume "HB_EnqRetCall s a b"
    then obtain p1 sn1 p2 sn2 where hb_s: "HB (his_seq s) (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_EnqRetCall_def HB_Act_def by auto

    from hb_s[unfolded HB_def] obtain k1 k2 where k_order: "k1 < k2"
      and m_ret: "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
      and m_call: "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
      by blast

    (* Technical note for this proof step.*)
    have k1_len: "k1 < length (his_seq s)" using m_ret unfolding match_ret_def Let_def by simp
    have k2_len: "k2 < length (his_seq s)" using m_call unfolding match_call_def Let_def by simp

    have m1: "match_ret (his_seq s') k1 (mk_op enq a p1 sn1)"
      using k1_len m_ret his_append unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s') k2 (mk_op enq b p2 sn2)"
      using k2_len m_call his_append unfolding match_call_def Let_def by (auto simp: nth_append)

    have "HB (his_seq s') (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_def using k_order m1 m2 by blast
    thus "HB_EnqRetCall s' a b" unfolding HB_EnqRetCall_def HB_Act_def by blast
  qed

  (* Technical note for this proof step.*)
  show "\<not> HB_EnqRetCall s' a b"
    using inv_hI16_BO_BT_No_HB a_bo_s b_bt_s hb_eq unfolding hI16_BO_BT_No_HB_def by blast
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma hI17_BT_BT_No_HB_E3_step:
  assumes inv_hI17_BT_BT_No_HB: "hI17_BT_BT_No_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and set_bt_stable: "SetBT s' = SetBT s"
  shows "hI17_BT_BT_No_HB s'"
  unfolding hI17_BT_BT_No_HB_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 a b)
  have a_bt_s: "a \<in> SetBT s" using 1 set_bt_stable by simp
  have b_bt_s: "b \<in> SetBT s" using 1 set_bt_stable by simp

  (* Key derivation: show that appending a return event does not change HB.*)
  have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
  proof
    (* Technical note for this proof step.*)
    assume "HB_EnqRetCall s' a b"
    then obtain p1 sn1 p2 sn2 where hb_s': "HB (his_seq s') (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_EnqRetCall_def HB_Act_def by auto

    (* Step 1: Technical note for this proof step.*)
    from hb_s'[unfolded HB_def] obtain k1 k2 where k_order: "k1 < k2"
      and m_ret: "match_ret (his_seq s') k1 (mk_op enq a p1 sn1)"
      and m_call: "match_call (his_seq s') k2 (mk_op enq b p2 sn2)"
      by blast

    have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp

    (* Step 2: Technical note for this proof step.*)
    have k2_len: "k2 < length (his_seq s')" 
      using m_call unfolding match_call_def Let_def by simp

    have k2_old: "k2 < length (his_seq s)"
    proof (rule ccontr)
      assume "\<not> k2 < length (his_seq s)"
      hence "k2 = length (his_seq s)" using k2_len len_s' by linarith
      hence "his_seq s' ! k2 = mk_act enq (v_var s p) p (s_var s p) ret" using his_append by (simp add: nth_append)
      hence "act_cr (his_seq s' ! k2) = ret" by (simp add: mk_act_def act_cr_def)
      thus False using m_call unfolding match_call_def Let_def by auto
    qed

    (* Step 3: useindex monotonicity.*)
    have k1_old: "k1 < length (his_seq s)" using k_order k2_old by linarith

    (* Step 4: Technical note for this proof step.*)
    have m1: "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
      using k1_old his_append m_ret unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
      using k2_old his_append m_call unfolding match_call_def Let_def by (auto simp: nth_append)

    have "HB (his_seq s) (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_def using k_order m1 m2 by blast
    thus "HB_EnqRetCall s a b" unfolding HB_EnqRetCall_def HB_Act_def by blast
  next
    (* Technical note for this proof step.*)
    assume "HB_EnqRetCall s a b"
    then obtain p1 sn1 p2 sn2 where hb_s: "HB (his_seq s) (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_EnqRetCall_def HB_Act_def by auto

    from hb_s[unfolded HB_def] obtain k1 k2 where k_order: "k1 < k2"
      and m_ret: "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
      and m_call: "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
      by blast

    (* Technical note for this proof step.*)
    have k1_len: "k1 < length (his_seq s)" using m_ret unfolding match_ret_def Let_def by simp
    have k2_len: "k2 < length (his_seq s)" using m_call unfolding match_call_def Let_def by simp

    have m1: "match_ret (his_seq s') k1 (mk_op enq a p1 sn1)"
      using k1_len m_ret his_append unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s') k2 (mk_op enq b p2 sn2)"
      using k2_len m_call his_append unfolding match_call_def Let_def by (auto simp: nth_append)

    have "HB (his_seq s') (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
      unfolding HB_def using k_order m1 m2 by blast
    thus "HB_EnqRetCall s' a b" unfolding HB_EnqRetCall_def HB_Act_def by blast
  qed

  (* Technical note for this proof step.*)
  show "\<not> HB_EnqRetCall s' a b"
    using inv_hI17_BT_BT_No_HB a_bt_s b_bt_s hb_eq unfolding hI17_BT_BT_No_HB_def by blast
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI18_Idx_Order_No_Rev_HB_E3_step:
  assumes inv_hI18_Idx_Order_No_Rev_HB: "hI18_Idx_Order_No_Rev_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and idx_stable: "\<And>x. Idx s' x = Idx s x"
    and inq_stable: "\<And>x. InQBack s' x = InQBack s x"
    and atidx_stable: "\<And>i. AtIdx s' i = AtIdx s i"
  shows "hI18_Idx_Order_No_Rev_HB s'"
  unfolding hI18_Idx_Order_No_Rev_HB_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 a b)
  have inq_a: "InQBack s' a" and inq_b: "InQBack s' b" and idx_lt: "Idx s' a < Idx s' b"
    using 1 by simp_all

  have inq_a_s: "InQBack s a" using inq_a inq_stable by simp
  have inq_b_s: "InQBack s b" using inq_b inq_stable by simp
  have idx_lt_s: "Idx s a < Idx s b" using idx_lt idx_stable by simp

  (* Key derivation: show that appending a return event does not change HB.*)
  have hb_eq: "HB_EnqRetCall s' b a = HB_EnqRetCall s b a"
  proof
    (* Technical note for this proof step.*)
    assume "HB_EnqRetCall s' b a"
    then obtain p1 sn1 p2 sn2 where hb_s': "HB (his_seq s') (mk_op enq b p1 sn1) (mk_op enq a p2 sn2)"
      unfolding HB_EnqRetCall_def HB_Act_def by auto

    (* Step 1: Technical note for this proof step.*)
    from hb_s'[unfolded HB_def] obtain k1 k2 where k_order: "k1 < k2"
      and m_ret: "match_ret (his_seq s') k1 (mk_op enq b p1 sn1)"
      and m_call: "match_call (his_seq s') k2 (mk_op enq a p2 sn2)"
      by blast

    have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp

    (* Step 2: Technical note for this proof step.*)
    have k2_len: "k2 < length (his_seq s')" 
      using m_call unfolding match_call_def Let_def by simp

    have k2_old: "k2 < length (his_seq s)"
    proof (rule ccontr)
      assume "\<not> k2 < length (his_seq s)"
      hence "k2 = length (his_seq s)" using k2_len len_s' by linarith
      hence "his_seq s' ! k2 = mk_act enq (v_var s p) p (s_var s p) ret" using his_append by (simp add: nth_append)
      hence "act_cr (his_seq s' ! k2) = ret" by (simp add: mk_act_def act_cr_def)
      thus False using m_call unfolding match_call_def Let_def by auto
    qed

    (* Step 3: useindex monotonicity.*)
    have k1_old: "k1 < length (his_seq s)" using k_order k2_old by linarith

    (* Step 4: Technical note for this proof step.*)
    have m1: "match_ret (his_seq s) k1 (mk_op enq b p1 sn1)"
      using k1_old his_append m_ret unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s) k2 (mk_op enq a p2 sn2)"
      using k2_old his_append m_call unfolding match_call_def Let_def by (auto simp: nth_append)

    have "HB (his_seq s) (mk_op enq b p1 sn1) (mk_op enq a p2 sn2)"
      unfolding HB_def using k_order m1 m2 by blast
    thus "HB_EnqRetCall s b a" unfolding HB_EnqRetCall_def HB_Act_def by blast
  next
    (* Technical note for this proof step.*)
    assume "HB_EnqRetCall s b a"
    then obtain p1 sn1 p2 sn2 where hb_s: "HB (his_seq s) (mk_op enq b p1 sn1) (mk_op enq a p2 sn2)"
      unfolding HB_EnqRetCall_def HB_Act_def by auto

    from hb_s[unfolded HB_def] obtain k1 k2 where k_order: "k1 < k2"
      and m_ret: "match_ret (his_seq s) k1 (mk_op enq b p1 sn1)"
      and m_call: "match_call (his_seq s) k2 (mk_op enq a p2 sn2)"
      by blast

    (* Technical note for this proof step.*)
    have k1_len: "k1 < length (his_seq s)" using m_ret unfolding match_ret_def Let_def by simp
    have k2_len: "k2 < length (his_seq s)" using m_call unfolding match_call_def Let_def by simp

    have m1: "match_ret (his_seq s') k1 (mk_op enq b p1 sn1)"
      using k1_len m_ret his_append unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s') k2 (mk_op enq a p2 sn2)"
      using k2_len m_call his_append unfolding match_call_def Let_def by (auto simp: nth_append)

    have "HB (his_seq s') (mk_op enq b p1 sn1) (mk_op enq a p2 sn2)"
      unfolding HB_def using k_order m1 m2 by blast
    thus "HB_EnqRetCall s' b a" unfolding HB_EnqRetCall_def HB_Act_def by blast
  qed

  have "\<not> HB_EnqRetCall s b a" using inv_hI18_Idx_Order_No_Rev_HB inq_a_s inq_b_s idx_lt_s unfolding hI18_Idx_Order_No_Rev_HB_def by blast
  thus "\<not> HB_EnqRetCall s' b a" using hb_eq by simp
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma hI19_Scanner_Catches_Later_Enq_E3_step:
  assumes inv_hI19_Scanner_Catches_Later_Enq: "hI19_Scanner_Catches_Later_Enq s"
    and inv_sys: "system_invariant s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and other_vars: "\<And>q. q \<noteq> p \<Longrightarrow> (program_counter s' q = program_counter s q \<and> 
                                   j_var s' q = j_var s q \<and> 
                                   l_var s' q = l_var s q \<and> 
                                   s_var s' q = s_var s q)"
    and idx_stable: "\<And>x. Idx s' x = Idx s x"
    and type_stable: "\<And>x. TypeB s' x = TypeB s x"
    and inqback_stable: "\<And>x. InQBack s' x = InQBack s x"  (* Technical note for this proof step.*)
    and hb_stable: "\<And>a b. HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
  shows "hI19_Scanner_Catches_Later_Enq s'"
proof (unfold hI19_Scanner_Catches_Later_Enq_def, intro allI impI, goal_cases)
  case (1 a b)
  
  (* Step 1: extract the core assumptions of the goal.*)
  from 1 have inqa': "InQBack s' a" by blast
  from 1 have inqb': "InQBack s' b" by blast
  from 1 have tba': "TypeB s' a" by blast
  from 1 have tbb': "TypeB s' b" by blast
  from 1 have idx_ab': "Idx s' a < Idx s' b" by blast
  
  (* Step 2: obtain a pending scanner q in state D3.*)
  from 1 obtain q where q_props: 
    "HasPendingDeq s' q" 
    "program_counter s' q = ''D3''"
    "Idx s' a < j_var s' q" 
    "j_var s' q \<le> Idx s' b" 
    "Idx s' b < l_var s' q"
    by blast

  (* Step 3: Technical note for this transition-specific proof step.*)
  have q_neq_p: "q \<noteq> p"
  proof
    assume "q = p"
    with q_props(2) have "program_counter s' p = ''D3''" by simp
    moreover have "program_counter s' p = ''L0''" using pc_eq by simp
    ultimately show False by simp
  qed

  (* Step 4: transport the concrete facts back to the pre-state.*)
  
  (* Technical note for this proof step.*)
  have inqa_s: "InQBack s a" using inqa' inqback_stable by simp
  have inqb_s: "InQBack s b" using inqb' inqback_stable by simp
  have tba_s: "TypeB s a" using tba' type_stable by simp
  have tbb_s: "TypeB s b" using tbb' type_stable by simp
  have idx_ab_s: "Idx s a < Idx s b" using idx_ab' idx_stable by simp
  
  (* Technical note for this proof step.*)
  have pc_q_s: "program_counter s q = ''D3''" using q_props(2) other_vars q_neq_p by auto
  have j_var_eq: "j_var s' q = j_var s q" using other_vars q_neq_p by simp
  have l_var_eq: "l_var s' q = l_var s q" using other_vars q_neq_p by simp
  
  have bound1: "Idx s a < j_var s q" using q_props(3) idx_stable j_var_eq by simp
  have bound2: "j_var s q \<le> Idx s b" using q_props(4) idx_stable j_var_eq by simp
  have bound3: "Idx s b < l_var s q" using q_props(5) idx_stable l_var_eq by simp
  
  (* Technical note for this transition-specific proof step.*)
  have pend_q_s: "HasPendingDeq s q"
  proof -
    have s_var_eq: "s_var s' q = s_var s q" using other_vars q_neq_p by simp
    
    (* Technical note for this proof step.*)
    have "HasPendingDeq s' q = HasPendingDeq s q"
      unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
      using his_append s_var_eq q_neq_p by (auto simp: mk_act_def act_pid_def act_name_def)
      
    thus ?thesis using q_props(1) by simp
  qed

  (* Step 5: Technical note for this invariant-preservation argument.*)
  have "\<not> HB_EnqRetCall s a b"
    using inv_hI19_Scanner_Catches_Later_Enq inqa_s inqb_s tba_s tbb_s idx_ab_s
          pend_q_s pc_q_s bound1 bound2 bound3
    unfolding hI19_Scanner_Catches_Later_Enq_def by blast

  (* Step 6: Technical note for this proof step.*)
  then show "\<not> HB_EnqRetCall s' a b" using hb_stable by simp
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma hI21_Ret_Implies_Call_E3_step:
  assumes inv_hI21_Ret_Implies_Call: "hI21_Ret_Implies_Call s"
    and inv_hI12_D_Phase_Pending_Deq: "hI12_D_Phase_Pending_Deq s" 
    and inv_sys: "system_invariant s"  (* Technical note for this proof step.*)
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_p_s: "program_counter s p = ''E3''"
  shows "hI21_Ret_Implies_Call s'"
  unfolding hI21_Ret_Implies_Call_def Let_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 k')
  (* Technical note for this proof step.*)
  have k'_bound: "k' < length (his_seq s')" using 1 by simp
  have ret_k': "act_cr (his_seq s' ! k') = ret" using 1 by simp

  have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp

  consider (old) "k' < length (his_seq s)" | (new) "k' = length (his_seq s)"
    using k'_bound len_s' by linarith

  then show ?case
  proof cases
    case old
    (* Technical note for this invariant-preservation argument.*)
    have ret_old: "act_cr (his_seq s ! k') = ret"
      using old his_append ret_k' by (simp add: nth_append)

    from inv_hI21_Ret_Implies_Call[unfolded hI21_Ret_Implies_Call_def Let_def, rule_format, OF old ret_old]
    obtain tm where tm_props: "tm < k'"
      "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k')"
      "act_name (his_seq s ! tm) = act_name (his_seq s ! k')"
      "act_cr (his_seq s ! tm) = call"
      "(if act_name (his_seq s ! k') = enq
        then act_val (his_seq s ! tm) = act_val (his_seq s ! k')
        else act_val (his_seq s ! tm) = BOT)"
      by blast

    (* Technical note for this proof step.*)
    show ?thesis
    proof -
      have "his_seq s' ! tm = his_seq s ! tm" using tm_props(1) old his_append by (simp add: nth_append)
      moreover have "his_seq s' ! k' = his_seq s ! k'" using old his_append by (simp add: nth_append)
      ultimately show ?thesis using tm_props by auto
    qed
  next
    case new
    (* Technical note for this invariant-preservation argument.*)
    have new_ret: "his_seq s' ! k' = mk_act enq (v_var s p) p (s_var s p) ret"
      using new his_append by (simp add: nth_append)

    have oper: "act_name (his_seq s' ! k') = enq" using new_ret by (simp add: mk_act_def act_name_def)
    have val: "act_val (his_seq s' ! k') = v_var s p" using new_ret by (simp add: mk_act_def act_val_def)
    have pid: "act_pid (his_seq s' ! k') = p" using new_ret by (simp add: mk_act_def act_pid_def)
    have ssn: "act_ssn (his_seq s' ! k') = s_var s p" using new_ret by (simp add: mk_act_def act_ssn_def)

    (* Technical note for this invariant-preservation argument.*)
    have "hI1_E_Phase_Pending_Enq s" using inv_sys unfolding system_invariant_def by auto
    hence pending: "HasPendingEnq s p (v_var s p)" using pc_p_s unfolding hI1_E_Phase_Pending_Enq_def by auto

    from pending[unfolded HasPendingEnq_def Let_def]
    have "EnqCallInHis s p (v_var s p) (s_var s p)" by blast

    (* Technical note for this proof step.*)
    then obtain tm where tm_props:
      "tm < length (his_seq s)"
      "his_seq s ! tm = mk_act enq (v_var s p) p (s_var s p) call"
      unfolding EnqCallInHis_def Let_def
      by (force simp: in_set_conv_nth mk_act_def act_pid_def act_name_def act_cr_def act_val_def act_ssn_def)

    show ?thesis
    proof -
      have "tm < k'" using tm_props(1) new by simp
      moreover have "his_seq s' ! tm = mk_act enq (v_var s p) p (s_var s p) call"
        using tm_props his_append by (simp add: nth_append)
      ultimately show ?thesis
        using oper val pid ssn new_ret
        by (auto simp: mk_act_def act_pid_def act_name_def act_cr_def act_val_def act_ssn_def)
    qed
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI22_Deq_Local_Pattern_E3_step:
  assumes inv_hI22_Deq_Local_Pattern: "hI22_Deq_Local_Pattern s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and x_var_eq: "\<And>q. x_var s' q = x_var s q"   (* Technical note for this transition-specific proof step.*)
    and Q_arr_eq: "\<And>k. Q_arr s' k = Q_arr s k"
    and Qback_arr_eq: "\<And>k. Qback_arr s' k = Qback_arr s k"
  shows "hI22_Deq_Local_Pattern s'"
  unfolding hI22_Deq_Local_Pattern_def Let_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 q v sn)
  (* Step 1: Technical note for this proof step.*)
  have "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = v \<and> (\<forall>q'. x_var s' q' \<noteq> v)" using 1 by simp
  then obtain k where k_props: "Q_arr s' k = BOT" "Qback_arr s' k = v" "\<forall>q'. x_var s' q' \<noteq> v" by blast
  have ret_s': "DeqRetInHis s' q v sn" using 1 by simp

  (* Step 2: Technical note for this proof step.*)
  have qarr_s: "Q_arr s k = BOT" using k_props(1) Q_arr_eq by simp
  have qback_s: "Qback_arr s k = v" using k_props(2) Qback_arr_eq by simp
  have x_cond_s: "\<forall>q'. x_var s q' \<noteq> v" using k_props(3) x_var_eq by simp

  (* Step 3: Technical note for this proof step.*)
  have not_deq: "act_name (mk_act enq (v_var s p) p (s_var s p) ret) \<noteq> deq \<or> 
                 act_cr (mk_act enq (v_var s p) p (s_var s p) ret) \<noteq> ret"
    by (simp add: mk_act_def act_name_def)
    
  have ret_s: "DeqRetInHis s q v sn"
    using DeqRet_rev[OF ret_s' his_append not_deq] by simp

  (* Step 4: Technical note for this invariant-preservation argument.*)
  have "(\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = v \<and> (\<forall>q'. x_var s q' \<noteq> v)) \<and> DeqRetInHis s q v sn"
    using qarr_s qback_s x_cond_s ret_s by blast
    
  from inv_hI22_Deq_Local_Pattern[unfolded hI22_Deq_Local_Pattern_def Let_def, rule_format, OF this]
  obtain i where i_props:
    "i < length (filter (\<lambda>e. act_pid e = q) (his_seq s))"
    "filter (\<lambda>e. act_pid e = q) (his_seq s) ! i = mk_act deq v q sn ret"
    "0 < i"
    "filter (\<lambda>e. act_pid e = q) (his_seq s) ! (i - 1) = mk_act deq BOT q sn call"
    by blast

  (* Step 5: Technical note for this proof step.*)
  let ?f = "\<lambda>e. act_pid e = q"
  
  (* Technical note for this proof step.*)
  have filter_ext: "take (length (filter ?f (his_seq s))) (filter ?f (his_seq s')) = filter ?f (his_seq s)"
    using his_append by simp

  (* Step 6: close the loop.*)
  show ?case
  proof -
    have "i < length (filter ?f (his_seq s'))"
      using i_props(1) his_append by simp
      
    (* Technical note for this proof step.*)
    moreover have "filter ?f (his_seq s') ! i = mk_act deq v q sn ret"
      using i_props(1,2) filter_ext by (metis nth_take)
      
    moreover have "0 < i" by (rule i_props(3))
    
    moreover have "filter ?f (his_seq s') ! (i - 1) = mk_act deq BOT q sn call"
    proof -
      have "i - 1 < length (filter ?f (his_seq s))" using i_props(1,3) by simp
      thus ?thesis using i_props(4) filter_ext by (metis nth_take)
    qed
    
    ultimately show ?thesis by blast
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI23_Deq_Call_Ret_Balanced_E3_step:
  assumes inv_hI23_Deq_Call_Ret_Balanced: "hI23_Deq_Call_Ret_Balanced s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
  shows "hI23_Deq_Call_Ret_Balanced s'"
  unfolding hI23_Deq_Call_Ret_Balanced_def Let_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 q k)
  have k_bounds: "k \<le> length (his_seq s')" using 1 by simp
  have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp

  consider (old_k) "k \<le> length (his_seq s)" | (new_k) "k = length (his_seq s')"
    using k_bounds len_s' by linarith

  then show ?case
  proof cases
    case old_k
    (* inside the old-history range, the slices are identical.*)
    have take_eq: "take k (his_seq s') = take k (his_seq s)"
      using old_k his_append by simp
      
    (* Technical note for this proof step.*)
    have old_prop: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (filter (\<lambda>e. act_pid e = q) (take k (his_seq s))))
          \<le> length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)))) \<and>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)))) -
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)))) \<le> 1 \<and>
          (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)) \<noteq> [] \<and>
           act_cr (last (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)))) = call \<and>
           act_name (last (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)))) \<noteq> deq \<longrightarrow>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)))) =
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (filter (\<lambda>e. act_pid e = q) (take k (his_seq s)))))"
      using inv_hI23_Deq_Call_Ret_Balanced old_k unfolding hI23_Deq_Call_Ret_Balanced_def Let_def by blast
      
    thus ?thesis unfolding take_eq by simp
  next
    case new_k
    have take_all: "take k (his_seq s') = his_seq s'" using new_k by simp
    
    let ?f_q = "\<lambda>e. act_pid e = q"
    let ?f_call = "\<lambda>e. act_name e = deq \<and> act_cr e = call"
    let ?f_ret  = "\<lambda>e. act_name e = deq \<and> act_cr e = ret"
    
    (* the appended enqueue event does not affect dequeue counts*)
    have count_call_eq: "length (filter ?f_call (filter ?f_q (his_seq s'))) = length (filter ?f_call (filter ?f_q (his_seq s)))"
      using his_append by (auto simp: mk_act_def act_name_def)
      
    have count_ret_eq: "length (filter ?f_ret (filter ?f_q (his_seq s'))) = length (filter ?f_ret (filter ?f_q (his_seq s)))"
      using his_append by (auto simp: mk_act_def act_name_def)

    (* Technical note for this proof step.*)
    have old_prop: "length (filter ?f_ret (filter ?f_q (his_seq s))) \<le> length (filter ?f_call (filter ?f_q (his_seq s))) \<and>
          length (filter ?f_call (filter ?f_q (his_seq s))) - length (filter ?f_ret (filter ?f_q (his_seq s))) \<le> 1 \<and>
          (filter ?f_q (his_seq s) \<noteq> [] \<and> act_cr (last (filter ?f_q (his_seq s))) = call \<and> act_name (last (filter ?f_q (his_seq s))) \<noteq> deq \<longrightarrow>
           length (filter ?f_call (filter ?f_q (his_seq s))) = length (filter ?f_ret (filter ?f_q (his_seq s))))"
      using inv_hI23_Deq_Call_Ret_Balanced unfolding hI23_Deq_Call_Ret_Balanced_def Let_def
      by (metis (no_types, lifting) le_refl take_all_iff) 

    (* Key derivation: provetail condition.*)
    have tail_cond: "filter ?f_q (his_seq s') \<noteq> [] \<and> act_cr (last (filter ?f_q (his_seq s'))) = call \<and> act_name (last (filter ?f_q (his_seq s'))) \<noteq> deq \<longrightarrow>
           length (filter ?f_call (filter ?f_q (his_seq s'))) = length (filter ?f_ret (filter ?f_q (his_seq s')))"
    proof (cases "q = p")
      case True
      (* if q = p, the appended event enters the filtered list; the new tail is a return, so the condition becomes false.*)
      have "filter ?f_q (his_seq s') = filter ?f_q (his_seq s) @ [mk_act enq (v_var s p) p (s_var s p) ret]"
        using his_append True by (simp add: mk_act_def act_pid_def)
      hence "last (filter ?f_q (his_seq s')) = mk_act enq (v_var s p) p (s_var s p) ret"
        by simp
      hence "act_cr (last (filter ?f_q (his_seq s'))) = ret"
        by (simp add: mk_act_def act_cr_def)
      thus ?thesis by simp
    next
      case False
      (* if q \<noteq> p, the filtered list is unchanged and we reduce to the pre-state.*)
      have "filter ?f_q (his_seq s') = filter ?f_q (his_seq s)"
        using his_append False by (auto simp: mk_act_def act_pid_def)
      thus ?thesis using old_prop count_call_eq count_ret_eq by simp
    qed

    (* Technical note for this proof step.*)
    show ?thesis
      unfolding take_all
      using old_prop count_call_eq count_ret_eq tail_cond by auto
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI24_HB_Implies_Idx_Order_E3_step:
  assumes inv_hI24_HB_Implies_Idx_Order: "hI24_HB_Implies_Idx_Order s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and q_arr_eq: "CState.Q_arr (fst s') = CState.Q_arr (fst s)"  (* Technical note for this proof step.*)
  shows "hI24_HB_Implies_Idx_Order s'"
  unfolding hI24_HB_Implies_Idx_Order_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 u1 u2 v1 v2 idx1 idx2 sn1 sn2)
  
  (* Step 1: Technical note for this proof step.*)
  have hb_s': "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)" using 1 by simp
  have arr1: "CState.Q_arr (fst s') idx1 = v1" using 1 by simp
  have arr2: "CState.Q_arr (fst s') idx2 = v2" using 1 by simp

  (* Technical note for this proof step.*)
  have arr1_s: "CState.Q_arr (fst s) idx1 = v1" using arr1 q_arr_eq by simp
  have arr2_s: "CState.Q_arr (fst s) idx2 = v2" using arr2 q_arr_eq by simp

  (* Step 2: Technical note for this proof step.*)
  have hb_s: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
  proof -
    from hb_s'[unfolded HB_Act_def HB_def] obtain k1 k2 where k_order: "k1 < k2"
      and m_ret: "match_ret (his_seq s') k1 (mk_op enq v2 u2 sn2)"
      and m_call: "match_call (his_seq s') k2 (mk_op enq v1 u1 sn1)"
      by blast

    have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp

    (* Technical note for this proof step.*)
    have k2_len: "k2 < length (his_seq s')"
      using m_call unfolding match_call_def Let_def by simp

    have k2_old: "k2 < length (his_seq s)"
    proof (rule ccontr)
      assume "\<not> k2 < length (his_seq s)"
      hence "k2 = length (his_seq s)" using k2_len len_s' by linarith
      hence "his_seq s' ! k2 = mk_act enq (v_var s p) p (s_var s p) ret" using his_append by (simp add: nth_append)
      hence "act_cr (his_seq s' ! k2) = ret" by (simp add: mk_act_def act_cr_def)
      thus False using m_call unfolding match_call_def Let_def by auto
    qed

    have k1_old: "k1 < length (his_seq s)" using k_order k2_old by linarith

    have m1: "match_ret (his_seq s) k1 (mk_op enq v2 u2 sn2)"
      using k1_old his_append m_ret unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s) k2 (mk_op enq v1 u1 sn1)"
      using k2_old his_append m_call unfolding match_call_def Let_def by (auto simp: nth_append)

    show ?thesis unfolding HB_Act_def HB_def using k_order m1 m2 by blast
  qed

  (* Step 3: Technical note for this proof step.*)
  show ?case
    using inv_hI24_HB_Implies_Idx_Order hb_s arr1_s arr2_s unfolding hI24_HB_Implies_Idx_Order_def by blast
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI25_Enq_Call_Ret_Balanced_E3_step:
  assumes inv_hI25_Enq_Call_Ret_Balanced: "hI25_Enq_Call_Ret_Balanced s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and pc_p: "program_counter s p = ''E3''"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
  shows "hI25_Enq_Call_Ret_Balanced s'"
  unfolding hI25_Enq_Call_Ret_Balanced_def Let_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 q k)
  have k_bounds: "k \<le> length (his_seq s')" using 1 by simp
  have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp

  let ?f_q = "\<lambda>e. act_pid e = q \<and> act_name e = enq"
  let ?f_call = "\<lambda>e. act_cr e = call"
  let ?f_ret  = "\<lambda>e. act_cr e = ret"

  consider (old_k) "k \<le> length (his_seq s)" | (new_k) "k = length (his_seq s')"
    using k_bounds len_s' by linarith
  then show ?case
  proof cases
    case old_k
    have take_eq: "take k (his_seq s') = take k (his_seq s)"
      using old_k his_append by simp
      
    (* Technical note for this proof step.*)
    have old_prop: "length (filter ?f_ret (filter ?f_q (take k (his_seq s)))) \<le> length (filter ?f_call (filter ?f_q (take k (his_seq s)))) \<and>
          length (filter ?f_call (filter ?f_q (take k (his_seq s)))) - length (filter ?f_ret (filter ?f_q (take k (his_seq s)))) \<le> 1 \<and>
          (k = length (his_seq s) \<longrightarrow> (program_counter s q \<in> {''E1'', ''E2'', ''E3''} = 
          (length (filter ?f_call (filter ?f_q (take k (his_seq s)))) - length (filter ?f_ret (filter ?f_q (take k (his_seq s)))) = 1)))"
      using inv_hI25_Enq_Call_Ret_Balanced[unfolded hI25_Enq_Call_Ret_Balanced_def Let_def, rule_format, of k q] old_k by auto
      
    (* Technical note for this proof step.*)
    have tail_vacuous: "k = length (his_seq s') \<longrightarrow> (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} = 
          (length (filter ?f_call (filter ?f_q (take k (his_seq s')))) - length (filter ?f_ret (filter ?f_q (take k (his_seq s')))) = 1))"
      using old_k len_s' by simp

    show ?thesis unfolding take_eq using old_prop tail_vacuous
      using take_eq by force 
  next
    case new_k
    have take_all: "take k (his_seq s') = his_seq s'" using new_k by simp
    
    (* Technical note for this proof step.*)
    have old_prop: "length (filter ?f_ret (filter ?f_q (his_seq s))) \<le> length (filter ?f_call (filter ?f_q (his_seq s))) \<and>
          length (filter ?f_call (filter ?f_q (his_seq s))) - length (filter ?f_ret (filter ?f_q (his_seq s))) \<le> 1 \<and>
          (program_counter s q \<in> {''E1'', ''E2'', ''E3''} = 
          (length (filter ?f_call (filter ?f_q (his_seq s))) - length (filter ?f_ret (filter ?f_q (his_seq s))) = 1))"
      using inv_hI25_Enq_Call_Ret_Balanced[unfolded hI25_Enq_Call_Ret_Balanced_def Let_def, rule_format, of "length (his_seq s)" q] by simp

    show ?thesis
    proof (cases "q = p")
      case False
      (* Technical note for this proof step.*)
      have filter_eq: "filter ?f_q (his_seq s') = filter ?f_q (his_seq s)"
        using his_append False by (auto simp: mk_act_def act_pid_def)
      have pc_q: "program_counter s' q = program_counter s q" using False pc_other by simp
      
      show ?thesis unfolding take_all filter_eq pc_q using old_prop new_k by auto
    next
      case True
      (* Technical note for this proof step.*)
      have filter_eq: "filter ?f_q (his_seq s') = filter ?f_q (his_seq s) @ [mk_act enq (v_var s p) p (s_var s p) ret]"
        using his_append True by (simp add: mk_act_def act_pid_def act_name_def)
        
      (* Technical note for this proof step.*)
      have count_call: "length (filter ?f_call (filter ?f_q (his_seq s'))) = length (filter ?f_call (filter ?f_q (his_seq s)))"
        unfolding filter_eq by (simp add: mk_act_def act_cr_def)
      have count_ret: "length (filter ?f_ret (filter ?f_q (his_seq s'))) = length (filter ?f_ret (filter ?f_q (his_seq s))) + 1"
        unfolding filter_eq by (simp add: mk_act_def act_cr_def)

      (* Technical note for this transition-specific proof step.*)
      have "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" using pc_p by simp
      hence diff_old: "length (filter ?f_call (filter ?f_q (his_seq s))) - length (filter ?f_ret (filter ?f_q (his_seq s))) = 1"
        using old_prop True by blast
        
      (* Technical note for this proof step.*)
      have old_call_eq: "length (filter ?f_call (filter ?f_q (his_seq s))) = length (filter ?f_ret (filter ?f_q (his_seq s))) + 1"
        using diff_old old_prop True by linarith
        
      (* Technical note for this proof step.*)
      have new_diff: "length (filter ?f_call (filter ?f_q (his_seq s'))) - length (filter ?f_ret (filter ?f_q (his_seq s'))) = 0"
        using count_call count_ret old_call_eq by simp
      have new_le: "length (filter ?f_ret (filter ?f_q (his_seq s'))) \<le> length (filter ?f_call (filter ?f_q (his_seq s')))"
        using count_call count_ret old_call_eq by simp

      (* Technical note for this transition-specific proof step.*)
      have pc_s': "program_counter s' p = ''L0''" using pc_eq by (simp add: fun_upd_def)
      have not_in_E: "program_counter s' p \<notin> {''E1'', ''E2'', ''E3''}" using pc_s' by simp
      
      show ?thesis
        unfolding take_all
        using new_diff new_le not_in_E True new_k by auto
    qed
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma hI26_DeqRet_D4_Mutex_E3_step:
  assumes inv_hI26_DeqRet_D4_Mutex: "hI26_DeqRet_D4_Mutex s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    and x_var_eq: "\<And>q. x_var s' q = x_var s q"  (* Technical note for this proof step.*)
  shows "hI26_DeqRet_D4_Mutex s'"
  unfolding hI26_DeqRet_D4_Mutex_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 q a)
  have a_val: "a \<in> Val" using 1 by simp

  (* Key tactic: usestandard contradiction patternprove \<not> X.*)
  show ?case
  proof
    assume bad: "(\<exists>sn. DeqRetInHis s' q a sn) \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a"

    have pc_q_s': "program_counter s' q = ''D4''" using bad by simp

    (* Step 1: prove q <noteq> p.*)
    have q_not_p: "q \<noteq> p"
    proof
      assume "q = p"
      hence "program_counter s' q = ''L0''" using pc_eq by (simp add: fun_upd_def)
      with pc_q_s' show False by simp
    qed

    (* Step 2: Technical note for this proof step.*)
    have pc_q_s: "program_counter s q = ''D4''" using pc_q_s' q_not_p pc_other by simp
    have x_q_s: "x_var s q = a" using bad x_var_eq by simp

    (* Step 3: Technical note for this proof step.*)
    from bad obtain sn where ret_s': "DeqRetInHis s' q a sn" by blast
    
    have not_deq_ret: "act_name (mk_act enq (v_var s p) p (s_var s p) ret) \<noteq> deq \<or> 
                       act_cr (mk_act enq (v_var s p) p (s_var s p) ret) \<noteq> ret"
      by (simp add: mk_act_def act_name_def)

    have ret_s: "DeqRetInHis s q a sn"
      using DeqRet_rev[OF ret_s' his_append not_deq_ret] by simp

    (* Step 4: Technical note for this proof step.*)
    have "\<not> ((\<exists>sn. DeqRetInHis s q a sn) \<and> program_counter s q = ''D4'' \<and> x_var s q = a)"
      using inv_hI26_DeqRet_D4_Mutex a_val unfolding hI26_DeqRet_D4_Mutex_def by blast

    thus False using ret_s pc_q_s x_q_s by blast
  qed
qed

(* ========================================================================= *)
(* Technical note for this transition-specific proof step.*)
(* ========================================================================= *)

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)

(* ========== Preservation of linearization invariants ========== *)

lemma lI1_Op_Sets_Equivalence_E3_step:
  assumes inv_lI1_Op_Sets_Equivalence: "lI1_Op_Sets_Equivalence s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and oplin_eq: "OPLin s' = OPLin s"
    and setA_eq: "SetA s' = SetA s"
    and setB_eq: "SetB s' = SetB s"
  shows "lI1_Op_Sets_Equivalence s'"
proof -
  (* Step 1: Technical note for this proof step.*)
  have set_s': "set (his_seq s') = set (his_seq s) \<union> {mk_act enq (v_var s p) p (s_var s p) ret}"
    using his_append by auto

  (* Step 2: Technical note for this proof step.*)
  have enq_call_eq: "\<And>q a sn. EnqCallInHis s' q a sn = EnqCallInHis s q a sn"
    unfolding EnqCallInHis_def Let_def set_s'
    by (auto simp: mk_act_def act_cr_def)

  have deq_call_eq: "\<And>q sn. DeqCallInHis s' q sn = DeqCallInHis s q sn"
    unfolding DeqCallInHis_def Let_def set_s'
    by (auto simp: mk_act_def act_cr_def)

  (* Step 3: Technical note for this proof step.*)
  have opA_eq: "OP_A_enq s' = OP_A_enq s"
    unfolding OP_A_enq_def using setA_eq enq_call_eq by simp

  have opA_deq_eq: "OP_A_deq s' = OP_A_deq s"
    unfolding OP_A_deq_def using setA_eq deq_call_eq
    using oplin_eq by auto 

  have opB_eq: "OP_B_enq s' = OP_B_enq s"
    unfolding OP_B_enq_def using setB_eq enq_call_eq by simp

  (* Step 4: Technical note for this proof step.*)
  show ?thesis
    using inv_lI1_Op_Sets_Equivalence oplin_eq opA_eq opA_deq_eq opB_eq unfolding lI1_Op_Sets_Equivalence_def by simp
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma lI3_HB_Ret_Lin_Sync_E3_step:
  assumes inv_lI3_HB_Ret_Lin_Sync: "lI3_HB_Ret_Lin_Sync s"
    and inv_lI1_Op_Sets_Equivalence: "lI1_Op_Sets_Equivalence s"
    and inv_sys: "system_invariant s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and lin_eq: "lin_seq s' = lin_seq s"
    and pc_p: "program_counter s p = ''E3''"
  shows "lI3_HB_Ret_Lin_Sync s'"
  unfolding lI3_HB_Ret_Lin_Sync_def
  apply (intro conjI allI impI)
proof (goal_cases)

  (* Case 1: Technical note for this invariant-preservation argument.*)
  case (1 k1 k2)
  have k_bounds: "k1 < length (lin_seq s)" "k2 < length (lin_seq s)" 
    using 1 lin_eq by simp_all
  have hb_act_s': "HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2)" using 1 by simp
  have hb_act_s: "HB_Act s (lin_seq s ! k1) (lin_seq s ! k2)"
  proof -
    from hb_act_s'[unfolded HB_Act_def HB_def] obtain h1 h2 where
      h_order: "h1 < h2" and
      m_ret: "match_ret (his_seq s') h1 (lin_seq s ! k1)" and
      m_call: "match_call (his_seq s') h2 (lin_seq s ! k2)"
      using lin_eq by auto
    have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp
    have h2_old: "h2 < length (his_seq s)"
    proof (rule ccontr)
      assume not_old: "\<not> h2 < length (his_seq s)"
      have h2_bound: "h2 < length (his_seq s')" using m_call unfolding match_call_def Let_def by simp
      with not_old len_s' have "h2 = length (his_seq s)" by linarith
      then have "his_seq s' ! h2 = mk_act enq (v_var s p) p (s_var s p) ret"
        using his_append by (simp add: nth_append)
      hence "act_cr (his_seq s' ! h2) = ret" by (simp add: mk_act_def act_cr_def)
      with m_call show False unfolding match_call_def Let_def by simp
    qed
    have h1_old: "h1 < length (his_seq s)" using h_order h2_old by linarith
    have m1: "match_ret (his_seq s) h1 (lin_seq s ! k1)"
      using h1_old his_append m_ret unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s) h2 (lin_seq s ! k2)"
      using h2_old his_append m_call unfolding match_call_def Let_def by (auto simp: nth_append)
    thus ?thesis unfolding HB_Act_def HB_def using h_order m1 m2 by blast
  qed
  show "k1 < k2" using inv_lI3_HB_Ret_Lin_Sync k_bounds hb_act_s unfolding lI3_HB_Ret_Lin_Sync_def by blast

next

  (* Case 2: Technical note for this proof step.*)
  case (2 p_id a sn)
  have ret_s': "EnqRetInHis s' p_id a sn" using 2 by simp

  have "EnqRetInHis s p_id a sn \<or> (p_id = p \<and> a = v_var s p \<and> sn = s_var s p)"
    using ret_s' his_append unfolding EnqRetInHis_def Let_def
    by (auto simp: mk_act_def act_pid_def act_name_def act_cr_def act_val_def act_ssn_def)

  thus "\<exists>k<length (lin_seq s'). lin_seq s' ! k = mk_op enq a p_id sn"
  proof (elim disjE, goal_cases)
    case 1
    then obtain k where "k < length (lin_seq s)" "lin_seq s ! k = mk_op enq a p_id sn"
      using inv_lI3_HB_Ret_Lin_Sync unfolding lI3_HB_Ret_Lin_Sync_def by blast
    thus ?case using lin_eq by auto
  next
    case 2
    then have curr: "p_id = p" "a = v_var s p" "sn = s_var s p" by simp_all

    from inv_sys have hI1_E_Phase_Pending_Enq: "hI1_E_Phase_Pending_Enq s" unfolding system_invariant_def by auto
    with pc_p have pending: "EnqCallInHis s p (v_var s p) (s_var s p)"
      unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def
      using insert_commute by fastforce 

    from inv_sys have hI20_Enq_Val_Valid: "hI20_Enq_Val_Valid s" unfolding system_invariant_def by auto
    have val_bound: "v_var s p \<in> Val" 
      using pending hI20_Enq_Val_Valid unfolding EnqCallInHis_def Let_def hI20_Enq_Val_Valid_def 
      by (metis in_set_conv_nth)

    from inv_sys have sI4_E3_Qback_Written: "sI4_E3_Qback_Written s" unfolding system_invariant_def by auto
    have "Qback_arr s (i_var s p) = v_var s p" 
      using sI4_E3_Qback_Written pc_p unfolding sI4_E3_Qback_Written_def by blast
    hence in_qback: "InQBack s (v_var s p)" unfolding InQBack_def by blast

    (* Technical note for this invariant-preservation argument.*)
    have "QHas s (v_var s p) \<or> \<not> QHas s (v_var s p)" by blast
    then show ?case
    proof (elim disjE, goal_cases)
      case 1
      hence "TypeB s (v_var s p)" unfolding TypeB_def by blast
      hence "v_var s p \<in> SetB s" unfolding SetB_def using val_bound by blast
      hence "mk_op enq (v_var s p) p (s_var s p) \<in> OP_B_enq s"
        unfolding OP_B_enq_def using pending by blast
      with inv_lI1_Op_Sets_Equivalence have "mk_op enq (v_var s p) p (s_var s p) \<in> OPLin s"
        unfolding lI1_Op_Sets_Equivalence_def by blast
      thus ?thesis unfolding OPLin_def using lin_eq curr
        by (simp add: in_set_conv_nth) 
    next
      case 2
      hence "TypeA s (v_var s p)" unfolding TypeA_def using in_qback by blast
      hence "v_var s p \<in> SetA s" unfolding SetA_def using val_bound by blast
      hence "mk_op enq (v_var s p) p (s_var s p) \<in> OP_A_enq s"
        unfolding OP_A_enq_def using pending by blast
      with inv_lI1_Op_Sets_Equivalence have "mk_op enq (v_var s p) p (s_var s p) \<in> OPLin s"
        unfolding lI1_Op_Sets_Equivalence_def by blast
      thus ?thesis unfolding OPLin_def using lin_eq curr
        by (simp add: in_set_conv_nth)
    qed
  qed

next

  (* Case 3: Technical note for this proof step.*)
  case (3 p_id a sn)
  have ret_s': "DeqRetInHis s' p_id a sn" using 3 by simp
  have "DeqRetInHis s p_id a sn"
    using DeqRet_rev[OF ret_s' his_append] by (auto simp: mk_act_def act_name_def)
  then obtain k where "k < length (lin_seq s)" "lin_seq s ! k = mk_op deq a p_id sn"
    using inv_lI3_HB_Ret_Lin_Sync unfolding lI3_HB_Ret_Lin_Sync_def by blast
  thus "\<exists>k<length (lin_seq s'). lin_seq s' ! k = mk_op deq a p_id sn"
    using lin_eq by auto
qed


lemma lI7_D4_Deq_Deq_HB_E3_step:
  assumes inv_lI7_D4_Deq_Deq_HB: "lI7_D4_Deq_Deq_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_curr_p_s': "program_counter s' p = ''L0''"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    and vars_other: "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI7_D4_Deq_Deq_HB s'"
  unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 k1 k2 q)
  (* Technical note for this proof step.*)
  have k1_len: "k1 < length (lin_seq s')" using 1 by simp
  have k2_len: "k2 < length (lin_seq s')" using 1 by simp
  have act_k1: "op_name (lin_seq s' ! k1) = deq" using 1 by simp
  have k2_eq: "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)" using 1 by simp
  have term_cond: "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q" using 1 by simp
  have pc_q: "program_counter s' q = ''D4''" using 1 by simp
  have hb: "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)" using 1
    by auto 

  (* Technical note for this transition-specific proof step.*)
  have q_not_p: "q \<noteq> p"
  proof
    assume "q = p"
    then have "program_counter s' p = ''D4''" using pc_q by simp
    with pc_curr_p_s' show False by simp
  qed

  (* Technical note for this proof step.*)
  have k1_len_s: "k1 < length (lin_seq s)" and k2_len_s: "k2 < length (lin_seq s)"
    using k1_len k2_len lin_eq by simp_all
  have act_k1_s: "op_name (lin_seq s ! k1) = deq" using act_k1 lin_eq by simp
  have k2_eq_s: "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
    using k2_eq q_not_p vars_other lin_eq by auto
  have term_cond_s: "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
    using term_cond lin_eq by auto
  have pc_q_s: "program_counter s q = ''D4''"
    using pc_q q_not_p pc_other by simp

  (* Technical note for this proof step.*)
  have hb_s: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
  proof -
    from hb[unfolded HB_def] obtain h1 h2 where
      h_order: "h1 < h2" and
      m_ret: "match_ret (his_seq s') h1 (lin_seq s ! k1)" and
      m_call: "match_call (his_seq s') h2 (lin_seq s ! k2)"
      using lin_eq by auto
    have len_s': "length (his_seq s') = length (his_seq s) + 1" using his_append by simp
    have h2_old: "h2 < length (his_seq s)"
    proof (rule ccontr)
      assume not_old: "\<not> h2 < length (his_seq s)"
      have h2_bound: "h2 < length (his_seq s')" using m_call unfolding match_call_def Let_def by simp
      with not_old len_s' have "h2 = length (his_seq s)" by linarith
      then have "his_seq s' ! h2 = mk_act enq (v_var s p) p (s_var s p) ret"
        using his_append by (simp add: nth_append)
      hence "act_cr (his_seq s' ! h2) = ret" by (simp add: mk_act_def act_cr_def)
      with m_call show False unfolding match_call_def Let_def by simp
    qed
    have h1_old: "h1 < length (his_seq s)" using h_order h2_old by linarith
    have m1: "match_ret (his_seq s) h1 (lin_seq s ! k1)"
      using h1_old his_append m_ret unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s) h2 (lin_seq s ! k2)"
      using h2_old his_append m_call unfolding match_call_def Let_def by (auto simp: nth_append)
    thus ?thesis unfolding HB_def using h_order m1 m2 by blast
  qed

  (* ========================================================================= *)
  (* Step 4: Technical note for this invariant-preservation argument.*)
  (* Technical note for this proof step.*)
  (* ========================================================================= *)
  show "k1 < k2"
  proof -
    (* Technical note for this proof step.*)
    from inv_lI7_D4_Deq_Deq_HB k1_len_s k2_len_s act_k1_s k2_eq_s term_cond_s pc_q_s hb_s
    show "k1 < k2"
      unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
      by blast
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma lI8_D3_Deq_Returned_E3_step:
  assumes inv_lI8_D3_Deq_Returned: "lI8_D3_Deq_Returned s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_curr_p_s': "program_counter s' p = ''L0''"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI8_D3_Deq_Returned s'"
  unfolding lI8_D3_Deq_Returned_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 q k)
  (* Step 1: Technical note for this proof step.*)
  have pc_q_s': "program_counter s' q = ''D3''" using 1 by simp
  have k_len: "k < length (lin_seq s')" using 1 by simp
  have op_deq: "op_name (lin_seq s' ! k) = deq" 
   and pid_q: "op_pid (lin_seq s' ! k) = q" using 1 by simp_all

  (* Step 2: Technical note for this proof step.*)
  have q_not_p: "q \<noteq> p"
  proof
    assume "q = p"
    hence "program_counter s' p = ''D3''" using pc_q_s' by simp
    with pc_curr_p_s' show False by simp
  qed

  (* Step 3: map topre-state s.*)
  have k_len_s: "k < length (lin_seq s)" using k_len lin_eq by simp
  have pc_q_s: "program_counter s q = ''D3''" using pc_q_s' q_not_p pc_other by simp
  have op_s: "op_name (lin_seq s ! k) = deq" 
   and pid_s: "op_pid (lin_seq s ! k) = q" using op_deq pid_q lin_eq by auto

  (* Step 4: Technical note for this proof step.*)
  have ret_in_his_s: "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
  proof -
    from inv_lI8_D3_Deq_Returned pc_q_s k_len_s op_s pid_s
    show ?thesis unfolding lI8_D3_Deq_Returned_def by blast
  qed

  (* Step 5: Technical note for this proof step.*)
  have ret_in_his_s': "DeqRetInHis s' q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
    using DeqRet_mono[OF ret_in_his_s his_append] by simp

  (* Step 6: Technical note for this proof step.*)
  show ?case
    using ret_in_his_s' lin_eq by simp
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma lI9_D1_D2_Deq_Returned_E3_step:
  assumes inv_lI9_D1_D2_Deq_Returned: "lI9_D1_D2_Deq_Returned s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_curr_p_s': "program_counter s' p = ''L0''"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI9_D1_D2_Deq_Returned s'"
  unfolding lI9_D1_D2_Deq_Returned_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 q k)
  (* Step 1: Technical note for this proof step.*)
  have pc_q_s': "program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2''" using 1 by simp
  have k_len: "k < length (lin_seq s')" using 1 by simp
  have op_deq: "op_name (lin_seq s' ! k) = deq" 
   and pid_q: "op_pid (lin_seq s' ! k) = q" using 1 by simp_all

  (* Step 2: Technical note for this proof step.*)
  have q_not_p: "q \<noteq> p"
  proof
    assume "q = p"
    hence "program_counter s' p = ''D1'' \<or> program_counter s' p = ''D2''" using pc_q_s' by simp
    with pc_curr_p_s' show False by simp
  qed

  (* Step 3: map topre-state s.*)
  have k_len_s: "k < length (lin_seq s)" using k_len lin_eq by simp
  have pc_q_s: "program_counter s q = ''D1'' \<or> program_counter s q = ''D2''"
    using pc_q_s' q_not_p pc_other by auto
  have op_s: "op_name (lin_seq s ! k) = deq" 
   and pid_s: "op_pid (lin_seq s ! k) = q" using op_deq pid_q lin_eq by auto

  (* Step 4: Technical note for this proof step.*)
  have ret_in_his_s: "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
  proof -
    from inv_lI9_D1_D2_Deq_Returned pc_q_s k_len_s op_s pid_s
    show ?thesis unfolding lI9_D1_D2_Deq_Returned_def by blast
  qed

  (* Step 5: Technical note for this proof step.*)
  have ret_in_his_s': "DeqRetInHis s' q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
    using DeqRet_mono[OF ret_in_his_s his_append] by simp

  (* Step 6: Technical note for this proof step.*)
  show ?case
    using ret_in_his_s' lin_eq by simp
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this proof step.*)
(* ========================================================================= *)
lemma lI10_D4_Enq_Deq_HB_E3_step:
  assumes inv_lI10_D4_Enq_Deq_HB: "lI10_D4_Enq_Deq_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    and pc_curr_p_s': "program_counter s' p = ''L0''"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    and vars_other: "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI10_D4_Enq_Deq_HB s'"
  unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 k1 k2 q)
  (* Step 1: Technical note for this proof step.*)
  have k1_len: "k1 < length (lin_seq s')" using 1 by simp
  have k2_len: "k2 < length (lin_seq s')" using 1 by simp
  have act_k1: "op_name (lin_seq s' ! k1) = enq" using 1 by simp
  have k2_eq: "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)" using 1 by simp
  have term_cond: "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q" using 1 by simp
  have pc_q: "program_counter s' q = ''D4''" using 1 by simp
  have hb: "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)" using 1
    by blast

  (* Step 2: Technical note for this proof step.*)
  have q_not_p: "q \<noteq> p"
  proof
    assume "q = p"
    then have "program_counter s' p = ''D4''" using pc_q by simp
    with pc_curr_p_s' show False by simp
  qed

  (* Step 3: Technical note for this proof step.*)
  have k1_len_s: "k1 < length (lin_seq s)" and k2_len_s: "k2 < length (lin_seq s)"
    using k1_len k2_len lin_eq by simp_all
  have act_k1_s: "op_name (lin_seq s ! k1) = enq" using act_k1 lin_eq by simp
  have k2_eq_s: "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
    using k2_eq q_not_p vars_other lin_eq by auto
  have term_cond_s: "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
    using term_cond lin_eq by auto
  have pc_q_s: "program_counter s q = ''D4''"
    using pc_q q_not_p pc_other by simp

  (* Step 4: Technical note for this invariant-preservation argument.*)
  have hb_s: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
  proof -
    from hb[unfolded HB_def] obtain h1 h2 where
      h_order: "h1 < h2" and
      m_ret: "match_ret (his_seq s') h1 (lin_seq s ! k1)" and
      m_call: "match_call (his_seq s') h2 (lin_seq s ! k2)"
      using lin_eq by auto
    
    have h2_old: "h2 < length (his_seq s)"
    proof (rule ccontr)
      assume not_old: "\<not> h2 < length (his_seq s)"
      
      (* Step 1: Technical note for this proof step.*)
      have len_eq: "length (his_seq s') = length (his_seq s) + 1" 
        using his_append by simp
      
      (* Step 2: Technical note for this proof step.*)
      have h2_bound: "h2 < length (his_seq s')" 
        using m_call unfolding match_call_def Let_def by simp
      
      (* Step 3: Technical note for this proof step.*)
      have "h2 = length (his_seq s)" 
        using not_old len_eq h2_bound by linarith
      
      (* Step 4: Technical note for this proof step.*)
      hence "his_seq s' ! h2 = mk_act enq (v_var s p) p (s_var s p) ret"
        using his_append by (simp add: nth_append)
      hence "act_cr (his_seq s' ! h2) = ret" by (simp add: mk_act_def act_cr_def)
      thus False using m_call unfolding match_call_def Let_def by simp
    qed
    
    have h1_old: "h1 < length (his_seq s)" using h_order h2_old by linarith
    have m1: "match_ret (his_seq s) h1 (lin_seq s ! k1)"
      using h1_old his_append m_ret unfolding match_ret_def Let_def by (auto simp: nth_append)
    have m2: "match_call (his_seq s) h2 (lin_seq s ! k2)"
      using h2_old his_append m_call unfolding match_call_def Let_def by (auto simp: nth_append)
    thus ?thesis unfolding HB_def using h_order m1 m2 by blast
  qed

  (* Step 5: Technical note for this invariant-preservation argument.*)
  show "k1 < k2"
  proof -
    from inv_lI10_D4_Enq_Deq_HB k1_len_s k2_len_s act_k1_s k2_eq_s term_cond_s pc_q_s hb_s
    show "k1 < k2"
      unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
      by blast
  qed
qed

(* ========================================================================= *)
(* Technical note for this invariant-preservation argument.*)
(* Technical note for this invariant-preservation argument.*)
(* ========================================================================= *)
lemma hI3_L0_E_Phase_Bounds_E3_step:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E3 p s s'"
  assumes hI2_SSN_Bounds_s': "hI2_SSN_Bounds s'"
  shows "hI3_L0_E_Phase_Bounds s'"
proof -
  (* Step 0: Technical note for this invariant-preservation argument.*)
  have hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s" and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s" and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" 
   and hI23_Deq_Call_Ret_Balanced_s: "hI23_Deq_Call_Ret_Balanced s" and hI6_SSN_Order_s: "hI6_SSN_Order s" 
    using INV unfolding system_invariant_def by auto

  (* Step 1: Technical note for this transition-specific proof step.*)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  have his_eq: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
    using STEP unfolding Sys_E3_def U_E3_def U_E4_def bridge by auto
  have pc_p_new: "program_counter s' p = ''L0'' "
    using STEP unfolding Sys_E3_def C_E3_def bridge by auto
  have pc_p_old: "program_counter s p = ''E3'' "
    using STEP unfolding Sys_E3_def C_E3_def bridge by auto
  have V_eq: "V_var s' = V_var s"
    using STEP unfolding Sys_E3_def C_E3_def bridge by auto
  have qback_eq: "Qback_arr s' = Qback_arr s"
    using STEP unfolding Sys_E3_def C_E3_def bridge by auto

  have pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    using STEP unfolding Sys_E3_def C_E3_def bridge by auto
  have s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
    using STEP unfolding Sys_E3_def C_E3_def U_E3_def U_E4_def bridge by auto
  have v_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> v_var s' q = v_var s q"
    using STEP unfolding Sys_E3_def C_E3_def bridge by auto

  (* Step 2: Technical note for this invariant-preservation argument.*)
  show ?thesis
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    show ?case
    proof (cases "q = p")
      case True
      have q_L0: "program_counter s' p = ''L0'' " 
        using pc_p_new by simp
      have no_ssn: "\<forall>e\<in>set (his_seq s'). act_pid e = p \<longrightarrow> act_ssn e < s_var s' p"
        using hI2_SSN_Bounds_s' q_L0 unfolding hI2_SSN_Bounds_def by blast
      
      have no_pend_enq: "\<not> HasPendingEnq s' p a" for a
        unfolding HasPendingEnq_def Let_def Model.EnqCallInHis_def
        using no_ssn by force

      have no_pend_deq: "\<not> HasPendingDeq s' p"
        unfolding HasPendingDeq_def Let_def Model.DeqCallInHis_def
        using no_ssn by force
        
      show ?thesis 
        using True no_pend_enq no_pend_deq by blast
    next
      case False
      have old_L0: "program_counter s q = ''L0'' " 
        using 1 False pc_other by auto
      
      have pend_enq_eq: "HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a" for a
        using False his_eq s_var_other[OF False] 
        unfolding HasPendingEnq_def Let_def Model.EnqCallInHis_def
        by (auto simp: mk_act_def act_pid_def)
        
      have pend_deq_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
        using False his_eq s_var_other[OF False] 
        unfolding HasPendingDeq_def Let_def Model.DeqCallInHis_def
        by (auto simp: mk_act_def act_pid_def)
        
      show ?thesis
        using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s old_L0] pend_enq_eq pend_deq_eq by simp
    qed

  next
    case (2 q)
    show ?case
    proof (cases "q = p")
      case True
      have call_count: 
        "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s')) =
         length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s))"
        using his_eq by (simp add: mk_act_def act_name_def act_cr_def)
        
      have ret_count:
        "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s')) =
         length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
        using his_eq by (simp add: mk_act_def act_pid_def act_name_def act_cr_def)

      (* Technical note for this invariant-preservation argument.*)
      have "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
            length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
      proof -
        let ?H = "his_seq s"
        let ?p_his = "filter (\<lambda>e. act_pid e = p) ?H"
        
        (* Step 1: Technical note for this transition-specific proof step.*)
        have "HasPendingEnq s p (v_var s p)"
          using hI1_E_Phase_Pending_Enq_s pc_p_old unfolding hI1_E_Phase_Pending_Enq_def by auto
          
        (* Step 2: Technical note for this proof step.*)
        have last_call: "last ?p_his = mk_act enq (v_var s p) p (s_var s p) call"
          using pending_enq_is_last[OF `HasPendingEnq s p (v_var s p)` hI2_SSN_Bounds_s hI6_SSN_Order_s] by simp
          
        have p_his_nempty: "?p_his \<noteq> []"
          using `HasPendingEnq s p (v_var s p)`
          unfolding HasPendingEnq_def Let_def Model.EnqCallInHis_def
          by (metis (mono_tags, lifting) empty_filter_conv)
          
        (* Step 3: Technical note for this invariant-preservation argument.*)
        have "act_cr (last ?p_his) = call" 
          using last_call by (simp add: mk_act_def act_cr_def)
        moreover have "act_name (last ?p_his) \<noteq> deq"
          using last_call by (simp add: mk_act_def act_name_def)
          
        (* Step 4: invoke hI23_Deq_Call_Ret_Balanced discharge.*)
        ultimately have "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) ?p_his) = 
                         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) ?p_his)"
          using hI23_Deq_Call_Ret_Balanced_s[unfolded hI23_Deq_Call_Ret_Balanced_def, rule_format, where q=p and k="length ?H"] p_his_nempty
          unfolding Let_def by simp
          
        (* Step 5: Technical note for this proof step.*)
        thus ?thesis
          by simp
      qed
        
      then show ?thesis
        using True call_count ret_count by simp
    next
      case False
      have old_L0: "program_counter s q = ''L0'' " 
        using 2 False pc_other by auto
      have "length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
            length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
        using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s old_L0] by simp
      then show ?thesis
        using False his_eq by (simp add: mk_act_def act_pid_def act_name_def act_cr_def)
    qed

  next
    case (3 q)
    have q_ne_p: "q \<noteq> p" 
      using 3 pc_p_new by auto
    have old_E: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" 
      using 3 q_ne_p pc_other by auto
    have v_eq_q: "v_var s' q = v_var s q"
      using v_var_other[OF q_ne_p] by simp
    show ?case
      using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s old_E] v_eq_q V_eq by simp

  next
    case (4 k)
    let ?n = "length (his_seq s)"
    have len': "length (his_seq s') = Suc ?n"
      using his_eq by simp
    show ?case
    proof (cases "k < ?n")
      case True
      have "his_seq s' ! k = his_seq s ! k"
        using his_eq True by (simp add: nth_append)
      thus ?thesis
        using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s True] 4 V_eq by auto
    next
      case False
      with 4 len' have "k = ?n" by linarith
      have "his_seq s' ! k = mk_act enq (v_var s p) p (s_var s p) ret"
        using his_eq `k = ?n` by simp
      then show ?thesis
        using 4 by (simp add: mk_act_def act_name_def act_cr_def)
    qed

  next
    case (5 k)
    show ?case
      using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s, of k] qback_eq V_eq by auto
  qed
qed

(* ========================================================================= *)
(* Technical note for this transition-specific proof step.*)
(* ========================================================================= *)
lemma E3_preserves_invariant_core:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E3 p s s'"  
  shows "system_invariant s'"
proof -   
  (* Step 0: Technical note for this proof step.*)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

(* Step 1: Technical note for this proof step.*)
  have TypeOK_s: "TypeOK s" and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s" and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" 
   and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s" and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s" 
   and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" 
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
   and hI21_s: "hI29_E2_Scanner_Immunity s" and hI22_s: "hI30_Ticket_HB_Immunity s" 
   and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" 
   and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" and lI5_SA_Prefix_s: "lI5_SA_Prefix s" and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" 
   and lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" and lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s" and lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s" 
   and lI10_D4_Enq_Deq_HB_s: "lI10_D4_Enq_Deq_HB s" and lI11_D4_Deq_Unique_s: "lI11_D4_Deq_Unique s" 
   and di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  (* Step 2: Technical note for this transition-specific proof step.*)
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

    show "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s" "x_var s' = x_var s"
         "j_var s' = j_var s" "l_var s' = l_var s" "X_var s' = X_var s" "V_var s' = V_var s"
         "program_counter s p = ''E3'' " "program_counter s' p = ''L0'' "
         "i_var s' p = BOT" "v_var s' p = BOT"
    proof -
      from c_step show "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s" "x_var s' = x_var s"
           "j_var s' = j_var s" "l_var s' = l_var s" "X_var s' = X_var s" "V_var s' = V_var s"
           "program_counter s p = ''E3'' " "program_counter s' p = ''L0'' "
           "i_var s' p = BOT" "v_var s' p = BOT"
        unfolding C_E3_def bridge
        by (auto simp: prod_eq_iff)
    qed

    show "s_var s' p = s_var s p + 1"
      using u_step1 u_step2
      unfolding U_E3_def U_E4_def bridge
      by (auto simp: prod_eq_iff)

    show "lin_seq s' = lin_seq s"
      using u_step1 u_step2
      unfolding U_E3_def U_E4_def bridge
      by (auto simp: prod_eq_iff)

    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
      using u_step1 u_step2
      unfolding U_E3_def U_E4_def bridge
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
      c_step: "C_E3 p (fst s) (fst s')"
      and u_step1: "U_E3 p (CState.v_var (fst s) p) (s_var s p) (snd s) us_mid"
      and u_step2: "U_E4 p us_mid (snd s')"
      unfolding Sys_E3_def
      by blast

    show "program_counter s' q = program_counter s q"
         "i_var s' q = i_var s q"
         "v_var s' q = v_var s q"
    proof -
      from c_step \<open>q \<noteq> p\<close>
      show "program_counter s' q = program_counter s q"
           "i_var s' q = i_var s q"
           "v_var s' q = v_var s q"
        unfolding C_E3_def bridge
        by (auto simp: prod_eq_iff)
    qed

    show "s_var s' q = s_var s q"
      using u_step1 u_step2 \<open>q \<noteq> p\<close>
      unfolding U_E3_def U_E4_def bridge
      by (auto simp: prod_eq_iff)
  qed

  (* Technical note for this proof step.*)
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

  have deqret_eq [simp]: "\<And>q a sn. DeqRetInHis s' q a sn = DeqRetInHis s q a sn"
    unfolding DeqRetInHis_def Let_def
    using step_facts(9)
    by (auto simp: mk_act_def act_name_def act_cr_def)

  have pending_deq_other_eq [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> HasPendingDeq s' q = HasPendingDeq s q"
    unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
    using step_facts(9) other_facts(4)
    by (auto simp: mk_act_def act_pid_def act_name_def act_cr_def)

  have pending_enq_other_eq [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> HasPendingEnq s' q (v_var s' q) = HasPendingEnq s q (v_var s q)"
    unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def Let_def
    using step_facts(9) other_facts(3,4)
    by (auto simp: mk_act_def act_pid_def act_name_def act_cr_def)

(* Step 3: Technical note for this transition-specific proof step.*)
  have typeb_eq: "\<And>x. TypeB s' x = TypeB s x"
  proof -
    fix x
    (* Technical note for this transition-specific proof step.*)
    have "\<And>q. program_counter s q = ''E2'' \<Longrightarrow> q \<noteq> p"
      using step_facts by auto

    hence "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow> 
           (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
      using pc_eqs step_facts other_facts
      by force 
      
    thus "TypeB s' x = TypeB s x"
      unfolding TypeB_def
      using QHas_def by auto 
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


  (* ------------------------------------------------------------------------- *)
  (* Step 4: Technical note for this proof step.*)
  (* ------------------------------------------------------------------------- *)
  have "TypeOK s'"
  proof -
    have pc_ok: "\<forall>q. program_counter s' q \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
      using TypeOK_s pc_eqs unfolding TypeOK_def by auto
    have vars_ok: "\<forall>q. (j_var s' q = BOT \<or> j_var s' q \<in> Val) \<and> (l_var s' q = BOT \<or> l_var s' q \<in> Val) \<and> 
                       (x_var s' q = BOT \<or> x_var s' q \<in> Val) \<and> (v_var s' q = BOT \<or> v_var s' q \<in> Val)"
      using TypeOK_s step_facts other_facts unfolding TypeOK_def by (metis Un_iff empty_iff insert_iff) 
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
    show ?thesis using TypeOK_s pc_ok vars_ok s_ok step_facts unfolding TypeOK_def
      by (metis Un_iff insertI1 other_facts(2)) 
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

  (* Technical note for this invariant-preservation argument.*)
  have "hI2_SSN_Bounds s'"
    unfolding hI2_SSN_Bounds_def
  proof (intro allI ballI impI)
    fix q e
    assume e_in: "e \<in> set (his_seq s')"
    assume e_pid: "act_pid e = q"

    have e_cases: "e \<in> set (his_seq s) \<or> e = mk_act enq (v_var s p) p (s_var s p) ret"
      using e_in step_facts(9) by auto

    show "act_ssn e \<le> s_var s' q \<and> (program_counter s' q = ''L0'' \<longrightarrow> act_ssn e < s_var s' q)"
    proof
      show "act_ssn e \<le> s_var s' q"
      proof (cases "q = p")
        case True
        from e_cases show ?thesis 
        proof
          assume old_e: "e \<in> set (his_seq s)"
          have "act_ssn e \<le> s_var s p" using hI2_SSN_Bounds_s old_e True e_pid unfolding hI2_SSN_Bounds_def by blast
          thus ?thesis using True step_facts(14) by simp
        next
          assume new_e: "e = mk_act enq (v_var s p) p (s_var s p) ret"
          have "act_ssn e = s_var s p" using new_e by (simp add: mk_act_def act_ssn_def)
          thus ?thesis using True step_facts(14) by simp
        qed
      next
        case False
        have "e \<noteq> mk_act enq (v_var s p) p (s_var s p) ret"
          using False e_pid by (auto simp: mk_act_def act_pid_def)
        hence e_old: "e \<in> set (his_seq s)" using e_cases by blast
        have "act_ssn e \<le> s_var s q" using hI2_SSN_Bounds_s e_old e_pid unfolding hI2_SSN_Bounds_def by blast
        thus ?thesis using False other_facts by simp
      qed

      show "program_counter s' q = ''L0'' \<longrightarrow> act_ssn e < s_var s' q"
      proof (intro impI)
        assume q_L0: "program_counter s' q = ''L0''"
        show "act_ssn e < s_var s' q"
        proof (cases "q = p")
          case True
          from e_cases show ?thesis 
          proof
            assume old_e: "e \<in> set (his_seq s)"
            have "act_ssn e \<le> s_var s p" using hI2_SSN_Bounds_s old_e True e_pid unfolding hI2_SSN_Bounds_def by blast
            thus ?thesis using True step_facts(14) by simp
          next
            assume new_e: "e = mk_act enq (v_var s p) p (s_var s p) ret"
            have "act_ssn e = s_var s p" using new_e by (simp add: mk_act_def act_ssn_def)
            thus ?thesis using True step_facts(14) by simp
          qed
        next
          case False
          have pc_s_q: "program_counter s q = ''L0''" using q_L0 False pc_eqs by simp
          have "e \<noteq> mk_act enq (v_var s p) p (s_var s p) ret"
            using False e_pid by (auto simp: mk_act_def act_pid_def)
          hence e_old: "e \<in> set (his_seq s)" using e_cases by blast
          have "act_ssn e < s_var s q" using hI2_SSN_Bounds_s pc_s_q e_old e_pid unfolding hI2_SSN_Bounds_def by blast
          thus ?thesis using False other_facts by simp
        qed
      qed
    qed
  qed

  have "hI3_L0_E_Phase_Bounds s'"
    using hI3_L0_E_Phase_Bounds_E3_step[OF INV STEP `hI2_SSN_Bounds s'`] .

  have "sI11_x_var_Scope s'" using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def using pc_eqs step_facts other_facts by auto

  (* Technical note for this invariant-preservation argument.*)
  have "hI1_E_Phase_Pending_Enq s'"
    unfolding hI1_E_Phase_Pending_Enq_def
  proof (intro allI impI)
    fix q assume q_E: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
    have q_neq_p: "q \<noteq> p" using q_E step_facts pc_eqs by auto
    
    have pend_old: "HasPendingEnq s q (v_var s q)" 
      using q_E pc_eqs hI1_E_Phase_Pending_Enq_s unfolding hI1_E_Phase_Pending_Enq_def by auto
      
    have call_old: "EnqCallInHis s q (v_var s q) (s_var s q)"
      and no_ret_old: "\<forall>e\<in>set (his_seq s). \<not> (act_pid e = q \<and> act_ssn e = s_var s q \<and> act_cr e = ret)"
      using pend_old unfolding HasPendingEnq_def Let_def by auto

    have part1: "EnqCallInHis s' q (v_var s' q) (s_var s' q)"
    proof -
      have "EnqCallInHis s' q (v_var s q) (s_var s q)"
        using EnqCall_mono[OF call_old step_facts(9)] by simp
      thus ?thesis using q_neq_p other_facts by simp
    qed

    have part2: "\<forall>e\<in>set (his_seq s'). \<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)"
    proof
      fix e assume "e \<in> set (his_seq s')"
      hence "e \<in> set (his_seq s) \<or> e = mk_act enq (v_var s p) p (s_var s p) ret"
        using step_facts(9) by auto
      thus "\<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)"
      proof
        assume old_e: "e \<in> set (his_seq s)"
        show ?thesis using no_ret_old old_e q_neq_p other_facts by auto
      next
        assume new_e: "e = mk_act enq (v_var s p) p (s_var s p) ret"
        have "act_pid e = p" using new_e by (simp add: mk_act_def act_pid_def)
        thus ?thesis using q_neq_p by simp
      qed
    qed

    show "HasPendingEnq s' q (v_var s' q)"
      unfolding HasPendingEnq_def using part1 part2 by simp
  qed

  have "sI12_D3_Scanned_Prefix s'" using sI12_D3_Scanned_Prefix_s unfolding sI12_D3_Scanned_Prefix_def using pc_eqs step_facts other_facts by auto

  (* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI4_X_var_Lin_Sync s'"
  proof -
    have X_var_eq: "X_var s' = X_var s" using step_facts by simp
    have lin_seq_eq: "lin_seq s' = lin_seq s" using step_facts by simp
    show ?thesis
      using hI4_X_var_Lin_Sync_s X_var_eq lin_seq_eq
      unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def
      by auto
  qed

  (* ------------------------------------------------------------------------- *)
  (* Step 5: Technical note for this invariant-preservation argument.*)
  (* ------------------------------------------------------------------------- *)

  (* Technical note for this invariant-preservation argument.*)
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
        "j < k" "act_pid (his_seq s ! j) = act_pid (his_seq s ! k)"
        "act_ssn (his_seq s ! j) = act_ssn (his_seq s ! k)" "act_name (his_seq s ! j) = act_name (his_seq s ! k)"
        "act_cr (his_seq s ! j) = call"
        "(if act_name (his_seq s ! k) = enq then act_val (his_seq s ! j) = act_val (his_seq s ! k) else act_val (his_seq s ! j) = BOT)"
        by auto
        
      show ?thesis
        apply (intro exI[where x=j])
        using j_props old step_facts by (auto simp: nth_append)
        
    next
      case new
      have e_k: "his_seq s' ! k = mk_act enq (v_var s p) p (s_var s p) ret"
        using new step_facts by (simp add: nth_append)
        
      (* Technical note for this invariant-preservation argument.*)
      have "HasPendingEnq s p (v_var s p)"
        using hI1_E_Phase_Pending_Enq_s step_facts pc_eqs unfolding hI1_E_Phase_Pending_Enq_def by auto
      then obtain call_e where call_in: "call_e \<in> set (his_seq s)"
        and call_def: "call_e = mk_act enq (v_var s p) p (s_var s p) call"
        unfolding HasPendingEnq_def EnqCallInHis_def Let_def 
        by (force simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

      from call_in obtain j where j_props:
        "j < length (his_seq s)" "his_seq s ! j = call_e"
        by (meson in_set_conv_nth)

      have p1: "j < k" using j_props(1) new by simp
      have e_j: "his_seq s' ! j = mk_act enq (v_var s p) p (s_var s p) call"
        using j_props step_facts call_def by (simp add: nth_append)
      
      show ?thesis
        apply (intro exI[where x=j])
        using p1 e_k e_j
        by (simp add: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    qed
  qed

  have "hI8_Val_Unique s'" 
    using hI8_Val_Unique_s unfolding hI8_Val_Unique_def 
    using step_facts(9) by (auto simp: nth_append mk_act_def act_name_def act_cr_def)

  (* Technical note for this invariant-preservation argument.*)
  have "hI6_SSN_Order s'"
    unfolding hI6_SSN_Order_def
  proof (intro allI impI)
    fix i j
    assume bounds: "i < length (his_seq s')" "j < length (his_seq s')"
    assume props_raw: "i < j \<and> act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
    
    have props: "i < j" "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
      using props_raw by auto

    have len_eq: "length (his_seq s') = length (his_seq s) + 1" 
      using step_facts(9) by simp

    consider (both_old) "j < length (his_seq s)" 
           | (i_old_j_new) "i < length (his_seq s)" "j = length (his_seq s)"
      using bounds props(1) len_eq by linarith

    thus "act_ssn (his_seq s' ! i) < act_ssn (his_seq s' ! j) \<or>
          (act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j) \<and> 
           act_cr (his_seq s' ! i) = call \<and> act_cr (his_seq s' ! j) = ret)"
    proof cases
      case both_old
      thus ?thesis using hI6_SSN_Order_s unfolding hI6_SSN_Order_def 
        using bounds props step_facts(9) by (auto simp: nth_append)
    next
      case i_old_j_new
      have j_is_new: "his_seq s' ! j = mk_act enq (v_var s p) p (s_var s p) ret"
        using i_old_j_new step_facts(9) by (simp add: nth_append)
      hence pid_j: "act_pid (his_seq s' ! j) = p"
        and ssn_j: "act_ssn (his_seq s' ! j) = s_var s p"
        and cr_j:  "act_cr (his_seq s' ! j) = ret"
        by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)

      from props(2) pid_j have pid_i: "act_pid (his_seq s' ! i) = p" by simp
      have i_is_old: "his_seq s' ! i = his_seq s ! i"
        using i_old_j_new step_facts(9) by (simp add: nth_append)

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
          hence "act_cr (his_seq s ! i) = ret" using i_is_old by (cases "act_cr (his_seq s ! i)") auto

          from hI1_E_Phase_Pending_Enq_s step_facts(10) have pending: "HasPendingEnq s p (v_var s p)"
            unfolding hI1_E_Phase_Pending_Enq_def by blast
          from pending have no_ret: "\<forall>e \<in> set (his_seq s). act_pid e = p \<and> act_ssn e = s_var s p \<longrightarrow> act_cr e \<noteq> ret"
            unfolding HasPendingEnq_def Let_def by auto

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

  (* Technical note for this invariant-preservation argument.*)
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
      using step_facts(9) by simp

    let ?L = "length (his_seq s)"
    consider (both_old) "i < ?L" "j < ?L"
           | (i_old_j_new) "i < ?L" "j = ?L"
           | (i_new_j_old) "i = ?L" "j < ?L"
           | (both_new) "i = ?L" "j = ?L"
      using bounds len_eq by linarith

    thus "i = j"
    proof cases
      case both_old
      thus ?thesis using hI5_SSN_Unique_s props bounds step_facts(9) 
        unfolding hI5_SSN_Unique_def by (auto simp: nth_append)
    next
      case i_old_j_new
      have j_is_new: "his_seq s' ! j = mk_act enq (v_var s p) p (s_var s p) ret"
        using i_old_j_new step_facts(9) by (simp add: nth_append)
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
        using i_old_j_new step_facts(9) by (simp add: nth_append)
      have i_in_set: "his_seq s ! i \<in> set (his_seq s)" using i_old_j_new by simp

      from hI1_E_Phase_Pending_Enq_s step_facts(10) have pending: "HasPendingEnq s p (v_var s p)"
        unfolding hI1_E_Phase_Pending_Enq_def by blast
      from pending have no_ret: "\<forall>e \<in> set (his_seq s). act_pid e = p \<and> act_ssn e = s_var s p \<longrightarrow> act_cr e \<noteq> ret"
        unfolding HasPendingEnq_def Let_def by auto

      have "act_cr (his_seq s ! i) \<noteq> ret"
        using no_ret i_in_set i_props(1) i_props(2) i_is_old by simp
      thus ?thesis using i_props(3) i_is_old by simp 
    next
      case i_new_j_old
      have i_is_new: "his_seq s' ! i = mk_act enq (v_var s p) p (s_var s p) ret"
        using i_new_j_old step_facts(9) by (simp add: nth_append)
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
        using i_new_j_old step_facts(9) by (simp add: nth_append)
      have j_in_set: "his_seq s ! j \<in> set (his_seq s)" using i_new_j_old by simp

      from hI1_E_Phase_Pending_Enq_s step_facts(10) have pending: "HasPendingEnq s p (v_var s p)"
        unfolding hI1_E_Phase_Pending_Enq_def by blast
      from pending have no_ret: "\<forall>e \<in> set (his_seq s). act_pid e = p \<and> act_ssn e = s_var s p \<longrightarrow> act_cr e \<noteq> ret"
        unfolding HasPendingEnq_def Let_def by auto

      have "act_cr (his_seq s ! j) \<noteq> ret"
        using no_ret j_in_set j_props(1) j_props(2) j_is_old by simp
      thus ?thesis using j_props(3) j_is_old by simp
    next
      case both_new
      thus ?thesis by simp
    qed
  qed

  (* Technical note for this invariant-preservation argument.*)
  have "hI9_Deq_Ret_Unique s'" using hI9_Deq_Ret_Unique_s step_facts(9) unfolding hI9_Deq_Ret_Unique_def 
    by (auto simp: nth_append mk_act_def act_name_def)

  (* Technical note for this invariant-preservation argument.*)
  have "hI10_Enq_Call_Existence s'"
    unfolding hI10_Enq_Call_Existence_def
  proof (intro conjI)
    show "\<forall>q a. (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' q = a) \<longrightarrow> EnqCallInHis s' q a (s_var s' q)"
    proof (intro allI impI)
      fix q a assume prems: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' q = a"
      have "q \<noteq> p" using prems step_facts pc_eqs by auto
      have "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" using prems \<open>q \<noteq> p\<close> step_facts pc_eqs by auto
      moreover have "v_var s q = a" using prems \<open>q \<noteq> p\<close> step_facts other_facts by auto
      ultimately have "EnqCallInHis s q a (s_var s q)" using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def by blast
      moreover have "s_var s q = s_var s' q" using \<open>q \<noteq> p\<close> step_facts other_facts by auto
      ultimately show "EnqCallInHis s' q a (s_var s' q)" using EnqCall_mono[OF _ step_facts(9)] by auto
    qed

    show "\<forall>a. (\<exists>k. Qback_arr s' k = a) \<longrightarrow> (\<exists>q sn. EnqCallInHis s' q a sn)"
    proof (intro allI impI)
      fix a assume "\<exists>k. Qback_arr s' k = a"
      hence "\<exists>k. Qback_arr s k = a" using step_facts other_facts by auto
      then obtain q sn where old_call: "EnqCallInHis s q a sn" using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def by blast 
      have "EnqCallInHis s' q a sn" using EnqCall_mono[OF old_call step_facts(9)] by simp
      thus "\<exists>q sn. EnqCallInHis s' q a sn" by blast
    qed
  qed
    
  (* Technical note for this invariant-preservation argument.*)
  have "hI11_Enq_Ret_Existence s'"
    unfolding hI11_Enq_Ret_Existence_def
    apply (intro allI impI)
  proof (goal_cases)
    case (1 q a sn)
    have pc_cond_s': "program_counter s' q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn"
      and qback_s': "\<exists>k. Qback_arr s' k = a"
      and call_s': "EnqCallInHis s' q a sn"
      using 1 by auto

    have call_in_s: "EnqCallInHis s q a sn"
    proof -
      have "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
        using step_facts by simp
      thus ?thesis using call_s' unfolding EnqCallInHis_def Let_def by (auto simp: mk_act_def act_cr_def)
    qed

    have qback_s: "\<exists>k. Qback_arr s k = a" using qback_s' step_facts other_facts by simp

    (* Technical note for this proof step.*)
    have split_outer: "(q = p \<and> a = v_var s p \<and> sn = s_var s p) \<or> \<not> (q = p \<and> a = v_var s p \<and> sn = s_var s p)" 
      by blast
    from split_outer show "EnqRetInHis s' q a sn"
    proof (elim disjE, goal_cases)
      case 1
      (* Branch 1: Technical note for this proof step.*)
      have "mk_act enq (v_var s p) p (s_var s p) ret \<in> set (his_seq s')" 
        using step_facts by simp
      thus ?case using 1 unfolding EnqRetInHis_def Let_def 
        by (force simp: mk_act_def act_pid_def act_val_def act_ssn_def act_name_def act_cr_def)
    next
      case 2
      (* Branch 2: Technical note for this proof step.*)
      have pc_cond_s: "program_counter s q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s q \<noteq> a \<or> s_var s q \<noteq> sn"
      proof -
        (* Technical note for this proof step.*)
        have split_inner: "q = p \<or> q \<noteq> p" by blast
        from split_inner show ?thesis
        proof (elim disjE, goal_cases)
          case 1
          with 2 have "a \<noteq> v_var s p \<or> sn \<noteq> s_var s p" by simp
          thus ?thesis using 1 step_facts other_facts by auto
        next
          case 2
          have "program_counter s q = program_counter s' q" using 2 other_facts by auto
          moreover have "v_var s q = v_var s' q" using 2 other_facts by auto
          moreover have "s_var s q = s_var s' q" using 2 other_facts by auto
          ultimately show ?thesis using pc_cond_s' by metis
        qed
      qed
      have "EnqRetInHis s q a sn" using hI11_Enq_Ret_Existence_s pc_cond_s qback_s call_in_s unfolding hI11_Enq_Ret_Existence_def by blast
      thus ?case using step_facts unfolding EnqRetInHis_def Let_def by auto
    qed
  qed

  (* Technical note for this invariant-preservation argument.*)
  have "hI12_D_Phase_Pending_Deq s'" 
    unfolding hI12_D_Phase_Pending_Deq_def
  proof (intro allI impI)
    fix q
    assume pc_q: "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    
    (* Step 1: Technical note for this transition-specific proof step.*)
    have "q \<noteq> p"
    proof
      assume "q = p"
      hence "program_counter s' p \<in> {''D1'', ''D2'', ''D3'', ''D4''}" using pc_q by simp
      thus False using step_facts by simp
    qed
    
    (* Step 2: Technical note for this proof step.*)
    have pc_s: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using pc_q \<open>q \<noteq> p\<close> other_facts by auto
    have pending_s: "HasPendingDeq s q"
      using hI12_D_Phase_Pending_Deq_s pc_s unfolding hI12_D_Phase_Pending_Deq_def by blast
      
    (* Step 3: Technical note for this proof step.*)
    show "HasPendingDeq s' q"
      using pending_s \<open>q \<noteq> p\<close> step_facts other_facts
      (* Technical note for this invariant-preservation argument.*)
      unfolding HasPendingDeq_def Let_def DeqCallInHis_def
      by (auto simp: mk_act_def act_pid_def act_name_def act_cr_def act_ssn_def)
  qed


  have "hI13_Qback_Deq_Sync s'"
  proof (rule hI13_Qback_Deq_Sync_E3_step)
    show "hI13_Qback_Deq_Sync s" using hI13_Qback_Deq_Sync_s by simp      
    show "Q_arr s' = Q_arr s" using step_facts by simp      
    show "Qback_arr s' = Qback_arr s" using step_facts by simp      
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
      using step_facts by simp        
    show "program_counter s' = (program_counter s)(p := ''L0'')" 
      using pc_eqs by (auto simp: fun_upd_def)        
    show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q" 
      using other_facts by simp        
    show "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q" 
      using other_facts by simp
    show "program_counter s p = ''E3''"  (* Technical note for this proof step.*)
      using step_facts by simp
  qed

  have "hI14_Pending_Enq_Qback_Exclusivity s'"
  proof (rule hI14_Pending_Enq_Qback_Exclusivity_E3_step)
    show "hI14_Pending_Enq_Qback_Exclusivity s" using hI14_Pending_Enq_Qback_Exclusivity_s by simp      
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
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

  (* Technical note for this invariant-preservation argument.*)
  have "hI15_Deq_Result_Exclusivity s'"
  proof (rule hI15_Deq_Result_Exclusivity_E3_step)
    show "hI15_Deq_Result_Exclusivity s" using hI15_Deq_Result_Exclusivity_s by simp
    show "system_invariant s" using INV by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s' = (program_counter s)(p := ''L0'')" using step_facts other_facts by (auto simp: fun_upd_def fun_eq_iff)
    show "program_counter s p = ''E3''" using step_facts by simp
    show "s_var s' p = s_var s p + 1" using step_facts by simp
    show "Q_arr s' = Q_arr s" using step_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q" using step_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q" using other_facts by simp
  qed

  have "hI16_BO_BT_No_HB s'"
  proof (rule hI16_BO_BT_No_HB_E3_step)
    show "hI16_BO_BT_No_HB s" using hI16_BO_BT_No_HB_s by simp      
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
      using step_facts by simp        
    show "SetBO s' = SetBO s" using set_facts by simp
    show "SetBT s' = SetBT s" using set_facts by simp
  qed

  have "hI17_BT_BT_No_HB s'"
  proof (rule hI17_BT_BT_No_HB_E3_step)
    show "hI17_BT_BT_No_HB s" using hI17_BT_BT_No_HB_s by simp      
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
      using step_facts by simp        
    show "SetBT s' = SetBT s" using set_facts by simp
  qed

  have "hI18_Idx_Order_No_Rev_HB s'"
  proof (rule hI18_Idx_Order_No_Rev_HB_E3_step)
    show "hI18_Idx_Order_No_Rev_HB s" using hI18_Idx_Order_No_Rev_HB_s by simp      
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
      using step_facts by simp        
    show "\<And>x. Idx s' x = Idx s x" 
      using step_facts unfolding Idx_def AtIdx_def by presburger         
    show "\<And>x. InQBack s' x = InQBack s x" 
      using step_facts unfolding InQBack_def by auto        
    show "\<And>i. AtIdx s' i = AtIdx s i" 
      using step_facts unfolding AtIdx_def by auto
  qed
  
  (* Technical note for this invariant-preservation argument.*)
  have "hI19_Scanner_Catches_Later_Enq s'"
  proof (rule hI19_Scanner_Catches_Later_Enq_E3_step)
    show "hI19_Scanner_Catches_Later_Enq s" using hI19_Scanner_Catches_Later_Enq_s by simp
    show "system_invariant s" using INV by simp
    
    have seq_eq: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
      using step_facts by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" 
      using seq_eq by simp
      
    show "program_counter s' = (program_counter s)(p := ''L0'')" 
      using pc_eqs by (auto simp: fun_upd_def fun_eq_iff)
      
    show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q \<and> j_var s' q = j_var s q \<and> l_var s' q = l_var s q \<and> s_var s' q = s_var s q" 
      using step_facts pc_eqs by auto
      
    show "\<And>x. Idx s' x = Idx s x" 
      using step_facts unfolding Idx_def AtIdx_def by simp
      
    show "\<And>x. TypeB s' x = TypeB s x" 
      using set_facts unfolding TypeB_def QHas_def by (auto simp: InQBack_def)

    (* Technical note for this proof step.*)
    show "\<And>x. InQBack s' x = InQBack s x"
      using step_facts unfolding InQBack_def by auto

    (* Technical note for this invariant-preservation argument.*)
    show "\<And>a b. HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
    proof -
      fix a b
      show "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def
        using HB_enq_stable_ret_append[OF seq_eq]
        by (meson HB_def) 
    qed
  qed
  
  (* Technical note for this invariant-preservation argument.*)
  have "hI20_Enq_Val_Valid s'"
  proof -
    (* Step 1: Technical note for this invariant-preservation argument.*)
    have "EnqCallInHis s p (v_var s p) (s_var s p)"
      using hI1_E_Phase_Pending_Enq_s step_facts unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def
      using hI10_Enq_Call_Existence_def hI10_Enq_Call_Existence_s by blast 
    then obtain e where "e \<in> set (his_seq s)" "act_name e = enq" "act_val e = v_var s p"
      unfolding EnqCallInHis_def Let_def by auto
      
    (* Step 2: Technical note for this invariant-preservation argument.*)
    hence v_in_val: "v_var s p \<in> Val"
      using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def 
      by (auto simp: in_set_conv_nth act_name_def act_val_def)

    (* Step 3: Technical note for this invariant-preservation argument.*)
    show ?thesis
      using hI20_Enq_Val_Valid_s v_in_val step_facts
      unfolding hI20_Enq_Val_Valid_def
      by (auto simp: nth_append mk_act_def act_name_def act_val_def)
  qed

  (* Technical note for this invariant-preservation argument.*)
  have "hI21_Ret_Implies_Call s'"
  proof (rule hI21_Ret_Implies_Call_E3_step)
    show "hI21_Ret_Implies_Call s" using hI21_Ret_Implies_Call_s by simp
    show "hI12_D_Phase_Pending_Deq s" using hI12_D_Phase_Pending_Deq_s by simp
    show "system_invariant s" using INV by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s p = ''E3''" using step_facts by simp
  qed

  (* Technical note for this invariant-preservation argument.*)
  have "hI22_Deq_Local_Pattern s'"
  proof (rule hI22_Deq_Local_Pattern_E3_step)
    show "hI22_Deq_Local_Pattern s" using hI22_Deq_Local_Pattern_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "\<And>q. x_var s' q = x_var s q" using step_facts by simp
    show "\<And>k. Q_arr s' k = Q_arr s k" using step_facts by simp
    show "\<And>k. Qback_arr s' k = Qback_arr s k" using step_facts by simp
  qed

(* Technical note for this invariant-preservation argument.*)
  have "hI23_Deq_Call_Ret_Balanced s'"
  proof (rule hI23_Deq_Call_Ret_Balanced_E3_step)
    show "hI23_Deq_Call_Ret_Balanced s" using hI23_Deq_Call_Ret_Balanced_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
  qed
  
(* Technical note for this invariant-preservation argument.*)
  have "hI24_HB_Implies_Idx_Order s'"
  proof (rule hI24_HB_Implies_Idx_Order_E3_step)
    show "hI24_HB_Implies_Idx_Order s" using hI24_HB_Implies_Idx_Order_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "CState.Q_arr (fst s') = CState.Q_arr (fst s)" using step_facts unfolding Q_arr_def by simp
  qed
  
(* Technical note for this invariant-preservation argument.*)
  have "hI25_Enq_Call_Ret_Balanced s'"
  proof (rule hI25_Enq_Call_Ret_Balanced_E3_step)
    show "hI25_Enq_Call_Ret_Balanced s" using hI25_Enq_Call_Ret_Balanced_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s' = (program_counter s)(p := ''L0'')" using step_facts other_facts by (auto simp: fun_upd_def fun_eq_iff)
    show "program_counter s p = ''E3''" using step_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q" using other_facts by simp
  qed

(* Technical note for this invariant-preservation argument.*)
  have "hI26_DeqRet_D4_Mutex s'"
  proof (rule hI26_DeqRet_D4_Mutex_E3_step)
    show "hI26_DeqRet_D4_Mutex s" using hI26_DeqRet_D4_Mutex_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s' = (program_counter s)(p := ''L0'')" using step_facts other_facts by (auto simp: fun_upd_def fun_eq_iff)
    show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q" using other_facts by simp
    show "\<And>q. x_var s' q = x_var s q" using step_facts by simp
  qed

  (* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI27_Pending_PC_Sync s'"
  proof -
    show ?thesis
      unfolding hI27_Pending_PC_Sync_def
    proof (intro conjI allI impI)
      fix q
      assume pend': "HasPendingDeq s' q"

      show "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof (cases "q = p")
        case True
        have "\<not> DeqCallInHis s' p (s_var s' p)"
        proof
          assume "DeqCallInHis s' p (s_var s' p)"
          then obtain e where
            "e \<in> set (his_seq s')" "act_pid e = p" "act_ssn e = s_var s' p" "act_name e = deq" "act_cr e = call"
            unfolding DeqCallInHis_def Let_def
            by blast 
          moreover from `hI2_SSN_Bounds s'` step_facts(11)
          have "\<forall>e\<in>set (his_seq s'). act_pid e = p \<longrightarrow> act_ssn e < s_var s' p"
            unfolding hI2_SSN_Bounds_def by auto
          ultimately show False by auto
        qed
        hence "\<not> HasPendingDeq s' p"
          unfolding HasPendingDeq_def Let_def by simp
        with pend' True show ?thesis by simp
      next
        case False
        hence pend: "HasPendingDeq s q" using pend' by simp
        have "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
          using hI19_s pend
          unfolding hI27_Pending_PC_Sync_def
          by blast
        moreover have "program_counter s' q = program_counter s q"
          using False other_facts(1) by simp
        ultimately show ?thesis by simp
      qed
    next
      fix q
      assume pend': "HasPendingEnq s' q (v_var s' q)"

      show "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
      proof (cases "q = p")
        case True
        have "\<not> EnqCallInHis s' p (v_var s' p) (s_var s' p)"
        proof
          assume "EnqCallInHis s' p (v_var s' p) (s_var s' p)"
          then obtain e where
            "e \<in> set (his_seq s')" "act_pid e = p" "act_ssn e = s_var s' p" "act_name e = enq" "act_cr e = call" "act_val e = v_var s' p"
            unfolding EnqCallInHis_def Let_def
            by blast
          moreover from `hI2_SSN_Bounds s'` step_facts(11)
          have "\<forall>e\<in>set (his_seq s'). act_pid e = p \<longrightarrow> act_ssn e < s_var s' p"
            unfolding hI2_SSN_Bounds_def by auto
          ultimately show False by auto
        qed
        hence "\<not> HasPendingEnq s' p (v_var s' p)"
          unfolding HasPendingEnq_def Let_def by simp
        with pend' True show ?thesis by simp
      next
        case False
        hence pend: "HasPendingEnq s q (v_var s q)" using pend'
          using pending_enq_other_eq by auto 
        have "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
          using hI19_s pend
          unfolding hI27_Pending_PC_Sync_def
          by blast
        moreover have "program_counter s' q = program_counter s q"
          using False other_facts(1) by simp
        ultimately show ?thesis by simp
      qed
    qed
  qed

  (* ========================================================================= *)
  (* Technical note for this invariant-preservation argument.*)
  (* ========================================================================= *)
  have "hI28_Fresh_Enq_Immunity s'"
  proof -
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
          have "program_counter s' p = ''L0''"
            using step_facts(11) by simp
          with pc_e_prime True show False by simp
        next
          case False
          have old_pc: "program_counter s p_enq \<in> {''E1'', ''E2''}"
            using pc_e_prime False other_facts(1) by simp
          have old_v: "v_var s p_enq = a"
            using v_eq_prime False other_facts(3) by simp
          have his_s: "DeqRetInHis s q_deq a sn"
            using his_prime by simp

          from hI20_s[unfolded hI28_Fresh_Enq_Immunity_def] old_pc old_v a_not_bot his_s
          show False by blast
        qed
      qed
    qed
  qed

    (* ========================================================================= *)
    (* Technical note for this invariant-preservation argument.*)
    (* ========================================================================= *)
    have "hI29_E2_Scanner_Immunity s'"
    proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI, goal_cases)
      case (1 p_enq a q_deq)
      
      (* Step 1: Technical note for this proof step.*)
      from 1 have pc_e': "program_counter s' p_enq = ''E2''" by blast
      from 1 have inqa': "InQBack s' a" by blast
      from 1 have tba': "TypeB s' a" by blast
      from 1 have pend_q': "HasPendingDeq s' q_deq" by blast
      from 1 have pc_q_D3': "program_counter s' q_deq = ''D3''" by blast
      from 1 have idx1': "Idx s' a < j_var s' q_deq" by blast
      from 1 have idx2': "j_var s' q_deq \<le> i_var s' p_enq" by blast
      from 1 have idx3': "i_var s' p_enq < l_var s' q_deq" by blast

      (* Step 2: Technical note for this proof step.*)
      have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast
      
      (* Step 3: Technical note for this transition-specific proof step.*)
      have p_enq_neq_p: "p_enq \<noteq> p"
      proof
        assume "p_enq = p"
        with pc_e' have "program_counter s' p = ''E2''" by simp
        moreover have "program_counter s' p \<noteq> ''E2''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed
      
      have q_deq_neq_p: "q_deq \<noteq> p"
      proof
        assume "q_deq = p"
        with pc_q_D3' have "program_counter s' p = ''D3''" by simp
        moreover have "program_counter s' p \<noteq> ''D3''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed

      (* Step 4: transport the concrete facts back to the pre-state.*)
      have pc_e_s: "program_counter s p_enq = ''E2''" using pc_e' p_enq_neq_p step_facts pc_eqs by auto
      have pc_q_s: "program_counter s q_deq = ''D3''" using pc_q_D3' q_deq_neq_p step_facts pc_eqs by auto
      
      have inqa_s: "InQBack s a" using inqa' step_facts unfolding InQBack_def by auto
      have tba_s: "TypeB s a" using tba' step_facts pc_eqs unfolding TypeB_def QHas_def by auto
      
      (* Technical note for this transition-specific proof step.
         Technical note for this proof step.*)
      have pend_q_s: "HasPendingDeq s q_deq"
        using pend_q' q_deq_neq_p by simp
      
      (* Technical note for this proof step.*)
      have idx_eq: "\<And>x. Idx s' x = Idx s x" using step_facts unfolding Idx_def AtIdx_def by auto
      have j_var_eq: "j_var s' q_deq = j_var s q_deq" using q_deq_neq_p step_facts by auto
      have l_var_eq: "l_var s' q_deq = l_var s q_deq" using q_deq_neq_p step_facts by auto
      have i_var_eq: "i_var s' p_enq = i_var s p_enq" using p_enq_neq_p step_facts by auto
      have v_var_eq: "v_var s' p_enq = v_var s p_enq" using p_enq_neq_p step_facts by auto

      have bound1: "Idx s a < j_var s q_deq" using idx1' idx_eq j_var_eq by simp
      have bound2: "j_var s q_deq \<le> i_var s p_enq" using idx2' j_var_eq i_var_eq by simp
      have bound3: "i_var s p_enq < l_var s q_deq" using idx3' i_var_eq l_var_eq by simp

      (* Step 5: Technical note for this proof step.*)
      have no_hb_old: "\<not> HB_EnqRetCall s a (v_var s p_enq)"
        using hI21_s pc_e_s inqa_s tba_s pend_q_s pc_q_s bound1 bound2 bound3
        unfolding hI29_E2_Scanner_Immunity_def by blast

      (* Step 6: Technical note for this proof step.*)
      show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
      proof -
        (* Technical note for this proof step.*)
        have seq_eq: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
          using step_facts by simp
          
        (* Technical note for this proof step.
           Technical note for this proof step.*)
        have hb_stable: "HB_EnqRetCall s' a (v_var s' p_enq) = HB_EnqRetCall s a (v_var s p_enq)"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def
          using HB_enq_stable_ret_append[OF seq_eq] v_var_eq
          by (metis HB_def)
          
        (* close*)
        thus ?thesis using no_hb_old by simp
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

      (* Step 2: Technical note for this proof step.*)
      have hI22_old: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast

      (* Step 3: Technical note for this transition-specific proof step.*)
      have q_neq_p: "q \<noteq> p"
      proof
        assume "q = p"
        with pc_q' have "program_counter s' p \<in> {''E2'', ''E3''}" by simp
        moreover have "program_counter s' p = ''L0''" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed

      (* Step 4: transport the concrete facts back to the pre-state.*)
      (* Technical note for this proof step.*)
      have pc_eq_q: "program_counter s' q = program_counter s q"
        using q_neq_p step_facts pc_eqs by auto
      have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}" 
        using pc_q' pc_eq_q by simp

      have v_var_eq: "v_var s' q = v_var s q" using q_neq_p step_facts by auto
      have i_var_eq: "i_var s' q = i_var s q" using q_neq_p step_facts by auto
      
      have inqb_s: "InQBack s b" using inqb' step_facts unfolding InQBack_def by auto
      have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_var_eq by simp

      (* Technical note for this invariant-preservation argument.*)
      have seq_eq: "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]"
        using step_facts by simp

      (* Technical note for this proof step.*)
      have hb_eq: "HB_EnqRetCall s' b (v_var s' q) = HB_EnqRetCall s b (v_var s q)"
        unfolding HB_EnqRetCall_def HB_Act_def
        using HB_enq_stable_ret_append[OF seq_eq] v_var_eq
        by metis
      have hb_s: "HB_EnqRetCall s b (v_var s q)" using hb' hb_eq by simp

      have idx_eq: "Idx s' b = Idx s b" unfolding Idx_def AtIdx_def using step_facts by simp

      (* Step 5: Technical note for this proof step.*)
      have "Idx s b < i_var s q"
        using hI22_old pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
        unfolding hI30_Ticket_HB_Immunity_def by blast

      (* Step 6: Technical note for this proof step.*)
      thus "Idx s' b < i_var s' q" using idx_eq i_var_eq by simp
    qed

  (* ------------------------------------------------------------------------- *)
  (* Step 6: Technical note for this proof step.*)
  (* ------------------------------------------------------------------------- *)

  (* Technical note for this invariant-preservation argument.*)
  have "lI1_Op_Sets_Equivalence s'"
  proof (rule lI1_Op_Sets_Equivalence_E3_step)
    show "lI1_Op_Sets_Equivalence s" using lI1_Op_Sets_Equivalence_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "OPLin s' = OPLin s" using step_facts unfolding OPLin_def by simp

    (* Technical note for this invariant-preservation argument.*)
    have typeb_eq: "\<And>x. TypeB s' x = TypeB s x"
    proof -
      fix x
      have "\<And>q. (program_counter s' q = ''E2'' \<and> v_var s' q = x) = (program_counter s q = ''E2'' \<and> v_var s q = x)"
      proof -
        fix q
        have split_q: "q = p \<or> q \<noteq> p" by blast
        from split_q show "(program_counter s' q = ''E2'' \<and> v_var s' q = x) = (program_counter s q = ''E2'' \<and> v_var s q = x)"
        proof (elim disjE, goal_cases)
          case 1
          (* Technical note for this transition-specific proof step.*)
          have "program_counter s p = ''E3''" using step_facts by simp
          thus ?case using 1 pc_eqs by auto
        next
          case 2
          (* Technical note for this proof step.*)
          thus ?case using other_facts pc_eqs by auto
        qed
      qed
      hence "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) = (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
        by simp 
      thus "TypeB s' x = TypeB s x" unfolding TypeB_def
        by (simp add: QHas_def) 
    qed

    (* Technical note for this proof step.*)
    show "SetA s' = SetA s"
      unfolding SetA_def QHas_def using step_facts typeb_eq by simp

    show "SetB s' = SetB s"
      unfolding SetB_def QHas_def using step_facts typeb_eq by simp
  qed

  have "lI2_Op_Cardinality s'" using lI2_Op_Cardinality_s step_facts unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def by auto

(* Technical note for this invariant-preservation argument.*)
  have "lI3_HB_Ret_Lin_Sync s'"
  proof (rule lI3_HB_Ret_Lin_Sync_E3_step)
    show "lI3_HB_Ret_Lin_Sync s" using lI3_HB_Ret_Lin_Sync_s by simp
    show "lI1_Op_Sets_Equivalence s" using lI1_Op_Sets_Equivalence_s by simp
    show "system_invariant s" using INV by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "lin_seq s' = lin_seq s" using step_facts by simp
    show "program_counter s p = ''E3''" using step_facts by simp
  qed

  have "lI4_FIFO_Semantics s'" using lI4_FIFO_Semantics_s step_facts unfolding lI4_FIFO_Semantics_def by simp
  have "lI5_SA_Prefix s'" using lI5_SA_Prefix_s step_facts unfolding lI5_SA_Prefix_def by simp

  have "lI6_D4_Deq_Linearized s'"
  proof -
    show ?thesis
      unfolding lI6_D4_Deq_Linearized_def
    proof (intro allI impI)
      fix q
      assume pc_q: "program_counter s' q = ''D4''"

      have "program_counter s q = ''D4''"
        using pc_q by simp
      then have "mk_op deq (x_var s q) q (s_var s q) \<in> set (lin_seq s)"
        using lI6_D4_Deq_Linearized_s
        unfolding lI6_D4_Deq_Linearized_def
        by blast
      thus "mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s')"
        using pc_q by auto
    qed
  qed



(* Technical note for this invariant-preservation argument.*)
  have "lI7_D4_Deq_Deq_HB s'"
  proof (rule lI7_D4_Deq_Deq_HB_E3_step)
    show "lI7_D4_Deq_Deq_HB s" using lI7_D4_Deq_Deq_HB_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s' p = ''L0''" using step_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q" using other_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q" using other_facts step_facts by auto
    show "lin_seq s' = lin_seq s" using step_facts by simp
  qed

(* Technical note for this invariant-preservation argument.*)
  have "lI8_D3_Deq_Returned s'"
  proof (rule lI8_D3_Deq_Returned_E3_step)
    show "lI8_D3_Deq_Returned s" using lI8_D3_Deq_Returned_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s' p = ''L0'' " using step_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q" using other_facts by simp
    show "lin_seq s' = lin_seq s" using step_facts by simp
  qed

(* Technical note for this invariant-preservation argument.*)
  have "lI9_D1_D2_Deq_Returned s'"
  proof (rule lI9_D1_D2_Deq_Returned_E3_step)
    show "lI9_D1_D2_Deq_Returned s" using lI9_D1_D2_Deq_Returned_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s' p = ''L0'' " using step_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q" using other_facts by simp
    show "lin_seq s' = lin_seq s" using step_facts by simp
  qed

(* Technical note for this invariant-preservation argument.*)
  have "lI10_D4_Enq_Deq_HB s'"
  proof (rule lI10_D4_Enq_Deq_HB_E3_step)
    show "lI10_D4_Enq_Deq_HB s" using lI10_D4_Enq_Deq_HB_s by simp
    show "his_seq s' = his_seq s @ [mk_act enq (v_var s p) p (s_var s p) ret]" using step_facts by simp
    show "program_counter s' p = ''L0'' " using step_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q" using other_facts by simp
    show "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q" using other_facts step_facts by auto
    show "lin_seq s' = lin_seq s" using step_facts by simp
  qed

  have "lI11_D4_Deq_Unique s'"
  proof -
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
                 op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
                 k3 < k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3)))"
        using pc_q_s' by force
    qed
  qed



  have "data_independent (lin_seq s')" using di_lin_s step_facts by simp

  have "Simulate_PC s'" using STEP unfolding Sys_E3_def by simp

  (* Step 6: Technical note for this proof step.*)
  show ?thesis 
    unfolding system_invariant_def
    using `Simulate_PC s'` `TypeOK s'` `sI1_Zero_Index_BOT s'`
    `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'`  `hI3_L0_E_Phase_Bounds s'` 
    `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'` `sI12_D3_Scanned_Prefix s'` `hI4_X_var_Lin_Sync s'` 
    `hI7_His_WF s'` `hI8_Val_Unique s'` `hI5_SSN_Unique s'` `hI6_SSN_Order s'` 
    `hI9_Deq_Ret_Unique s'` `hI10_Enq_Call_Existence s'` `hI11_Enq_Ret_Existence s'` `hI12_D_Phase_Pending_Deq s'` `hI13_Qback_Deq_Sync s'` `hI14_Pending_Enq_Qback_Exclusivity s'` `hI15_Deq_Result_Exclusivity s'` `hI16_BO_BT_No_HB s'` `hI17_BT_BT_No_HB s'` `hI18_Idx_Order_No_Rev_HB s'` `hI19_Scanner_Catches_Later_Enq s'` `hI20_Enq_Val_Valid s'` `hI21_Ret_Implies_Call s'` `hI22_Deq_Local_Pattern s'` `hI23_Deq_Call_Ret_Balanced s'` `hI24_HB_Implies_Idx_Order s'` `hI25_Enq_Call_Ret_Balanced s'`  `hI26_DeqRet_D4_Mutex s'`
    `hI27_Pending_PC_Sync s'` `hI28_Fresh_Enq_Immunity s'` `hI29_E2_Scanner_Immunity s'` `hI30_Ticket_HB_Immunity s'` (* Technical note for this proof step.*)
    `lI1_Op_Sets_Equivalence s'` `lI2_Op_Cardinality s'` `lI3_HB_Ret_Lin_Sync s'` `lI4_FIFO_Semantics s'` `lI5_SA_Prefix s'`
    `lI6_D4_Deq_Linearized s'` `lI7_D4_Deq_Deq_HB s'` `lI8_D3_Deq_Returned s'` `lI9_D1_D2_Deq_Returned s'` `lI10_D4_Enq_Deq_HB s'` `lI11_D4_Deq_Unique s'`
    `data_independent (lin_seq s')`
    by blast
qed


lemma E3_preserves_state_invs_rest:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E3 p s s'"
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
  using E3_preserves_invariant_core[OF INV STEP]
  unfolding system_invariant_def by auto

lemma E3_preserves_history_invs_rest:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E3 p s s'"
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
  using E3_preserves_invariant_core[OF INV STEP]
  unfolding system_invariant_def by auto

lemma E3_preserves_linearization_invs_rest:
  assumes INV: "system_invariant s"
      and STEP: "Sys_E3 p s s'"
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
  using E3_preserves_invariant_core[OF INV STEP]
  unfolding system_invariant_def by auto

end