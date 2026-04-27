(* Preservation of the system invariant for the D4 transition rule *)
theory D4Lemmas
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    DeqLib
begin




(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI2_SSN_Bounds *)
(* ========================================================================= *)
lemma hI2_SSN_Bounds_D4_step:
  assumes INV: "system_invariant s"
    and STEP: "Sys_D4 p s s'"
  shows "hI2_SSN_Bounds s'"
proof -
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  have hI2_SSN_Bounds_s: "hI2_SSN_Bounds s"
    using INV unfolding system_invariant_def by blast

  have step_facts [simp]:
    "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    "program_counter s' p = ''L0''"
    "s_var s' p = s_var s p + 1"
  proof -
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
      using u_steps unfolding U_D3_def U_D4_def bridge by auto
    show "program_counter s' p = ''L0''" "s_var s' p = s_var s p + 1"
      using STEP u_steps unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
  qed

  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  proof -
    fix q assume "q \<noteq> p"
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    thus "program_counter s' q = program_counter s q" "s_var s' q = s_var s q"
      using STEP `q \<noteq> p` unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
  qed

  show ?thesis
    unfolding hI2_SSN_Bounds_def
  proof (intro allI ballI impI)
    fix q e
    assume e_in: "e \<in> set (his_seq s')"
    assume e_pid: "act_pid e = q"

    have e_cases: "e \<in> set (his_seq s) \<or> e = mk_act deq (x_var s p) p (s_var s p) ret"
      using e_in step_facts(1) by auto

    show "act_ssn e \<le> s_var s' q \<and> (program_counter s' q = ''L0'' \<longrightarrow> act_ssn e < s_var s' q)"
    proof
      show "act_ssn e \<le> s_var s' q"
      proof (cases "q = p")
        case True
        from e_cases show ?thesis
        proof
          assume old_e: "e \<in> set (his_seq s)"
          have "act_ssn e \<le> s_var s p"
            using hI2_SSN_Bounds_s old_e True e_pid unfolding hI2_SSN_Bounds_def by blast
          thus ?thesis using True step_facts(3) by simp
        next
          assume new_e: "e = mk_act deq (x_var s p) p (s_var s p) ret"
          have "act_ssn e = s_var s p" using new_e by (simp add: mk_act_def act_ssn_def)
          thus ?thesis using True step_facts(3) by simp
        qed
      next
        case False
        have "e \<noteq> mk_act deq (x_var s p) p (s_var s p) ret"
          using False e_pid by (auto simp: mk_act_def act_pid_def)
        hence e_old: "e \<in> set (his_seq s)" using e_cases by blast
        have "act_ssn e \<le> s_var s q"
          using hI2_SSN_Bounds_s e_old e_pid unfolding hI2_SSN_Bounds_def by blast
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
            have "act_ssn e \<le> s_var s p"
              using hI2_SSN_Bounds_s old_e True e_pid unfolding hI2_SSN_Bounds_def by blast
            thus ?thesis using True step_facts(3) by simp
          next
            assume new_e: "e = mk_act deq (x_var s p) p (s_var s p) ret"
            have "act_ssn e = s_var s p" using new_e by (simp add: mk_act_def act_ssn_def)
            thus ?thesis using True step_facts(3) by simp
          qed
        next
          case False
          have pc_s_q: "program_counter s q = ''L0''" using q_L0 False other_facts by simp
          have "e \<noteq> mk_act deq (x_var s p) p (s_var s p) ret"
            using False e_pid by (auto simp: mk_act_def act_pid_def)
          hence e_old: "e \<in> set (his_seq s)" using e_cases by blast
          have "act_ssn e < s_var s q"
            using hI2_SSN_Bounds_s pc_s_q e_old e_pid unfolding hI2_SSN_Bounds_def by blast
          thus ?thesis using False other_facts by simp
        qed
      qed
    qed
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves sI11_x_var_Scope *)
(* ========================================================================= *)
lemma sI11_x_var_Scope_D4_step:
  assumes inv_sI11_x_var_Scope: "sI11_x_var_Scope s"
    and STEP: "Sys_D4 p s s'"
  shows "sI11_x_var_Scope s'"
proof -
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  have step_facts [simp]:
    "program_counter s' p = ''L0''"
    "x_var s' p = BOT"
  proof -
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    show "program_counter s' p = ''L0''" "x_var s' p = BOT"
      using STEP u_steps unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
  qed

  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
  proof -
    fix q assume "q \<noteq> p"
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    thus "program_counter s' q = program_counter s q" "x_var s' q = x_var s q"
      using STEP `q \<noteq> p` unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
  qed

  show ?thesis
    unfolding sI11_x_var_Scope_def
  proof (intro allI impI)
    fix q
    assume q_not_D4: "program_counter s' q \<noteq> ''D4''"
    show "x_var s' q = BOT"
    proof (cases "q = p")
      case True
      then show ?thesis using step_facts by simp
    next
      case False
      have "program_counter s q = program_counter s' q" using False other_facts by simp
      hence "program_counter s q \<noteq> ''D4''" using q_not_D4 by force
      hence "x_var s q = BOT" using inv_sI11_x_var_Scope unfolding sI11_x_var_Scope_def by blast
      thus ?thesis using False other_facts by simp
    qed
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI1_E_Phase_Pending_Enq *)
(* ========================================================================= *)
lemma hI1_E_Phase_Pending_Enq_D4_step:
  assumes inv_hI1_E_Phase_Pending_Enq: "hI1_E_Phase_Pending_Enq s"
    and STEP: "Sys_D4 p s s'"
  shows "hI1_E_Phase_Pending_Enq s'"
proof -
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  have step_facts [simp]:
    "v_var s' = v_var s"
    "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    "program_counter s' p = ''L0''"
  proof -
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    show "v_var s' = v_var s" "program_counter s' p = ''L0''"
      using STEP u_steps unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
    show "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
      using u_steps unfolding U_D3_def U_D4_def bridge by auto
  qed

  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  proof -
    fix q assume "q \<noteq> p"
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    thus "program_counter s' q = program_counter s q" "s_var s' q = s_var s q"
      using STEP `q \<noteq> p` unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
  qed

  show ?thesis
    unfolding hI1_E_Phase_Pending_Enq_def
  proof (intro allI impI)
    fix q
    assume q_E: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
    have q_neq_p: "q \<noteq> p" using q_E step_facts by auto
    have pc_old: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" using q_E q_neq_p other_facts by auto

    have pend_old: "HasPendingEnq s q (v_var s q)"
      using inv_hI1_E_Phase_Pending_Enq pc_old unfolding hI1_E_Phase_Pending_Enq_def by auto

    have call_old: "EnqCallInHis s q (v_var s q) (s_var s q)"
      and no_ret_old: "\<forall>e\<in>set (his_seq s). \<not> (act_pid e = q \<and> act_ssn e = s_var s q \<and> act_cr e = ret)"
      using pend_old unfolding HasPendingEnq_def Let_def by auto

    have part1: "EnqCallInHis s' q (v_var s' q) (s_var s' q)"
    proof -
      have "EnqCallInHis s' q (v_var s q) (s_var s q)"
        using EnqCall_mono[OF call_old step_facts(2)] by simp
      thus ?thesis using q_neq_p other_facts step_facts(1) by simp
    qed

    have part2: "\<forall>e\<in>set (his_seq s'). \<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)"
    proof
      fix e assume "e \<in> set (his_seq s')"
      hence "e \<in> set (his_seq s) \<or> e = mk_act deq (x_var s p) p (s_var s p) ret"
        using step_facts(2) by auto
      thus "\<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)"
      proof
        assume old_e: "e \<in> set (his_seq s)"
        show ?thesis using no_ret_old old_e q_neq_p other_facts by auto
      next
        assume new_e: "e = mk_act deq (x_var s p) p (s_var s p) ret"
        have "act_pid e = p" using new_e by (simp add: mk_act_def act_pid_def)
        thus ?thesis using q_neq_p by simp
      qed
    qed

    show "HasPendingEnq s' q (v_var s' q)"
      unfolding HasPendingEnq_def Let_def using part1 part2 by simp
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI4_X_var_Lin_Sync *)
(* ========================================================================= *)
lemma hI4_X_var_Lin_Sync_D4_step:
  assumes inv_hI4_X_var_Lin_Sync: "hI4_X_var_Lin_Sync s"
    and STEP: "Sys_D4 p s s'"
  shows "hI4_X_var_Lin_Sync s'"
proof -
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  have X_var_eq: "X_var s' = X_var s"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
  proof -
    from STEP obtain us_mid where u_steps: "U_D3 p (x_var s p) (s_var s p) (snd s) us_mid" "U_D4 p us_mid (snd s')"
      unfolding Sys_D4_def bridge by blast
    show "X_var s' = X_var s"
      using STEP u_steps unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge
      by (auto simp: prod_eq_iff)
    show "lin_seq s' = lin_seq s"
      using u_steps unfolding U_D3_def U_D4_def bridge by auto
  qed

  show ?thesis
    using inv_hI4_X_var_Lin_Sync X_var_eq lin_seq_eq
    unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def
    by auto
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI13_Qback_Deq_Sync  *)
(* ========================================================================= *)
lemma hI13_Qback_Deq_Sync_D4_step:
  assumes inv_hI13_Qback_Deq_Sync: "hI13_Qback_Deq_Sync s"
    and Q_arr_eq: "Q_arr s' = Q_arr s"
    and Qback_arr_eq: "Qback_arr s' = Qback_arr s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and x_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
    and s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  shows "hI13_Qback_Deq_Sync s'"
proof -
  {
    fix a
    assume a_not_bot: "a \<noteq> BOT"
    assume prems_s': "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a"

    (* 1. transport the concrete facts back to the old state s *)
    have prems_s: "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a"
      using prems_s' Q_arr_eq Qback_arr_eq by auto
    
    (* 2. extract the witnesses q_old and sn_old from the old-state invariant *)
    then obtain q_old sn_old where q_prop: 
      "(program_counter s q_old = ''D4'' \<and> x_var s q_old = a \<and> s_var s q_old = sn_old) \<or> 
       DeqRetInHis s q_old a sn_old"
      using inv_hI13_Qback_Deq_Sync a_not_bot unfolding hI13_Qback_Deq_Sync_def by blast

    (* 3. construct the existential witness required after the D4 step *)
    have "\<exists>q sn. (program_counter s' q = ''D4'' \<and> x_var s' q = a \<and> s_var s' q = sn) \<or> 
                 DeqRetInHis s' q a sn"
    proof (cases "q_old = p")
      case True
      (* ============================================================== *)
      (* This is p: instead of intro, build the exact witness with have *)
      (* ============================================================== *)
      have right_side: "DeqRetInHis s' p a sn_old"
      proof (cases "program_counter s p = ''D4'' \<and> x_var s p = a \<and> s_var s p = sn_old")
        case True_p: True
        (* show that the element belongs to the set *)
        have "mk_act deq a p sn_old ret \<in> set (his_seq s')"
          using his_append True_p True by auto
        (* show that all fields of the element are correct *)
        moreover have "act_pid (mk_act deq a p sn_old ret) = p \<and> 
                       act_ssn (mk_act deq a p sn_old ret) = sn_old \<and> 
                       act_name (mk_act deq a p sn_old ret) = deq \<and> 
                       act_cr (mk_act deq a p sn_old ret) = ret \<and> 
                       act_val (mk_act deq a p sn_old ret) = a"
          by (simp add: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
        (* ultimately combine the two facts and derive the definition directly *)
        ultimately show "DeqRetInHis s' p a sn_old"
          unfolding DeqRetInHis_def Let_def by blast
      next
        case False_p: False
        have "DeqRetInHis s p a sn_old" using q_prop True False_p by blast
        then show "DeqRetInHis s' p a sn_old" 
          unfolding DeqRetInHis_def using his_append by auto
      qed
      
      (* Use the constructed right_side fact to discharge the existential thesis *)
      thus ?thesis using True by blast
      
    next
      case False
      (* ============================================================== *)
      (* This is another process: again construct the full witness with have *)
      (* ============================================================== *)
      have left_or_right: "(program_counter s' q_old = ''D4'' \<and> x_var s' q_old = a \<and> s_var s' q_old = sn_old) \<or> 
                           DeqRetInHis s' q_old a sn_old"
      proof (cases "program_counter s q_old = ''D4'' \<and> x_var s q_old = a \<and> s_var s q_old = sn_old")
        case True_q: True
        have "program_counter s' q_old = ''D4'' \<and> x_var s' q_old = a \<and> s_var s' q_old = sn_old"
          using False True_q pc_eq x_var_other s_var_other by (auto simp: fun_upd_def)
        thus ?thesis by blast
      next
        case False_q: False
        have "DeqRetInHis s q_old a sn_old" using q_prop False False_q by blast
        hence "DeqRetInHis s' q_old a sn_old" 
          unfolding DeqRetInHis_def using his_append by auto
        thus ?thesis by blast
      qed
      
      (* Use blast once more to discharge the outer existential goal *)
      thus ?thesis by blast
    qed
  }
  (* 4. final assembly *)
  thus "hI13_Qback_Deq_Sync s'"
    unfolding hI13_Qback_Deq_Sync_def by blast
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI14_Pending_Enq_Qback_Exclusivity  *)
(* ========================================================================= *)
lemma hI14_Pending_Enq_Qback_Exclusivity_D4_step:
  assumes inv_hI14_Pending_Enq_Qback_Exclusivity: "hI14_Pending_Enq_Qback_Exclusivity s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and Qback_arr_eq: "Qback_arr s' = Qback_arr s"
    and i_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> i_var s' q = i_var s q"
    and s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  shows "hI14_Pending_Enq_Qback_Exclusivity s'"
  unfolding hI14_Pending_Enq_Qback_Exclusivity_def
proof (intro conjI allI impI)
  (* ========================================================================= *)
  (* Part 1: Qback_arr exclusivity for processes in E2 or E3 *)
  (* ========================================================================= *)
  fix q a
  assume prems: "HasPendingEnq s' q a \<and> program_counter s' q \<in> {''E2'', ''E3''}"

  have "program_counter s' p = ''L0''" using pc_eq by (simp add: fun_upd_def)
  have q_not_p: "q \<noteq> p" using prems `program_counter s' p = ''L0''` by auto

  have pc_s: "program_counter s q \<in> {''E2'', ''E3''}"
    using q_not_p prems pc_eq by (auto simp: fun_upd_def)

  (* Use set-based backward reasoning to show that any PendingEnq fact in the new state comes from the old state *)
  have "HasPendingEnq s q a"
  proof -
    (* 1. Unfold Let_def explicitly and match the structure of the underlying implication *)
    have "HasPendingEnq s' q a" using prems by blast
    hence pending_s': "EnqCallInHis s' q a (s_var s' q) \<and> 
                       (\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret)"
      unfolding HasPendingEnq_def Let_def by blast
      
    have enq_s': "EnqCallInHis s' q a (s_var s' q)" using pending_s' by blast
    have no_ret_s': "\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret" using pending_s' by blast

    (* 2. state transport *)
    have sn_eq: "s_var s' q = s_var s q" using q_not_p s_var_other by simp
    have set_s': "set (his_seq s') = insert (mk_act deq (x_var s p) p (s_var s p) ret) (set (his_seq s))"
      using his_append by auto
      
    (* 3. show that the call already exists in the old history *)
    have enq_s: "EnqCallInHis s q a (s_var s q)"
      using enq_s' sn_eq set_s' q_not_p
      unfolding EnqCallInHis_def mk_act_def act_pid_def by auto
      
    (* 4. show that the return is absent from the old history *)
    have no_ret_s: "\<forall>e\<in>set (his_seq s). act_ssn e = s_var s q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
      using no_ret_s' sn_eq set_s' by auto
      
    (* 5. reassemble the old-state HasPendingEnq fact *)
    show ?thesis 
      unfolding HasPendingEnq_def Let_def 
      using enq_s no_ret_s by blast
  qed

  have "\<not> (\<exists>k. Qback_arr s k = a \<and> k \<noteq> i_var s q)"
    using inv_hI14_Pending_Enq_Qback_Exclusivity pc_s `HasPendingEnq s q a` unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
  moreover have "Qback_arr s' = Qback_arr s" using Qback_arr_eq by auto
  moreover have "i_var s' q = i_var s q" using q_not_p i_var_other by auto
  ultimately show "\<not> (\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q)" by auto

next
  (* ========================================================================= *)
  (* Part 2: Qback_arr exclusivity for processes in E1 *)
  (* ========================================================================= *)
  fix q a
  assume prems: "HasPendingEnq s' q a \<and> program_counter s' q = ''E1''"
  
  have "program_counter s' p = ''L0''" using pc_eq by (simp add: fun_upd_def)
  have q_not_p: "q \<noteq> p" using prems `program_counter s' p = ''L0''` by auto

  have pc_s: "program_counter s q = ''E1''"
    using q_not_p prems pc_eq by (auto simp: fun_upd_def)

  have "HasPendingEnq s q a"
  proof -
    have "HasPendingEnq s' q a" using prems by blast
    hence pending_s': "EnqCallInHis s' q a (s_var s' q) \<and> 
                       (\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret)"
      unfolding HasPendingEnq_def Let_def by blast
      
    have enq_s': "EnqCallInHis s' q a (s_var s' q)" using pending_s' by blast
    have no_ret_s': "\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret" using pending_s' by blast

    have sn_eq: "s_var s' q = s_var s q" using q_not_p s_var_other by simp
    have set_s': "set (his_seq s') = insert (mk_act deq (x_var s p) p (s_var s p) ret) (set (his_seq s))"
      using his_append by auto
      
    have enq_s: "EnqCallInHis s q a (s_var s q)"
      using enq_s' sn_eq set_s' q_not_p
      unfolding EnqCallInHis_def mk_act_def act_pid_def by auto
      
    have no_ret_s: "\<forall>e\<in>set (his_seq s). act_ssn e = s_var s q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
      using no_ret_s' sn_eq set_s' by auto
      
    show ?thesis 
      unfolding HasPendingEnq_def Let_def 
      using enq_s no_ret_s by blast
  qed

  have "\<not> (\<exists>k. Qback_arr s k = a)"
    using inv_hI14_Pending_Enq_Qback_Exclusivity pc_s `HasPendingEnq s q a` unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
  moreover have "Qback_arr s' = Qback_arr s" using Qback_arr_eq by auto
  ultimately show "\<not> (\<exists>k. Qback_arr s' k = a)" by auto
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI15_Deq_Result_Exclusivity  *)
(* ========================================================================= *)
lemma hI15_Deq_Result_Exclusivity_D4_step:
  assumes inv_hI15_Deq_Result_Exclusivity: "hI15_Deq_Result_Exclusivity s"
    and inv_sys: "system_invariant s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and Q_arr_eq: "Q_arr s' = Q_arr s"
    and x_var_p: "x_var s' p = BOT"
    and x_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
    and pc_s_p: "program_counter s p = ''D4''"
    and s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
  shows "hI15_Deq_Result_Exclusivity s'"
proof -
  (* ========================================================================= *)
  (* Internal tool 1: decompose the source of DeqRet facts *)
  (* Show that any DeqRet in the new state either comes from the old history or is the freshly appended return of p *)
  (* ========================================================================= *)
  have deq_ret_s'_cases: "\<And>q a sn. DeqRetInHis s' q a sn \<Longrightarrow> DeqRetInHis s q a sn \<or> (q = p \<and> a = x_var s p \<and> sn = s_var s p)"
  proof -
    fix q a sn assume "DeqRetInHis s' q a sn"
    (* Pick an element e from the set directly, without index bookkeeping *)
    then obtain e where e_props: "e \<in> set (his_seq s')" "act_pid e = q"
      "act_ssn e = sn" "act_name e = deq" "act_cr e = ret" "act_val e = a"
      unfolding DeqRetInHis_def Let_def by blast
      
    (* Appending to the list is directly reflected as insert at the set level *)
    have seq_eq: "set (his_seq s') = insert (mk_act deq (x_var s p) p (s_var s p) ret) (set (his_seq s))" 
      using his_append by auto
      
    show "DeqRetInHis s q a sn \<or> (q = p \<and> a = x_var s p \<and> sn = s_var s p)"
    proof (cases "e \<in> set (his_seq s)")
      case True
      (* Case A: the element e already belongs to the old history *)
      hence "DeqRetInHis s q a sn" unfolding DeqRetInHis_def Let_def
        using e_props by auto
      thus ?thesis by simp
    next
      case False
      (* Case B: otherwise it must be the freshly appended event *)
      hence "e = mk_act deq (x_var s p) p (s_var s p) ret" 
        using e_props(1) seq_eq by auto
      (* Compare the expanded definitions and derive the required equalities *)
      hence "q = p \<and> a = x_var s p \<and> sn = s_var s p" 
        using e_props by (simp add: mk_act_def act_pid_def act_val_def act_ssn_def act_name_def act_cr_def)
      thus ?thesis by simp
    qed
  qed

  (* ========================================================================= *)
  (* Internal tool 2: collapse the ownership disjunction without relying on a slow blast call *)
  (* Show that ownership in the new state maps back to the corresponding ownership fact in the old state *)
  (* ========================================================================= *)
  have cond_collapse: "\<And>q a sn. DeqRetInHis s' q a sn \<or> (program_counter s' q = ''D4'' \<and> x_var s' q = a \<and> s_var s' q = sn) \<Longrightarrow> 
                                DeqRetInHis s q a sn \<or> (program_counter s q = ''D4'' \<and> x_var s q = a \<and> s_var s q = sn)"
  proof -
    fix q a sn assume pre: "DeqRetInHis s' q a sn \<or> (program_counter s' q = ''D4'' \<and> x_var s' q = a \<and> s_var s' q = sn)"
    show "DeqRetInHis s q a sn \<or> (program_counter s q = ''D4'' \<and> x_var s q = a \<and> s_var s q = sn)"
    proof (cases "DeqRetInHis s' q a sn")
      case True
      (* obtain the two possible ownership cases *)
      have "DeqRetInHis s q a sn \<or> (q = p \<and> a = x_var s p \<and> sn = s_var s p)"
        using True deq_ret_s'_cases by simp
      thus ?thesis
      proof
        (* Possibility 1: it comes from the old history, so the left disjunct holds directly *)
        assume "DeqRetInHis s q a sn"
        thus ?thesis by simp
      next
        (* Possibility 2: it is the newly appended element *)
        assume new_elem: "q = p \<and> a = x_var s p \<and> sn = s_var s p"
        (* Feed it pc_s_p so that the D4 control-state fact is available immediately *)
        hence "program_counter s q = ''D4'' \<and> x_var s q = a \<and> s_var s q = sn"
          using pc_s_p by simp
        thus ?thesis by simp
      qed
    next
      case False
      (* name the intermediate conclusion *)
      hence q_state_s': "program_counter s' q = ''D4'' \<and> x_var s' q = a \<and> s_var s' q = sn" 
        using pre by blast
      hence "q \<noteq> p" using pc_eq by (auto simp: fun_upd_def)
      hence "program_counter s q = ''D4'' \<and> x_var s q = a \<and> s_var s q = sn" 
        using q_state_s' pc_eq x_var_other s_var_other by (auto simp: fun_upd_def)
      thus ?thesis by simp
    qed
  qed

(* ========================================================================= *)
  (* Final derivation: use a separate have to avoid prefix issues, then let blast close the goal *)
  (* ========================================================================= *)
  
  (* Part 1 : ownership of the same value is exclusive across different processes *)
  have part1: "\<forall>(a::nat) (p1::nat) (p2::nat) (sn1::nat) (sn2::nat). a \<in> Val \<longrightarrow> p1 \<noteq> p2 \<longrightarrow> \<not> ((DeqRetInHis s' p1 a sn1 \<or> program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a \<and> s_var s' p1 = sn1) \<and> 
                                                   (DeqRetInHis s' p2 a sn2 \<or> program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a \<and> s_var s' p2 = sn2))"
  proof (intro allI impI notI)
    fix a p1 p2 sn1 sn2 :: nat (* <--- Key adjustment: fix the local variable types explicitly at this point *)
    assume a_val: "a \<in> Val" and p1_neq_p2: "p1 \<noteq> p2"
    assume "(DeqRetInHis s' p1 a sn1 \<or> program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a \<and> s_var s' p1 = sn1) \<and> 
            (DeqRetInHis s' p2 a sn2 \<or> program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a \<and> s_var s' p2 = sn2)"
    hence "(DeqRetInHis s p1 a sn1 \<or> program_counter s p1 = ''D4'' \<and> x_var s p1 = a \<and> s_var s p1 = sn1) \<and> 
           (DeqRetInHis s p2 a sn2 \<or> program_counter s p2 = ''D4'' \<and> x_var s p2 = a \<and> s_var s p2 = sn2)"
      using cond_collapse by blast
    thus False using inv_hI15_Deq_Result_Exclusivity a_val p1_neq_p2 unfolding hI15_Deq_Result_Exclusivity_def by blast
  qed

(* Part 2 : A value held by an active dequeue (including D4) cannot simultaneously remain in Q_arr *)
  have part2: "\<forall>(q::nat) (a::nat) (k::nat). a \<in> Val \<longrightarrow> HasPendingDeq s' q \<longrightarrow> \<not> (x_var s' q = a \<and> Q_arr s' k = a)"
  proof (intro allI impI notI) 
    fix q a k :: nat
    assume a_val: "a \<in> Val" 
    assume pending_s': "HasPendingDeq s' q" 
    assume target_s': "x_var s' q = a \<and> Q_arr s' k = a"
    
    have "a \<noteq> BOT" using a_val Val_def BOT_def by auto
    hence "x_var s' q \<noteq> BOT" using target_s' by auto
    hence q_not_p: "q \<noteq> p" using x_var_p by auto
    
    (* introduce the SN-equivalence fact to match the updated set definition *)
    have sn_eq: "s_var s' q = s_var s q" using q_not_p s_var_other by simp
    
    (* avoid the obsolete encoding and transport the state with the new set-based reasoning *)
    have pending_q: "HasPendingDeq s q" 
    proof -
      (* 1. unpack the Pending fact in the new state *)
      have "HasPendingDeq s' q" using pending_s' by blast
      hence call_s': "DeqCallInHis s' q (s_var s' q)" 
        and no_ret_s': "\<forall>e\<in>set (his_seq s'). act_ssn e = s_var s' q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
        unfolding HasPendingDeq_def Let_def by auto
        
      (* 2. translate the appended-list view into a set insertion *)
      have set_s': "set (his_seq s') = insert (mk_act deq (x_var s p) p (s_var s p) ret) (set (his_seq s))" 
        using his_append by auto
        
      (* Step 3: 3. Call : the appended element belongs to p, whereas the target process is q, so the witness must already be in the old set *)
      have call_s: "DeqCallInHis s q (s_var s q)"
        using call_s' sn_eq set_s' q_not_p
        unfolding DeqCallInHis_def mk_act_def act_pid_def by auto
        
      (* Step 4: 4. Ret : if the new set has no return, then the old set cannot have one either *)
      have no_ret_s: "\<forall>e\<in>set (his_seq s). act_ssn e = s_var s q \<longrightarrow> act_pid e = q \<longrightarrow> act_cr e \<noteq> ret"
        using no_ret_s' sn_eq set_s' by auto
        
      (* 5. reassemble the old-state HasPendingDeq fact *)
      show ?thesis 
        unfolding HasPendingDeq_def Let_def
        using call_s no_ret_s by blast
    qed

    have x_var_s: "x_var s q = a" using target_s' q_not_p x_var_other by auto
    have q_arr_s: "Q_arr s k = a" using target_s' Q_arr_eq by auto
    
    show False 
      using inv_hI15_Deq_Result_Exclusivity a_val pending_q x_var_s q_arr_s unfolding hI15_Deq_Result_Exclusivity_def by blast
  qed

  (* Part 3 : A value already returned in the history cannot still be found in Q_arr *)
  have part3: "\<forall>(q::nat) (a::nat) (sn::nat). a \<in> Val \<longrightarrow> DeqRetInHis s' q a sn \<longrightarrow> (\<forall>(k::nat). Q_arr s' k \<noteq> a)"
  proof (intro allI impI)
    fix q a sn k :: nat (* <--- Key adjustment: fix the local variable types explicitly at this point *)
    assume a_val: "a \<in> Val" and ret_s': "DeqRetInHis s' q a sn"
    have "Q_arr s' k = Q_arr s k" using Q_arr_eq by simp
    
    from ret_s' have "DeqRetInHis s q a sn \<or> (q = p \<and> a = x_var s p \<and> sn = s_var s p)"
      using deq_ret_s'_cases by blast
    thus "Q_arr s' k \<noteq> a"
    proof
      assume "DeqRetInHis s q a sn"
      thus ?thesis using inv_hI15_Deq_Result_Exclusivity a_val `Q_arr s' k = Q_arr s k` unfolding hI15_Deq_Result_Exclusivity_def
        by metis 
    next
      assume new_ret: "q = p \<and> a = x_var s p \<and> sn = s_var s p"
      show "Q_arr s' k \<noteq> a"
      proof
        assume "Q_arr s' k = a"
        hence "Q_arr s k = a" using `Q_arr s' k = Q_arr s k` by simp
        have a_not_bot: "a \<noteq> BOT" using a_val Val_def BOT_def by auto
        
        have "Q_arr s k = Qback_arr s k \<or> Q_arr s k = BOT" 
          using inv_sys unfolding system_invariant_def sI8_Q_Qback_Sync_def by blast
        hence qback_k: "Qback_arr s k = a" using `Q_arr s k = a` a_not_bot by simp
        
        have "Qback_arr s (j_var s p) = a \<and> Q_arr s (j_var s p) = BOT"
          using inv_sys pc_s_p new_ret unfolding system_invariant_def sI7_D4_Deq_Result_def by auto
        hence qback_p: "Qback_arr s (j_var s p) = a" and qarr_p: "Q_arr s (j_var s p) = BOT" by auto
          
        have "k = j_var s p"
        proof (rule ccontr)
          assume k_neq: "k \<noteq> j_var s p"
          have "\<forall>i j. i \<noteq> j \<longrightarrow> Qback_arr s i = BOT \<or> Qback_arr s j = BOT \<or> Qback_arr s i \<noteq> Qback_arr s j"
            using inv_sys unfolding system_invariant_def sI10_Qback_Unique_Vals_def by blast
          hence "Qback_arr s k = BOT \<or> Qback_arr s (j_var s p) = BOT \<or> Qback_arr s k \<noteq> Qback_arr s (j_var s p)"
            using k_neq by blast
          thus False using qback_k qback_p a_not_bot by simp
        qed
        
        thus False using `Q_arr s k = a` qarr_p a_not_bot by simp
      qed
    qed
  qed

  (* ========================================================================= *)
  (* final assembly: Combine the three facts and let blast handle the remaining Model-level prefix mappings *)
  (* ========================================================================= *)
  show ?thesis
    unfolding hI15_Deq_Result_Exclusivity_def
    using part1 part2 part3 by blast
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI16_BO_BT_No_HB (goal_cases ) *)
(* ========================================================================= *)
lemma hI16_BO_BT_No_HB_D4_step:
  assumes inv_hI16_BO_BT_No_HB: "hI16_BO_BT_No_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and set_bo_stable: "SetBO s' = SetBO s"
    and set_bt_stable: "SetBT s' = SetBT s"
  shows "hI16_BO_BT_No_HB s'"
  (* 1. enter the proof context before unfolding the goal *)
proof (unfold hI16_BO_BT_No_HB_def Let_def, intro allI impI, goal_cases)
  (* 2. Use goal_cases to bind a, b, and the corresponding assumptions *)
  case (1 a b)
  (* Read a_BO and b_BT directly from case 1 so that they match the goal variables exactly *)
  hence a_BO: "a \<in> SetBO s'" and b_BT: "b \<in> SetBT s'" by simp_all

  (* 3. use the stability premises to transport the facts back to the old state *)
  have a_BO_s: "a \<in> SetBO s" using a_BO set_bo_stable by simp
  have b_BT_s: "b \<in> SetBT s" using b_BT set_bt_stable by simp

  (* 4. Happens-Before equivalence derivation *)
  have HB_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
    unfolding HB_EnqRetCall_def HB_Act_def
  proof
    assume "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s')"
    hence "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret])"
      using his_append by simp
    thus "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s)"
      using HB_enq_stable_deq_append by blast
  next
    assume "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s)"
    hence "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret])"
      by (metis HB_enq_stable_deq_append)
    thus "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s')"
      using his_append by simp
  qed

  (* 5. extract the old-state conclusion *)
  have "\<not> HB_EnqRetCall s a b"
    using inv_hI16_BO_BT_No_HB a_BO_s b_BT_s unfolding hI16_BO_BT_No_HB_def Let_def by blast

  (* 6. Use ?case in the final show command for robust variable alignment *)
  show ?case 
    using `\<not> HB_EnqRetCall s a b` HB_eq by simp
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI17_BT_BT_No_HB  *)
(* ========================================================================= *)
lemma hI17_BT_BT_No_HB_D4_step:
  assumes inv_hI17_BT_BT_No_HB: "hI17_BT_BT_No_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and set_bt_stable: "SetBT s' = SetBT s"
  shows "hI17_BT_BT_No_HB s'"
proof (unfold hI17_BT_BT_No_HB_def Let_def, intro allI impI, goal_cases)
  (* Use goal_cases to fix a and b from the target and keep the types aligned *)
  case (1 a b)
  hence a_BT: "a \<in> SetBT s'" and b_BT: "b \<in> SetBT s'" by simp_all

  (* 1. transport the set-membership facts *)
  have a_BT_s: "a \<in> SetBT s" using a_BT set_bt_stable by simp
  have b_BT_s: "b \<in> SetBT s" using b_BT set_bt_stable by simp

  (* 2. Happens-Before prove the required equivalence, including the existential witnesses *)
  have HB_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
    unfolding HB_EnqRetCall_def HB_Act_def
  proof
    (* Forward direction: s' -> s *)
    assume "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s')"
    hence "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret])"
      using his_append by simp
    thus "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s)"
      using HB_enq_stable_deq_append by blast
  next
    (* Backward direction: s -> s' *)
    assume "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s)"
    hence "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret])"
      by (metis HB_enq_stable_deq_append)
    thus "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) (his_seq s')"
      using his_append by simp
  qed

  (* 3. extract the old-state conclusion and close the goal *)
  have "\<not> HB_EnqRetCall s a b"
    using inv_hI17_BT_BT_No_HB a_BT_s b_BT_s unfolding hI17_BT_BT_No_HB_def Let_def by blast
    
  show ?case 
    using `\<not> HB_EnqRetCall s a b` HB_eq by simp
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI18_Idx_Order_No_Rev_HB ( - HB ) *)
(* ========================================================================= *)
lemma hI18_Idx_Order_No_Rev_HB_D4_step:
  assumes inv_hI18_Idx_Order_No_Rev_HB: "hI18_Idx_Order_No_Rev_HB s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and idx_stable: "\<And>x. Idx s' x = Idx s x"
    and inq_stable: "\<And>x. InQBack s' x = InQBack s x"
    and atidx_stable: "\<And>i. AtIdx s' i = AtIdx s i"
  shows "hI18_Idx_Order_No_Rev_HB s'"
proof (unfold hI18_Idx_Order_No_Rev_HB_def Let_def, intro allI impI, goal_cases)
  case (1 a b)
  
  (* --- Key revision: prove the HB equivalence for arbitrary x and y --- *)
  have HB_eq: "\<And>x y. HB_EnqRetCall s' x y = HB_EnqRetCall s x y"
  proof -
    fix x y
    show "HB_EnqRetCall s' x y = HB_EnqRetCall s x y"
      unfolding HB_EnqRetCall_def HB_Act_def
    proof
      assume "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq x p1 sn1) (mk_op enq y p2 sn2) (his_seq s')"
      thus "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq x p1 sn1) (mk_op enq y p2 sn2) (his_seq s)"
        using his_append HB_enq_stable_deq_append by blast
    next
      assume "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq x p1 sn1) (mk_op enq y p2 sn2) (his_seq s)"
      thus "\<exists>p1 p2 sn1 sn2. happens_before (mk_op enq x p1 sn1) (mk_op enq y p2 sn2) (his_seq s')"
        using his_append HB_enq_stable_deq_append by (metis)
    qed
  qed

  (* 3. Main argument: use index stability and InQ stability to map the s' facts back to s *)
  (* Assumption 1 here bundles InQBack s' a, InQBack s' b, and Idx s' a < Idx s' b *)
  hence stable_pre: "InQBack s a \<and> InQBack s b \<and> Idx s a < Idx s b"
    using 1 idx_stable inq_stable by simp

  (* extract from the old-state invariant \<not> HB_EnqRetCall s b a *)
  have "\<not> HB_EnqRetCall s b a"
    using inv_hI18_Idx_Order_No_Rev_HB stable_pre unfolding hI18_Idx_Order_No_Rev_HB_def Let_def by blast

  (* 4. combine the result with HB_eq (instantiated at b and a) to close the goal *)
  show ?case
    using `\<not> HB_EnqRetCall s b a` HB_eq 1
    by (simp add: HB_eq) 
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI19_Scanner_Catches_Later_Enq  *)
(* ========================================================================= *)
lemma hI19_Scanner_Catches_Later_Enq_D4_step:
  assumes inv_hI19_Scanner_Catches_Later_Enq: "hI19_Scanner_Catches_Later_Enq s"
    and inv_sys: "system_invariant s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and pc_eq: "program_counter s' = (program_counter s)(p := ''L0'')"
    and other_vars: "\<And>q. q \<noteq> p \<Longrightarrow> (program_counter s' q = program_counter s q \<and> 
                                   j_var s' q = j_var s q \<and> 
                                   l_var s' q = l_var s q \<and> 
                                   s_var s' q = s_var s q)"
    and idx_stable: "\<And>x. Idx s' x = Idx s x"
    and type_stable: "\<And>x. TypeB s' x = TypeB s x"
    and inqback_stable: "\<And>x. InQBack s' x = InQBack s x"  (* 💥 add both transport premises explicitly *)
    and hb_stable: "\<And>a b. HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
  shows "hI19_Scanner_Catches_Later_Enq s'"
proof (unfold hI19_Scanner_Catches_Later_Enq_def, intro allI impI, goal_cases)
  case (1 a b)
  
  (* 1. extract the two key preconditions from the target *)
  from 1 have inqa': "InQBack s' a" by blast
  from 1 have inqb': "InQBack s' b" by blast
  from 1 have tba': "TypeB s' a" by blast
  from 1 have tbb': "TypeB s' b" by blast
  from 1 have idx_ab': "Idx s' a < Idx s' b" by blast
  
  (* 2. obtain the pending scanner q that is currently in D3 *)
  from 1 obtain q where q_props: 
    "HasPendingDeq s' q" 
    "program_counter s' q = ''D3''"
    "Idx s' a < j_var s' q" 
    "j_var s' q \<le> Idx s' b" 
    "Idx s' b < l_var s' q"
    by blast

  (* 3. separate the current D4 step of p from the scanner q: q stays in D3 while p moves to L0 *)
  have q_neq_p: "q \<noteq> p"
  proof
    assume "q = p"
    with q_props(2) have "program_counter s' p = ''D3''" by simp
    moreover have "program_counter s' p = ''L0''" using pc_eq by simp
    ultimately show False by simp
  qed

  (* 4. transport all required concrete facts back to the old state s *)
  
  (* a. transport the concrete facts for the old elements a and b *)
  have inqa_s: "InQBack s a" using inqa' inqback_stable by simp
  have inqb_s: "InQBack s b" using inqb' inqback_stable by simp
  have tba_s: "TypeB s a" using tba' type_stable by simp
  have tbb_s: "TypeB s b" using tbb' type_stable by simp
  have idx_ab_s: "Idx s a < Idx s b" using idx_ab' idx_stable by simp
  
  (* b. transport the scanner facts for q *)
  have pc_q_s: "program_counter s q = ''D3''" using q_props(2) other_vars q_neq_p by auto
  have j_var_eq: "j_var s' q = j_var s q" using other_vars q_neq_p by simp
  have l_var_eq: "l_var s' q = l_var s q" using other_vars q_neq_p by simp
  
  have bound1: "Idx s a < j_var s q" using q_props(3) idx_stable j_var_eq by simp
  have bound2: "j_var s q \<le> Idx s b" using q_props(4) idx_stable j_var_eq by simp
  have bound3: "Idx s b < l_var s q" using q_props(5) idx_stable l_var_eq by simp
  
  (* c. derive HasPendingDeq: the D4 step appends a return for p and does not affect the pending status of q \<noteq> p *)
  have pend_q_s: "HasPendingDeq s q"
  proof -
    have s_var_eq: "s_var s' q = s_var s q" using other_vars q_neq_p by simp
    have "HasPendingDeq s' q = HasPendingDeq s q"
      unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
      using his_append s_var_eq q_neq_p by (auto simp: mk_act_def act_pid_def)
    thus ?thesis using q_props(1) by simp
  qed

  (* 5. invoke the old-state invariant hI19_Scanner_Catches_Later_Enq, supply all required premises *)
  have "\<not> HB_EnqRetCall s a b"
    using inv_hI19_Scanner_Catches_Later_Enq inqa_s inqb_s tba_s tbb_s idx_ab_s
          pend_q_s pc_q_s bound1 bound2 bound3
    unfolding hI19_Scanner_Catches_Later_Enq_def by blast

  (* 6. close the final goal in the new state *)
  then show "\<not> HB_EnqRetCall s' a b" using hb_stable by simp
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI21_Ret_Implies_Call (if-else ) *)
(* ========================================================================= *)
lemma hI21_Ret_Implies_Call_D4_step:
  assumes inv_hI21_Ret_Implies_Call: "hI21_Ret_Implies_Call s"
    and inv_hI12_D_Phase_Pending_Deq: "hI12_D_Phase_Pending_Deq s"
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and pc_D4: "program_counter s p = ''D4''"
  shows "hI21_Ret_Implies_Call s'"
proof (unfold hI21_Ret_Implies_Call_def Let_def, intro allI impI, goal_cases)
  case (1 k)
  
  have k_bounds: "k < length (his_seq s')" using 1 by simp
  have k_is_ret: "act_cr (his_seq s' ! k) = ret" using 1 by simp

  have len_s': "length (his_seq s') = length (his_seq s) + 1"
    using his_append by simp

  consider (old_event) "k < length (his_seq s)" | (new_event) "k = length (his_seq s)"
    using k_bounds len_s' by linarith
  
  then show ?case
  proof cases
    case old_event
    (* --- Branch 1: old event --- *)
    have k_is_ret_s: "act_cr (his_seq s ! k) = ret" 
      using old_event k_is_ret his_append by (simp add: nth_append)
    
    (* recover the correct if-else branch during extraction *)
    from inv_hI21_Ret_Implies_Call[unfolded hI21_Ret_Implies_Call_def Let_def, rule_format, OF old_event k_is_ret_s]
    obtain tm where tm_props: 
      "tm < k" 
      "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k)"
      "act_name (his_seq s ! tm) = act_name (his_seq s ! k)" 
      "act_cr (his_seq s ! tm) = call"
      "(if act_name (his_seq s ! k) = enq 
        then act_val (his_seq s ! tm) = act_val (his_seq s ! k) 
        else act_val (his_seq s ! tm) = BOT)" 
      by blast
      
    show ?thesis 
    proof -
      have "his_seq s' ! tm = his_seq s ! tm" 
        using tm_props(1) old_event his_append by (simp add: nth_append)
      moreover have "his_seq s' ! k = his_seq s ! k"
        using old_event his_append by (simp add: nth_append)
      ultimately show ?thesis
        using tm_props by auto
    qed

  next
    case new_event
    (* --- Branch 2: newly appended dequeue return --- *)
    have new_elm: "his_seq s' ! k = mk_act deq (x_var s p) p (s_var s p) ret"
      using new_event his_append by (simp add: nth_append)

    have pending_p: "HasPendingDeq s p"
      using inv_hI12_D_Phase_Pending_Deq pc_D4 unfolding hI12_D_Phase_Pending_Deq_def by auto

    have "mk_act deq BOT p (s_var s p) call \<in> set (his_seq s)"
      using pending_p 
      unfolding HasPendingDeq_def Let_def DeqCallInHis_def 
                mk_act_def act_pid_def act_name_def act_cr_def act_val_def act_ssn_def
      by force

    then obtain tm where tm_props: 
      "tm < length (his_seq s)" 
      "his_seq s ! tm = mk_act deq BOT p (s_var s p) call"
      unfolding in_set_conv_nth by blast

    have tm_attrs:
          "act_pid (his_seq s ! tm) = p"
          "act_name (his_seq s ! tm) = deq"
          "act_cr (his_seq s ! tm) = call"
          "act_val (his_seq s ! tm) = BOT"
      using tm_props(2) by (simp_all add: mk_act_def act_pid_def act_name_def act_cr_def act_val_def)

    show ?thesis 
    proof -
      have "tm < k" using tm_props(1) new_event by simp
      moreover have "his_seq s' ! tm = his_seq s ! tm"
        using tm_props(1) his_append by (simp add: nth_append)
      ultimately show ?thesis 
        using tm_attrs new_event new_elm his_append 
        (* Here the simplifier automatically selects the else-branch and matches BOT = BOT *)
        by (auto simp: mk_act_def nth_append act_pid_def act_name_def act_cr_def act_val_def)
    qed
  qed
qed



(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI22_Deq_Local_Pattern ( D4 ) *)
(* ========================================================================= *)
lemma hI22_Deq_Local_Pattern_D4_step:
  assumes inv_hI22_Deq_Local_Pattern: "hI22_Deq_Local_Pattern s"
    and inv_hI12_D_Phase_Pending_Deq: "hI12_D_Phase_Pending_Deq s"
    and inv_hI15_Deq_Result_Exclusivity: "hI15_Deq_Result_Exclusivity s"
    and inv_hI26_DeqRet_D4_Mutex: "hI26_DeqRet_D4_Mutex s"   (* New point: handle same-process exclusion explicitly *)
    and his_append: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    and pc_D4: "program_counter s p = ''D4''"
    and last_call_fact: "last (filter (\<lambda>e. act_pid e = p) (his_seq s)) = mk_act deq BOT p (s_var s p) call"
    and step_facts: (* use the fact that D4 clears the local variables *)
        "(\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q)"
        "x_var s' p = BOT"
        "(\<And>k. Q_arr s' k = Q_arr s k)"
        "(\<And>k. Qback_arr s' k = Qback_arr s k)"
        "(\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q)"   (* Key point: add the fact q \<noteq> p *)
  shows "hI22_Deq_Local_Pattern s'"
proof (unfold hI22_Deq_Local_Pattern_def Let_def, intro allI impI, goal_cases)
  case (1 q v sn)
  
  have cond: "(\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = v \<and> (\<forall>q'. x_var s' q' \<noteq> v)) \<and> DeqRetInHis s' q v sn"
    using 1 by simp
    
  then obtain k t where t_props:
    "Q_arr s' k = BOT" "Qback_arr s' k = v" "\<forall>q'. x_var s' q' \<noteq> v"
    "t < length (his_seq s')"
    "act_pid (his_seq s' ! t) = q"
    "act_name (his_seq s' ! t) = deq"
    "act_cr (his_seq s' ! t) = ret"
    "act_val (his_seq s' ! t) = v"
    "act_ssn (his_seq s' ! t) = sn"
  proof -
    have "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = v \<and> (\<forall>q'. x_var s' q' \<noteq> v)"
     and "\<exists>e\<in>set (his_seq s'). act_pid e = q \<and> act_ssn e = sn \<and> act_name e = deq \<and> act_cr e = ret \<and> act_val e = v"
      using cond unfolding DeqRetInHis_def Let_def by auto
    then obtain k e where k_e:
      "Q_arr s' k = BOT" "Qback_arr s' k = v" "\<forall>q'. x_var s' q' \<noteq> v"
      "e \<in> set (his_seq s')"
      "act_pid e = q" "act_ssn e = sn" "act_name e = deq" "act_cr e = ret" "act_val e = v"
      by blast
    from k_e(4) obtain idx where "idx < length (his_seq s')" "his_seq s' ! idx = e"
      unfolding in_set_conv_nth by blast
    thus ?thesis using k_e that by force
  qed

  have Phys: "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = v" 
    using t_props(1,2) step_facts by auto

  have len_eq: "length (his_seq s') = length (his_seq s) + 1"
    using his_append by simp

  consider (old_t) "t < length (his_seq s)" | (new_t) "t = length (his_seq s)"
    using t_props(4) len_eq by linarith
  
  hence ret_split: "DeqRetInHis s q v sn \<or> (q = p \<and> v = x_var s p \<and> sn = s_var s p)"
  proof cases
    case old_t
    hence "DeqRetInHis s q v sn"
      using t_props his_append step_facts
      unfolding DeqRetInHis_def Let_def
      by (auto simp: nth_append)
    thus ?thesis ..
  next
    case new_t
    hence "q = p \<and> v = x_var s p \<and> sn = s_var s p"
      using t_props his_append step_facts
      by (auto simp: nth_append mk_act_def act_pid_def act_val_def act_ssn_def)
    thus ?thesis ..
  qed

  from ret_split consider (old_ret) "DeqRetInHis s q v sn" | (new_ret) "q = p \<and> v = x_var s p \<and> sn = s_var s p" by blast
  then show ?case
  proof cases
    case old_ret
    have x_var_s: "\<forall>q'. x_var s q' \<noteq> v"
    proof (intro allI)
      fix q'
      show "x_var s q' \<noteq> v"
      proof (cases "q' = p")
        case True
        (* 1. derive v \<noteq> BOT and thus conclude v \<in> Val *)
        have "x_var s' p \<noteq> v" using t_props(3) by blast
        moreover have "x_var s' p = BOT" using step_facts(2) by simp
        ultimately have "v \<noteq> BOT" by simp
        hence v_val: "v \<in> Val" unfolding Val_def BOT_def by simp
          
        (* 2. split on whether the process q that produced the old dequeue record equals p *)
        show ?thesis 
        proof (cases "q = p")
          case True_q: True
          (* Same-process case: use hI26_DeqRet_D4_Mutex *)
          from inv_hI26_DeqRet_D4_Mutex old_ret pc_D4 v_val True_q show ?thesis
            unfolding hI26_DeqRet_D4_Mutex_def DeqRetInHis_def Let_def
            using True by blast 
        next
          case False_q: False
          (* Different-process case: use hI15_Deq_Result_Exclusivity *)
          from inv_hI15_Deq_Result_Exclusivity old_ret pc_D4 v_val False_q show ?thesis
            unfolding hI15_Deq_Result_Exclusivity_def DeqRetInHis_def Let_def
            using True by blast
        qed
      next
        case False
        hence "x_var s q' = x_var s' q'" using step_facts by simp
        thus ?thesis using t_props(3)
          by simp 
      qed
    qed

    from inv_hI22_Deq_Local_Pattern[unfolded hI22_Deq_Local_Pattern_def Let_def, rule_format] old_ret Phys x_var_s
    have "\<exists>i < length (filter (\<lambda>e. act_pid e = q) (his_seq s)).
            filter (\<lambda>e. act_pid e = q) (his_seq s) ! i = mk_act deq v q sn ret \<and>
            0 < i \<and> filter (\<lambda>e. act_pid e = q) (his_seq s) ! (i - 1) = mk_act deq BOT q sn call"
      by blast

    then obtain i where i_props:
      "i < length (filter (\<lambda>e. act_pid e = q) (his_seq s))"
      "filter (\<lambda>e. act_pid e = q) (his_seq s) ! i = mk_act deq v q sn ret"
      "0 < i"
      "filter (\<lambda>e. act_pid e = q) (his_seq s) ! (i - 1) = mk_act deq BOT q sn call"
      by blast

    let ?f = "\<lambda>e. act_pid e = q"
    show ?thesis
    proof -
      have filter_ext: "take (length (filter ?f (his_seq s))) (filter ?f (his_seq s')) = filter ?f (his_seq s)"
        using his_append by simp
      
      have "i < length (filter ?f (his_seq s'))"
        using i_props(1) his_append by simp
      moreover have "filter ?f (his_seq s') ! i = mk_act deq v q sn ret"
        using i_props(1,2) filter_ext step_facts by (metis nth_take)
      moreover have "filter ?f (his_seq s') ! (i - 1) = mk_act deq BOT q sn call"
      proof -
        have "i - 1 < length (filter ?f (his_seq s))" using i_props(1,3) by simp
        thus ?thesis using i_props(4) filter_ext step_facts by (metis nth_take)
      qed
      ultimately show ?thesis using i_props(3) by blast
    qed

  next
    case new_ret
    let ?q_his = "filter (\<lambda>e. act_pid e = q) (his_seq s)"
    let ?q_his' = "filter (\<lambda>e. act_pid e = q) (his_seq s')"
    
    have q_his'_def: "?q_his' = ?q_his @ [mk_act deq v q sn ret]"
      using new_ret his_append by (auto simp: mk_act_def act_pid_def)
    
    have pending_p: "HasPendingDeq s p"
      using inv_hI12_D_Phase_Pending_Deq pc_D4 unfolding hI12_D_Phase_Pending_Deq_def by auto
    have call_in_set: "mk_act deq BOT p (s_var s p) call \<in> set (his_seq s)"
      using pending_p unfolding HasPendingDeq_def Let_def DeqCallInHis_def
                mk_act_def act_pid_def act_name_def act_cr_def act_val_def act_ssn_def
      by force
    have hI12_D_Phase_Pending_Deq_not_empty: "?q_his \<noteq> []"
    proof -
      (* 1. Use simp to calculate the tuple fields and identify p as the process id *)
      have "act_pid (mk_act deq BOT p (s_var s p) call) = p"
        by (simp add: mk_act_def act_pid_def)
        
      (* 2. Use blast only for the set/existential reasoning, without low-level tuple destructuring *)
      hence "\<exists>e \<in> set (his_seq s). act_pid e = p"
        using call_in_set by blast
        
      (* 3. Combine filter_empty_conv with q = p in the new-event branch to close the goal *)
      thus ?thesis
        using new_ret by (simp add: filter_empty_conv)
    qed
      
    have hI12_D_Phase_Pending_Deq_last: "last ?q_his = mk_act deq BOT q sn call"
      using last_call_fact new_ret by simp
    
    let ?i = "length ?q_his"
    show ?thesis
    proof -
      have "?i < length ?q_his'" using q_his'_def by simp
      moreover have "?q_his' ! ?i = mk_act deq v q sn ret" 
        using q_his'_def step_facts by (simp add: nth_append)
      moreover have "0 < ?i" using hI12_D_Phase_Pending_Deq_not_empty by simp 
      moreover have "?q_his' ! (?i - 1) = mk_act deq BOT q sn call"
        using q_his'_def hI12_D_Phase_Pending_Deq_last last_conv_nth[of ?q_his] step_facts
        by (simp add: hI12_D_Phase_Pending_Deq_not_empty nth_append_left) 
      ultimately show ?thesis by blast
    qed
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI23_Deq_Call_Ret_Balanced (local dequeue consistency) *)
(* 💡 Generalized version: avoid dependence on the concrete arity of mk_act so that later model refactorings do not break the proof *)
(* ========================================================================= *)
lemma hI23_Deq_Call_Ret_Balanced_D4_step:
  assumes inv_hI23_Deq_Call_Ret_Balanced: "hI23_Deq_Call_Ret_Balanced s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_props: "act_pid e_ret = p" "act_name e_ret = deq" "act_cr e_ret = ret"
    and p_his_not_empty: "filter (\<lambda>e. act_pid e = p) (his_seq s) \<noteq> []"
    and p_his_last: "act_name (last (filter (\<lambda>e. act_pid e = p) (his_seq s))) = deq"
                    "act_cr (last (filter (\<lambda>e. act_pid e = p) (his_seq s))) = call"
  shows "hI23_Deq_Call_Ret_Balanced s'"
proof (unfold hI23_Deq_Call_Ret_Balanced_def Let_def, intro allI impI)
  fix q k
  assume k_bounds: "k \<le> length (his_seq s')"

  let ?f_q    = "\<lambda>e. act_pid e = q"
  let ?f_call = "\<lambda>e. act_name e = deq \<and> act_cr e = call"
  let ?f_ret  = "\<lambda>e. act_name e = deq \<and> act_cr e = ret"

  have len_s': "length (his_seq s') = length (his_seq s) + 1"
    using his_append by simp

  consider (old_k) "k \<le> length (his_seq s)" | (new_k) "k = length (his_seq s')"
    using k_bounds len_s' by linarith
    
  then show "length (filter ?f_ret (filter ?f_q (take k (his_seq s'))))
             \<le> length (filter ?f_call (filter ?f_q (take k (his_seq s')))) \<and>
             length (filter ?f_call (filter ?f_q (take k (his_seq s')))) -
             length (filter ?f_ret (filter ?f_q (take k (his_seq s')))) \<le> 1 \<and>
             (filter ?f_q (take k (his_seq s')) \<noteq> [] \<and>
              act_cr (last (filter ?f_q (take k (his_seq s')))) = call \<and>
              act_name (last (filter ?f_q (take k (his_seq s')))) \<noteq> deq \<longrightarrow>
              length (filter ?f_call (filter ?f_q (take k (his_seq s')))) =
              length (filter ?f_ret (filter ?f_q (take k (his_seq s')))))"
  proof cases
    case old_k
    have take_eq: "take k (his_seq s') = take k (his_seq s)"
      using old_k his_append by simp
      
    have old_prop: "length (filter ?f_ret (filter ?f_q (take k (his_seq s))))
          \<le> length (filter ?f_call (filter ?f_q (take k (his_seq s)))) \<and>
          length (filter ?f_call (filter ?f_q (take k (his_seq s)))) -
          length (filter ?f_ret (filter ?f_q (take k (his_seq s)))) \<le> 1 \<and>
          (filter ?f_q (take k (his_seq s)) \<noteq> [] \<and>
           act_cr (last (filter ?f_q (take k (his_seq s)))) = call \<and>
           act_name (last (filter ?f_q (take k (his_seq s)))) \<noteq> deq \<longrightarrow>
           length (filter ?f_call (filter ?f_q (take k (his_seq s)))) =
           length (filter ?f_ret (filter ?f_q (take k (his_seq s)))))"
      using inv_hI23_Deq_Call_Ret_Balanced old_k unfolding hI23_Deq_Call_Ret_Balanced_def Let_def by blast
      
    thus ?thesis unfolding take_eq by simp
  next
    case new_k
    have take_all: "take k (his_seq s') = his_seq s'"
      using new_k by simp
      
    consider (other_proc) "q \<noteq> p" | (curr_proc) "q = p" by blast
    then show ?thesis
    proof cases
      case other_proc
      have filter_eq: "filter ?f_q (his_seq s') = filter ?f_q (his_seq s)"
        using his_append other_proc e_ret_props by simp
        
      have old_prop: "length (filter ?f_ret (filter ?f_q (take (length (his_seq s)) (his_seq s))))
          \<le> length (filter ?f_call (filter ?f_q (take (length (his_seq s)) (his_seq s)))) \<and>
          length (filter ?f_call (filter ?f_q (take (length (his_seq s)) (his_seq s)))) -
          length (filter ?f_ret (filter ?f_q (take (length (his_seq s)) (his_seq s)))) \<le> 1 \<and>
          (filter ?f_q (take (length (his_seq s)) (his_seq s)) \<noteq> [] \<and>
           act_cr (last (filter ?f_q (take (length (his_seq s)) (his_seq s)))) = call \<and>
           act_name (last (filter ?f_q (take (length (his_seq s)) (his_seq s)))) \<noteq> deq \<longrightarrow>
           length (filter ?f_call (filter ?f_q (take (length (his_seq s)) (his_seq s)))) =
           length (filter ?f_ret (filter ?f_q (take (length (his_seq s)) (his_seq s)))))"
        using inv_hI23_Deq_Call_Ret_Balanced unfolding hI23_Deq_Call_Ret_Balanced_def Let_def by blast
        
      have old_prop_simp: "length (filter ?f_ret (filter ?f_q (his_seq s)))
          \<le> length (filter ?f_call (filter ?f_q (his_seq s))) \<and>
          length (filter ?f_call (filter ?f_q (his_seq s))) -
          length (filter ?f_ret (filter ?f_q (his_seq s))) \<le> 1 \<and>
          (filter ?f_q (his_seq s) \<noteq> [] \<and>
           act_cr (last (filter ?f_q (his_seq s))) = call \<and>
           act_name (last (filter ?f_q (his_seq s))) \<noteq> deq \<longrightarrow>
           length (filter ?f_call (filter ?f_q (his_seq s))) =
           length (filter ?f_ret (filter ?f_q (his_seq s))))"
        using old_prop by simp

      show ?thesis
        unfolding take_all filter_eq
        using old_prop_simp by simp
    next
      case curr_proc
      let ?old_q_his = "filter ?f_q (his_seq s)"
      let ?new_q_his = "filter ?f_q (his_seq s')"

      have new_q_his_eq: "?new_q_his = ?old_q_his @ [e_ret]"
        using his_append curr_proc e_ret_props by simp

      have count_calls: "length (filter ?f_call ?new_q_his) = length (filter ?f_call ?old_q_his)"
        using new_q_his_eq e_ret_props by simp
      have count_rets: "length (filter ?f_ret ?new_q_his) = length (filter ?f_ret ?old_q_his) + 1"
        using new_q_his_eq e_ret_props by simp

      have pending_deq: "length (filter ?f_call ?old_q_his) - length (filter ?f_ret ?old_q_his) = 1"
      proof -
        have p_his_props: "?old_q_his \<noteq> []" 
          using p_his_not_empty curr_proc by simp
          
        have split_his: "?old_q_his = butlast ?old_q_his @ [last ?old_q_his]"
          using p_his_props by (metis append_butlast_last_id)

        have c_old: "length (filter ?f_call ?old_q_his) = length (filter ?f_call (butlast ?old_q_his)) + 1"
        proof -
          have "length (filter ?f_call ?old_q_his) = length (filter ?f_call (butlast ?old_q_his @ [last ?old_q_his]))"
            by (subst split_his) (rule refl)
          moreover have "act_name (last ?old_q_his) = deq \<and> act_cr (last ?old_q_his) = call"
            using p_his_last curr_proc by simp
          ultimately show ?thesis by simp
        qed

        have r_old: "length (filter ?f_ret ?old_q_his) = length (filter ?f_ret (butlast ?old_q_his))"
        proof -
          have "length (filter ?f_ret ?old_q_his) = length (filter ?f_ret (butlast ?old_q_his @ [last ?old_q_his]))"
            by (subst split_his) (rule refl)
          moreover have "act_name (last ?old_q_his) = deq \<and> act_cr (last ?old_q_his) = call"
            using p_his_last curr_proc by simp
          ultimately show ?thesis by simp
        qed

        obtain idx where idx_props: 
          "idx \<le> length (his_seq s)" 
          "filter ?f_q (take idx (his_seq s)) = butlast ?old_q_his"
          using filter_butlast_take[OF p_his_props] by blast

        have hI23_Deq_Call_Ret_Balanced_idx: "length (filter ?f_ret (filter ?f_q (take idx (his_seq s))))
              \<le> length (filter ?f_call (filter ?f_q (take idx (his_seq s))))"
          using inv_hI23_Deq_Call_Ret_Balanced idx_props(1) curr_proc unfolding hI23_Deq_Call_Ret_Balanced_def Let_def by blast
          
        have butlast_le: "length (filter ?f_ret (butlast ?old_q_his)) \<le> length (filter ?f_call (butlast ?old_q_his))"
          using hI23_Deq_Call_Ret_Balanced_idx idx_props(2) by simp

        have hI23_Deq_Call_Ret_Balanced_full: "length (filter ?f_call (filter ?f_q (take (length (his_seq s)) (his_seq s)))) -
              length (filter ?f_ret (filter ?f_q (take (length (his_seq s)) (his_seq s)))) \<le> 1"
          using inv_hI23_Deq_Call_Ret_Balanced curr_proc unfolding hI23_Deq_Call_Ret_Balanced_def Let_def by blast
          
        have diff_le_1: "length (filter ?f_call ?old_q_his) - length (filter ?f_ret ?old_q_his) \<le> 1"
          using hI23_Deq_Call_Ret_Balanced_full by simp
          
        show ?thesis using c_old r_old butlast_le diff_le_1 by linarith
      qed

      have hI23_Deq_Call_Ret_Balanced_full_R_le_C: "length (filter ?f_ret (filter ?f_q (take (length (his_seq s)) (his_seq s))))
             \<le> length (filter ?f_call (filter ?f_q (take (length (his_seq s)) (his_seq s))))"
        using inv_hI23_Deq_Call_Ret_Balanced curr_proc unfolding hI23_Deq_Call_Ret_Balanced_def Let_def by blast

      have old_R_le_C: "length (filter ?f_ret ?old_q_his) \<le> length (filter ?f_call ?old_q_his)"
        using hI23_Deq_Call_Ret_Balanced_full_R_le_C by simp
        
      have last_is_ret: "act_cr (last ?new_q_his) = ret"
        using new_q_his_eq e_ret_props by simp

      show ?thesis
        unfolding take_all
        using count_calls count_rets pending_deq old_R_le_C last_is_ret by auto
    qed
  qed
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI24_HB_Implies_Idx_Order (core consistency fact: happens-before implies strict index monotonicity) *)
(* 💡 Generalized version: decouple from the concrete event encoding; appending a dequeue event does not affect enqueue HB facts *)
(* ========================================================================= *)
lemma hI24_HB_Implies_Idx_Order_D4_step:
  assumes inv_hI24_HB_Implies_Idx_Order: "hI24_HB_Implies_Idx_Order s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_is_deq: "act_name e_ret = deq"
    and q_arr_eq: "CState.Q_arr (fst s') = CState.Q_arr (fst s)"
  shows "hI24_HB_Implies_Idx_Order s'"
  unfolding hI24_HB_Implies_Idx_Order_def
proof (intro allI impI, goal_cases)
  (* Bind the quantified variables in the exact order used by hI24_HB_Implies_Idx_Order_def *)
  case (1 u1 u2 v1 v2 idx1 idx2 sn1 sn2)
  
  assume cond: "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1) \<and>
                CState.Q_arr (fst s') idx1 = v1 \<and>
                CState.Q_arr (fst s') idx2 = v2"

  have q1: "CState.Q_arr (fst s) idx1 = v1" using cond q_arr_eq by simp
  have q2: "CState.Q_arr (fst s) idx2 = v2" using cond q_arr_eq by simp

  have hb_s: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
  proof -
    have hb_s': "HB (his_seq s') (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
      using cond unfolding HB_Act_def by simp
      
    from hb_s' obtain k1 k2 where k_props:
      "k1 < k2" "k1 < length (his_seq s')" "k2 < length (his_seq s')"
      "act_name (his_seq s' ! k1) = enq" "act_pid (his_seq s' ! k1) = u2"
      "act_val (his_seq s' ! k1) = v2" "act_ssn (his_seq s' ! k1) = sn2" "act_cr (his_seq s' ! k1) = ret"
      "act_name (his_seq s' ! k2) = enq" "act_pid (his_seq s' ! k2) = u1"
      "act_cr (his_seq s' ! k2) = call" "act_val (his_seq s' ! k2) = v1" "act_ssn (his_seq s' ! k2) = sn1"
      unfolding HB_def Let_def mk_op_def op_name_def op_pid_def op_val_def op_ssn_def match_ret_def match_call_def
      by auto
      
    have new_idx: "length (his_seq s') = length (his_seq s) + 1"
      using his_append by simp
      
    have "k2 \<noteq> length (his_seq s)"
    proof
      assume "k2 = length (his_seq s)"
      hence "his_seq s' ! k2 = e_ret"
        using his_append by (simp add: nth_append)
      hence "act_name (his_seq s' ! k2) = deq"
        using e_ret_is_deq by simp
      thus False using k_props(9) by simp
    qed
    
    hence k2_old: "k2 < length (his_seq s)"
      using k_props(3) new_idx by linarith
    hence k1_old: "k1 < length (his_seq s)"
      using k_props(1) by linarith
      
    have eq1: "his_seq s' ! k1 = his_seq s ! k1"
      using k1_old his_append by (simp add: nth_append)
    have eq2: "his_seq s' ! k2 = his_seq s ! k2"
      using k2_old his_append by (simp add: nth_append)
      
    have all_props: "k1 < k2 \<and> k1 < length (his_seq s) \<and> k2 < length (his_seq s) \<and>
          act_name (his_seq s ! k1) = enq \<and> act_pid (his_seq s ! k1) = u2 \<and>
          act_val (his_seq s ! k1) = v2 \<and> act_ssn (his_seq s ! k1) = sn2 \<and> act_cr (his_seq s ! k1) = ret \<and>
          act_name (his_seq s ! k2) = enq \<and> act_pid (his_seq s ! k2) = u1 \<and>
          act_cr (his_seq s ! k2) = call \<and> act_val (his_seq s ! k2) = v1 \<and> act_ssn (his_seq s ! k2) = sn1"
      using k_props k1_old k2_old eq1 eq2 by simp
      
    thus ?thesis
      unfolding HB_Act_def HB_def Let_def mk_op_def op_name_def op_pid_def op_val_def op_ssn_def match_ret_def match_call_def
      by auto
  qed

  (* 2: instantiate the parameters in the matching order *)
  show "idx2 < idx1"
    using inv_hI24_HB_Implies_Idx_Order[unfolded hI24_HB_Implies_Idx_Order_def, rule_format, of u1 u2 v1 v2 idx1 idx2 sn1 sn2]
    using q1 q2 hb_s
    using hI24_HB_Implies_Idx_Order_def inv_hI24_HB_Implies_Idx_Order by blast 
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI25_Enq_Call_Ret_Balanced (single-thread atomicity of enqueue operations) *)
(* 💡 Generalized version: appending a dequeue event is harmless as long as no process changes into or out of E1~E3 *)
(* ========================================================================= *)
lemma hI25_Enq_Call_Ret_Balanced_D4_step:
  assumes inv_hI25_Enq_Call_Ret_Balanced: "hI25_Enq_Call_Ret_Balanced s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_is_deq: "act_name e_ret = deq"
    and pc_p_s: "program_counter s p = ''D4''"
    and pc_p_s': "program_counter s' p = ''L0''"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
  shows "hI25_Enq_Call_Ret_Balanced s'"
  unfolding hI25_Enq_Call_Ret_Balanced_def Let_def
proof (intro allI impI)
  fix q k
  assume k_bounds: "k \<le> length (his_seq s')"

  let ?f_enq  = "\<lambda>e. act_pid e = q \<and> act_name e = enq"
  let ?f_call = "\<lambda>e. act_cr e = call"
  let ?f_ret  = "\<lambda>e. act_cr e = ret"

  have len_s': "length (his_seq s') = length (his_seq s) + 1"
    using his_append by simp

  consider (old_k) "k \<le> length (his_seq s)" | (new_k) "k = length (his_seq s')"
    using k_bounds len_s' by linarith

  then show "length (filter ?f_ret (filter ?f_enq (take k (his_seq s'))))
             \<le> length (filter ?f_call (filter ?f_enq (take k (his_seq s')))) \<and>
             length (filter ?f_call (filter ?f_enq (take k (his_seq s')))) -
             length (filter ?f_ret (filter ?f_enq (take k (his_seq s')))) \<le> 1 \<and>
             (k = length (his_seq s') \<longrightarrow>
              (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow>
               length (filter ?f_call (filter ?f_enq (take k (his_seq s')))) -
               length (filter ?f_ret (filter ?f_enq (take k (his_seq s')))) = 1))"
  proof cases
    case old_k
    (* Branch 1: k is within the range of the old history *)
    have take_eq: "take k (his_seq s') = take k (his_seq s)"
      using old_k his_append by simp

    have not_new: "k \<noteq> length (his_seq s')"
      using old_k len_s' by simp

    have "length (filter ?f_ret (filter ?f_enq (take k (his_seq s))))
          \<le> length (filter ?f_call (filter ?f_enq (take k (his_seq s)))) \<and>
          length (filter ?f_call (filter ?f_enq (take k (his_seq s)))) -
          length (filter ?f_ret (filter ?f_enq (take k (his_seq s)))) \<le> 1"
      using inv_hI25_Enq_Call_Ret_Balanced old_k unfolding hI25_Enq_Call_Ret_Balanced_def Let_def by blast

    thus ?thesis unfolding take_eq using not_new by auto
  next
    case new_k
    (* Branch 2: k reaches the freshly appended event *)
    have take_all: "take k (his_seq s') = his_seq s'"
      using new_k by simp

    (* 🚨 Key observation: the D4 step appends a dequeue event, while the filter keeps only enqueue events, so the new event is invisible🚨 *)
    have filter_eq: "filter ?f_enq (his_seq s') = filter ?f_enq (his_seq s)"
      using his_append e_ret_is_deq by simp

    (* extract the full old-state facts carefully *)
    have old_prop: "length (filter ?f_ret (filter ?f_enq (his_seq s)))
          \<le> length (filter ?f_call (filter ?f_enq (his_seq s))) \<and>
          length (filter ?f_call (filter ?f_enq (his_seq s))) -
          length (filter ?f_ret (filter ?f_enq (his_seq s))) \<le> 1 \<and>
          (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow>
           length (filter ?f_call (filter ?f_enq (his_seq s))) -
           length (filter ?f_ret (filter ?f_enq (his_seq s))) = 1)"
    proof -
      have inst: "length (filter ?f_ret (filter ?f_enq (take (length (his_seq s)) (his_seq s))))
            \<le> length (filter ?f_call (filter ?f_enq (take (length (his_seq s)) (his_seq s)))) \<and>
            length (filter ?f_call (filter ?f_enq (take (length (his_seq s)) (his_seq s)))) -
            length (filter ?f_ret (filter ?f_enq (take (length (his_seq s)) (his_seq s)))) \<le> 1 \<and>
            (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow>
             length (filter ?f_call (filter ?f_enq (take (length (his_seq s)) (his_seq s)))) -
             length (filter ?f_ret (filter ?f_enq (take (length (his_seq s)) (his_seq s)))) = 1)"
        using inv_hI25_Enq_Call_Ret_Balanced unfolding hI25_Enq_Call_Ret_Balanced_def Let_def by blast
      thus ?thesis by simp
    qed

    (* show that this D4 step does not move any process into or out of E1~E3 *)
    have pc_eq: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
    proof (cases "q = p")
      case True
      thus ?thesis using pc_p_s pc_p_s' by auto
    next
      case False
      thus ?thesis using pc_other False by auto
    qed

    (* close the goal by straightforward substitution *)
    show ?thesis
      unfolding take_all filter_eq new_k
      using old_prop pc_eq
      using filter_eq by force 
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves hI26_DeqRet_D4_Mutex (exclusivity of dequeue returns) *)
(* 💡 Generalized version: use set reasoning to obtain the required equivalence of history-existence predicates *)
(* ========================================================================= *)
lemma hI26_DeqRet_D4_Mutex_D4_step:
  assumes inv_hI26_DeqRet_D4_Mutex: "hI26_DeqRet_D4_Mutex s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_pid: "act_pid e_ret = p"
    and pc_p_s': "program_counter s' p = ''L0''"
    and pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    and x_other: "\<And>q. q \<noteq> p \<Longrightarrow> x_var s' q = x_var s q"
  shows "hI26_DeqRet_D4_Mutex s'"
  unfolding hI26_DeqRet_D4_Mutex_def
proof (intro allI impI)
  fix q a
  assume val: "a \<in> Val"

  show "\<not> ((\<exists>sn. DeqRetInHis s' q a sn) \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a)"
  proof (cases "q = p")
    case True
    (* The current process p has left D4 and returned to L0 *)
    have "program_counter s' p = ''L0''" using pc_p_s' by simp
    thus ?thesis using True by simp
  next
    case False
    (* , *)
    have pc_q: "program_counter s' q = program_counter s q" using pc_other False by auto
    have x_q: "x_var s' q = x_var s q" using x_other False by auto

    (* , auto *)
    have deq_eq: "(\<exists>sn. DeqRetInHis s' q a sn) \<longleftrightarrow> (\<exists>sn. DeqRetInHis s q a sn)"
    proof -
      (* Proof note. *)
      have "set (his_seq s') = set (his_seq s) \<union> {e_ret}"
        using his_append by simp
        
      (* , auto e_ret ( act_pid e_ret = p \<noteq> q) *)
      thus ?thesis
        using False e_ret_pid 
        unfolding DeqRetInHis_def Let_def 
        by (auto simp: act_pid_def)
    qed

    (* Proof note. *)
    show ?thesis
      using inv_hI26_DeqRet_D4_Mutex[unfolded hI26_DeqRet_D4_Mutex_def, rule_format, of q a] val False pc_q x_q deq_eq
      using hI26_DeqRet_D4_Mutex_def inv_hI26_DeqRet_D4_Mutex by presburger
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves lI1_Op_Sets_Equivalence  *)
(* , ret \<noteq> call , *)
(* ========================================================================= *)
lemma lI1_Op_Sets_Equivalence_D4_step:
  assumes inv_lI1_Op_Sets_Equivalence: "lI1_Op_Sets_Equivalence s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_cr: "act_cr e_ret = ret"
    and oplin_eq: "OPLin s' = OPLin s"
    and setA_eq: "SetA s' = SetA s"
    and setB_eq: "SetB s' = SetB s"
  shows "lI1_Op_Sets_Equivalence s'"
proof -
  (* Step 1: 1. : call D4 *)
  (* nth set, e_ret ret, call *)
  have enq_call_eq: "\<And>p a sn. EnqCallInHis s' p a sn \<longleftrightarrow> EnqCallInHis s p a sn"
    using his_append e_ret_cr unfolding EnqCallInHis_def Let_def
    by (auto simp: nth_append act_cr_def)

  have deq_call_eq: "\<And>p sn. DeqCallInHis s' p sn \<longleftrightarrow> DeqCallInHis s p sn"
    using his_append e_ret_cr unfolding DeqCallInHis_def Let_def
    by (auto simp: nth_append act_cr_def)

  (* Step 2: 2. , , auto *)
  have eq_a_enq: "OP_A_enq s' = OP_A_enq s"
    unfolding OP_A_enq_def using setA_eq enq_call_eq by simp

  have eq_a_deq: "OP_A_deq s' = OP_A_deq s"
    unfolding OP_A_deq_def using oplin_eq setA_eq deq_call_eq by simp

  have eq_b_enq: "OP_B_enq s' = OP_B_enq s"
    unfolding OP_B_enq_def using setB_eq enq_call_eq by simp

  (* Step 3: 3. , *)
  show ?thesis
    using inv_lI1_Op_Sets_Equivalence unfolding lI1_Op_Sets_Equivalence_def
    unfolding oplin_eq eq_a_enq eq_a_deq eq_b_enq 
    by simp
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves lI3_HB_Ret_Lin_Sync  *)
(* h2_old linarith *)
(* ========================================================================= *)
lemma lI3_HB_Ret_Lin_Sync_D4_step:
  assumes inv_lI3_HB_Ret_Lin_Sync: "lI3_HB_Ret_Lin_Sync s"
    and inv_lI6_D4_Deq_Linearized: "lI6_D4_Deq_Linearized s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_props: "act_name e_ret = deq" "act_cr e_ret = ret" 
                     "act_pid e_ret = p" "act_val e_ret = v" "act_ssn e_ret = sn"
    and pc_p: "program_counter s p = ''D4''"
    and x_p: "x_var s p = v"
    and s_p: "s_var s p = sn"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI3_HB_Ret_Lin_Sync s'"
  unfolding lI3_HB_Ret_Lin_Sync_def
proof (intro conjI)
  
  (* 1. HB *)
  show "\<forall>k1 k2. k1 < length (lin_seq s') \<and> k2 < length (lin_seq s') \<and>
                HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2) \<longrightarrow> k1 < k2"
  proof (intro allI impI)
    fix k1 k2
    assume cond: "k1 < length (lin_seq s') \<and> k2 < length (lin_seq s') \<and>
                  HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2)"
    
    have hb_s: "HB_Act s (lin_seq s ! k1) (lin_seq s ! k2)"
    proof -
      have hb_raw: "HB (his_seq s') (lin_seq s ! k1) (lin_seq s ! k2)"
        using cond lin_eq unfolding HB_Act_def by simp
        
      from hb_raw[unfolded HB_def Let_def] 
      obtain h1 h2 where h_props:
        "h1 < h2" "h1 < length (his_seq s')" "h2 < length (his_seq s')"
        "match_ret (his_seq s') h1 (lin_seq s ! k1)"
        "match_call (his_seq s') h2 (lin_seq s ! k2)"
        using match_call_def by auto
        
      (* , h2 < n + 1 *)
      have h2_old: "h2 < length (his_seq s)"
      proof -
        from his_append have "length (his_seq s') = length (his_seq s) + 1" by simp
        with h_props(3) have h2_le_n: "h2 < length (his_seq s) + 1" by simp
        
        have "h2 \<noteq> length (his_seq s)"
        proof
          assume "h2 = length (his_seq s)"
          hence "his_seq s' ! h2 = e_ret" using his_append by (simp add: nth_append)
          hence "act_cr (his_seq s' ! h2) = ret" using e_ret_props by simp
          thus False using h_props(5) unfolding match_call_def by simp
        qed
        with h2_le_n show ?thesis by linarith
      qed
      
      have h1_old: "h1 < length (his_seq s)" using h_props(1) h2_old by linarith
      
      have m1: "match_ret (his_seq s) h1 (lin_seq s ! k1)"
        using h1_old his_append h_props(4) unfolding match_ret_def by (simp add: nth_append)
      have m2: "match_call (his_seq s) h2 (lin_seq s ! k2)"
        using h2_old his_append h_props(5) unfolding match_call_def by (simp add: nth_append)
        
      thus ?thesis 
        unfolding HB_Act_def HB_def Let_def
        using h1_old h2_old \<open>h1 < h2\<close> m1 m2 by blast
    qed
    
    show "k1 < k2"
      using inv_lI3_HB_Ret_Lin_Sync[unfolded lI3_HB_Ret_Lin_Sync_def] hb_s lin_eq
      using cond by auto 
  qed

  (* 2. Enq *)
  show "\<forall>p_id a sn_val. EnqRetInHis s' p_id a sn_val \<longrightarrow> 
                        (\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op enq a p_id sn_val)"
  proof (intro allI impI)
    fix p_id a sn_val
    assume "EnqRetInHis s' p_id a sn_val"
    hence "EnqRetInHis s p_id a sn_val"
      using his_append e_ret_props unfolding EnqRetInHis_def Let_def 
      by (auto simp: nth_append mk_act_def act_name_def act_cr_def)
    thus "\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op enq a p_id sn_val"
      using inv_lI3_HB_Ret_Lin_Sync[unfolded lI3_HB_Ret_Lin_Sync_def] lin_eq by auto
  qed

  (* 3. Deq *)
  show "\<forall>p_id a sn_val. DeqRetInHis s' p_id a sn_val \<longrightarrow> 
                        (\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op deq a p_id sn_val)"
  proof (intro allI impI)
    fix p_id a sn_val
    assume cond: "DeqRetInHis s' p_id a sn_val"
    
    consider (old) "DeqRetInHis s p_id a sn_val" 
           | (new) "p_id = p \<and> a = v \<and> sn_val = sn"
      using cond his_append e_ret_props 
      by (auto simp: DeqRetInHis_def Let_def nth_append mk_act_def act_pid_def act_val_def act_ssn_def act_name_def act_cr_def)
      
    then show "\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op deq a p_id sn_val"
    proof cases
      case old
      thus ?thesis using inv_lI3_HB_Ret_Lin_Sync[unfolded lI3_HB_Ret_Lin_Sync_def] lin_eq by auto
    next
      case new
      have "mk_op deq v p sn \<in> set (lin_seq s)"
        using inv_lI6_D4_Deq_Linearized pc_p x_p s_p unfolding lI6_D4_Deq_Linearized_def by blast
      then obtain k where "k < length (lin_seq s)" "lin_seq s ! k = mk_op deq v p sn"
        unfolding in_set_conv_nth by blast
      thus ?thesis using new lin_eq by auto
    qed
  qed
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves lI7_D4_Deq_Deq_HB (Pending ) *)
(* D4 ret, call, HB *)
(* ========================================================================= *)
lemma lI7_D4_Deq_Deq_HB_D4_step:
  assumes inv_lI7_D4_Deq_Deq_HB: "lI7_D4_Deq_Deq_HB s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_props: "act_name e_ret = deq" "act_cr e_ret = ret" "act_pid e_ret = curr_p"
    and pc_curr_p_s': "program_counter s' curr_p = ''L0'' "
    and pc_other: "\<And>q. q \<noteq> curr_p \<Longrightarrow> program_counter s' q = program_counter s q"
    and vars_other: "\<And>q. q \<noteq> curr_p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI7_D4_Deq_Deq_HB s'"
  unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 k1 k2 q)
  (* 1. q D4 (program_counter s' q = ''D4'') 2. L ! k2 q pending 3. L ! k1 L ! k2 HB *)
  
  have pc_q_s': "program_counter s' q = ''D4'' " using 1 by simp
  
  (* Step 1: 1. q \<noteq> curr_p  *)
  have "q \<noteq> curr_p"
  proof
    assume "q = curr_p"
    hence "program_counter s' q = ''L0'' " using pc_curr_p_s' by simp
    with pc_q_s' show False by simp
  qed

  (* Step 2: 2. : q D4, *)
  have pc_q_s: "program_counter s q = ''D4'' "
    using pc_q_s' \<open>q \<noteq> curr_p\<close> pc_other by auto
  have vars_q: "x_var s' q = x_var s q" "s_var s' q = s_var s q"
    using \<open>q \<noteq> curr_p\<close> vars_other by auto

  (* Step 3: 3. : HB (HB s' \<Longrightarrow> HB s) *)
    have hb_s: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
    proof -
      (* 1 goal_cases, HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2) *)
      have hb_raw: "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
        using 1
        by auto 
        
      (* HB_def obtain *)
      (* Step 1: 1. unfolding HB_def, unfolding match_... *)
      (* Step 2: 2. where HB_def *)
      from hb_raw[unfolded HB_def] 
      obtain h1 h2 where 
        "h1 < h2" 
        "match_ret (his_seq s') h1 (lin_seq s' ! k1)" 
        "match_call (his_seq s') h2 (lin_seq s' ! k2)"
        by blast

      (* Step 4: 4. h2 (h2 e_ret) *)
      have h2_old: "h2 < length (his_seq s)"
      proof -
        (* match_call k < length H, *)
        from \<open>match_call (his_seq s') h2 (lin_seq s' ! k2)\<close> 
        have "h2 < length (his_seq s')" unfolding match_call_def by (simp add: Let_def)
        
        from his_append have len_eq: "length (his_seq s') = length (his_seq s) + 1" by simp
        
        have "h2 \<noteq> length (his_seq s)"
        proof
          assume "h2 = length (his_seq s)"
          hence "his_seq s' ! h2 = e_ret" using his_append by (simp add: nth_append)
          hence "act_cr (his_seq s' ! h2) = ret" using e_ret_props by simp
          (* match_call act_cr call *)
          thus False using \<open>match_call (his_seq s') h2 (lin_seq s' ! k2)\<close> 
            unfolding match_call_def by (simp add: Let_def)
        qed
        with \<open>h2 < length (his_seq s')\<close> len_eq show ?thesis by linarith
      qed
      
      have h1_old: "h1 < length (his_seq s)" using \<open>h1 < h2\<close> h2_old by linarith
      
      (* Step 5: 5. s *)
      (* nth_append match_ret/call , *)
      have m1: "match_ret (his_seq s) h1 (lin_seq s ! k1)"
        using h1_old his_append \<open>match_ret (his_seq s') h1 (lin_seq s' ! k1)\<close> lin_eq
        unfolding match_ret_def by (simp add: Let_def nth_append)
        
      have m2: "match_call (his_seq s) h2 (lin_seq s ! k2)"
        using h2_old his_append \<open>match_call (his_seq s') h2 (lin_seq s' ! k2)\<close> lin_eq
        unfolding match_call_def by (simp add: Let_def nth_append)
        
      thus ?thesis 
        unfolding HB_def using \<open>h1 < h2\<close>
        using m1 by auto 
    qed

  (* Step 4: 4. lI7_D4_Deq_Deq_HB *)
  show "k1 < k2"
  proof -
    (* lI7_D4_Deq_Deq_HB_list *)
    have "lI7_D4_Deq_Deq_HB_list (lin_seq s) (his_seq s) (\<lambda>p. program_counter s p) (\<lambda>p. x_var s p) (\<lambda>p. s_var s p)"
      using inv_lI7_D4_Deq_Deq_HB unfolding lI7_D4_Deq_Deq_HB_def by simp
    
    with hb_s pc_q_s show ?thesis
      using 1 vars_q lin_eq 
      unfolding lI7_D4_Deq_Deq_HB_list_def
      by metis 
  qed
qed


(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves lI8_D3_Deq_Returned (D3 ) *)
(* goal_cases , *)
(* ========================================================================= *)
lemma lI8_D3_Deq_Returned_D4_step:
  assumes inv_lI8_D3_Deq_Returned: "lI8_D3_Deq_Returned s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_pid: "act_pid e_ret = curr_p"
    and pc_curr_p_s': "program_counter s' curr_p = ''L0'' "
    and pc_other: "\<And>q. q \<noteq> curr_p \<Longrightarrow> program_counter s' q = program_counter s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI8_D3_Deq_Returned s'"
  unfolding lI8_D3_Deq_Returned_def
  (* \<forall> \<longrightarrow> *)
  apply (intro allI impI)
proof (goal_cases)
  (* q k *)
  case (1 q k)  
  (* , *)
  have pc_q_s': "program_counter s' q = ''D3'' " using 1 by simp
  have k_cond: "k < length (lin_seq s') \<and> op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
    using 1 by simp

  show "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
  proof -
    (* Step 1: 1. q \<noteq> curr_p ( D3 \<noteq> L0) *)
    have "q \<noteq> curr_p"
    proof
      assume "q = curr_p"
      hence "program_counter s' q = ''L0'' " using pc_curr_p_s' by simp
      with pc_q_s' show False by simp
    qed

    (* Step 2: 2. : q D3 *)
    have pc_q_s: "program_counter s q = ''D3'' "
      using pc_q_s' \<open>q \<noteq> curr_p\<close> pc_other by auto

    (* 3. History equivalence: the appended event belongs to curr_p, so the predicate for q is unaffected *)
    have his_eq: "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k)) \<longleftrightarrow> 
                  DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
    proof -
      have "set (his_seq s') = set (his_seq s) \<union> {e_ret}"
        using his_append by simp
      thus ?thesis
        unfolding DeqRetInHis_def Let_def
        using \<open>q \<noteq> curr_p\<close> e_ret_pid lin_eq
        by (auto simp: act_pid_def)
    qed

    (* Step 4: 4. *)
    have "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
      using inv_lI8_D3_Deq_Returned[unfolded lI8_D3_Deq_Returned_def, rule_format, OF pc_q_s]
      using k_cond lin_eq by auto

    thus ?thesis using his_eq by simp
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves lI9_D1_D2_Deq_Returned (D1/D2 ) *)
(* D4 curr_p , q (q\<noteq>curr_p) *)
(* ========================================================================= *)
lemma lI9_D1_D2_Deq_Returned_D4_step:
  assumes inv_lI9_D1_D2_Deq_Returned: "lI9_D1_D2_Deq_Returned s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_pid: "act_pid e_ret = curr_p"
    and pc_curr_p_s': "program_counter s' curr_p = ''L0'' "
    and pc_other: "\<And>q. q \<noteq> curr_p \<Longrightarrow> program_counter s' q = program_counter s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI9_D1_D2_Deq_Returned s'"
  unfolding lI9_D1_D2_Deq_Returned_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 q k)
  (* 1. q , k 2. program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2'' 3. op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q *)
  
  have pc_q_s': "program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2'' " 
    using 1 by simp
  have k_cond: "k < length (lin_seq s') \<and> op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
    using 1 by simp

  show "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
  proof -
    (* Step 1: 1. q \<noteq> curr_p ( D1/D2 L0 ) *)
    have "q \<noteq> curr_p"
    proof
      assume "q = curr_p"
      hence "program_counter s' q = ''L0'' " using pc_curr_p_s' by simp
      with pc_q_s' show False by simp
    qed

    (* Step 2: 2. : q D1 D2 *)
    have pc_q_s: "program_counter s q = ''D1'' \<or> program_counter s q = ''D2'' "
      using pc_q_s' \<open>q \<noteq> curr_p\<close> pc_other by auto

    (* 3. History equivalence: the appended event belongs to curr_p, so the predicate for q is unaffected *)
    have his_eq: "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k)) \<longleftrightarrow> 
                  DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
    proof -
      have "set (his_seq s') = set (his_seq s) \<union> {e_ret}"
        using his_append by simp
      thus ?thesis
        unfolding DeqRetInHis_def Let_def
        using \<open>q \<noteq> curr_p\<close> e_ret_pid lin_eq
        by (auto simp: act_pid_def)
    qed

    (* Step 4: 4. *)
    have "DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
      using inv_lI9_D1_D2_Deq_Returned[unfolded lI9_D1_D2_Deq_Returned_def, rule_format, OF pc_q_s]
      using k_cond lin_eq by auto

    thus ?thesis using his_eq by simp
  qed
qed

(* ========================================================================= *)
(* Auxiliary lemma: the D4 transition step preserves lI10_D4_Enq_Deq_HB (Pending ) *)
(* D4 ret, call, HB *)
(* ========================================================================= *)
lemma lI10_D4_Enq_Deq_HB_D4_step:
  assumes inv_lI10_D4_Enq_Deq_HB: "lI10_D4_Enq_Deq_HB s"
    and his_append: "his_seq s' = his_seq s @ [e_ret]"
    and e_ret_props: "act_name e_ret = deq" "act_cr e_ret = ret" "act_pid e_ret = curr_p"
    and pc_curr_p_s': "program_counter s' curr_p = ''L0'' "
    and pc_other: "\<And>q. q \<noteq> curr_p \<Longrightarrow> program_counter s' q = program_counter s q"
    and vars_other: "\<And>q. q \<noteq> curr_p \<Longrightarrow> x_var s' q = x_var s q \<and> s_var s' q = s_var s q"
    and lin_eq: "lin_seq s' = lin_seq s"
  shows "lI10_D4_Enq_Deq_HB s'"
  unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
  apply (intro allI impI)
proof (goal_cases)
  case (1 k1 k2 q)
  (* Step 1: 1. : q D4 , k2 Pending *)
  have pc_q_s': "program_counter s' q = ''D4'' " using 1 by simp
  
  (* Step 2: 2. q \<noteq> curr_p ( p D4 L0) *)
  have "q \<noteq> curr_p"
  proof
    assume "q = curr_p"
    hence "program_counter s' q = ''L0'' " using pc_curr_p_s' by simp
    with pc_q_s' show False by simp
  qed

  (* Step 3: 3. : q D4 *)
  have pc_q_s: "program_counter s q = ''D4'' "
    using pc_q_s' \<open>q \<noteq> curr_p\<close> pc_other by auto
  have vars_q: "x_var s' q = x_var s q" "s_var s' q = s_var s q"
    using \<open>q \<noteq> curr_p\<close> vars_other by auto

  (* Step 4: 4. : HB (HB s' \<Longrightarrow> HB s) *)
  have hb_s: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
  proof -
    have hb_raw: "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
      using 1
      by blast
      
    (* HB *)
    from hb_raw[unfolded HB_def] 
    obtain h1 h2 where h_props:
      "h1 < h2" 
      "match_ret (his_seq s') h1 (lin_seq s' ! k1)"
      "match_call (his_seq s') h2 (lin_seq s' ! k2)"
      by blast

    (* h2 ( ) *)
    have h2_old: "h2 < length (his_seq s)"
    proof -
      from \<open>match_call (his_seq s') h2 (lin_seq s' ! k2)\<close> 
      have "h2 < length (his_seq s')" unfolding match_call_def by (simp add: Let_def)
      
      from his_append have len_eq: "length (his_seq s') = length (his_seq s) + 1" by simp
      
      have "h2 \<noteq> length (his_seq s)"
      proof
        assume "h2 = length (his_seq s)"
        hence "his_seq s' ! h2 = e_ret" using his_append by (simp add: nth_append)
        hence "act_cr (his_seq s' ! h2) = ret" using e_ret_props by simp
        thus False using \<open>match_call (his_seq s') h2 (lin_seq s' ! k2)\<close> 
          unfolding match_call_def by (simp add: Let_def)
      qed
      with \<open>h2 < length (his_seq s')\<close> len_eq show ?thesis by linarith
    qed
    
    have h1_old: "h1 < length (his_seq s)" using h_props(1) h2_old by linarith
    
    (* match s *)
    have m1: "match_ret (his_seq s) h1 (lin_seq s ! k1)"
      using h1_old his_append \<open>match_ret (his_seq s') h1 (lin_seq s' ! k1)\<close> lin_eq
      unfolding match_ret_def by (simp add: Let_def nth_append)
      
    have m2: "match_call (his_seq s) h2 (lin_seq s ! k2)"
      using h2_old his_append \<open>match_call (his_seq s') h2 (lin_seq s' ! k2)\<close> lin_eq
      unfolding match_call_def by (simp add: Let_def nth_append)
      
    thus ?thesis unfolding HB_def using \<open>h1 < h2\<close>
      using m1 by auto 
  qed

  (* Step 5: 5. *)
  show "k1 < k2"
  proof -
    have "lI10_D4_Enq_Deq_HB_list (lin_seq s) (his_seq s) (\<lambda>p. program_counter s p) (\<lambda>p. x_var s p) (\<lambda>p. s_var s p)"
      using inv_lI10_D4_Enq_Deq_HB unfolding lI10_D4_Enq_Deq_HB_def by simp
    
    with hb_s pc_q_s show ?thesis
      using 1 vars_q lin_eq 
      unfolding lI10_D4_Enq_Deq_HB_list_def
      by metis 
  qed
qed


lemma hI3_L0_E_Phase_Bounds_D4_step:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_D4 p s s'"
  assumes hI2_SSN_Bounds_s': "hI2_SSN_Bounds s'"
  shows "hI3_L0_E_Phase_Bounds s'"
proof -
  (* Step 0: 0. *)
  have hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s" and hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s" and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s" 
   and hI23_Deq_Call_Ret_Balanced_s: "hI23_Deq_Call_Ret_Balanced s" and hI6_SSN_Order_s: "hI6_SSN_Order s"
    using INV unfolding system_invariant_def by auto

  (* Step 1: 1. D4 , , *)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def 
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def 
                s_var_def lin_seq_def his_seq_def

  have his_eq: "his_seq s' = his_seq s @ [mk_act deq (x_var s p) p (s_var s p) ret]"
    using STEP unfolding Sys_D4_def U_D3_def U_D4_def bridge by auto
  have pc_p_new: "program_counter s' p = ''L0''"
    using STEP unfolding Sys_D4_def C_D4_def bridge by auto
  have pc_p_old: "program_counter s p = ''D4''"
    using STEP unfolding Sys_D4_def C_D4_def bridge by auto
  have V_eq: "V_var s' = V_var s"
    using STEP unfolding Sys_D4_def C_D4_def bridge by auto
  have v_eq: "v_var s' = v_var s"
    using STEP unfolding Sys_D4_def C_D4_def bridge by auto
  have qback_eq: "Qback_arr s' = Qback_arr s"
    using STEP unfolding Sys_D4_def C_D4_def bridge by auto

  have pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    using STEP unfolding Sys_D4_def C_D4_def bridge by auto
  have s_var_other: "\<And>q. q \<noteq> p \<Longrightarrow> s_var s' q = s_var s q"
    using STEP unfolding Sys_D4_def C_D4_def U_D3_def U_D4_def bridge by auto

  (* Step 2: 2. hI3_L0_E_Phase_Bounds 5 *)
  show ?thesis
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    show ?case
    proof (cases "q = p")
      case True
      have q_L0: "program_counter s' p = ''L0''" 
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
      have old_L0: "program_counter s q = ''L0''" 
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
         length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s)) + 1"
        using his_eq by (simp add: mk_act_def act_pid_def act_name_def act_cr_def)

      have "HasPendingDeq s p" using hI12_D_Phase_Pending_Deq_s pc_p_old unfolding hI12_D_Phase_Pending_Deq_def by blast
      hence "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
             length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s)) + 1"
      proof -
        let ?H = "his_seq s"
        let ?p_his = "filter (\<lambda>e. act_pid e = p) ?H"
        let ?C_len = "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) ?p_his)"
        let ?R_len = "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) ?p_his)"

        assume pend: "HasPendingDeq s p"
        then have "?p_his \<noteq> []"
          unfolding HasPendingDeq_def Let_def Model.DeqCallInHis_def
          by (metis (mono_tags, lifting) empty_filter_conv) 

        have last_call: "last ?p_his = mk_act deq BOT p (s_var s p) call"
          using pending_call_is_last[OF pend hI2_SSN_Bounds_s hI6_SSN_Order_s] by simp

        have p_his_decomp: "?p_his = butlast ?p_his @ [mk_act deq BOT p (s_var s p) call]"
          using \<open>?p_his \<noteq> []\<close> last_call by (metis append_butlast_last_id)

        (* ?p_his , his_seq s *)
        have C_eq: "?C_len = length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (butlast ?p_his)) + 1"
        proof -
          let ?pred = "\<lambda>e. act_name e = deq \<and> act_cr e = call"
          (* call *)
          have "?pred (mk_act deq BOT p (s_var s p) call)"
            by (simp add: mk_act_def act_name_def act_cr_def)
          hence "filter ?pred ?p_his = filter ?pred (butlast ?p_his) @ [mk_act deq BOT p (s_var s p) call]"
            using p_his_decomp
            by (smt (verit) filter.simps(1,2) filter_append) 
          thus ?thesis by simp
        qed

        have R_eq: "?R_len = length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (butlast ?p_his))"
        proof -
          let ?pred = "\<lambda>e. act_name e = deq \<and> act_cr e = ret"
          (* call, ret , filter *)
          have "\<not> ?pred (mk_act deq BOT p (s_var s p) call)"
            by (simp add: mk_act_def act_name_def act_cr_def)
          hence "filter ?pred ?p_his = filter ?pred (butlast ?p_his)"
            using p_his_decomp
            by (smt (verit, ccfv_threshold) filter.simps(2) filter_append
                self_append_conv) 
          thus ?thesis by simp
        qed

        have "?C_len - ?R_len \<le> 1"
          using hI23_Deq_Call_Ret_Balanced_s[unfolded hI23_Deq_Call_Ret_Balanced_def, rule_format, of p "length ?H"] 
          unfolding Let_def
          by (metis (mono_tags, lifting) hI23_Deq_Call_Ret_Balanced_def hI23_Deq_Call_Ret_Balanced_s le_refl
              take_all_iff) 

        hence butlast_le: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (butlast ?p_his)) \<le>
                           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (butlast ?p_his))"
          using C_eq R_eq by linarith

        obtain idx where idx_props:
          "idx \<le> length ?H"
          "filter (\<lambda>e. act_pid e = p) (take idx ?H) = butlast ?p_his"
          using filter_butlast_take[OF \<open>?p_his \<noteq> []\<close>] by blast

        have "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (butlast ?p_his)) \<le>
              length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (butlast ?p_his))"
          using hI23_Deq_Call_Ret_Balanced_s[unfolded hI23_Deq_Call_Ret_Balanced_def, rule_format, where q=p and k=idx] idx_props
          unfolding Let_def by simp

        hence "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (butlast ?p_his)) =
               length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (butlast ?p_his))"
          using butlast_le by linarith

        hence "?C_len = ?R_len + 1"
          using C_eq R_eq by linarith
        thus ?thesis
          by simp
      qed

      then show ?thesis
        using True call_count ret_count by simp
    next
      case False
      have old_L0: "program_counter s q = ''L0''" 
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
      using v_eq by simp
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
      have "his_seq s' ! k = mk_act deq (x_var s p) p (s_var s p) ret"
        using his_eq \<open>k = ?n\<close> by simp
      then show ?thesis
        using 4 by (simp add: mk_act_def act_name_def act_cr_def)
    qed

  next
    case (5 k)
    show ?case
      using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s, of k] qback_eq V_eq by auto
  qed
qed

end