theory D3Lemmas
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    DeqLib
begin

(* ========== Basic lemmas ========== *)


(* Auxiliary lemma: the successful D3 step preserves the core concrete-state invariants *)
(* Encapsulate the concrete-state argument to keep the main proof concise *)
lemma Sys_D3_success_phys_invariants:
  assumes "system_invariant s"
  assumes "program_counter s p = ''D3''"
  assumes "Q_arr s (j_var s p) \<noteq> BOT"
  defines "s' \<equiv> Sys_D3_success_update s p"
  shows "TypeOK s' \<and> sI2_X_var_Upper_Bound s' \<and> sI7_D4_Deq_Result s' \<and> sI8_Q_Qback_Sync s' \<and> sI9_Qback_Discrepancy_E3 s' \<and> sI10_Qback_Unique_Vals s'"
proof -
  (* 1. extract the invariants of the old state *)
  from assms(1) have 
    TypeOK_s: "TypeOK s" and
    sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s" and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and
    sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s" and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s"
    unfolding system_invariant_def by auto

  (* 2. introduce local abbreviations *)
  let ?jp = "j_var s p"
  let ?q_val = "Q_arr s ?jp"
  let ?sn = "s_var s p"
  
  (* 3. prepare the key facts *)
  (* Since Q[jp] is not BOT, it is a valid queue value. *)
  have q_valid: "?q_val \<in> Val"
    using TypeOK_def TypeOK_s assms(3) by blast 
    
  (* By sI8_Q_Qback_Sync, a non-BOT Q[jp] must coincide with Qback[jp]. *)
  have q_eq_back: "?q_val = Qback_arr s ?jp"
    using sI8_Q_Qback_Sync_def sI8_Q_Qback_Sync_s assms(3) by auto

  (* Step 4: unfold all relevant fields of s', including the SSN-related updates. *)
  have s'_fields: 
    "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    "Q_arr s' = (\<lambda>x. if x = ?jp then BOT else Q_arr s x)"
    "x_var s' = (\<lambda>x. if x = p then ?q_val else x_var s x)"
    "lin_seq s' = (if should_modify (lin_seq s) (his_seq s) ?q_val then modify_lin (lin_seq s) (his_seq s) ?q_val else lin_seq s) @ [mk_op deq ?q_val p ?sn]" 
    "Qback_arr s' = Qback_arr s"
    "X_var s' = X_var s"
    "V_var s' = V_var s" 
    "v_var s' = v_var s" 
    "i_var s' = i_var s"
    "j_var s' = j_var s"
    "l_var s' = l_var s"
    "his_seq s' = his_seq s"
    "s_var s' = s_var s"
    using q_eq_back 
    unfolding s'_def Sys_D3_success_update_def Let_def 
              program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
              X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def s_var_def
    by auto

  (* --- prove the required conjuncts one by one --- *)

  (* Proof of TypeOK *)
  have "TypeOK s'"
    unfolding TypeOK_def
  proof (intro conjI)
    show "\<forall>p. program_counter s' p \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
      using TypeOK_s s'_fields unfolding TypeOK_def by auto
    show "X_var s' \<in> Val" using TypeOK_s s'_fields unfolding TypeOK_def by simp
    show "V_var s' \<in> Val" using TypeOK_s s'_fields unfolding TypeOK_def by simp
    show "\<forall>idx. Q_arr s' idx \<in> Val \<union> {BOT}" using TypeOK_s s'_fields unfolding TypeOK_def by auto
    show "\<forall>idx. Qback_arr s' idx \<in> Val \<union> {BOT}" using TypeOK_s s'_fields unfolding TypeOK_def by auto
    show "\<forall>p. i_var s' p \<in> Val \<union> {BOT}" using TypeOK_s s'_fields unfolding TypeOK_def by auto
    show "\<forall>p. j_var s' p \<in> Val \<union> {BOT}" using TypeOK_s s'_fields unfolding TypeOK_def by auto
    show "\<forall>p. l_var s' p \<in> Val \<union> {BOT}" using TypeOK_s s'_fields unfolding TypeOK_def by auto
    show "\<forall>p. x_var s' p \<in> Val \<union> {BOT}" using s'_fields q_valid TypeOK_s unfolding TypeOK_def by auto
    show "\<forall>p. v_var s' p \<in> Val \<union> {BOT}" using TypeOK_s s'_fields unfolding TypeOK_def by simp
    (* 💥 include the TypeOK obligation for s_var *)
    show "\<forall>p. s_var s' p \<in> Val" using TypeOK_s s'_fields unfolding TypeOK_def by simp
  qed

  moreover have "sI2_X_var_Upper_Bound s'"
  proof -
    (* sI2_X_var_Upper_Bound: Slots beyond X must stay BOT; turning one slot into BOT cannot violate sI2_X_var_Upper_Bound *)
    show ?thesis 
      using sI2_X_var_Upper_Bound_s s'_fields unfolding sI2_X_var_Upper_Bound_def by auto
  qed

  moreover have "sI7_D4_Deq_Result s'"
    unfolding sI7_D4_Deq_Result_def
  proof (intro allI impI)
    fix p'
    assume pc_D4: "program_counter s' p' = ''D4''"
    show "j_var s' p' \<in> Val \<and> Q_arr s' (j_var s' p') = BOT \<and> 
          Qback_arr s' (j_var s' p') = x_var s' p' \<and> x_var s' p' \<noteq> BOT"
    proof (cases "p' = p")
      case True
      (* Here p has just entered D4, so we check the D4-specific invariant in the new state *)
      have "j_var s' p \<in> Val" using sI6_D3_Scan_Pointers_s assms(2) unfolding sI6_D3_Scan_Pointers_def by (simp add: s'_fields)
      moreover have "Q_arr s' (j_var s' p) = BOT" using s'_fields True by simp
      moreover have "Qback_arr s' (j_var s' p) = x_var s' p" using s'_fields True q_eq_back by simp
      moreover have "x_var s' p \<noteq> BOT" using s'_fields True q_valid unfolding Val_def BOT_def by simp
      ultimately show ?thesis using True by simp
    next
      case False
      (* If p' is not p, then its control state is unchanged *)
      have old_pc_D4: "program_counter s p' = ''D4''" using pc_D4 False s'_fields(1)
        by auto 
      have old_sI7_D4_Deq_Result: "j_var s p' \<in> Val \<and> Q_arr s (j_var s p') = BOT \<and> Qback_arr s (j_var s p') = x_var s p' \<and> x_var s p' \<noteq> BOT"
        using sI7_D4_Deq_Result_s old_pc_D4 unfolding sI7_D4_Deq_Result_def by simp
      (* Q_arr changes only at ?jp, so every location that was already BOT stays BOT *)
      have "Q_arr s' (j_var s p') = BOT" using s'_fields(2) old_sI7_D4_Deq_Result by simp
      thus ?thesis using old_sI7_D4_Deq_Result s'_fields False by auto
    qed
  qed

  moreover have "sI8_Q_Qback_Sync s'"
    unfolding sI8_Q_Qback_Sync_def
  proof (intro allI)
    fix k
    show "Q_arr s' k = Qback_arr s' k \<or> Q_arr s' k = BOT"
    proof (cases "k = ?jp")
      case True
      then show ?thesis using s'_fields(2) by simp
    next
      case False
      then show ?thesis using sI8_Q_Qback_Sync_s s'_fields(2,5) unfolding sI8_Q_Qback_Sync_def by auto
    qed
  qed

  moreover have "sI9_Qback_Discrepancy_E3 s'"
    unfolding sI9_Qback_Discrepancy_E3_def
  proof (intro allI impI)
    fix k q
    assume prem: "Q_arr s' k = BOT \<and> Qback_arr s' k \<noteq> BOT"
    assume q_cond: "program_counter s' q \<in> {''E3''} \<and> i_var s' q = k"
    
    (* Key simplification: p D4, hence any process q in E3 must be different from p *)
    have "q \<noteq> p" using q_cond s'_fields(1) by auto
    hence pc_q: "program_counter s q = ''E3''" using q_cond s'_fields(1) by auto
    have i_q: "i_var s q = k" using q_cond s'_fields by auto
    
    (* sI4_E3_Qback_Written ensures that any process q still in E3 satisfies Qback[i] = v *)
    have "Qback_arr s (i_var s q) = v_var s q"
      using sI4_E3_Qback_Written_s pc_q unfolding sI4_E3_Qback_Written_def by blast
      
    (* A direct substitution proves the claim without a case split on k *)
    thus "v_var s' q = Qback_arr s' k"
      using i_q s'_fields by auto
  qed

  moreover have "sI10_Qback_Unique_Vals s'"
  proof -
    (* Qback is unchanged, so uniqueness is preserved immediately *)
    show ?thesis using sI10_Qback_Unique_Vals_s s'_fields unfolding sI10_Qback_Unique_Vals_def by simp
  qed

  ultimately show ?thesis by blast
qed

(* ----------------------------------------------------------------- *)
(* Auxiliary lemma: D3 preserves under the successful transition hI13_Qback_Deq_Sync (revised version) *)
(* ----------------------------------------------------------------- *)
lemma D3_preserves_hI13_Qback_Deq_Sync:
  assumes "hI13_Qback_Deq_Sync s"
  assumes "sI8_Q_Qback_Sync s"                    (* Revision: use sI8_Q_Qback_Sync instead of sI2_X_var_Upper_Bound *)
  assumes "program_counter s p = ''D3''"
  assumes "jp = j_var s p"
  assumes "q_val = Q_arr s jp"       
  assumes "q_val \<noteq> BOT"
  assumes "s' = Sys_D3_success_update s p"
  shows "hI13_Qback_Deq_Sync s'"
proof -
  (* Step 1: 1. s' , SMT *)
  have s'_fields: 
    "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    "x_var s' = (\<lambda>x. if x = p then q_val else x_var s x)"
    "Q_arr s' = (\<lambda>x. if x = jp then BOT else Q_arr s x)"
    "Qback_arr s' = Qback_arr s"
    "his_seq s' = his_seq s"
    using assms unfolding Sys_D3_success_update_def Let_def 
          program_counter_def x_var_def Q_arr_def Qback_arr_def his_seq_def j_var_def
    by auto

  (* 2. unfold hI13_Qback_Deq_Sync and prove the goal directly *)
  show ?thesis
    unfolding hI13_Qback_Deq_Sync_def
  proof (intro allI impI)
    fix a
    assume "a \<noteq> BOT"
    assume "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a"
    then obtain k where k_props: "Q_arr s' k = BOT" "Qback_arr s' k = a" by blast

    (* 💥 Revision note: The target statement contains \<exists>sn *)
    show "\<exists>proc. (program_counter s' proc = ''D4'' \<and> x_var s' proc = a) \<or> (\<exists>sn. DeqRetInHis s' proc a sn)"
    proof (cases "k = jp")
      (* === Case A: k is the slot just manipulated by process p === *)
      case True
      (* Use k_props and the update equations of s' to derive the value of a *)
      have "Qback_arr s jp = a" using k_props(2) True s'_fields(4) by simp
      
      (* Use sI8_Q_Qback_Sync to show that a must equal q_val *)
      have "Q_arr s jp = Qback_arr s jp"
        using `sI8_Q_Qback_Sync s` `q_val \<noteq> BOT` assms(5) unfolding sI8_Q_Qback_Sync_def 
        by (metis) 
        
      hence "q_val = a" 
        using `Qback_arr s jp = a` assms(5) by simp
      
      (* Construct the witness that p is in D4 and carries value a *)
      have "program_counter s' p = ''D4''" using s'_fields(1) by simp
      moreover have "x_var s' p = a" using s'_fields(2) `q_val = a` by simp
      ultimately show ?thesis by blast
      
    next
      (* === Case B: k is not the slot touched by the current step === *)
      case False
      (* Here both Q_arr and Qback_arr are inherited from s *)
      have "Q_arr s k = BOT" 
        using k_props(1) s'_fields(3) False by simp
      have "Qback_arr s k = a" 
        using k_props(2) s'_fields(4) by simp
        
      (* Invoke the old-state invariant hI13_Qback_Deq_Sync s *)
      have hI13_Qback_Deq_Sync_pre: "\<exists>proc. (program_counter s proc = ''D4'' \<and> x_var s proc = a) \<or> (\<exists>sn. DeqRetInHis s proc a sn)"
        using `hI13_Qback_Deq_Sync s` `a \<noteq> BOT` `Q_arr s k = BOT` `Qback_arr s k = a` 
        unfolding hI13_Qback_Deq_Sync_def by blast
        
      then obtain proc where pre_cond: 
        "(program_counter s proc = ''D4'' \<and> x_var s proc = a) \<or> (\<exists>sn. DeqRetInHis s proc a sn)" 
        by blast
      
      (* prove that this property is preserved in s' *)
      show ?thesis
      proof (cases "program_counter s proc = ''D4'' \<and> x_var s proc = a")
        case True
        (* If proc was in D4 in s, then proc \<noteq> p because p is in D3 *)
        then have "proc \<noteq> p" using assms(3) by auto
        
        (* For all other processes, both the control state and x_var are unchanged *)
        have "program_counter s' proc = program_counter s proc" using `proc \<noteq> p` s'_fields(1) by simp
        have "x_var s' proc = x_var s proc" using `proc \<noteq> p` s'_fields(2) by simp
          
        (* Therefore proc still satisfies the required condition in s' *)
        then show ?thesis using True `program_counter s' proc = program_counter s proc` by auto
      next
        case False
        (* 💥 Revision note: If the D4 disjunct does not hold, then the SSN-indexed DeqRetInHis alternative must hold *)
        then have "\<exists>sn. DeqRetInHis s proc a sn" using pre_cond by blast
        then obtain sn where "DeqRetInHis s proc a sn" by blast
        
        (* The history sequence is unchanged, so the property is preserved *)
        then have "DeqRetInHis s' proc a sn"
          using s'_fields(5) unfolding DeqRetInHis_def by simp
        then show ?thesis by blast
      qed
    qed
  qed
qed

(* ----------------------------------------------------------------- *)
(* Auxiliary lemma: D3 preserves under the successful transition hI15_Deq_Result_Exclusivity (exclusivity of dequeue results) *)
(* ----------------------------------------------------------------- *)


lemma D3_BOT_preserves_hI15_Deq_Result_Exclusivity:
  assumes INV: "system_invariant s"
      and PC: "program_counter s p = ''D3''"
      and SIMPLE: "s' = (
    (fst s)\<lparr>
      c_program_counter := (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else CState.c_program_counter (fst s) x),
      Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
      j_var := (\<lambda>x. if x = p then (if jp \<noteq> lp - 1 then jp + 1 else jp) else CState.j_var (fst s) x),
      x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
    \<rparr>,
    snd s
  )"
      and HIS_EQ: "his_seq s' = his_seq s"
      and Q_EQ: "Q_arr s' = Q_arr s"
  shows "hI15_Deq_Result_Exclusivity s'"
proof -
  have inv_hI15_Deq_Result_Exclusivity: "hI15_Deq_Result_Exclusivity s"
    using INV unfolding system_invariant_def by blast
  have inv_sI11_x_var_Scope: "sI11_x_var_Scope s"
    using INV unfolding system_invariant_def by blast

  have x_p_bot_s: "x_var s p = BOT"
    using inv_sI11_x_var_Scope PC unfolding sI11_x_var_Scope_def by simp

  have x_eq: "x_var s' = x_var s"
    using SIMPLE x_p_bot_s by (auto simp: x_var_def fun_eq_iff)
  have s_var_eq: "s_var s' = s_var s"
    using SIMPLE by (auto simp: s_var_def)

  have pc_D4_eq: "\<forall>q. (program_counter s' q = ''D4'') \<longleftrightarrow> (program_counter s q = ''D4'')"
    using SIMPLE PC by (auto simp: program_counter_def)

  have deq_ret_eq: "\<forall>q a sn. DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
    unfolding DeqRetInHis_def using HIS_EQ by auto

  have pending_eq: "\<forall>q. HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
    unfolding HasPendingDeq_def using HIS_EQ
    using DeqCallInHis_def s_var_eq by presburger

  show ?thesis
    using inv_hI15_Deq_Result_Exclusivity
    unfolding hI15_Deq_Result_Exclusivity_def
    using Q_EQ x_eq pc_D4_eq deq_ret_eq pending_eq
    by presburger
qed



lemma D3_BOT_preserves_hI16_BO_BT_No_HB:
  fixes s s' :: SysState and p jp lp q_val :: nat
  assumes INV: "system_invariant s"
  assumes pc_D3: "program_counter s p = ''D3''"
  assumes jp_def: "jp = j_var s p"
  assumes lp_def: "lp = l_var s p"
  assumes q_val_def: "q_val = Q_arr s jp"
  assumes q_is_bot: "q_val = BOT"
  assumes s'_simple: "s' = (
    (fst s)\<lparr>
      c_program_counter := (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else CState.c_program_counter (fst s) x),
      Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
      j_var := (\<lambda>x. if x = p then (if jp \<noteq> lp - 1 then jp + 1 else jp) else CState.j_var (fst s) x),
      x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
    \<rparr>,
    snd s
  )"
  assumes his_seq_eq: "his_seq s' = his_seq s"
  assumes Q_unchanged: "Q_arr s' = Q_arr s"
  assumes T_unchanged: "Qback_arr s' = Qback_arr s"
  shows "hI16_BO_BT_No_HB s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def
    have "hI16_BO_BT_No_HB s'"
    proof -
      (* 1. basic facts *)
      have his_eq: "his_seq s' = his_seq s" using his_seq_eq .
      have Q_eq: "Q_arr s' = Q_arr s" using Q_unchanged .
      have T_eq: "Qback_arr s' = Qback_arr s" using T_unchanged .

      (* 2. prove the equivalence of TypeB (SetB s' = SetB s) *)
      have TypeB_iff: "\<And>x. TypeB s' x \<longleftrightarrow> TypeB s x"
      proof -
        fix x
        (* Part 1: QHas is unchanged *)
        have "QHas s' x \<longleftrightarrow> QHas s x" using Q_eq unfolding QHas_def by simp
        (* Part 2: the E2-state condition is unchanged *)
        have "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow> 
              (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
        proof
          assume "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x"
          then obtain q where q_stat: "program_counter s' q = ''E2''" "v_var s' q = x" by blast
          have "q \<noteq> p" using q_stat s'_simple pc_D3 bridge_defs  by (auto split: if_splits)
          then have "program_counter s q = ''E2''" "v_var s q = x" using q_stat s'_simple bridge_defs  by auto
          then show "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x" by blast
        next
          assume "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x"
          then obtain q where q_stat: "program_counter s q = ''E2''" "v_var s q = x" by blast
          have "q \<noteq> p" using q_stat pc_D3 by auto
          then have "program_counter s' q = ''E2''" "v_var s' q = x" using q_stat s'_simple bridge_defs  by auto
          then show "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x" by blast
        qed
        then show "TypeB s' x \<longleftrightarrow> TypeB s x" unfolding TypeB_def using `QHas s' x \<longleftrightarrow> QHas s x` by blast
      qed

      (* 3. key lemma: inclusion of TypeBT (SetBT s' \<subseteq> SetBT s) *)
      have TypeBT_subset: "\<And>x. TypeBT s' x \<Longrightarrow> TypeBT s x"
      proof -
        fix x assume bt_new: "TypeBT s' x"
        
        (* unfold the definition of TypeBT *)
        have base_cond: "TypeB s x \<and> InQBack s x"
          using bt_new TypeB_iff T_eq unfolding TypeBT_def InQBack_def by simp
          
        (* analyze the main disjunct in the TypeBT definition ( - 1) *)
        have cond_new: "((\<forall>k < Idx s' x. Q_arr s' k = BOT) \<or>
                        (\<exists>q. program_counter s' q = ''D3'' \<and>
                             j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and>
                             (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)))"
          using bt_new unfolding TypeBT_def by simp
          
        let ?idx = "Idx s x"
        have idx_eq: "Idx s' x = ?idx" 
          using T_eq unfolding Idx_def AtIdx_def by simp

        (* show that the corresponding condition already holds in s ( - 1) *)
        have cond_old: "((\<forall>k < ?idx. Q_arr s k = BOT) \<or>
                         (\<exists>q. program_counter s q = ''D3'' \<and>
                              j_var s q \<le> ?idx \<and> ?idx < l_var s q \<and>
                              (\<forall>k. j_var s q \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s k = BOT)))"
        proof (cases "\<forall>k < ?idx. Q_arr s k = BOT")
          case True then show ?thesis by simp
        next
          case False
          (* part2_new - 1 *)
          then have part2_new: "\<exists>q. program_counter s' q = ''D3'' \<and>
                                    j_var s' q \<le> ?idx \<and> ?idx < l_var s' q \<and>
                                    (\<forall>k. j_var s' q \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s' k = BOT)"
            using cond_new idx_eq Q_eq by auto
          
          obtain q where q_new: "program_counter s' q = ''D3''"
                                "j_var s' q \<le> ?idx" "?idx < l_var s' q"
                                "\<forall>k. j_var s' q \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s' k = BOT"
            using part2_new by blast

          show ?thesis
          proof (cases "q = p")
            case False
            have "program_counter s q = ''D3''" "j_var s q = j_var s' q" "l_var s q = l_var s' q"
              using s'_simple False q_new(1) bridge_defs  by auto
            then show ?thesis using q_new Q_eq by auto
          next
            case True
            have in_D3_s: "program_counter s p = ''D3''" using pc_D3 by simp
            have j_rel: "j_var s' p = jp + 1"
              using s'_simple True q_new(1) unfolding jp_def lp_def bridge_defs  by (auto split: if_splits)
            have l_rel: "l_var s p = l_var s' p"
              using s'_simple True unfolding lp_def bridge_defs  by auto
            
            (* derive the required bounds ( : - 1) *)
            have range_s: "j_var s p \<le> ?idx \<and> ?idx < l_var s p"
            proof -
              (* show j_var s p <= ?idx *)
              have "j_var s p = jp" unfolding jp_def by simp
              have "jp < jp + 1" by simp
              also have "... = j_var s' p" using j_rel by simp
              also have "... \<le> ?idx" using q_new(2) True by simp
              finally have "j_var s p \<le> ?idx" unfolding jp_def by simp
              
              (* show ?idx < l_var s p *)
              have "?idx < l_var s' p" using q_new(3) True by simp
              then have "?idx < l_var s p" using l_rel by simp
              
              then show ?thesis using `j_var s p \<le> ?idx` by simp
            qed
              
            (* derive the BOT checks *)
            have bot_s: "\<forall>k. j_var s p \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s k = BOT"
            proof (intro allI impI)
              fix k assume k_range: "j_var s p \<le> k \<and> k < ?idx"
              show "Q_arr s k = BOT"
              proof (cases "k = jp")
                case True then show ?thesis using q_is_bot q_val_def by simp
              next
                case False
                then have "k \<ge> jp + 1" using k_range unfolding jp_def by simp
                then have "j_var s' p \<le> k \<and> k < ?idx" using k_range True j_rel by simp
                then show ?thesis using q_new(4) True Q_eq by auto
              qed
            qed
            
            show ?thesis using in_D3_s range_s bot_s by blast
          qed
        qed
        
        show "TypeBT s x" unfolding TypeBT_def using base_cond cond_old by simp
      qed

      (* 4. assemble the final proof hI16_BO_BT_No_HB *)
      show ?thesis
        unfolding hI16_BO_BT_No_HB_def SetBO_def SetBT_def TypeBO_def
      proof (intro allI impI notI)
        fix a b
        assume sets: "a \<in> {x \<in> Val. TypeB s' x \<and> \<not> TypeBT s' x} \<and> b \<in> {x \<in> Val. TypeBT s' x}"
        assume HB_new: "HB_EnqRetCall s' a b"
        
        (* split the assumptions *)
        from sets have a_BO_new: "a \<in> {x \<in> Val. TypeB s' x \<and> \<not> TypeBT s' x}" 
                   and b_BT_new: "b \<in> {x \<in> Val. TypeBT s' x}" by auto
        
        (* extract the Val-side facts *)
        have val_a: "a \<in> Val" using a_BO_new by simp
        have val_b: "b \<in> Val" using b_BT_new by simp

        (* recover the corresponding state facts in s *)
        have hb_old: "HB_EnqRetCall s a b"
          using HB_new his_eq unfolding HB_EnqRetCall_def
          by (simp add: HB_Act_def)
        
        have b_BT_old: "TypeBT s b"
          using b_BT_new TypeBT_subset by simp
          
        have a_TypeB_old: "TypeB s a"
          using a_BO_new TypeB_iff by simp
          
        (* Proof note. *)
        have b_in_SetBT_s: "b \<in> SetBT s"
          using val_b b_BT_old unfolding SetBT_def by simp

        (* a s BO BT *)
        show False
        proof (cases "TypeBT s a")
          case True
          (* Case A: a s BT. hI17_BT_BT_No_HB *)
          have a_in_SetBT_s: "a \<in> SetBT s"
            using val_a True unfolding SetBT_def by simp

        have hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s"
          using INV unfolding system_invariant_def by blast
        have hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s"
          using INV unfolding system_invariant_def by blast



         have "\<not> HB_EnqRetCall s a b"
            using INV a_in_SetBT_s b_in_SetBT_s
            unfolding system_invariant_def hI17_BT_BT_No_HB_def
            by blast
            
          then show False using hb_old by simp
        next
          case False
          (* Case B: a s BT. BO. hI16_BO_BT_No_HB *)
          have a_in_SetBO_s: "a \<in> SetBO s"
            using val_a a_TypeB_old False unfolding SetBO_def TypeBO_def by simp
            
        have "\<not> HB_EnqRetCall s a b"
            using INV a_in_SetBO_s b_in_SetBT_s
            unfolding system_invariant_def hI16_BO_BT_No_HB_def
            by blast

          then show False using hb_old by simp
        qed
      qed
    qed
  thus ?thesis .
qed


lemma D3_BOT_preserves_hI17_BT_BT_No_HB:
  fixes s s' :: SysState and p jp lp q_val :: nat
  assumes INV: "system_invariant s"
  assumes pc_D3: "program_counter s p = ''D3''"
  assumes jp_def: "jp = j_var s p"
  assumes lp_def: "lp = l_var s p"
  assumes q_val_def: "q_val = Q_arr s jp"
  assumes q_is_bot: "q_val = BOT"
  assumes s'_simple: "s' = (
    (fst s)\<lparr>
      c_program_counter := (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else CState.c_program_counter (fst s) x),
      Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
      j_var := (\<lambda>x. if x = p then (if jp \<noteq> lp - 1 then jp + 1 else jp) else CState.j_var (fst s) x),
      x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
    \<rparr>,
    snd s
  )"
  assumes his_seq_eq: "his_seq s' = his_seq s"
  assumes Q_unchanged: "Q_arr s' = Q_arr s"
  assumes T_unchanged: "Qback_arr s' = Qback_arr s"
  shows "hI17_BT_BT_No_HB s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def
    have "hI17_BT_BT_No_HB s'"
    proof -
      (* 1. basic facts *)
      have his_eq: "his_seq s' = his_seq s" using his_seq_eq .
      have Q_eq: "Q_arr s' = Q_arr s" using Q_unchanged .
      have T_eq: "Qback_arr s' = Qback_arr s" using T_unchanged .

      (* 2. prove the equivalence of TypeB (TypeB s' x \<longleftrightarrow> TypeB s x) *)
      have TypeB_iff: "\<And>x. TypeB s' x \<longleftrightarrow> TypeB s x"
      proof -
        fix x
        (* Part 1: QHas is unchanged *)
        have "QHas s' x \<longleftrightarrow> QHas s x" using Q_eq unfolding QHas_def by simp
        (* Part 2: the E2-state condition is unchanged *)
        have "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow> 
              (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
        proof
          assume "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x"
          then obtain q where q_stat: "program_counter s' q = ''E2''" "v_var s' q = x" by blast
          have "q \<noteq> p" using q_stat s'_simple pc_D3 bridge_defs  by (auto split: if_splits)
          then have "program_counter s q = ''E2''" "v_var s q = x" using q_stat s'_simple bridge_defs  by auto
          then show "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x" by blast
        next
          assume "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x"
          then obtain q where q_stat: "program_counter s q = ''E2''" "v_var s q = x" by blast
          have "q \<noteq> p" using q_stat pc_D3 by auto
          then have "program_counter s' q = ''E2''" "v_var s' q = x" using q_stat s'_simple bridge_defs  by auto
          then show "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x" by blast
        qed
        then show "TypeB s' x \<longleftrightarrow> TypeB s x" unfolding TypeB_def using `QHas s' x \<longleftrightarrow> QHas s x` by blast
      qed

      (* 3. key lemma: inclusion of TypeBT (TypeBT s' x \<Longrightarrow> TypeBT s x) *)
      have TypeBT_subset: "\<And>x. TypeBT s' x \<Longrightarrow> TypeBT s x"
      proof -
        fix x assume bt_new: "TypeBT s' x"
        
        (* unfold the definition of TypeBT *)
        have base_cond: "TypeB s x \<and> InQBack s x"
          using bt_new TypeB_iff T_eq unfolding TypeBT_def InQBack_def by simp
          
        (* analyze the main disjunct in the TypeBT definition ( : - 1) *)
        have cond_new: "((\<forall>k < Idx s' x. Q_arr s' k = BOT) \<or>
                        (\<exists>q. program_counter s' q = ''D3'' \<and>
                             j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and>
                             (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)))"
          using bt_new unfolding TypeBT_def by simp
          
        let ?idx = "Idx s x"
        have idx_eq: "Idx s' x = ?idx" 
          using T_eq unfolding Idx_def AtIdx_def by simp

        (* show that the corresponding condition already holds in s ( : - 1) *)
        have cond_old: "((\<forall>k < ?idx. Q_arr s k = BOT) \<or>
                         (\<exists>q. program_counter s q = ''D3'' \<and>
                              j_var s q \<le> ?idx \<and> ?idx < l_var s q \<and>
                              (\<forall>k. j_var s q \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s k = BOT)))"
        proof (cases "\<forall>k < ?idx. Q_arr s k = BOT")
          case True then show ?thesis by simp
        next
          case False
          then have part2_new: "\<exists>q. program_counter s' q = ''D3'' \<and>
                                    j_var s' q \<le> ?idx \<and> ?idx < l_var s' q \<and>
                                    (\<forall>k. j_var s' q \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s' k = BOT)"
            using cond_new idx_eq Q_eq by auto
          
          obtain q where q_new: "program_counter s' q = ''D3''"
                                "j_var s' q \<le> ?idx" "?idx < l_var s' q"
                                "\<forall>k. j_var s' q \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s' k = BOT"
            using part2_new by blast

          show ?thesis
          proof (cases "q = p")
            case False
            have "program_counter s q = ''D3''" "j_var s q = j_var s' q" "l_var s q = l_var s' q"
              using s'_simple False q_new(1) bridge_defs  by auto
            then show ?thesis using q_new Q_eq by auto
          next
            case True
            (* p: s' j' = jp + 1 *)
            have in_D3_s: "program_counter s p = ''D3''" using pc_D3 by simp
            have j_rel: "j_var s' p = jp + 1"
              using s'_simple True q_new(1) unfolding jp_def lp_def bridge_defs  by (auto split: if_splits)
            have l_rel: "l_var s p = l_var s' p"
              using s'_simple True unfolding lp_def bridge_defs  by auto
            
            (* A. derive the required bounds: jp + 1 \<le> idx ==> jp \<le> idx ( : - 1) *)
            have range_s: "j_var s p \<le> ?idx \<and> ?idx < l_var s p"
              using q_new(2,3) True j_rel l_rel unfolding jp_def by simp
              
            (* B. BOT : s' [jp+1, idx) BOT, Q[jp]=BOT *)
            have bot_s: "\<forall>k. j_var s p \<le> k \<and> k < ?idx \<longrightarrow> Q_arr s k = BOT"
            proof (intro allI impI)
              fix k assume k_range: "j_var s p \<le> k \<and> k < ?idx"
              show "Q_arr s k = BOT"
              proof (cases "k = jp")
                case True then show ?thesis using q_is_bot q_val_def by simp
              next
                case False
                then have "k \<ge> jp + 1" using k_range unfolding jp_def by simp
                then have "j_var s' p \<le> k \<and> k < ?idx" using k_range True j_rel by simp
                then show ?thesis using q_new(4) True Q_eq by auto
              qed
            qed
            
            show ?thesis using in_D3_s range_s bot_s by blast
          qed
        qed
        
        show "TypeBT s x" unfolding TypeBT_def using base_cond cond_old by simp
      qed

      (* 4. assemble the final proof hI17_BT_BT_No_HB *)
      show ?thesis
        unfolding hI17_BT_BT_No_HB_def SetBT_def
      proof (intro allI impI notI)
        fix a b
        (* Proof note. *)
        assume sets: "a \<in> {x \<in> Val. TypeBT s' x} \<and> b \<in> {x \<in> Val. TypeBT s' x}"
        assume HB_new: "HB_EnqRetCall s' a b"
        
        from sets have a_BT_new: "TypeBT s' a" and b_BT_new: "TypeBT s' b" 
                   and a_val: "a \<in> Val" and b_val: "b \<in> Val" by auto

        (* Proof note. *)
        have a_BT_old: "TypeBT s a" using a_BT_new TypeBT_subset by simp
        have b_BT_old: "TypeBT s b" using b_BT_new TypeBT_subset by simp
        
        (* Proof note. *)
        have in_SetBT_s: "a \<in> SetBT s \<and> b \<in> SetBT s"
          using a_BT_old b_BT_old a_val b_val unfolding SetBT_def by simp
          
        (* HB *)
        have HB_old: "HB_EnqRetCall s a b"
          using HB_new his_eq unfolding HB_EnqRetCall_def
          using HB_Act_def by auto 
          
        (* hI17_BT_BT_No_HB *)
        show False
          using INV in_SetBT_s HB_old
          unfolding system_invariant_def hI17_BT_BT_No_HB_def
          by blast
      qed
    qed
  thus ?thesis .
qed


lemma D3_BOT_preserves_hI19_Scanner_Catches_Later_Enq:
  fixes s s' :: SysState and p jp lp q_val :: nat
  assumes INV: "system_invariant s"
  assumes pc_D3: "program_counter s p = ''D3''"
  assumes jp_def: "jp = j_var s p"
  assumes lp_def: "lp = l_var s p"
  assumes q_val_def: "q_val = Q_arr s jp"
  assumes q_is_bot: "q_val = BOT"
  assumes s'_simple: "s' = (
    (fst s)\<lparr>
      c_program_counter := (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else CState.c_program_counter (fst s) x),
      Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
      j_var := (\<lambda>x. if x = p then (if jp \<noteq> lp - 1 then jp + 1 else jp) else CState.j_var (fst s) x),
      x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
    \<rparr>,
    snd s
  )"
  assumes his_seq_eq: "his_seq s' = his_seq s"
  assumes Q_unchanged: "Q_arr s' = Q_arr s"
  assumes T_unchanged: "Qback_arr s' = Qback_arr s"
  shows "hI19_Scanner_Catches_Later_Enq s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def
    have "hI19_Scanner_Catches_Later_Enq s'"
      unfolding hI19_Scanner_Catches_Later_Enq_def
    proof (intro allI impI, goal_cases)
      case (1 a b)
      
      (* Step 1: 1. ( : InQBack TypeB ) *)
      from 1 have inqa': "InQBack s' a" by blast
      from 1 have inqb': "InQBack s' b" by blast
      from 1 have tba': "TypeB s' a" by blast
      from 1 have tbb': "TypeB s' b" by blast
      from 1 have idx_lt': "Idx s' a < Idx s' b" by blast
      from 1 have ex_q': "\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and> 
                              Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q" by blast
                              
      (* Step 2: 2. *)
      have inv_hI19_Scanner_Catches_Later_Enq: "hI19_Scanner_Catches_Later_Enq s" using INV unfolding system_invariant_def by blast
      have inv_hI20_Enq_Val_Valid: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast
      
      (* Step 3: 3. : \<And>x *)
      have T_eq: "Qback_arr s' = Qback_arr s" using T_unchanged .
      have Q_eq: "Q_arr s' = Q_arr s" using Q_unchanged .
      have s_var_eq: "s_var s' = s_var s" using s'_simple by (auto simp: s_var_def)
      have v_var_eq: "v_var s' = v_var s" using s'_simple by (auto simp: v_var_def)
      
      (* E23 , TypeB E2, E2 p D3 D4, E2, *)
      have E2_eq: "\<And>q. program_counter s' q = ''E2'' \<longleftrightarrow> program_counter s q = ''E2''"
        using s'_simple pc_D3 by (auto simp: program_counter_def)
        
      have TypeB_eq: "\<And>x. TypeB s' x \<longleftrightarrow> TypeB s x"
        unfolding TypeB_def SetB_def InQBack_def QHas_def 
        using T_eq Q_eq E2_eq v_var_eq by auto
        
      have Idx_eq: "\<And>x. Idx s' x = Idx s x"
        unfolding Idx_def AtIdx_def using T_eq by simp
        
      have pending_eq: "\<And>q. HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
        unfolding HasPendingDeq_def DeqCallInHis_def Let_def using his_seq_eq s_var_eq by simp
        
      have HB_eq: "HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
        using his_seq_eq by auto

      (* Step 4: 4. s *)
      have inqa: "InQBack s a" using inqa' T_eq unfolding InQBack_def by simp
      have inqb: "InQBack s b" using inqb' T_eq unfolding InQBack_def by simp
      have tba: "TypeB s a" using tba' TypeB_eq by simp
      have tbb: "TypeB s b" using tbb' TypeB_eq by simp
      have idx_lt: "Idx s a < Idx s b" using idx_lt' Idx_eq by simp
        
      from ex_q' obtain q where Witness:
        "HasPendingDeq s' q" "program_counter s' q = ''D3''"
        "Idx s' a < j_var s' q" "j_var s' q \<le> Idx s' b" "Idx s' b < l_var s' q"
        by blast
        
      (* Step 5: 5. *)
      show ?case
      proof (cases "q = p")
        case False
        (* Step 5: 5.1 , , s hI19_Scanner_Catches_Later_Enq *)
        have pc_q: "program_counter s q = ''D3''" using s'_simple False Witness(2) bridge_defs by auto
        have j_q: "j_var s q = j_var s' q" using s'_simple False bridge_defs by auto
        have l_q: "l_var s q = l_var s' q" using s'_simple False bridge_defs by auto
        have pd_q: "HasPendingDeq s q" using Witness(1) pending_eq by simp
        
        have "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and> 
                  Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
          using pc_q j_q l_q pd_q Witness(3,4,5) Idx_eq by auto
        with inv_hI19_Scanner_Catches_Later_Enq inqa inqb tba tbb idx_lt show ?thesis
          unfolding hI19_Scanner_Catches_Later_Enq_def using HB_eq by blast
      next
        case True
        have q_is_p: "q = p" using True by simp
        
        (* Step 5: 5.2 p *)
        have in_D3_s: "program_counter s p = ''D3''" using pc_D3 by simp
        have pd_p: "HasPendingDeq s p" using Witness(1) pending_eq q_is_p by simp
        
        have j_update: "j_var s' p = jp + 1" and l_same: "l_var s' p = lp"
          using s'_simple q_is_p Witness(2) unfolding jp_def lp_def bridge_defs by (auto split: if_splits)
          
        show ?thesis
        proof (cases "Idx s a < jp")
          case True
          (* Step 5: 5.2.1 Idx a < jp, p s Witness *)
          have "jp + 1 \<le> Idx s' b" using Witness(4) j_update q_is_p by simp
          then have "jp \<le> Idx s b" using Idx_eq by simp
          have "Idx s b < lp" using Witness(5) l_same q_is_p Idx_eq by simp
          
          have "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and> 
                    Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
            using pd_p in_D3_s True `jp \<le> Idx s b` `Idx s b < lp` unfolding jp_def lp_def by blast
          with inv_hI19_Scanner_Catches_Later_Enq inqa inqb tba tbb idx_lt show ?thesis
            unfolding hI19_Scanner_Catches_Later_Enq_def using HB_eq by blast
        next
          case False
          (* Step 5: 5.2.2 Idx a = jp, *)
          have "Idx s' a < jp + 1" using Witness(3) j_update q_is_p by simp
          then have "Idx s a < jp + 1" using Idx_eq by simp
          with False have Idx_a_jp: "Idx s a = jp" by simp
          
          have Q_jp_bot: "Q_arr s jp = BOT" using q_is_bot q_val_def jp_def by simp
          
          show ?thesis
          proof
            assume hb_s': "HB_EnqRetCall s' a b"
            then have hb: "HB_EnqRetCall s a b" using HB_eq by simp
            
            (* metis, a \<noteq> BOT *)
            have a_not_bot: "a \<noteq> BOT"
            proof -
              obtain p1 sn1 p2 sn2 where hb_act: "HB (his_seq s) (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
                using hb unfolding HB_EnqRetCall_def HB_Act_def by blast
                
              obtain k where match_k: "match_ret (his_seq s) k (mk_op enq a p1 sn1)"
                using hb_act unfolding HB_def Let_def by blast
                
              have k_len: "k < length (his_seq s)" using match_k unfolding match_ret_def by auto
              have k_oper: "act_name (his_seq s ! k) = enq" using match_k unfolding match_ret_def mk_op_def op_name_def
                by (metis fst_eqD) 
              have k_val: "act_val (his_seq s ! k) = a" using match_k unfolding match_ret_def mk_op_def op_val_def
                by (metis fst_conv snd_conv) 
                
              have "act_val (his_seq s ! k) \<in> Val" using k_len k_oper inv_hI20_Enq_Val_Valid unfolding hI20_Enq_Val_Valid_def by blast
              then have "a \<in> Val" using k_val by simp
              then show ?thesis unfolding Val_def BOT_def by auto
            qed
              
            (* D3Lib \<not> TypeB s a *)
            have "\<not> TypeB s a"
              using Idx_eq_j_and_Q_BOT_implies_not_TypeB[OF INV inqa Idx_a_jp Q_jp_bot a_not_bot] .
              
            (* tba (TypeB s a) *)
            then show False using tba by simp
          qed
        qed
      qed
    qed
  thus ?thesis .
qed

lemma D3_BOT_preserves_hI30_Ticket_HB_Immunity:
  fixes s s' :: SysState and p jp lp q_val :: nat
  assumes INV: "system_invariant s"
  assumes pc_D3: "program_counter s p = ''D3''"
  assumes jp_def: "jp = j_var s p"
  assumes lp_def: "lp = l_var s p"
  assumes q_val_def: "q_val = Q_arr s jp"
  assumes q_is_bot: "q_val = BOT"
  assumes s'_simple: "s' = (
    (fst s)\<lparr>
      c_program_counter := (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else CState.c_program_counter (fst s) x),
      Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
      j_var := (\<lambda>x. if x = p then (if jp \<noteq> lp - 1 then jp + 1 else jp) else CState.j_var (fst s) x),
      x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
    \<rparr>,
    snd s
  )"
  assumes his_seq_eq: "his_seq s' = his_seq s"
  assumes Q_unchanged: "Q_arr s' = Q_arr s"
  assumes T_unchanged: "Qback_arr s' = Qback_arr s"
  shows "hI30_Ticket_HB_Immunity s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def

  have "hI30_Ticket_HB_Immunity s'"
  proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI, goal_cases)
    case (1 b q)
    
    from 1 have pc_q': "program_counter s' q \<in> {''E2'', ''E3''}" by blast
    from 1 have inqb': "InQBack s' b" by blast
    from 1 have b_not_bot': "b \<noteq> BOT" by blast
    from 1 have b_neq_v': "b \<noteq> v_var s' q" by blast
    from 1 have hb': "HB_EnqRetCall s' b (v_var s' q)" by blast
    
    have inv_hI22: "hI30_Ticket_HB_Immunity s"
      using INV unfolding system_invariant_def by blast
    
    have q_neq_p: "q \<noteq> p"
    proof
      assume "q = p"
      with pc_q' have "program_counter s' p \<in> {''E2'', ''E3''}" by simp
      moreover have "program_counter s' p \<in> {''D1'', ''D3''}" 
        using s'_simple by (auto simp: program_counter_def split: if_splits)
      ultimately show False by auto 
    qed

    have his_eq: "his_seq s' = his_seq s" using s'_simple by (auto simp: his_seq_def)
    have v_eq: "v_var s' = v_var s" using s'_simple by (auto simp: v_var_def)
    have qback_eq: "Qback_arr s' = Qback_arr s" using s'_simple by (auto simp: Qback_arr_def)
    have i_eq: "i_var s' = i_var s" using s'_simple by (auto simp: i_var_def)
    
    have pc_eq: "program_counter s' q = program_counter s q" 
      using s'_simple q_neq_p by (auto simp: program_counter_def)

    have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}" using pc_q' pc_eq by simp
    have inqb_s: "InQBack s b" using inqb' qback_eq unfolding InQBack_def by simp
    have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_eq by auto
    
    have hb_eq: "HB_EnqRetCall s' b (v_var s' q) = HB_EnqRetCall s b (v_var s q)"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq v_eq by auto
    have hb_s: "HB_EnqRetCall s b (v_var s q)" using hb' hb_eq by simp
    
    have idx_eq: "Idx s' b = Idx s b" unfolding Idx_def AtIdx_def using qback_eq by simp

    have "Idx s b < i_var s q"
      using inv_hI22 pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
      unfolding hI30_Ticket_HB_Immunity_def by blast
      
    thus "Idx s' b < i_var s' q" using idx_eq i_eq by simp
  qed

  thus ?thesis .
qed

lemma D3_success_preserves_hI14_Pending_Enq_Qback_Exclusivity:
  assumes INV: "system_invariant s"
      and PC: "program_counter s p = ''D3''"
      and STEP: "s' = Sys_D3_success_update s p"
  shows "hI14_Pending_Enq_Qback_Exclusivity s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def 
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def

  have inv_hI14_Pending_Enq_Qback_Exclusivity: "hI14_Pending_Enq_Qback_Exclusivity s"
    using INV unfolding system_invariant_def by blast

  have his_eq: "his_seq s' = his_seq s"
    using STEP unfolding Sys_D3_success_update_def Let_def his_seq_def lin_seq_def by auto

  have Qback_eq: "Qback_arr s' = Qback_arr s"
    using STEP unfolding Sys_D3_success_update_def Let_def bridge_defs 
    by (auto simp: fun_eq_iff)

  have i_var_eq: "i_var s' = i_var s"
    using STEP unfolding Sys_D3_success_update_def Let_def bridge_defs 
    by (auto simp: fun_eq_iff)

  have s_var_eq: "s_var s' = s_var s"
    using STEP unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs 
    by (auto simp: fun_eq_iff)

  have pending_eq: "\<And>q a. HasPendingEnq s' q a = HasPendingEnq s q a"
    unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def
    using his_eq s_var_eq by simp

  have pc_p_not_E: "program_counter s' p \<notin> {''E1'', ''E2'', ''E3''}"
    using STEP PC
    unfolding Sys_D3_success_update_def Let_def bridge_defs program_counter_def
    by (auto simp: fun_eq_iff)

  have pc_other_eq: "\<forall>q. q \<noteq> p \<longrightarrow> program_counter s' q = program_counter s q"
    using STEP PC
    unfolding Sys_D3_success_update_def Let_def bridge_defs program_counter_def
    by (auto simp: fun_eq_iff)

  show ?thesis
    using inv_hI14_Pending_Enq_Qback_Exclusivity pc_p_not_E pc_other_eq i_var_eq Qback_eq pending_eq
    unfolding hI14_Pending_Enq_Qback_Exclusivity_def
    by (metis insertCI)
qed

lemma D3_preserves_hI15_Deq_Result_Exclusivity:
  assumes "system_invariant s"
  assumes "program_counter s p = ''D3''"
  assumes "s' = Sys_D3_success_update s p"
  assumes "q_val = Q_arr s (j_var s p)"  (* Q_arr *)
  assumes "Q_arr s (j_var s p) \<noteq> BOT"    (* BOT *)
  shows "hI15_Deq_Result_Exclusivity s'"
proof -
  (* Step 1: 1. basic facts *)
  from assms(1) have 
    hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and 
    sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s" and TypeOK_s: "TypeOK s"
    unfolding system_invariant_def by auto
    
  define jp where "jp = j_var s p"
    
  (* 1: q_val *)
  have Q_is_qval: "Q_arr s jp = q_val"
    using assms(4) jp_def by simp

  (* 2: q_val *)
  have q_val_valid: "q_val \<in> Val" 
    using assms(5) TypeOK_s unfolding TypeOK_def jp_def
    using Q_is_qval jp_def by blast 

  (* 3: sI8_Q_Qback_Sync : BOT, q_val *)
  have Qback_is_qval: "Qback_arr s jp = q_val"
    using sI8_Q_Qback_Sync_s assms(5) Q_is_qval unfolding sI8_Q_Qback_Sync_def jp_def by metis

  (* Step 1: 1.5 s' *)
  have s'_fields: 
    "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    "x_var s' = (\<lambda>x. if x = p then q_val else x_var s x)"
    "Q_arr s' = (\<lambda>x. if x = jp then BOT else Q_arr s x)"
    "s_var s' = s_var s"
    "his_seq s' = his_seq s"
    (* j_var_def simplifier jp *)
    using assms unfolding Sys_D3_success_update_def Let_def jp_def
          program_counter_def x_var_def Q_arr_def s_var_def his_seq_def j_var_def
    by auto

  (* Step 2: 2. : s q_val "" *)
  (* q_val *)
  have no_his_s: "\<forall>q sn. \<not> DeqRetInHis s q q_val sn"
  proof (intro allI)
    fix q sn
    show "\<not> DeqRetInHis s q q_val sn"
      using hI15_Deq_Result_Exclusivity_s q_val_valid Q_is_qval unfolding hI15_Deq_Result_Exclusivity_def by blast
  qed

  (* D4 q_val *)
  have no_D4_s: "\<forall>q. program_counter s q = ''D4'' \<longrightarrow> x_var s q \<noteq> q_val"
  proof (intro allI impI notI)
    fix q assume pc_D4: "program_counter s q = ''D4''"
    assume conflict: "x_var s q = q_val"
    
    have "Q_arr s (j_var s q) = BOT" "Qback_arr s (j_var s q) = q_val"
      using sI7_D4_Deq_Result_s pc_D4 conflict unfolding sI7_D4_Deq_Result_def by auto
      
    (* sI10_Qback_Unique_Vals: Qback q_val, *)
    have "j_var s q = jp"
      using sI10_Qback_Unique_Vals_s `Qback_arr s (j_var s q) = q_val` Qback_is_qval q_val_valid
      unfolding sI10_Qback_Unique_Vals_def
      by (metis Q_is_qval assms(5) jp_def) 
      
    (* BOT q_val( BOT) *)
    show False 
      using `Q_arr s (j_var s q) = BOT` `j_var s q = jp` assms(5) jp_def by simp
  qed


  (* Step 3: 3. hI15_Deq_Result_Exclusivity *)
  show ?thesis
    unfolding hI15_Deq_Result_Exclusivity_def
  proof (intro conjI allI impI notI)
    
    (* === Part 1: === *)
    fix a p1 p2 :: nat    (* nat *)
    assume a_val: "a \<in> Val" and neq: "p1 \<noteq> p2"
    assume conflict: 
      "((\<exists>sn1. DeqRetInHis s' p1 a sn1) \<or> (program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a)) \<and>
       ((\<exists>sn2. DeqRetInHis s' p2 a sn2) \<or> (program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a))"
    
    let ?HasIt_s' = "\<lambda>proc. (\<exists>sn. DeqRetInHis s' proc a sn) \<or> (program_counter s' proc = ''D4'' \<and> x_var s' proc = a)"
    let ?HasIt_s  = "\<lambda>proc. (\<exists>sn. DeqRetInHis s proc a sn)  \<or> (program_counter s proc = ''D4'' \<and> x_var s proc = a)"

    show False
    proof (cases "a = q_val")
      case True
      (* a = q_val: D4 p *)
      have "p1 = p" 
      proof (rule ccontr)
        assume "p1 \<noteq> p"
        have "\<forall>sn. \<not> DeqRetInHis s' p1 a sn" using no_his_s s'_fields(5) True unfolding DeqRetInHis_def by simp
        moreover have "\<not> (program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a)"
          using s'_fields(1,2) `p1 \<noteq> p` no_D4_s True by simp
        ultimately show False using conflict `p1 \<noteq> p` by blast
      qed
      
      have "p2 = p" 
      proof (rule ccontr)
        assume "p2 \<noteq> p"
        have "\<forall>sn. \<not> DeqRetInHis s' p2 a sn" using no_his_s s'_fields(5) True unfolding DeqRetInHis_def by simp
        moreover have "\<not> (program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a)"
          using s'_fields(1,2) `p2 \<noteq> p` no_D4_s True by simp
        ultimately show False using conflict `p2 \<noteq> p` by blast
      qed
      
      show False using `p1 = p` `p2 = p` neq by simp
    next
      case False
      (* a \<noteq> q_val: s *)
      {
        fix q
        assume "?HasIt_s' q"
        have "?HasIt_s q"
        proof (cases "q = p")
          case True
          (* s' p D4(q_val). a \<noteq> q_val, s' p D4 a *)
          have "x_var s' p = q_val" using s'_fields(2) by simp
          then have "x_var s' p \<noteq> a" using False by simp
          then have "\<not> (program_counter s' p = ''D4'' \<and> x_var s' p = a)" by simp
          (* p a *)
          then obtain sn where "DeqRetInHis s' p a sn" using `?HasIt_s' q` True by blast
          (* Proof note. *)
          then have "DeqRetInHis s p a sn" using s'_fields(5) unfolding DeqRetInHis_def by simp
          then show ?thesis using True by blast
        next
          case False_q: False
          (* Proof note. *)
          have "program_counter s' q = program_counter s q" using s'_fields(1) False_q by simp
          have "x_var s' q = x_var s q" using s'_fields(2) False_q by simp
          
          show ?thesis 
          proof (cases "\<exists>sn. DeqRetInHis s' q a sn")
            case True
            then obtain sn where "DeqRetInHis s' q a sn" by blast
            then have "DeqRetInHis s q a sn" using s'_fields(5) unfolding DeqRetInHis_def by simp
            then show ?thesis by blast
          next
            case False
            then have "program_counter s' q = ''D4'' \<and> x_var s' q = a" using `?HasIt_s' q` False_q by blast
            then show ?thesis using `program_counter s' q = program_counter s q` `x_var s' q = x_var s q` by simp
          qed
        qed
      }
      note transfer = this
      
      have s_conflict_1: "?HasIt_s p1" using conflict transfer by simp
      have s_conflict_2: "?HasIt_s p2" using conflict transfer by simp
      
      show False 
        using hI15_Deq_Result_Exclusivity_s a_val neq s_conflict_1 s_conflict_2 unfolding hI15_Deq_Result_Exclusivity_def by blast
    qed

  next
    (* === Part 2: Pending Deq === *)
    fix p_test a k
    assume a_val: "a \<in> Val" and pending: "HasPendingDeq s' p_test"
    assume bad: "x_var s' p_test = a \<and> Q_arr s' k = a"
    
    have "a \<noteq> q_val"
    proof
      assume "a = q_val"
      have "k \<noteq> jp" 
      proof
        assume "k = jp"
        then have "Q_arr s' k = BOT" using s'_fields(3) by simp
        then show False using bad a_val unfolding Val_def BOT_def by simp
      qed
      
      then have "Q_arr s k = q_val" using bad `a = q_val` s'_fields(3) by simp
      have "Qback_arr s k = q_val" using sI8_Q_Qback_Sync_s `Q_arr s k = q_val` q_val_valid unfolding sI8_Q_Qback_Sync_def
        using Q_is_qval assms(5) jp_def by force 
      have "k = jp" using sI10_Qback_Unique_Vals_s `Qback_arr s k = q_val` Qback_is_qval unfolding sI10_Qback_Unique_Vals_def
        by (metis Q_is_qval assms(5) jp_def) 
      thus False using `k \<noteq> jp` by simp
    qed
    
    (* Proof note. *)
    (* HasPendingDeq s_var, s_var *)
    have "HasPendingDeq s p_test" 
      using pending s'_fields(4,5) unfolding HasPendingDeq_def DeqCallInHis_def Let_def by simp
      
    have "x_var s p_test = a" 
      using bad s'_fields(2) `a \<noteq> q_val` by (auto split: if_splits)
    
    have "Q_arr s k = a" 
    proof (cases "k = jp")
      case True
      then have "Q_arr s' k = BOT" using s'_fields(3) by simp
      then have "a = BOT" using bad by simp
      with a_val show ?thesis unfolding Val_def BOT_def by simp
    next
      case False
      then show ?thesis using bad s'_fields(3) by simp
    qed
    
    show False using hI15_Deq_Result_Exclusivity_s a_val `HasPendingDeq s p_test` `x_var s p_test = a` `Q_arr s k = a` unfolding hI15_Deq_Result_Exclusivity_def by blast

  next
    (* === Part 3: History vs Q === *)
    fix p_test a k
    assume a_val: "a \<in> Val" and has_his: "\<exists>sn. DeqRetInHis s' p_test a sn" and in_Q: "Q_arr s' k = a"
    
    (* Proof note. *)
    obtain sn where "DeqRetInHis s p_test a sn" using has_his s'_fields(5) unfolding DeqRetInHis_def by auto
    
    have "Q_arr s k = a" 
    proof (cases "k = jp")
      case True
      then have "Q_arr s' k = BOT" using s'_fields(3) by simp
      with in_Q a_val show ?thesis unfolding Val_def BOT_def by simp
    next
      case False
      then show ?thesis using in_Q s'_fields(3) by simp
    qed
    
    show False using hI15_Deq_Result_Exclusivity_s a_val `DeqRetInHis s p_test a sn` `Q_arr s k = a` unfolding hI15_Deq_Result_Exclusivity_def by blast
  qed
qed


(* ================================================================= *)
(* lI2_Op_Cardinality D3 *)
(* SetA SetB *)
(* ================================================================= *)
lemma lI2_Op_Cardinality_D3_step_lemma:
  assumes INV_s: "system_invariant s"
  assumes q_val_SetB: "q_val \<in> SetB s"
  (* Revision note 1: mk_op sn (Isabelle sn ) *)
  assumes mset_eq: "mset (lin_seq s') = mset (lin_seq s) + {# mk_op deq q_val p sn #}"
  assumes SetA_eq: "SetA s' = SetA s \<union> {q_val}"
  assumes SetB_eq: "SetB s' = SetB s - {q_val}"
  shows "lI2_Op_Cardinality s'"
proof -
  (* Step 1: 1. lI2_Op_Cardinality *)
  from INV_s have lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" unfolding system_invariant_def by simp
  
  (* Step 3: 3. lI2_Op_Cardinality *)
  show ?thesis
    unfolding lI2_Op_Cardinality_def
  proof (intro conjI)
    
    (* === Part A: SetA === *)
    show "\<forall>a. a \<in> SetA s' \<longrightarrow> card (EnqIdxs s' a) = 1 \<and> card (DeqIdxs s' a) = 1"
    proof (intro allI impI)
      fix a assume a_in: "a \<in> SetA s'"
      
      show "card (EnqIdxs s' a) = 1 \<and> card (DeqIdxs s' a) = 1"
      proof (cases "a = q_val")
        case True
        (* Case A.1: a q_val *)
        
        (* Enq 1 *)
        have enq_count: "card (EnqIdxs s' q_val) = 1"
        proof -
          have "card (EnqIdxs s q_val) = 1"
            using lI2_Op_Cardinality_s q_val_SetB unfolding lI2_Op_Cardinality_def by simp
          (* s' = s + {deq}, deq , Enq *)
          moreover have "card (EnqIdxs s' q_val) = card (EnqIdxs s q_val)"
            using mset_eq by (simp add: card_EnqIdxs_mset_eq mk_op_def op_name_def)
          ultimately show ?thesis by simp
        qed

        (* Deq 1 *)
        have deq_count: "card (DeqIdxs s' q_val) = 1"
        proof -
          have "card (DeqIdxs s q_val) = 0"
            using lI2_Op_Cardinality_s q_val_SetB unfolding lI2_Op_Cardinality_def by simp
          (* s' = s + {deq(q_val)}, Deq + 1 *)
          moreover have "card (DeqIdxs s' q_val) = card (DeqIdxs s q_val) + 1"
            using mset_eq by (simp add: card_DeqIdxs_mset_incr mk_op_def op_name_def op_val_def)
          ultimately show ?thesis by simp
        qed
        
        show ?thesis using enq_count deq_count True by simp 
        
      next
        case False
        (* Case A.2: a SetA *)
        have old_A: "a \<in> SetA s" using a_in SetA_eq False by simp
        
        (* Enq/Deq , a != q_val *)
        have enq_stable: "card (EnqIdxs s' a) = card (EnqIdxs s a)"
          using mset_eq False by (simp add: card_EnqIdxs_mset_eq mk_op_def op_name_def op_val_def)
          
        have deq_stable: "card (DeqIdxs s' a) = card (DeqIdxs s a)"
          using mset_eq False by (simp add: card_DeqIdxs_mset_unchanged mk_op_def op_name_def op_val_def)
          
        show ?thesis
          using lI2_Op_Cardinality_s old_A enq_stable deq_stable unfolding lI2_Op_Cardinality_def by simp
      qed
    qed
    
    (* === Part B: SetB === *)
    show "\<forall>b. b \<in> SetB s' \<longrightarrow> card (EnqIdxs s' b) = 1 \<and> card (DeqIdxs s' b) = 0"
    proof (intro allI impI)
      fix b assume b_in: "b \<in> SetB s'"
      
      (* Proof note. *)
      have old_B: "b \<in> SetB s" using b_in SetB_eq by auto
      have b_neq: "b \<noteq> q_val" using b_in SetB_eq by auto
      
      (* Enq ( simp, metis) *)
      have enq_stable: "card (EnqIdxs s' b) = card (EnqIdxs s b)"
        using mset_eq b_neq by (simp add: card_EnqIdxs_mset_eq mk_op_def op_name_def op_val_def)
        
      (* Revision note 2: Deq . b \<noteq> q_val, Part A , *)
      have deq_stable: "card (DeqIdxs s' b) = card (DeqIdxs s b)"
        using mset_eq b_neq by (simp add: card_DeqIdxs_mset_unchanged mk_op_def op_name_def op_val_def) 
        
      (* Proof note. *)
      have "card (EnqIdxs s b) = 1" and "card (DeqIdxs s b) = 0"
        using lI2_Op_Cardinality_s old_B unfolding lI2_Op_Cardinality_def by auto
        
      show "card (EnqIdxs s' b) = 1 \<and> card (DeqIdxs s' b) = 0"
        using enq_stable deq_stable `card (EnqIdxs s b) = 1` `card (DeqIdxs s b) = 0` by simp
    qed
  qed
qed


(* ========================================================================= *)
(* Auxiliary lemma: SetB D3 *)
(* ========================================================================= *)
lemma SetB_D3_step_lemma:
  assumes INV_s: "system_invariant s"
  (* 【 】 s' = ..., *)
  (* Step 1: 1. Q BOT *)
  assumes Q_update: "Q_arr s' = (Q_arr s)(jp := BOT)"
  (* Step 2: 2. PC D4 *)
  assumes PC_update: "program_counter s' = (program_counter s)(p := ''D4'')"
  (* Step 3: 3. v_var (D3 v_var) *)
  assumes v_stable: "v_var s' = v_var s"
  
  (* Proof note. *)
  assumes q_val_def: "q_val = Q_arr s jp"
  assumes jp_def: "jp = head s p"
  assumes q_not_bot: "q_val \<noteq> BOT"
  assumes q_in_SetB: "q_val \<in> SetB s"
  assumes pc_at_D3: "program_counter s p = ''D3''"
  shows "SetB s' = SetB s - {q_val}"
proof (rule set_eqI)
  fix x
  
  have "TypeOK s" using INV_s unfolding system_invariant_def by simp
  have "sI3_E2_Slot_Exclusive s" using INV_s unfolding system_invariant_def by simp
  have "sI10_Qback_Unique_Vals s" using INV_s unfolding system_invariant_def by simp

  (* Step 1: 1. BOT *)
  have case_bot_logic: "x = BOT \<Longrightarrow> x \<notin> SetB s \<and> x \<notin> SetB s'"
  proof -
    assume "x = BOT"
    have "BOT \<notin> SetB s" 
      using `TypeOK s` unfolding TypeOK_def TypeB_def Val_def SetB_def by (simp add: BOT_def)
    have "BOT \<notin> SetB s'"
    proof
      assume "BOT \<in> SetB s'"
      have "SetB s' \<subseteq> Val" unfolding SetB_def Val_def TypeB_def by blast 
      then show False using `BOT \<in> SetB s'` unfolding Val_def using BOT_def by auto
    qed
    show ?thesis using `BOT \<notin> SetB s` `BOT \<notin> SetB s'` by (simp add: \<open>x = BOT\<close>)
  qed

  (* Step 3: 3. *)
  show "x \<in> SetB s' \<longleftrightarrow> x \<in> SetB s - {q_val}"
  proof (cases "x = BOT")
    case True then show ?thesis using case_bot_logic by simp
  next
    case False
    note x_not_bot = False
    
    show ?thesis
    proof (cases "x = q_val")
      case True
      (* === Case A: x q_val === *)
      have "q_val \<notin> SetB s'"
      proof
        assume "q_val \<in> SetB s'"
        then consider "QHas s' q_val" | "\<exists>t. program_counter s' t = ''E2'' \<and> v_var s' t = q_val"
          unfolding SetB_def TypeB_def by blast
        then show False
        proof cases
          case 1 (* QHas s' q_val *)
          obtain k where k_val: "Q_arr s' k = q_val" using 1 unfolding QHas_def by blast
          (* Q_update *)
          have "k \<noteq> jp" using k_val Q_update q_not_bot by (metis fun_upd_apply) 
          then have "Q_arr s k = q_val" using k_val Q_update by auto
          have "Q_arr s jp = q_val" using q_val_def by simp
          show False
            using `Q_arr s k = q_val` `Q_arr s jp = q_val` `k \<noteq> jp` 
            unfolding lI2_Op_Cardinality_def EnqIdxs_def
            by (metis sI10_Qback_Unique_Vals_def sI8_Q_Qback_Sync_def INV_s True \<open>Q_arr s k = q_val\<close> \<open>k \<noteq> jp\<close>
                q_val_def system_invariant_def x_not_bot)
    next
      case 2 (* E2 *)
      obtain t where t_state: "program_counter s' t = ''E2''" "v_var s' t = q_val" using 2 by blast
      
      (* Step 1: 1. t *)
      have "program_counter s' p = ''D4''" using PC_update by simp
      then have "t \<noteq> p" using t_state(1) by auto
      
      have pc_t: "program_counter s t = ''E2''" 
        using t_state(1) PC_update `t \<noteq> p` by auto
      have v_t: "v_var s t = q_val" 
        using t_state(2) v_stable by simp
      
      (* Step 2: 2. t Enq ( D3Lemmas ) *)
      have pending_t: "HasPendingEnq s t q_val"
        using E2_implies_HasPendingEnq[OF INV_s pc_t] v_t by simp

      (* Step 3: 3. q_val Qback *)
      (* sI8_Q_Qback_Sync sI10_Qback_Unique_Vals: Q[jp] = q_val -> Qback[jp] = q_val *)
      have ai8: "sI8_Q_Qback_Sync s" and ai10: "sI10_Qback_Unique_Vals s" and sI3_E2_Slot_Exclusive: "sI3_E2_Slot_Exclusive s"
        using INV_s unfolding system_invariant_def by auto
        
      have "Qback_arr s jp = q_val"
        by (metis sI8_Q_Qback_Sync_def ai8 q_not_bot q_val_def)


      (* Step 4: 4. t BOT (E2 ) *)
      have "Qback_arr s (i_var s t) = BOT"
        using sI3_E2_Slot_Exclusive pc_t unfolding sI3_E2_Slot_Exclusive_def by simp

      (* Step 5: 5. *)
      show False
        using pending_t `Qback_arr s jp = q_val` `Qback_arr s (i_var s t) = BOT`
        using INV_s
        (* , *)
        unfolding system_invariant_def hI14_Pending_Enq_Qback_Exclusivity_def HasPendingEnq_def
        using True pc_t x_not_bot by blast
    qed
      qed
      then show ?thesis using True by simp
    next
      case False
      (* === Case B: x \<noteq> q_val === *)
      note neq_q = False
      
      (* Step 1: 1. QHas *)
      have "QHas s' x \<longleftrightarrow> QHas s x"
      proof -
        have "\<forall>k. Q_arr s' k = (if k = jp then BOT else Q_arr s k)"
          using Q_update by auto
        then show ?thesis
          unfolding QHas_def
          using neq_q x_not_bot q_val_def by (metis)
      qed
      
      (* Step 2: 2. E2 *)
      have "(\<exists>p. program_counter s' p = ''E2'' \<and> v_var s' p = x) \<longleftrightarrow> 
            (\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = x)"
      proof
        (* -> *)
        assume "\<exists>p. program_counter s' p = ''E2'' \<and> v_var s' p = x"
        then obtain t where t_st: "program_counter s' t = ''E2''" "v_var s' t = x" by blast
        (* t != p *)
        have "program_counter s' p = ''D4''" using PC_update by simp
        then have "t \<noteq> p" using t_st by auto
        
        have "program_counter s t = ''E2''" using t_st PC_update `t \<noteq> p` by auto
        have "v_var s t = x" using t_st v_stable by simp
        then show "\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = x" 
          using `program_counter s t = ''E2''` by blast
      next
        (* <- *)
        assume "\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = x"
        then obtain t where t_st: "program_counter s t = ''E2''" "v_var s t = x" by blast
        (* t != p *)
        have "t \<noteq> p" using t_st pc_at_D3 by auto
        
        have "program_counter s' t = ''E2''" using t_st PC_update `t \<noteq> p` by auto
        have "v_var s' t = x" using t_st v_stable by simp
        then show "\<exists>p. program_counter s' p = ''E2'' \<and> v_var s' p = x" 
          using `program_counter s' t = ''E2''` by blast
      qed

      show ?thesis
        using `QHas s' x \<longleftrightarrow> QHas s x` 
        using `(\<exists>p. program_counter s' p = ''E2'' \<and> v_var s' p = x) \<longleftrightarrow> (\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = x)`
        unfolding SetB_def TypeB_def using neq_q by auto
    qed
  qed
qed


lemma modify_step_c0_consistent:
  (* 1. *)
  assumes sys_inv: "system_invariant s"
  assumes H_cons: "HB_consistent L H"
  assumes H_def: "H = his_seq s"
  assumes di: "data_independent L"
  assumes mset_eq: "mset L = mset (lin_seq s)"  
  assumes sa_iso: "\<forall>v. in_SA v L \<longleftrightarrow> in_SA v (lin_seq s)"
  (* 2. *)
  assumes L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
  assumes l2_decomp: "l2 = ll2 @ [l2_last]"
  
  (* 3. *)
  assumes last_sa_pos_def: "last_sa_pos = find_last_SA L"
  assumes l1_def: "l1 = take (nat (last_sa_pos + 1)) L"
  
  (* 4. *)
  assumes l2_last_enq: "op_name l2_last = enq"
  assumes bt_is_enq: "op_name bt_act = enq"
  assumes bt_val_type: "TypeBT s (op_val bt_act)" 
  
  (* Proof note. *)
  shows "HB_consistent (l1 @ ll2 @ [bt_act] @ [l2_last] @ l3) H"
proof -
  (* Step 1: 1. pre, L *)
  define pre where "pre = l1 @ ll2"
  
  have L_struct: "L = pre @ [l2_last] @ [bt_act] @ l3"
    using L_decomp l2_decomp pre_def by simp

  (* Step 2: 2. : l2_last bt_act HB *)
  (* HB_swap_adjacent HB *)
  have not_hb: "\<not> HB H l2_last bt_act"
  proof -
    (* HB_Act TypeBT_implies_no_HB *)
    have target: "\<not> HB_Act s l2_last bt_act"
    proof (rule TypeBT_implies_no_HB[OF sys_inv])
      
      (* Step 2: 2.1 : TypeBT *)
      show "TypeBT s (op_val bt_act)" using bt_val_type .

      (* Step 2: 2.2 : (l2_last) Enq *)
      show "l2_last \<in> active_enqs s"
      proof -
        (* Proof note. *)
        define rest where "rest = ll2 @ [l2_last] @ [bt_act] @ l3"
        have L_split: "L = l1 @ rest" using L_decomp l2_decomp rest_def by simp
        have rest_not_nil: "rest \<noteq> []" unfolding rest_def by simp
        
        (* l1 Enq SA *)
        have all_succ_not_SA: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
          using l1_contains_all_SA_in_L[OF di L_split rest_not_nil l1_def last_sa_pos_def]
          by simp

        (* l2_last L *)
        let ?idx = "length pre"
        have idx_ge: "?idx \<ge> length l1" unfolding pre_def by simp
        have idx_valid: "?idx < length L" using L_struct by simp
        have is_l2_last: "L ! ?idx = l2_last" using L_struct by (simp add: nth_append)
        
        (* l2_last SA *)
        have not_sa: "\<not> in_SA (op_val l2_last) L"
          using all_succ_not_SA idx_ge idx_valid is_l2_last l2_last_enq by blast

        (* lin_seq s *)
        have in_lin_seq: "l2_last \<in> set (lin_seq s)"
          using L_struct mset_eq
          by (metis idx_valid is_l2_last mset_eq_setD nth_mem)

        have not_sa_s: "\<not> in_SA (op_val l2_last) (lin_seq s)"
          using not_sa sa_iso by auto

        have lI1_Op_Sets_Equivalence: "lI1_Op_Sets_Equivalence s" using sys_inv unfolding system_invariant_def by simp
        have lI2_Op_Cardinality: "lI2_Op_Cardinality s" using sys_inv unfolding system_invariant_def by simp
        
        (* SA Enq *)
        show ?thesis
          using non_SA_enqs_are_active[OF lI1_Op_Sets_Equivalence lI2_Op_Cardinality] in_lin_seq l2_last_enq not_sa_s
          by blast
      qed

      (* Step 2: 2.3 *)
      show "l2_last \<noteq> bt_act"
      proof
        assume eq: "l2_last = bt_act"
        (* Enq *)
        have "length pre < length L" using L_struct by simp
        have "Suc (length pre) < length L" using L_struct by simp
        have "op_val (L ! length pre) = op_val (L ! Suc (length pre))"
          using eq L_struct l2_last_enq bt_is_enq by (simp add: nth_append)
        
        have "length pre = Suc (length pre)"
          apply (rule same_enq_value_same_index[OF di])
          using \<open>length pre < length L\<close> \<open>Suc (length pre) < length L\<close> 
          using L_struct l2_last_enq bt_is_enq \<open>op_val (L ! length pre) = op_val (L ! Suc (length pre))\<close>
          by (auto simp: nth_append)
        then show False by simp
      qed

      (* Step 2: 2.4 *)
      show "op_name l2_last = enq" using l2_last_enq .
      show "op_name bt_act = enq" using bt_is_enq .

      (* Step 2: 2.5 : bt_act *)
      show "op_val bt_act \<in> Val"
      proof -
        have "bt_act \<in> set (lin_seq s)" using L_struct mset_eq
          by (metis append_assoc append_Cons in_set_conv_decomp mset_eq_setD)
        thus ?thesis
          using lin_seq_enq_in_sets[OF sys_inv] bt_is_enq unfolding SetA_def SetB_def by blast
      qed

      (* Step 2: 2.6 : l2_last SetBO SetBT *)
      show "op_val l2_last \<in> SetBO s \<or> op_val l2_last \<in> SetBT s"
      proof -
        (* l2_last SetA *)
        have "op_val l2_last \<notin> SetA s"
        proof
          assume "op_val l2_last \<in> SetA s"
          then have "in_SA (op_val l2_last) (lin_seq s)"
            using SetA_implies_in_SA[OF sys_inv] by simp
          then have "in_SA (op_val l2_last) L"
            using sa_iso by simp
          
          (* l1 SA *)
          define rest where "rest = ll2 @ [l2_last] @ [bt_act] @ l3"
          have L_split: "L = l1 @ rest" using L_decomp l2_decomp rest_def by simp
          have "rest \<noteq> []" unfolding rest_def by simp
          have "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
            using l1_contains_all_SA_in_L[OF di L_split \<open>rest \<noteq> []\<close> l1_def last_sa_pos_def] by simp
          
          have "\<not> in_SA (op_val l2_last) L"
          proof -
            let ?idx = "length pre"
            have idx_ge: "?idx \<ge> length l1" 
              unfolding pre_def by simp
            have idx_valid: "?idx < length L" 
              using L_struct by simp
            have val_at_idx: "L ! ?idx = l2_last" 
              using L_struct by (simp add: nth_append)
            have is_enq: "op_name (L ! ?idx) = enq" 
              using val_at_idx l2_last_enq by simp
            show ?thesis
              using \<open>\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L\<close>
              using idx_ge idx_valid is_enq val_at_idx
              by blast
          qed
            
          thus False using \<open>in_SA (op_val l2_last) L\<close> by simp
        qed
        
        have "l2_last \<in> set (lin_seq s)"
          using L_struct mset_eq
          by (metis append_Cons in_set_conv_decomp mset_eq_setD) 
          
        (* LinSeq_Enq_State_Mapping *)
        show ?thesis
          using LinSeq_Enq_State_Mapping[OF sys_inv \<open>l2_last \<in> set (lin_seq s)\<close> l2_last_enq \<open>op_val l2_last \<notin> SetA s\<close>] .
      qed
    qed
    
    (* target , HB *)
    thus ?thesis unfolding HB_Act_def H_def .
  qed

  (* Step 3: 3. Swap *)
  (* pre = l1 @ ll2, pre @ [l2_last] @ [bt_act] @ l3 L *)
  have "HB_consistent (pre @ [bt_act] @ [l2_last] @ l3) H"
  proof (rule HB_swap_adjacent)
    show "HB_consistent (pre @ [l2_last] @ [bt_act] @ l3) H"
      using H_cons L_struct by simp
      
    (* HB, *)
    show "\<not> HB H l2_last bt_act"
      using not_hb .
  qed

  then show ?thesis unfolding pre_def by simp
qed


lemma modify_step_c1_consistent:
  (* 1. *)
  assumes sys_inv: "system_invariant s"
  assumes H_cons: "HB_consistent L H"
  assumes H_def: "H = his_seq s"        
  assumes mset_eq: "mset L = mset (lin_seq s)" 

  (* 2. *)
  assumes L_decomp: "L = prefix @ [b_act] @ [o1] @ suffix"
  
  (* 3. *)
  assumes b_is_enq: "op_name b_act = enq"
  assumes o1_is_deq: "op_name o1 = deq"
  
  (* [ ] *)
  assumes bt_in_L: "bt_act \<in> set L"
  assumes bt_is_enq: "op_name bt_act = enq"
  assumes bt_val_type: "TypeBT s (op_val bt_act)"
  
  (* 4. c1 *)
  assumes hb_o1_bt: "HB H o1 bt_act" 
  
  (* 5. *)
  assumes b_active: "b_act \<in> active_enqs s"
  assumes b_neq_bt: "b_act \<noteq> bt_act"
  assumes b_val_sets: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"

  (* Proof note. *)
  shows "HB_consistent (prefix @ [o1] @ [b_act] @ suffix) H"
proof -
  (* Step 1: 1. *)
  have L_struct: "L = prefix @ [b_act] @ [o1] @ suffix"
    using L_decomp by simp

  (* Step 2: 2. : b_act o1 HB *)
  have not_hb: "\<not> HB H b_act o1"
  proof
    (* === : b_act -> o1 === *)
    assume conflict: "HB H b_act o1"
    
    (* A. b_act -> bt_act *)
    (* 1: HB_Act , HB_transitive_lemma *)
    have "HB_Act s b_act bt_act"
    proof (rule HB_transitive_lemma[OF sys_inv H_def])
      
      (* A.1 1: b -> o1 ( ) *)
      show "HB_Act s b_act o1" 
        using conflict H_def unfolding HB_Act_def by simp
      
      (* A.2 2: o1 -> bt ( c1 ) *)
      show "HB_Act s o1 bt_act" 
        using hb_o1_bt H_def unfolding HB_Act_def by simp
      
      (* A.3 3: o1 *)
      show "op_name o1 = enq \<or> op_val o1 \<in> Val"
      proof -
        (* o1 L -> lin_seq s *)
        have "o1 \<in> set L" using L_struct by simp
        then have "o1 \<in> set (lin_seq s)" 
          using mset_eq by (metis mset_eq_setD)
          
        (* LinSeq_Deq_Val_Valid *)
        have "op_val o1 \<in> Val"
          using LinSeq_Deq_Val_Valid[OF sys_inv `o1 \<in> set (lin_seq s)` o1_is_deq] .
          
        thus ?thesis by simp
      qed
    qed
    
    (* 2: HB H *)
    then have b_hb_bt: "HB H b_act bt_act"
      using H_def unfolding HB_Act_def by simp

    (* B. TypeBT_No_HB_Target (\<not> b_act -> bt_act) *)
    (* TypeBT_No_HB_Target *)
    have not_b_hb_bt: "\<not> HB H b_act bt_act"
    proof (rule TypeBT_No_HB_Target[OF sys_inv])
      (* Proof note. *)
      show "lin_seq s = lin_seq s" ..
      show "H = his_seq s" using H_def .
      
      (* Step 1: 1. bt_act *)
      (* bt_act lin_seq *)
      show "bt_act \<in> set (lin_seq s)" 
        using bt_in_L mset_eq by (metis mset_eq_setD)

      show "op_name bt_act = enq" using bt_is_enq .
      show "TypeBT s (op_val bt_act)" using bt_val_type .
      
      (* Step 2: 2. b_act *)
      show "b_act \<in> set (lin_seq s)" 
        using L_struct mset_eq
        by (metis append_Cons in_set_conv_decomp mset_eq_setD) 
      show "op_name b_act = enq" using b_is_enq .
      show "b_act \<noteq> bt_act" using b_neq_bt .
      
      (* Step 3: 3. : b_act SetA *)
      show "op_val b_act \<notin> SetA s"
      proof
        assume "op_val b_act \<in> SetA s"
        (* SetA SetB (BO U BT) *)
        (* b_val_sets: b SetBO SetBT *)
        have "op_val b_act \<in> SetB s" 
          using b_val_sets unfolding SetB_partition by auto
          
        (* SetA SetB *)
        have "SetA s \<inter> SetB s = {}" 
          unfolding SetA_def SetB_def TypeA_def TypeB_def
          using LinSeq_Enq_Val_Valid TypeBT_implies_no_HB \<open>HB_Act s b_act bt_act\<close>
            \<open>bt_act \<in> set (lin_seq s)\<close> b_active b_is_enq b_neq_bt b_val_sets
            bt_is_enq bt_val_type sys_inv by blast
          
        then show False 
          using `op_val b_act \<in> SetA s` `op_val b_act \<in> SetB s` 
          by blast
      qed
    qed

    (* C. *)
    show False using b_hb_bt not_b_hb_bt by simp
  qed

  (* Step 3: 3. Swap *)
  show ?thesis
  proof (rule HB_swap_adjacent)
    show "HB_consistent (prefix @ [b_act] @ [o1] @ suffix) H"
      using H_cons L_struct by simp
    show "\<not> HB H b_act o1"
      using not_hb .
  qed
qed


lemma modify_step_c2_consistent:
  assumes sys: "system_invariant s"
  and hb_cons: "HB_consistent L H"
  and H_def: "H = his_seq s"
  and inv_mset: "mset L = mset (lin_seq s)"
  (* Proof note. *)
  and L_def: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
  and l22_not_nil: "l22 \<noteq> []"
  (* Proof note. *)
  and bt_enq: "op_name bt_act = enq"
  and bt_type: "TypeBT s (op_val bt_act)"
  and bt_in: "bt_act \<in> set L"
  and o1_def: "o1 = hd l22"
  and b_enq: "op_name b_act = enq"
  and b_active: "b_act \<in> active_enqs s"
  and b_neq_bt: "b_act \<noteq> bt_act"
  and b_val: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"
  (* Proof note. *)
  and not_c1: "\<not> HB H o1 bt_act" 
  and c2: "HB H b_act o1"
  (* l22 Deq ( D3 ) *)
  and l22_deqs: "\<forall>x \<in> set l22. op_name x = deq"
  (* Proof note. *)
shows "HB_consistent (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) H"
proof -
  (* Step 1: 1. *)
  define pre where "pre = l1 @ l21"
  define middle where "middle = [b_act] @ l22"
   
  (* Proof note. *)
  have L_struct: "L = pre @ middle @ [bt_act] @ l3"
    using L_def pre_def middle_def by simp

  (* Step 2: 2. b_act Happens-Before bt_act *)
  have not_hb_b_bt: "\<not> HB H b_act bt_act"
  proof
    assume "HB H b_act bt_act"
    
    (* hI16_BO_BT_No_HB/hI17_BT_BT_No_HB *)
    have hb_rel: "HB_EnqRetCall s (op_val b_act) (op_val bt_act)"
      unfolding HB_EnqRetCall_def
      apply (rule exI[where x="op_pid b_act"])
      apply (rule exI[where x="op_pid bt_act"])
      using `HB H b_act bt_act` b_enq bt_enq H_def 
      unfolding HB_Act_def mk_op_def op_name_def op_val_def op_pid_def
      by (metis split_pairs) 

    (* branch-specific reasoning *)
    from b_val show False
    proof (elim disjE)
      (* === Case A: b_act \<in> SetBO === *)
      assume in_BO: "op_val b_act \<in> SetBO s"
      
      have in_BT: "op_val bt_act \<in> SetBT s"
        using bt_type unfolding SetBT_def
        by (metis LinSeq_Enq_Val_Valid bt_enq bt_in inv_mset mem_Collect_eq
            mset_eq_setD sys) 

      show False
        using sys in_BO in_BT hb_rel
        unfolding system_invariant_def hI16_BO_BT_No_HB_def
        by blast
        
    next
      (* === Case B: b_act \<in> SetBT === *)
      assume in_BT_b: "op_val b_act \<in> SetBT s"
      
      have in_BT_bt: "op_val bt_act \<in> SetBT s"
        using bt_type unfolding SetBT_def
        by (metis LinSeq_Enq_Val_Valid bt_enq bt_in inv_mset mem_Collect_eq
            mset_eq_setD sys) 
      
      show False
        using sys in_BT_b in_BT_bt hb_rel
        unfolding system_invariant_def hI17_BT_BT_No_HB_def
        by blast
    qed
  qed

  (* Step 3: 3. l22 Happens-Before bt_act *)
  have no_hb_l22: "\<forall>d \<in> set l22. \<not> HB H d bt_act"
  proof
    fix d assume d_in: "d \<in> set l22"

    (* Step 3: 3.1 HB_barrier_protection *)
    define idx_o1 where "idx_o1 = length pre + 1" (* b_act *)
    
    (* d l22 k *)
    obtain k where k_valid: "k < length l22" and d_at_k: "l22 ! k = d"
      using d_in by (auto simp: in_set_conv_nth)
      
    define idx_d where "idx_d = idx_o1 + k"
    
    (* Step 3: 3.2 *)
    have idx_o1_valid: "idx_o1 < length L"
      using L_def l22_not_nil pre_def idx_o1_def by simp
      
    have idx_d_valid: "idx_d < length L" 
      using L_def l22_not_nil pre_def idx_o1_def idx_d_def k_valid by simp
    
    have L_at_idx_o1: "L ! idx_o1 = o1"
      unfolding L_def pre_def[symmetric] idx_o1_def o1_def
      using l22_not_nil
      by (metis (no_types, lifting) L_def L_struct append_Cons
          append_is_Nil_conv append_self_conv2 diff_is_0_eq' hd_append2
          hd_conv_nth le_numeral_extra(4) less_numeral_extra(1) middle_def
          nth_Cons_pos nth_append_length_plus)
      
    (* L , pre, *)
    have L_struct_simple: "L = pre @ [b_act] @ l22 @ [bt_act] @ l3"
      using L_def pre_def by simp

    (* idx_d *)
    have idx_val: "idx_d = length pre + 1 + k"
      using idx_d_def idx_o1_def by simp

    (* Proof note. *)
    have L_at_idx_d: "L ! idx_d = d"
      unfolding L_struct_simple idx_val
      apply (simp add: nth_append)
      by (simp add: d_at_k k_valid)

      
    have order: "idx_o1 \<le> idx_d" unfolding idx_d_def by simp

    (* Step 3: 3.3 o1 Deq *)
    have o1_is_deq: "op_name o1 = deq"
      using o1_def l22_not_nil l22_deqs by auto

    (* Step 3: 3.4 barrier *)
    show "\<not> HB H d bt_act"
      apply (rule HB_barrier_protection[OF hb_cons])
      (* Proof note. *)
      apply (rule idx_o1_valid)
      apply (rule idx_d_valid)
      (* Proof note. *)
      apply (rule L_at_idx_o1)
      apply (rule L_at_idx_d)
      (* Proof note. *)
      apply (rule order)
      (* Proof note. *)
      apply (rule c2)
      apply (rule not_hb_b_bt)
      apply (rule bt_enq)
      apply (rule o1_is_deq)
      done
  qed

  (* Step 4: 4. middle *)
  (* middle = [b_act] @ l22 *)
  have middle_safe: "\<forall>m \<in> set middle. \<not> HB H m bt_act"
    using not_hb_b_bt no_hb_l22 unfolding middle_def by auto

  (* Step 5: 5. HB_jump_left *)
  (* HB_consistent (pre @ [bt_act] @ middle @ l3) H *)
  
  have list_eq: "l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3 = pre @ [bt_act] @ middle @ l3"
    unfolding pre_def middle_def by simp

  show ?thesis
    unfolding list_eq
    apply (rule HB_jump_left)
    (* 1: Consistent *)
    using hb_cons L_struct apply simp
    (* 2: middle HB bt_act *)
    using middle_safe apply simp
    done
qed


lemma modify_step_c3_new_consistent:
  (* 1. *)
  assumes sys_inv: "system_invariant s"
  assumes H_cons: "HB_consistent L H"
  assumes H_def: "H = his_seq s"        
  assumes mset_eq: "mset L = mset (lin_seq s)" 

  (* 2. *)
  assumes L_decomp: "L = prefix @ [b_act] @ [o1] @ suffix"
  
  (* 3. *)
  assumes b_is_enq: "op_name b_act = enq"
  assumes o1_is_deq: "op_name o1 = deq"
  
  (* [ ] *)
  assumes bt_in_L: "bt_act \<in> set L"
  assumes bt_is_enq: "op_name bt_act = enq"
  assumes bt_val_type: "TypeBT s (op_val bt_act)"
  
  (* 4. c1 *)
  assumes hb_o1_bt: "\<not> HB H o1 bt_act \<and> \<not> HB H b_act o1"
  
  (* 5. *)
  assumes b_active: "b_act \<in> active_enqs s"
  assumes b_neq_bt: "b_act \<noteq> bt_act"
  assumes b_val_sets: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"

  (* Proof note. *)
  shows "HB_consistent (prefix @ [o1] @ [b_act] @ suffix) H"
proof -
  (* Step 1: 1. *)
  have L_struct: "L = prefix @ [b_act] @ [o1] @ suffix"
    using L_decomp by simp

  (* Step 2: 2. : b_act o1 HB *)
  have not_hb: "\<not> HB H b_act o1"
    by (simp add: hb_o1_bt)

  (* Step 3: 3. Swap *)
  show ?thesis
  proof (rule HB_swap_adjacent)
    show "HB_consistent (prefix @ [b_act] @ [o1] @ suffix) H"
      using H_cons L_struct by simp
    show "\<not> HB H b_act o1"
      using not_hb .
  qed
qed


lemma modify_step_c3_consistent:
  (* 1. ( c0 ) *)
  assumes sys_inv: "system_invariant s"
  assumes H_cons: "HB_consistent L H"
  assumes H_def: "H = his_seq s"
  assumes mset_eq: "mset L = mset (lin_seq s)"

  (* 2. ( c0 l2_decomp) *)
  assumes L_decomp: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
  assumes l22_decomp: "l22 = l22_rest @ [ou]"
  
  (* 3. ( c0 l2_last_enq ) *)
  (* bt_act *)
  assumes bt_is_enq: "op_name bt_act = enq"
  assumes bt_val_type: "TypeBT s (op_val bt_act)"
  assumes bt_in_L: "bt_act \<in> set L"
  
  (* ou (c3 ) *)
  assumes ou_is_deq: "op_name ou = deq"

  (* b_act ( ) *)
  assumes b_is_enq: "op_name b_act = enq"
  assumes b_active: "b_act \<in> active_enqs s"
  assumes b_neq_bt: "b_act \<noteq> bt_act"
  assumes b_val_sets: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"
  
  (* 4. (c3 ) *)
  assumes c3: "HB H b_act ou"
  
  (* ou bt_act *)
  shows "HB_consistent (l1 @ l21 @ [b_act] @ l22_rest @ [bt_act] @ [ou] @ l3) H"
proof -
  (* Step 1: 1. pre ( c0: define pre where "pre = l1 @ ll2") *)
  define pre where "pre = l1 @ l21 @ [b_act] @ l22_rest"
  
  (* L ( c0: have L_struct ...) *)
  have L_struct: "L = pre @ [ou] @ [bt_act] @ l3"
    using L_decomp l22_decomp pre_def by simp

  (* Step 2: 2. : ( c0: have not_hb ...) *)
  have not_hb: "\<not> HB H ou bt_act"
  proof
    (* Proof note. *)
    assume conflict: "HB H ou bt_act"
    
    (* c0 , *)
    
    (* A. b_act -> bt_act *)
    (* b_act -> ou (c3 ) -> bt_act ( ) *)
    have b_hb_bt: "HB H b_act bt_act"
    proof -
       (* HB_Act HB_transitive_lemma *)
       have "HB_Act s b_act bt_act"
       proof (rule HB_transitive_lemma[OF sys_inv H_def])
         show "HB_Act s b_act ou" using c3 H_def unfolding HB_Act_def by simp
         show "HB_Act s ou bt_act" using conflict H_def unfolding HB_Act_def by simp
         (* ou *)
         show "op_name ou = enq \<or> op_val ou \<in> Val"
         proof -
           have "ou \<in> set (lin_seq s)" using L_struct mset_eq
             by (metis append_Cons in_set_conv_decomp mset_eq_setD) 
           thus ?thesis using LinSeq_Deq_Val_Valid[OF sys_inv _ ou_is_deq] by simp
         qed
       qed
       thus ?thesis using H_def unfolding HB_Act_def by simp
    qed

    (* B. TypeBT (\<not> b_act -> bt_act) *)
    (* c0/c1 b_act bt_act HB *)
    have not_b_hb_bt: "\<not> HB H b_act bt_act"
    proof (rule TypeBT_No_HB_Target[OF sys_inv])
      show "lin_seq s = lin_seq s" ..
      show "H = his_seq s" using H_def .
      (* bt_act *)
      show "bt_act \<in> set (lin_seq s)" using bt_in_L mset_eq by (metis mset_eq_setD)
      show "op_name bt_act = enq" using bt_is_enq .
      show "TypeBT s (op_val bt_act)" using bt_val_type .
      (* b_act *)
      show "b_act \<in> set (lin_seq s)" using L_decomp mset_eq
        by (metis append.assoc append_Cons in_set_conv_decomp
            mset_eq_setD) 
      show "op_name b_act = enq" using b_is_enq .
      show "b_act \<noteq> bt_act" using b_neq_bt .
      (* b_act SetA *)
      show "op_val b_act \<notin> SetA s"
      proof
        assume "op_val b_act \<in> SetA s"
        
        (* Step 1: 1. b_act SetB *)
        have "op_val b_act \<in> SetB s" 
          using b_val_sets unfolding SetB_partition by auto
          
        (* Step 2: 2. HB *)
        (* TypeBT_implies_no_HB: HB x y y TypeBT, x SetA *)
        (* b_hb_bt ( HB H b_act bt_act) *)
        have "SetA s \<inter> SetB s = {}" 
          unfolding SetA_def SetB_def TypeA_def TypeB_def
          using LinSeq_Enq_Val_Valid TypeBT_implies_no_HB 
          using b_hb_bt[unfolded H_def]  (* <--- : H *)
          using bt_in_L mset_eq         (* bt_act lin_seq *)
          using b_active b_is_enq b_neq_bt b_val_sets
          using bt_is_enq bt_val_type sys_inv
          using HB_Act_def \<open>bt_act \<in> set (lin_seq s)\<close> by blast 
          
        then show False 
          using `op_val b_act \<in> SetA s` `op_val b_act \<in> SetB s` 
          by blast
      qed
    qed
      
    (* C. *)
    show False using b_hb_bt not_b_hb_bt by simp
  qed

(* Step 3: 3. Swap (revised version) *)
  show ?thesis
  proof -
    (* A. pre @ [bt_act] @ [ou] @ l3 *)
    (* simp *)
    have new_L_struct: "l1 @ l21 @ [b_act] @ l22_rest @ [bt_act] @ [ou] @ l3 = pre @ [bt_act] @ [ou] @ l3"
      unfolding pre_def by simp
      
    (* B. *)
    show ?thesis
      apply (subst new_L_struct)       (* pre @ ... *)
      apply (rule HB_swap_adjacent)    (* , *)
      
      (* C. *)
      (* 1: ( L) consistent *)
      using H_cons L_struct apply simp
      
      (* 2: HB *)
      using not_hb apply simp
      done
  qed
qed


lemma modify_step_c4_consistent:
  assumes sys: "system_invariant s"
  and hb_cons: "HB_consistent L H"
  and H_def: "H = his_seq s"
  and inv_mset: "mset L = mset (lin_seq s)"
  (* Proof note. *)
  and L_def: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
  and l22_not_nil: "l22 \<noteq> []"
  (* Proof note. *)
  and bt_enq: "op_name bt_act = enq"
  and bt_type: "TypeBT s (op_val bt_act)"
  and bt_in: "bt_act \<in> set L"
  and ou_def: "ou = last l22"
  and b_enq: "op_name b_act = enq"
  and b_active: "b_act \<in> active_enqs s"
  and b_neq_bt: "b_act \<noteq> bt_act"
  and b_val: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"
  (* Proof note. *)
  and not_c1: "\<not> HB H (hd l22) bt_act" 
  and not_c2: "\<not> HB H b_act (hd l22)"
  and not_c3: "\<not> HB H b_act ou"
  and c4: "HB H ou bt_act"
  (* Proof note. *)
  and not_hb_b_bt: "\<not> HB H b_act bt_act"
  (* Proof note. *)
  and l22_deqs: "\<forall>x \<in> set l22. op_name x = deq"
  (* b_act l22 *)
  shows "HB_consistent (l1 @ l21 @ l22 @ [b_act] @ [bt_act] @ l3) H"
proof -
  (* Step 1: 1. *)
  define pre where "pre = l1 @ l21"
  define middle where "middle = l22"
  define post where "post = [bt_act] @ l3"
  define x where "x = b_act"

  (* L HB_jump_right *)
  have L_struct: "L = pre @ [x] @ middle @ post"
    unfolding pre_def middle_def post_def x_def using L_def by simp

  (* Step 2: 2. x (b_act) Happens-Before middle (l22) *)
  have not_hb_x_middle: "\<forall>d \<in> set middle. \<not> HB H x d"
  proof
    fix d assume d_in: "d \<in> set middle"
    show "\<not> HB H x d"
    proof -  (* <--- : "-", False *)
      
      (* Step 2: 2.1 ou *)
      (* l22 index = length pre + 1 *)
      define idx_ou where "idx_ou = length pre + length l22"
      
      (* Step 2: 2.2 d *)
      (* d l22 , k *)
      obtain k where k_valid: "k < length l22" and d_at_k: "l22 ! k = d"
        using d_in unfolding middle_def by (auto simp: in_set_conv_nth)
        
      define idx_d where "idx_d = length pre + 1 + k"

      (* Step 2: 2.3 *)
      have idx_d_valid: "idx_d < length L"
        unfolding idx_d_def pre_def using L_def l22_not_nil k_valid by simp
        
      have idx_ou_valid: "idx_ou < length L"
        unfolding idx_ou_def pre_def using L_def l22_not_nil by simp

      (* L *)
      have L_struct_simple: "L = pre @ [b_act] @ l22 @ [bt_act] @ l3"
        using L_struct x_def middle_def post_def by simp

      (* L ! idx_d = d *)
      have L_at_idx_d: "L ! idx_d = d"
        unfolding idx_d_def 
        apply (subst L_struct_simple) (* Proof note. *)
        apply (simp add: nth_append)  (* pre *)
        using d_at_k k_valid
        apply simp                    (* b_act *)
        done

      (* L ! idx_ou = ou *)
      have L_at_idx_ou: "L ! idx_ou = ou"
        unfolding idx_ou_def 
        apply (subst L_struct_simple)
        apply (simp add: nth_append)  (* pre *)
        using l22_not_nil
        apply simp
        by (simp add: last_conv_nth nth_append_left ou_def)  
        
      (* d l22 , ou , idx_d <= idx_ou *)
      have order: "idx_d \<le> idx_ou"
        unfolding idx_d_def idx_ou_def using k_valid by simp

      (* Step 2: 2.4 *)
      have d_deq: "op_name d = deq"
        using d_in unfolding middle_def using l22_deqs by auto
      have ou_deq: "op_name ou = deq"
        using ou_def l22_not_nil l22_deqs
        by simp 

      (* Step 2: 2.5 HB_jump_right_protection *)
      (* show ?thesis *)
      show ?thesis
        unfolding x_def
        apply (rule HB_jump_right_protection[OF hb_cons])
        (* Step 1: 1. *)
        apply (rule idx_d_valid)
        apply (rule idx_ou_valid)
        (* Step 2: 2. *)
        apply (rule L_at_idx_d)
        apply (rule L_at_idx_ou)
        (* Step 3: 3. *)
        apply (rule order)
        (* Step 4: 4. HB *)
        apply (rule c4)            (* HB ou bt *)
        apply (rule not_hb_b_bt)   (* \<not> HB b bt *)
        (* Step 5: 5. *)
        apply (rule b_enq)
        apply (rule bt_enq)
        apply (rule d_deq)
        apply (rule ou_deq)
        done
    qed
  qed

  (* Step 3: 3. HB_jump_right *)
  (* pre @ middle @ [x] @ post *)
  have target_struct: "l1 @ l21 @ l22 @ [b_act] @ [bt_act] @ l3 = pre @ middle @ [x] @ post"
    unfolding pre_def middle_def post_def x_def by simp

  show ?thesis
    unfolding target_struct
    apply (rule HB_jump_right)
    (* 1 *)
    using hb_cons L_struct apply simp
    (* 2: x middle HB *)
    using not_hb_x_middle apply simp
    done
qed



lemma modify_preserves_HB_consistent:
  assumes sys_inv: "system_invariant s"
  assumes L_def: "L = lin_seq s"
  assumes H_def: "H = his_seq s"
  assumes hb_cons: "HB_consistent L H"
  assumes di: "data_independent L"
  assumes type_bt: "TypeBT s bt_val"
  shows "HB_consistent (modify_lin L H bt_val) H"
proof -
  (* === 1. : === *)
  have inv_mset: "mset L = mset (lin_seq s)" 
    using L_def by simp

  have inv_sa: "\<forall>v. in_SA v L \<longleftrightarrow> in_SA v (lin_seq s)" 
    using L_def by simp

  (* === 2. === *)
  show ?thesis
    using hb_cons di H_def type_bt inv_mset inv_sa
  proof (induct L H bt_val rule: modify_lin.induct)
    case (1 L H bt_val)
    show ?case
    proof (cases "should_modify L H bt_val")
      case False
      then show ?thesis using "1.prems"(1)
        by (subst modify_lin.simps, simp) 
    next
      case True
      note do_modify = True
      
      define last_sa_pos where "last_sa_pos = find_last_SA L"
      define remaining where "remaining = drop (nat (last_sa_pos + 1)) L"

      have search_not_none: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = None" by simp
        thus False using do_modify unfolding should_modify_def Let_def remaining_def last_sa_pos_def by simp
      qed
      
      then obtain bt_idx where bt_idx_def: 
        "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
        by auto

      have bt_idx_valid: "bt_idx < length remaining"
        using bt_idx_def by (rule find_unique_index_Some_less_length)

      define l1 where "l1 = take (nat (last_sa_pos + 1)) L"
      define l2 where "l2 = take bt_idx remaining"
      define l3 where "l3 = drop (Suc bt_idx) remaining"
      define bt_act where "bt_act = remaining ! bt_idx"

      (* Proof note. *)
      have bt_in_L: "bt_act \<in> set L"
        unfolding bt_act_def remaining_def
        by (metis bt_idx_valid in_set_dropD nth_mem remaining_def)

      have bt_is_enq: "op_name bt_act = enq"
        using bt_idx_def unfolding bt_act_def
        using find_unique_index_prop by auto

      have bt_val_eq: "op_val bt_act = bt_val"
        using bt_idx_def unfolding bt_act_def
        using find_unique_index_prop by auto

      have L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
        unfolding l1_def remaining_def using bt_idx_valid l2_def l3_def bt_act_def Cons_nth_drop_Suc
        using remaining_def
        by (metis append.left_neutral append_Cons append_take_drop_id)

      have l2_not_nil: "l2 \<noteq> []"
      proof (cases "l2 = []")
        case True
        have "bt_idx = 0" using True l2_def
          using bt_idx_valid by force
        have False using do_modify unfolding should_modify_def Let_def 
          using `bt_idx = 0` bt_idx_def last_sa_pos_def remaining_def by force
        then show ?thesis ..
      next
        case False then show ?thesis by simp
      qed

      define l2_last where "l2_last = last l2"

      show ?thesis
      proof (cases "op_name l2_last = enq")

        case True (* === c0: Enq Case === *)
        note l2_last_enq = True
        define ll2 where "ll2 = butlast l2"
        define new_L where "new_L = l1 @ ll2 @ [bt_act] @ [l2_last] @ l3"
        
        have local_di: "data_independent L" using "1.prems"(2) by blast
        have l2_split_exact: "l2 = ll2 @ [l2_last]" using l2_not_nil l2_last_def ll2_def by simp

        (* === , === *)
        have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
          unfolding l2_def l3_def bt_act_def
          using bt_idx_valid by (simp add: id_take_nth_drop)

        (* new_L *)
        have mset_new: "mset new_L = mset (lin_seq s)"
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def ll2_def remaining_def
          using L_decomp l2_split_exact "1.prems"(5)
          by (metis bt_act_def case1 l1_def l2_def l2_not_nil l3_def
              remaining_def)

        have sa_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)"
          using "1.prems"(6) in_SA_mset_eq mset_new "1.prems"(5) by  blast

        have di_new: "data_independent new_L"
          using local_di data_independent_cong mset_new "1.prems"(5) by blast

        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def do_modify True apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def ll2_def new_L_def remaining_def)

        have hb_new_L: "HB_consistent new_L H"
          using modify_step_c0_consistent[OF sys_inv _ "1.prems"(3) local_di "1.prems"(5) "1.prems"(6) L_decomp l2_split_exact last_sa_pos_def l1_def True bt_is_enq]
          using "1.prems"(1) "1.prems"(4) bt_val_eq
          by (simp add: new_L_def) 
        
        (* Step 1: 1. should_modify *)
        have fact_modify: "should_modify L H bt_val" by (fact do_modify)
        
        (* Step 2: 2. Let explicit  *)
        (* the (find_unique_index ...), *)
        have fact_bt_idx: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining) = bt_idx"
          using bt_idx_def by simp
          
        (* Step 3: 3. guard (op_name l2_last = enq) *)
        have fop_name: "op_name (last (take bt_idx remaining)) = enq"
          using True l2_last_def l2_def by simp

        (* Step 4: 4. HB_consistent *)
        (* new_L_def induct take/drop *)
        have fact_hb_new: "HB_consistent new_L H" by (fact hb_new_L)    

        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def do_modify True apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def ll2_def new_L_def remaining_def)

        show ?thesis
          (* Step 1: 1. , new_L *)
          unfolding step1
          
          (* Step 2: 2. . : [where...], rule modify_lin (new_L) H bt_val *)
          apply (rule "1.hyps"(1))

          (* Step 3: 3. : modify_lin, Let *)
          (* apply, Let *)
          apply (tactic \<open>ALLGOALS (simp_tac (put_simpset HOL_basic_ss @{context} 
            addsimps @{thms last_sa_pos_def remaining_def l1_def l2_def l3_def 
                            bt_act_def l2_last_def ll2_def new_L_def bt_idx_def} ))\<close>)
          
          (* Step 4: 4. 4 (Goal 1-4) *)
          using L_decomp remaining_decomp l2_split_exact
          using fact_modify apply auto[1]


          (* Step 5: 5. (the (Some x) = x) *)
          apply (metis (no_types, lifting) bt_idx_def last_sa_pos_def remaining_def option.sel)

          (* Step 6: 6. (Goal 5-9) *)
          using do_modify True hb_new_L di_new mset_new sa_new "1.prems"
                 apply simp_all
          subgoal
            (* , *)
            using l2_last_def l2_def remaining_def last_sa_pos_def
            (* op_name l2_last = enq *)
            using True by simp
          subgoal
            (* new_L , *)
            unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            (* Proof note. *)
            using hb_new_L by simp
          subgoal
            unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            using di_new by simp
          subgoal
            (* mset new_L = mset (lin_seq s) *)
            using mset_new
            (* new_L , multiset *)
            unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            by (simp add: ac_simps)
          subgoal
            using sa_new
            unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            by simp
          done
      next
        case False (* === Deq Cases === *)
        note not_enq = False

        have find_enq_valid: "find_last_enq l2 \<noteq> None"
          using do_modify False l2_not_nil unfolding should_modify_def l2_def remaining_def last_sa_pos_def l2_last_def
          using bt_idx_def by (smt (verit) last_sa_pos_def option.simps(4,5) remaining_def) 
        
        obtain l21 b_act l22 where l2_split: "find_last_enq l2 = Some (l21, b_act, l22)"
          using find_enq_valid by (cases "find_last_enq l2", auto)

        have b_act_enq: "op_name b_act = enq"
          using l2_split by (simp add: find_last_enq_props(2))  

        define o1 where "o1 = hd l22"
        
        have l22_not_nil: "l22 \<noteq> []"
          using l2_split l2_not_nil not_enq unfolding find_last_enq_def l2_last_def
          by (metis find_last_enq_props(1,2) l2_split last_snoc self_append_conv)

        have L_split_c1: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
          using L_decomp l2_split find_last_enq_props(1) by auto 

        (* ( ) *)
        define b_idx where "b_idx = length l1 + length l21"
        have b_idx_props: "L ! b_idx = b_act" "b_idx \<ge> length l1" "b_idx < length L"
          unfolding b_idx_def using L_split_c1 by (auto simp: nth_append)

        have b_act_active: "b_act \<in> active_enqs s"
        proof -
          (* Step 1: 1. : L remaining *)
          have L_rest: "L = l1 @ remaining"
            unfolding l1_def remaining_def by simp

          have rem_not_nil: "remaining \<noteq> []"
            using bt_idx_valid by auto

          (* Step 2: 2. , l1 enq SA *)
          have all_after_l1_not_sa: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
            using l1_contains_all_SA_in_L[OF "1.prems"(2) L_rest rem_not_nil l1_def last_sa_pos_def] .

          have not_sa_L: "\<not> in_SA (op_val b_act) L"
            using all_after_l1_not_sa b_idx_props b_act_enq by auto

          (* Step 3: 3. lin_seq s *)
          have not_sa_s: "\<not> in_SA (op_val b_act) (lin_seq s)"
            using not_sa_L "1.prems"(6) by simp

          have b_in_s: "b_act \<in> set (lin_seq s)"
            using b_idx_props(1) b_idx_props(3) "1.prems"(5)
            by (metis nth_mem set_mset_mset)

          (* Step 4: 4. , *)
          have inv1: "lI1_Op_Sets_Equivalence s" and inv2: "lI2_Op_Cardinality s"
            using sys_inv unfolding system_invariant_def by auto

          (* inv1 inv2 , blast *)
          show ?thesis
            using non_SA_enqs_are_active[OF inv1 inv2] b_in_s b_act_enq not_sa_s by blast
        qed

        have b_val_sets: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"
        proof -
          (* Step 1: 1. *)
          have L_rest: "L = l1 @ remaining"
            unfolding l1_def remaining_def by simp
            
          have rem_not_nil: "remaining \<noteq> []"
            using bt_idx_valid by auto
            
          (* Step 2: 2. : 1.prems(2) data_independent *)
          have all_after_l1_not_sa: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
            using l1_contains_all_SA_in_L[OF "1.prems"(2) L_rest rem_not_nil l1_def last_sa_pos_def] .

          (* Step 3: 3. , b_act SA *)
          have not_sa_L: "\<not> in_SA (op_val b_act) L"
            using all_after_l1_not_sa b_idx_props b_act_enq by auto

          have not_sa_s: "\<not> in_SA (op_val b_act) (lin_seq s)"
            using not_sa_L "1.prems"(6) by simp

          (* Step 4: 4. b_act *)
          have b_in_s: "b_act \<in> set (lin_seq s)"
            using b_idx_props(1) b_idx_props(3) "1.prems"(5)
            by (metis nth_mem set_mset_mset)

          (* Step 5: 5. b_act SetA *)
          have not_SetA: "op_val b_act \<notin> SetA s"
            using not_sa_s SetA_implies_in_SA[OF sys_inv] by blast

          (* Step 6: 6. state transport *)
          show ?thesis 
            using LinSeq_Enq_State_Mapping[OF sys_inv b_in_s b_act_enq not_SetA] by blast
        qed

        have o1_deq: "op_name o1 = deq"
          using l22_are_all_deq[OF l2_split l22_not_nil] o1_def
          by (simp add: l22_not_nil)

        have b_neq_bt: "b_act \<noteq> bt_act"
        proof
          assume eq: "b_act = bt_act"
          
          (* Step 1: 1. bt_act L *)
          define bt_idx_abs where "bt_idx_abs = length l1 + length l21 + 1 + length l22"

          (* Step 2: 2. L bt_act *)
          have L_bt: "L ! bt_idx_abs = bt_act"
            unfolding bt_idx_abs_def L_split_c1 by (auto simp: nth_append)

          have bt_idx_abs_less: "bt_idx_abs < length L"
            unfolding bt_idx_abs_def L_split_c1 by simp

          (* Step 3: 3. same_enq_value_same_index *)
          have val_eq: "op_val (L ! b_idx) = op_val (L ! bt_idx_abs)"
            using b_idx_props(1) L_bt eq by simp

          have op_b: "op_name (L ! b_idx) = enq"
            using b_idx_props(1) b_act_enq by simp

          have op_bt: "op_name (L ! bt_idx_abs) = enq"
            using L_bt bt_is_enq by simp

          (* Step 4: 4. : , *)
          have "b_idx = bt_idx_abs"
            using same_enq_value_same_index[OF "1.prems"(2) b_idx_props(3) bt_idx_abs_less op_b op_bt val_eq] .

          (* Step 5: 5. , *)
          moreover have "b_idx < bt_idx_abs"
            unfolding b_idx_def bt_idx_abs_def by simp

          ultimately show False by simp
        qed

        (* Proof note. *)
        consider 
          (c1) "happens_before o1 bt_act H" |
          (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H" |
          (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast

        then show ?thesis
        proof cases
          case c1 (* === c1 === *)
          define new_l22 where "new_l22 = tl l22"
          define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3"
          
          (* Step 1: 1. c1  *)
          have c1_decomp: "L = (l1 @ l21) @ [b_act] @ [o1] @ (new_l22 @ [bt_act] @ l3)"
            using L_split_c1 l22_not_nil o1_def new_l22_def by (metis append.assoc append_Cons append_Nil hd_Cons_tl)

          (* Step 2: 2. ✨ : new_L , prefix suffix *)
          have new_L_struct: "new_L = (l1 @ l21) @ [o1] @ [b_act] @ (new_l22 @ [bt_act] @ l3)"
            unfolding new_L_def by simp

          (* Step 3: 3. *)
          have hb_new_L: "HB_consistent new_L H"
            unfolding new_L_struct (* Proof note. *)
            apply (rule modify_step_c1_consistent[where bt_act=bt_act and s=s and L=L])
            apply (rule sys_inv)
            apply (rule "1.prems"(1))
            apply (rule "1.prems"(3))
            apply (rule "1.prems"(5))
            apply (rule c1_decomp) (* L_decomp *)
            apply (rule b_act_enq)
            apply (rule o1_deq)
            apply (rule bt_in_L)
            apply (rule bt_is_enq)
            apply (rule "1.prems"(4)[unfolded bt_val_eq[symmetric]])
            apply (rule c1)
            apply (rule b_act_active)
            apply (rule b_neq_bt)
            apply (rule b_val_sets)
            done

          have mset_new: "mset new_L = mset (lin_seq s)"
            unfolding new_L_def using L_split_c1 l22_not_nil o1_def new_l22_def "1.prems"(5)
            by (metis append.assoc case2)

          have di_new: "data_independent new_L"
            using "1.prems"(2) data_independent_cong mset_new "1.prems"(5) by blast

          have sa_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)"
            using in_SA_mset_eq[OF mset_new] "1.prems"(5) "1.prems"(6) by blast

          have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          (* Step 1: 1. *)
          apply (subst modify_lin.simps)
          (* Step 2: 2. Let *)
          apply (simp only: Let_def case_prod_unfold)
          
          (* Step 3: 3. *)
          (* , simp *)
          apply (simp only: last_sa_pos_def[symmetric] remaining_def[symmetric] 
                            l1_def[symmetric] bt_idx_def[symmetric] 
                            bt_act_def[symmetric] l2_def[symmetric] 
                            l3_def[symmetric] l2_last_def[symmetric])
          using bt_act_def bt_idx_def c1 do_modify l2_def l2_last_def l2_split
              l3_def new_L_def new_l22_def not_enq o1_def by force


        (* === show ?thesis === *)
        have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
          unfolding l2_def l3_def bt_act_def
          using bt_idx_valid by (simp add: id_take_nth_drop)

        (* === === *)
        show ?thesis
          (* Step 1: 1. *)
          unfolding step1
          
          (* Step 2: 2. *)
          apply (rule "1.hyps"(2))

          (* Step 3: 3. tactic: , *)
          apply (tactic \<open>ALLGOALS (simp_tac (put_simpset HOL_basic_ss @{context} 
            addsimps @{thms last_sa_pos_def remaining_def l1_def l2_def l3_def 
                            bt_act_def l2_last_def o1_def new_l22_def new_L_def bt_idx_def} ))\<close>)

          (* Step 4: 4. (Goals 1-4) *)
          (* fact_modify do_modify *)
          using L_decomp remaining_decomp l2_split do_modify
          apply auto[1]

          (* Step 5: 5. (the (Some x) = x) *)
          apply (metis (no_types, lifting) bt_idx_def last_sa_pos_def remaining_def option.sel)

          (* Step 6: 6. *)
          using do_modify not_enq c1 hb_new_L di_new mset_new sa_new "1.prems"
          apply simp_all

          (* === 7. Subgoal === *)
          
          (* Subgoal: op_name l2_last \<noteq> enq *)
          subgoal
            using l2_last_def l2_def remaining_def last_sa_pos_def
            using not_enq by simp

          (* Subgoal: find_last_enq *)
          subgoal
            using l2_split l2_def remaining_def last_sa_pos_def option.sel by simp

          (* Subgoal: happens_before *)
          subgoal
            using c1 o1_def l2_def remaining_def last_sa_pos_def
            using bt_act_def by blast 

          (* Subgoal: HB_consistent new_L *)
          subgoal
            unfolding new_L_def o1_def new_l22_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            using hb_new_L by simp

          (* Subgoal: data_independent new_L *)
          subgoal
            unfolding new_L_def o1_def new_l22_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            using di_new by simp

          (* Subgoal: mset new_L *)
          subgoal
            using mset_new
            unfolding new_L_def o1_def new_l22_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            by (simp add: ac_simps)

          (* Subgoal: in_SA new_L *)
          subgoal
            using sa_new
            unfolding new_L_def o1_def new_l22_def l1_def l2_def l3_def bt_act_def l2_last_def 
                      remaining_def last_sa_pos_def bt_idx_def
            by simp
            
          done

      next
        case c2 (* === c2 === *)
        
        (* Step 1: 1. c2 ( happens_before \<equiv> HB, ) *)
        have not_hb_strict: "\<not> HB H o1 bt_act" 
          using c2 by simp
          
        have hb_b_o1_strict: "HB H b_act o1" 
          using c2 by simp

        (* Step 2: 2. *)
        have c2_decomp: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
          using L_split_c1 by auto

        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"

        (* Step 3: 3. modify_step_c2_consistent *)
        have hb_new_L: "HB_consistent new_L H"
          unfolding new_L_def 
          apply (rule modify_step_c2_consistent[where bt_act=bt_act and s=s and L=L])
          apply (rule sys_inv)
          apply (rule "1.prems"(1))
          apply (rule "1.prems"(3))
          apply (rule "1.prems"(5))
          apply (rule c2_decomp)
          apply (rule l22_not_nil)
          apply (rule bt_is_enq)
          apply (rule "1.prems"(4)[unfolded bt_val_eq[symmetric]])
          apply (rule bt_in_L)        
          apply (rule o1_def)         
          apply (rule b_act_enq)      
          apply (rule b_act_active)   
          apply (rule b_neq_bt)       
          apply (rule b_val_sets)     
          apply (rule not_hb_strict)  
          apply (rule hb_b_o1_strict) 
          apply (rule l22_are_all_deq[OF l2_split l22_not_nil]) 
          done

        (* Step 4: 4. *)
        have mset_new: "mset new_L = mset (lin_seq s)"
          unfolding new_L_def using L_split_c1 "1.prems"(5)
          by (metis append_assoc case3) 

        have di_new: "data_independent new_L"
          using "1.prems"(2) data_independent_cong mset_new "1.prems"(5) by blast

        have sa_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)"
          using in_SA_mset_eq[OF mset_new] "1.prems"(5) "1.prems"(6) by blast

        (* Step 5: 5. ( c1 ) *)
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (simp only: last_sa_pos_def[symmetric] remaining_def[symmetric] 
                            l1_def[symmetric] bt_idx_def[symmetric] 
                            bt_act_def[symmetric] l2_def[symmetric] 
                            l3_def[symmetric] l2_last_def[symmetric])
          using bt_act_def bt_idx_def c2 do_modify l2_def l2_last_def l2_split 
                l3_def new_L_def not_enq o1_def by force

        have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
          unfolding l2_def l3_def bt_act_def
          using bt_idx_valid by (simp add: id_take_nth_drop)

        (* Step 6: 6. : Tactic *)
        show ?thesis
          unfolding step1
          (* rule modify_lin *)
          apply (rule "1.hyps"(3)) 
          
          (* Tactic: , *)
          apply (tactic \<open>ALLGOALS (simp_tac (put_simpset HOL_basic_ss @{context} 
                 addsimps @{thms last_sa_pos_def remaining_def l1_def l2_def l3_def 
                                 bt_act_def l2_last_def o1_def new_L_def bt_idx_def} ))\<close>)
          
          (* Proof note. *)
          using L_decomp remaining_decomp l2_split do_modify
          apply auto[1]
          apply (metis (no_types, lifting) bt_idx_def last_sa_pos_def remaining_def option.sel)
          
          (* Proof note. *)
          using do_modify not_enq c2 hb_new_L di_new mset_new sa_new "1.prems"
          apply simp_all

          (* === Subgoal ( ) === *)
          subgoal using l2_last_def l2_def remaining_def last_sa_pos_def not_enq by simp
          subgoal using l2_split l2_def remaining_def last_sa_pos_def option.sel by simp
          subgoal using c2 o1_def l2_def remaining_def last_sa_pos_def bt_act_def by blast
          subgoal using c2 o1_def l2_def remaining_def last_sa_pos_def bt_act_def by blast
          subgoal unfolding new_L_def o1_def l1_def l2_def l3_def bt_act_def l2_last_def 
                            remaining_def last_sa_pos_def bt_idx_def using hb_new_L by simp
          subgoal unfolding new_L_def o1_def l1_def l2_def l3_def bt_act_def l2_last_def 
                            remaining_def last_sa_pos_def bt_idx_def using di_new by simp
          subgoal using mset_new unfolding new_L_def o1_def l1_def l2_def l3_def bt_act_def l2_last_def 
                            remaining_def last_sa_pos_def bt_idx_def by (simp add: ac_simps)
          subgoal using sa_new unfolding new_L_def o1_def l1_def l2_def l3_def bt_act_def l2_last_def 
                            remaining_def last_sa_pos_def bt_idx_def by simp
          done

        next
        case c3 (* === c3 === *)
        define new_l22 where "new_l22 = tl l22"
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3"

        (* Step 1: 1. c3  *)
        (* L , hd tl *)
        have c3_decomp: "L = (l1 @ l21) @ [b_act] @ [o1] @ (new_l22 @ [bt_act] @ l3)"
          using L_split_c1 l22_not_nil o1_def new_l22_def 
          by (metis append.assoc append_Cons append_Nil hd_Cons_tl)

        (* new_L , c3_decomp *)
        have new_L_struct: "new_L = (l1 @ l21) @ [o1] @ [b_act] @ (new_l22 @ [bt_act] @ l3)"
          unfolding new_L_def by simp

        have hb_new_L: "HB_consistent new_L H"
          unfolding new_L_struct 
          apply (rule modify_step_c3_new_consistent[OF sys_inv `HB_consistent L H` "1.prems"(3) "1.prems"(5)])
          (* Proof note. *)
          using c3_decomp l22_not_nil o1_def new_l22_def b_act_enq o1_deq bt_in_L 
                bt_is_enq "1.prems"(4) bt_val_eq c3 b_act_active b_neq_bt b_val_sets 
          by auto

        have mset_new: "mset new_L = mset (lin_seq s)"
          unfolding new_L_def using L_split_c1 l22_not_nil o1_def new_l22_def "1.prems"(5)
          by (metis append_assoc case2)

        have di_new: "data_independent new_L"
          using "1.prems"(2) data_independent_cong mset_new "1.prems"(5) by blast

        have sa_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)"
          using in_SA_mset_eq[OF mset_new] "1.prems"(5) "1.prems"(6) by blast

        (* Step 2: 2.  *)
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (simp only: last_sa_pos_def[symmetric] remaining_def[symmetric] 
                            l1_def[symmetric] bt_idx_def[symmetric] 
                            bt_act_def[symmetric] l2_def[symmetric] 
                            l3_def[symmetric] l2_last_def[symmetric])
          using bt_act_def bt_idx_def c3 do_modify l2_def l2_last_def l2_split 
                l3_def new_L_def new_l22_def not_enq o1_def by force

        (* remaining , *)
        have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
          unfolding l2_def l3_def bt_act_def
          using bt_idx_valid by (simp add: id_take_nth_drop)

        (* Step 3: 3. *)
        (* Option , *)
        have fact_idx: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining) = bt_idx"
          using bt_idx_def by simp
          
        have fact_enq: "the (find_last_enq l2) = (l21, b_act, l22)"
          using l2_split by simp
          
        (* Proof note. *)
        have fact_hb: "HB_consistent (l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3) H"
          using hb_new_L unfolding new_L_def by simp
          
        have fact_di: "data_independent (l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3)"
          using di_new unfolding new_L_def by simp
          
        have fact_ms: "mset (l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3) = mset (lin_seq s)"
          using mset_new unfolding new_L_def by simp
          
        have fact_sa: "\<forall>v. in_SA v (l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3) = in_SA v (lin_seq s)"
          using sa_new unfolding new_L_def by simp

        (* Step 3: 3. *)
        (* Option *)
        have fact_idx: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining) = bt_idx"
          using bt_idx_def by simp
          
        have fact_enq: "the (find_last_enq l2) = (l21, b_act, l22)"
          using l2_split by simp
          
        (* 【 】: # , simp *)
        have fact_hb: "HB_consistent (l1 @ l21 @ o1 # b_act # new_l22 @ bt_act # l3) (his_seq s)"
          using hb_new_L H_def unfolding new_L_def
          using "1.prems"(3) by auto 
          
        have fact_di: "data_independent (l1 @ l21 @ o1 # b_act # new_l22 @ bt_act # l3)"
          using di_new unfolding new_L_def by simp
          
        have fact_ms: "mset (l1 @ l21 @ o1 # b_act # new_l22 @ bt_act # l3) = mset (lin_seq s)"
          using mset_new unfolding new_L_def by simp
          
        have fact_sa: "\<forall>v. in_SA v (l1 @ l21 @ o1 # b_act # new_l22 @ bt_act # l3) = in_SA v (lin_seq s)"
          using sa_new unfolding new_L_def by simp

        (* Proof note. *)
        show ?thesis
          unfolding step1 new_L_def
          apply (rule "1.hyps"(4))
          
          (* 27 , *)
          apply (simp_all add: last_sa_pos_def[symmetric])
          apply (simp_all add: remaining_def[symmetric])
          apply (simp_all add: fact_idx)
          apply (simp_all add: l2_def[symmetric])
          apply (simp_all add: fact_enq)
          apply (simp_all add: l2_last_def[symmetric] not_enq)
          apply (simp_all add: o1_def[symmetric] bt_act_def[symmetric] c3 H_def)
          apply (simp_all add: new_l22_def[symmetric])
          
          (* 27 let guard *)
          (* 8 , # , *)
          apply (simp_all add: do_modify fact_hb fact_di fact_ms fact_sa "1.prems" inv_mset inv_sa H_def)
          (* 27 let guard *)
          (* , , 4 *)

          (* Step 1: 1. should_modify( H his_seq s ) *)
          subgoal using do_modify H_def
            by (simp add: "1.prems"(3)) 

          (* Step 2: 2. l1 *)
          subgoal unfolding l1_def by simp

          (* Step 3: 3. l3 (Suc bt_idx bt_idx + 1) *)
          subgoal unfolding l3_def by simp

          (* Step 4: 4. mset ( ac_simps + add_mset ) *)
          subgoal using fact_ms by (simp add: ac_simps)

          done
        qed
      qed
    qed
  qed
qed


(* Auxiliary lemma: e *)
(* \<not> HB H e e , HB *)
lemma HB_consistent_append:
  assumes "HB_consistent L H"
  assumes "\<forall>x \<in> set L. \<not> HB H e x"
  assumes "\<not> HB H e e"  (* < *)
  shows "HB_consistent (L @ [e]) H"
  unfolding HB_consistent_def
proof (intro allI impI)
  fix i j
  assume asm: "i < length (L @ [e]) \<and> j < length (L @ [e]) \<and> HB H ((L @ [e]) ! i) ((L @ [e]) ! j)"
  from asm have valid_i: "i < length (L @ [e])" 
            and valid_j: "j < length (L @ [e])" 
            and hb: "HB H ((L @ [e]) ! i) ((L @ [e]) ! j)" 
    by simp_all

  show "i < j"
  proof (cases "j < length L")
    case True
    (* Case 1: j L *)
    have "i < length L"
    proof (rule ccontr)
      assume "\<not> i < length L"
      then have "i = length L" using valid_i by simp
      then have "(L @ [e]) ! i = e" by simp
      moreover have "(L @ [e]) ! j = L ! j" using True by (simp add: nth_append)
      ultimately have "HB H e (L ! j)" using hb by simp
      then show False using assms(2) nth_mem[OF True] by blast
    qed
    with True have "HB H (L ! i) (L ! j)" using hb by (simp add: nth_append)
    then show "i < j" using assms(1) unfolding HB_consistent_def using `i < length L` True by blast
  next
    case False
    (* Case 2: j e *)
    then have j_eq: "j = length L" using valid_j by simp
    show "i < j"
    proof (cases "i < length L")
      case True
      then show ?thesis using j_eq by simp
    next
      case False
      then have "i = length L" using valid_i by simp
      then have "i = j" using j_eq by simp
      with hb have "HB H e e"
        by (simp add: j_eq) 
      (* Proof note. *)
      then show ?thesis using assms(3) by blast
    qed
  qed
qed



lemma modify_lin_structural_props:
  assumes new_L_def: "new_L = modify_lin L H v"
  assumes lin_L_global: "lI4_FIFO_Semantics_list L"
  assumes independent_L_global: "data_independent L"
  assumes lI5_SA_Prefix_global: "lI5_SA_Prefix_list L"
  assumes v_pending: "\<forall>k < length L. op_val (L!k) = v \<longrightarrow> op_name (L!k) \<noteq> deq"
  shows 
    "(\<forall>kA' kD' A. kD' < length new_L \<and> kA' < length new_L \<longrightarrow>
        op_name (new_L!kD') = deq \<and> op_val (new_L!kD') = A \<longrightarrow>
        op_name (new_L!kA') = enq \<and> op_val (new_L!kA') = A \<longrightarrow> (kA' < kD')) \<and>
     (\<forall>kA' kV' A. kA' < length new_L \<and> kV' < length new_L \<longrightarrow>
        (op_name (new_L!kA') = enq \<and> op_val (new_L!kA') = A) \<longrightarrow>
        (\<exists>kD' < length new_L. op_name (new_L!kD') = deq \<and> op_val (new_L!kD') = A) \<longrightarrow>
        (op_name (new_L!kV') = enq \<and> op_val (new_L!kV') = v) \<longrightarrow> kA' < kV')"
proof -
  (* ==================================================================== *)
  (* 1: ( , structural_preservation) *)
  (* ==================================================================== *)
  let ?idx = "nat (find_last_SA L + 1)"
  
  have take_eq: "take ?idx new_L = take ?idx L"
    using modify_lin_structural_preservation[OF independent_L_global] new_L_def by simp
    
  have drop_mset: "mset (drop ?idx new_L) = mset (drop ?idx L)"
    using modify_lin_structural_preservation[OF independent_L_global] new_L_def by simp
    
  have mset_eq: "mset new_L = mset L"
    by (metis append_take_drop_id drop_mset mset_append take_eq)
    
  have len_eq: "length new_L = length L"
    using mset_eq by (metis mset_eq_length)
    
  have in_SA_eq: "\<forall>a. in_SA a new_L = in_SA a L"
    using in_SA_mset_eq mset_eq by blast
    
  have indep_new: "data_independent new_L"
    using independent_L_global mset_eq data_independent_cong by blast

  (* ==================================================================== *)
  (* 2: lI5_SA_Prefix ( , ) *)
  (* ==================================================================== *)
  have lI5_SA_Prefix_new: "lI5_SA_Prefix_list new_L"
    using modify_preserves_lI5_SA_Prefix[OF lin_L_global new_L_def independent_L_global lI5_SA_Prefix_global v_pending] .

  have sa_stable: "find_last_SA new_L = find_last_SA L"
  proof (rule find_last_SA_stable_prefix[OF len_eq take_eq])
    (* 1: L SA Enq *)
    show "\<forall>i\<in>{?idx..<length L}. \<not> (op_name (L ! i) = enq \<and> in_SA (op_val (L ! i)) L)"
    proof (intro ballI notI, elim conjE)
      fix i assume range: "i \<in> {?idx..<length L}"
      assume is_enq: "op_name (L ! i) = enq"
      assume in_sa: "in_SA (op_val (L ! i)) L"
      
      (* Step 1: 1. lI5_SA_Prefix : SA Enq, <= boundary *)
      have "int i \<le> find_last_SA L" 
        using lI5_SA_Prefix_global is_enq in_sa range
        unfolding lI5_SA_Prefix_list_def by auto
        
      (* Step 2: 2. : > boundary *)
      moreover have "int i > find_last_SA L"
        using range by auto (* Isabelle nat(x+1) *)
        
      (* Step 3: 3. *)
      ultimately show False by simp
    qed

    (* 2: new_L SA Enq *)
    show "\<forall>i\<in>{?idx..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
    proof (intro ballI notI, elim conjE)
      fix i assume range: "i \<in> {?idx..<length new_L}"
      assume is_enq: "op_name (new_L ! i) = enq"
      assume in_sa_new: "in_SA (op_val (new_L ! i)) new_L"
      
      let ?x = "new_L ! i"
      
      (* Step 1: 1. x new_L ... *)
      have "?x \<in> set (drop ?idx new_L)"
      proof -
        (* , *)
        let ?k = "i - ?idx"
        have bound: "?k < length (drop ?idx new_L)" 
          using range
          by (simp add: diff_less_mono)
        have val: "(drop ?idx new_L) ! ?k = ?x" 
          using range by simp
        (* ?k in_set_conv_nth , auto *)
        show ?thesis 
          using bound val by (auto simp: in_set_conv_nth)
      qed
        
      (* Step 2: 2. , L *)
      then have "?x \<in> set (drop ?idx L)"
        using drop_mset by (metis set_mset_mset)
        
      (* Step 3: 3. L ( k) *)
      then obtain j where j_bound: "j < length (drop ?idx L)" and val_eq: "(drop ?idx L) ! j = ?x"
        by (auto simp: in_set_conv_nth)
      
      let ?k = "?idx + j"
      have k_in_range: "?k \<in> {?idx..<length L}"
        using j_bound by auto
      have L_k_is_x: "L ! ?k = ?x"
        using val_eq j_bound by simp
        
      (* Step 4: 4. L *)
      have "op_name (L ! ?k) = enq" using is_enq L_k_is_x by simp
      moreover have "in_SA (op_val (L ! ?k)) L" 
        using in_sa_new in_SA_eq L_k_is_x by simp
      
      (* Step 5: 5. 1 (L SA Enq) *)
      (* lI5_SA_Prefix , *)
      ultimately have "\<not> (op_name (L ! ?k) = enq \<and> in_SA (op_val (L ! ?k)) L)"
        using k_in_range (* range *)
        using `\<forall>i\<in>{?idx..<length L}. \<not> (op_name (L ! i) = enq \<and> in_SA (op_val (L ! i)) L)`
        by blast
        
      thus False
        using L_k_is_x
          \<open>in_SA (op_val (L ! (nat (find_last_SA L + 1) + j))) L\<close> is_enq
        by auto 
    qed

    (* 3: in_SA *)
    show "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L" 
      using in_SA_eq by blast
  qed

  (* ==================================================================== *)
  (* 1 (Part 1): kA' < kD', *)
  (* ==================================================================== *)
  have part1: "\<forall>kA' kD' A. kD' < length new_L \<and> kA' < length new_L \<longrightarrow>
               op_name (new_L!kD') = deq \<and> op_val (new_L!kD') = A \<longrightarrow>
               op_name (new_L!kA') = enq \<and> op_val (new_L!kA') = A \<longrightarrow> kA' < kD'"
  proof (intro allI impI)
    fix kA' kD' A
    assume r: "kD' < length new_L \<and> kA' < length new_L"
    assume d: "op_name (new_L!kD') = deq \<and> op_val (new_L!kD') = A"
    assume e: "op_name (new_L!kA') = enq \<and> op_val (new_L!kA') = A"
    
    (* Step 1: 1. A Deq Enq, SA *)
    have in_sa_A: "in_SA A new_L"
    proof -
      have "find_indices (\<lambda>x. op_name x = enq \<and> op_val x = A) new_L = [kA']"
        by (simp add: e indep_new r unique_enq_index)
      moreover have "find_indices (\<lambda>x. op_name x = deq \<and> op_val x = A) new_L = [kD']"
        using d indep_new r unique_deq_index by auto
      ultimately show ?thesis unfolding in_SA_def find_unique_index_def Let_def by simp
    qed
      
    (* Step 2: 2. lI5_SA_Prefix: SA Enq, *)
    have kA'_bound: "int kA' \<le> find_last_SA new_L"
      using lI5_SA_Prefix_new[unfolded lI5_SA_Prefix_list_def Let_def, THEN spec, of kA'] r e in_sa_A by blast
      
    have kA'_lt_idx: "kA' < ?idx"
      using kA'_bound sa_stable by auto
      
    (* Step 3: 3. : kD' kA' *)
    show "kA' < kD'"
    proof (rule ccontr)
      assume "\<not> kA' < kD'"
      hence "kD' \<le> kA'" by simp
      hence kD'_lt_idx: "kD' < ?idx" using kA'_lt_idx by simp
      
      (* kD' kA' , new_L L *)
      have "new_L ! kA' = L ! kA'" using kA'_lt_idx take_eq by (metis nth_take)
      have "new_L ! kD' = L ! kD'" using kD'_lt_idx take_eq by (metis nth_take)
      
      have "op_name (L!kD') = deq" "op_val (L!kD') = A" using d `new_L ! kD' = L ! kD'` by auto
      have "op_name (L!kA') = enq" "op_val (L!kA') = A" using e `new_L ! kA' = L ! kA'` by auto
      have "kA' < length L" "kD' < length L" using r len_eq by auto
      
      (* lI4_FIFO_Semantics *)
      obtain kA_old where "kA_old < kD'" "op_name (L!kA_old) = enq" "op_val (L!kA_old) = A"
        using lin_L_global[unfolded lI4_FIFO_Semantics_list_def Let_def, THEN spec, of kD']
        using `kD' < length L` `op_name (L!kD') = deq` `op_val (L!kD') = A` by blast
        
      (* kA' *)
      have "kA_old = kA'"
      proof (rule same_enq_value_same_index[OF independent_L_global])
        show "kA_old < length L" using `kA_old < kD'` `kD' < length L` by simp
        show "kA' < length L" using `kA' < length L` .
        show "op_name (L!kA_old) = enq" using `op_name (L!kA_old) = enq` .
        show "op_name (L!kA') = enq" using `op_name (L!kA') = enq` .
        show "op_val (L!kA_old) = op_val (L!kA')" using `op_val (L!kA_old) = A` `op_val (L!kA') = A` by simp
      qed
        
      (* kA' < kD' kD' <= kA' *)
      thus False using `kA_old < kD'` `kD' \<le> kA'` by simp
    qed
  qed

  (* ==================================================================== *)
  (* 2 (Part 2): kA' < kV', SA *)
  (* ==================================================================== *)
  have part2: "\<forall>kA' kV' A. kA' < length new_L \<and> kV' < length new_L \<longrightarrow>
               (op_name (new_L!kA') = enq \<and> op_val (new_L!kA') = A) \<longrightarrow>
               (\<exists>kD' < length new_L. op_name (new_L!kD') = deq \<and> op_val (new_L!kD') = A) \<longrightarrow>
               (op_name (new_L!kV') = enq \<and> op_val (new_L!kV') = v) \<longrightarrow> kA' < kV'"
  proof (intro allI impI)
    fix kA' kV' A
    assume r: "kA' < length new_L \<and> kV' < length new_L"
    assume ea: "op_name (new_L!kA') = enq \<and> op_val (new_L!kA') = A"
    assume paired: "\<exists>kD' < length new_L. op_name (new_L!kD') = deq \<and> op_val (new_L!kD') = A"
    assume ev: "op_name (new_L!kV') = enq \<and> op_val (new_L!kV') = v"

    (* A SA *)
    have in_sa_A: "in_SA A new_L"
    proof -
      have "find_indices (\<lambda>x. op_name x = enq \<and> op_val x = A) new_L = [kA']"
        by (simp add: ea indep_new r unique_enq_index)
      moreover from paired obtain kD' where "kD' < length new_L" "op_name (new_L!kD') = deq" "op_val (new_L!kD') = A" by blast
      hence "find_indices (\<lambda>x. op_name x = deq \<and> op_val x = A) new_L = [kD']"
        using unique_deq_index[OF indep_new] by simp
      ultimately show ?thesis unfolding in_SA_def find_unique_index_def Let_def by simp
    qed
      
    (* v (bt_val) SA *)
    have not_in_sa_v: "\<not> in_SA v new_L"
    proof -
      have "\<forall>k < length new_L. op_val (new_L!k) = v \<longrightarrow> op_name (new_L!k) \<noteq> deq"
        using v_pending mset_eq by (metis in_set_conv_nth set_mset_mset)
      hence "find_indices (\<lambda>x. op_name x = deq \<and> op_val x = v) new_L = []"
        unfolding find_indices_def by (auto simp: filter_empty_conv)
      thus ?thesis unfolding in_SA_def find_unique_index_def Let_def by simp
    qed

    (* lI5_SA_Prefix : kA' <= , kV' > *)
    have "int kA' \<le> find_last_SA new_L"
      using lI5_SA_Prefix_new[unfolded lI5_SA_Prefix_list_def Let_def, THEN spec, of kA'] r ea in_sa_A by blast
      
    have "int kV' > find_last_SA new_L"
    proof (rule ccontr)
      assume "\<not> int kV' > find_last_SA new_L"
      hence "int kV' \<le> find_last_SA new_L" by simp
      hence "in_SA (op_val (new_L!kV')) new_L"
        using lI5_SA_Prefix_new[unfolded lI5_SA_Prefix_list_def Let_def, THEN spec, of kV'] r ev by blast
      thus False using not_in_sa_v ev by simp
    qed
    
    (* , kA' kV' *)
    thus "kA' < kV'" using `int kA' \<le> find_last_SA new_L` by linarith
  qed

  show ?thesis using part1 part2 by blast
qed



lemma move_pending_enq_preserves_lI4_FIFO_Semantics:
  fixes L L' :: "OpRec list" and H :: "ActRec list" and v :: nat
  assumes lI4_FIFO_Semantics_L: "lI4_FIFO_Semantics_list L"
  assumes L'_def: "L' = modify_lin L H v"
  assumes indep_L: "data_independent L"  
  assumes lI5_SA_Prefix_L: "lI5_SA_Prefix_list L"        
  assumes v_pending: "\<forall>k < length L. op_val (L!k) = v \<longrightarrow> op_name (L!k) \<noteq> deq"
  shows "lI4_FIFO_Semantics_list L'"
proof -
  (* Step 0: 0. *)
  have struct_props: 
    "(\<forall>kA' kD' A. kD' < length L' \<and> kA' < length L' \<longrightarrow>
        op_name (L'!kD') = deq \<and> op_val (L'!kD') = A \<longrightarrow>
        op_name (L'!kA') = enq \<and> op_val (L'!kA') = A \<longrightarrow> kA' < kD') \<and>
     (\<forall>kA' kV' A. kA' < length L' \<and> kV' < length L' \<longrightarrow>
        (op_name (L'!kA') = enq \<and> op_val (L'!kA') = A) \<longrightarrow>
        (\<exists>kD' < length L'. op_name (L'!kD') = deq \<and> op_val (L'!kD') = A) \<longrightarrow>
        (op_name (L'!kV') = enq \<and> op_val (L'!kV') = v) \<longrightarrow> kA' < kV')"
    using modify_lin_structural_props[OF L'_def lI4_FIFO_Semantics_L indep_L lI5_SA_Prefix_L v_pending] .

  (* Step 1: 1. Filter *)
  let ?P_enq = "\<lambda>x. op_name x = enq \<and> op_val x \<noteq> v"
  let ?P_deq = "\<lambda>x. op_name x = deq"

  (* Enq *)
  have enq_ord: "filter ?P_enq L' = filter ?P_enq L"
    using modify_lin_preserves_orders L'_def by blast

  (* Deq *)
  have deq_ord: "filter ?P_deq L' = filter ?P_deq L"
  proof -
    have no_deq_v_L: "\<forall>x \<in> set L. op_name x = deq \<longrightarrow> op_val x \<noteq> v"
      using v_pending by (metis in_set_conv_nth) 
    have "mset L' = mset L" unfolding L'_def
      using modify_preserves_mset by auto 
    then have no_deq_v_L': "\<forall>x \<in> set L'. op_name x = deq \<longrightarrow> op_val x \<noteq> v"
      using no_deq_v_L by (metis set_mset_mset)
    
    have "filter ?P_deq L' = filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> v) L'"
      using no_deq_v_L' by (auto intro: filter_cong)
    also have "... = filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> v) L"
      using L'_def modify_lin_preserves_orders by blast 
    also have "... = filter ?P_deq L"
      using no_deq_v_L by (auto intro: filter_cong)
    finally show ?thesis .
  qed

  (* Step 2: 2. lI4_FIFO_Semantics_list *)
  show ?thesis
    unfolding lI4_FIFO_Semantics_list_def Let_def
  proof (intro allI impI)
    (* Step 2: 2.1 *)
    fix k_deq_A' 
    assume k_bound: "k_deq_A' < length L'"
    assume is_deq: "op_name (L' ! k_deq_A') = deq"
    
    let ?act_deq = "L' ! k_deq_A'"
    let ?A = "op_val ?act_deq"

    (* Step 2: 2.2 A : A != v ( distinct ) *)
    have A_not_v: "?A \<noteq> v" 
    proof -
      have "?act_deq \<in> set L'" using k_bound by simp
      moreover have "mset L' = mset L" using L'_def modify_preserves_mset by auto
      ultimately have "?act_deq \<in> set L" by (metis set_mset_mset)
      thus ?thesis using is_deq v_pending
        by (metis in_set_conv_nth)
    qed

    (* Step 2: 2.3 Deq(A) L *)
    let ?rank_deq = "length (filter (\<lambda>x. op_name x = deq) (take k_deq_A' L'))"
    
    obtain k_deq_A_L where k_deq_A_L_def:
      "k_deq_A_L < length L"
      "L ! k_deq_A_L = ?act_deq"
      "length (filter (\<lambda>x. op_name x = deq) (take k_deq_A_L L)) = ?rank_deq"
      using deq_ord filter_nth_ex_rank is_deq k_bound by blast

    (* Step 2: 2.4 L lI4_FIFO_Semantics *)
    have lin_L_unfolded: 
      "\<exists>k2 < k_deq_A_L. op_name (L!k2) = enq \<and> op_val (L!k2) = ?A \<and>
        (\<forall>k3 < k2. op_name (L!k3) = enq \<longrightarrow> 
           (\<exists>k4. k3 < k4 \<and> k4 < k_deq_A_L \<and> op_name (L!k4) = deq \<and> op_val (L!k4) = op_val (L!k3)))"
      using lI4_FIFO_Semantics_L k_deq_A_L_def(1,2) is_deq unfolding lI4_FIFO_Semantics_list_def Let_def by fastforce
    
    obtain k_enq_A_L where enq_A_L_props:
      "k_enq_A_L < k_deq_A_L"
      "op_name (L!k_enq_A_L) = enq" "op_val (L!k_enq_A_L) = ?A"
      and fifo_L: "\<forall>k3 < k_enq_A_L. op_name (L!k3) = enq \<longrightarrow> 
               (\<exists>k4. k3 < k4 \<and> k4 < k_deq_A_L \<and> op_name (L!k4) = deq \<and> op_val (L!k4) = op_val (L!k3))"
      using lin_L_unfolded by blast

    (* Step 2: 2.5 Enq(A) L' *)
    let ?rank_enq_A = "length (filter ?P_enq (take k_enq_A_L L))"
    
    obtain k_enq_A' where k_enq_A'_def:
      "k_enq_A' < length L'"
      "L' ! k_enq_A' = L ! k_enq_A_L"
      "length (filter ?P_enq (take k_enq_A' L')) = ?rank_enq_A"
      using enq_ord filter_nth_ex_rank[where P="?P_enq" and i="k_enq_A_L"] 
      enq_A_L_props(2,3) A_not_v
      by (smt (verit, ccfv_SIG) A_not_v enq_A_L_props(1,2,3) enq_ord
          filter_nth_ex_rank k_deq_A_L_def(1) order.strict_trans)

    (* Step 2: 2.6 : Enq(A) Deq(A) *)
    have "k_enq_A' < k_deq_A'"
      using struct_props
      by (metis enq_A_L_props(2,3) is_deq k_bound k_enq_A'_def(1,2))

    (* Step 2: 2.7 L' FIFO *)
    show "\<exists>k2 < k_deq_A'. op_name (L' ! k2) = enq \<and> op_val (L' ! k2) = ?A \<and> 
          (\<forall>k3 < k2. op_name (L' ! k3) = enq \<longrightarrow> 
             (\<exists>k4. k3 < k4 \<and> k4 < k_deq_A' \<and> 
                   op_name (L' ! k4) = deq \<and> op_val (L' ! k4) = op_val (L' ! k3)))"
    proof (rule exI[where x=k_enq_A'], intro conjI impI allI)
      show "k_enq_A' < k_deq_A'" using `k_enq_A' < k_deq_A'` .
      show "op_name (L' ! k_enq_A') = enq" using k_enq_A'_def(2) enq_A_L_props(2) by simp
      show "op_val (L' ! k_enq_A') = ?A" using k_enq_A'_def(2) enq_A_L_props(3) by simp
      
      fix k3 assume "k3 < k_enq_A'"
      assume is_enq_B: "op_name (L' ! k3) = enq"
      let ?B = "op_val (L' ! k3)"

      show "\<exists>k4. k3 < k4 \<and> k4 < k_deq_A' \<and> op_name (L' ! k4) = deq \<and> op_val (L' ! k4) = ?B"
      proof (cases "?B = v")
        case True
        have exists_deq_A: "\<exists>kD' < length L'. op_name (L' ! kD') = deq \<and> op_val (L' ! kD') = ?A"
          using k_bound is_deq by auto
          
        have "k_enq_A' < k3"
          using struct_props k_enq_A'_def(1) `k3 < k_enq_A'` order.strict_trans
          using enq_A_L_props(2,3) k_enq_A'_def(2) exists_deq_A is_enq_B True
          by (smt (verit, del_insts))
          
        then show ?thesis using `k3 < k_enq_A'` by simp
      next
        case False
        let ?rank_B = "length (filter ?P_enq (take k3 L'))"
        have "?rank_B < ?rank_enq_A"
        proof -
          have "take k_enq_A' L' = take k3 L' @ (L' ! k3) # (take (k_enq_A' - k3 - 1) (drop (k3 + 1) L'))"
            using `k3 < k_enq_A'` k_enq_A'_def(1)
            by (metis Cons_nth_drop_Suc One_nat_def Suc_pred add.right_neutral
                add_Suc_right add_diff_cancel_left' add_strict_mono
                less_imp_add_positive take_Suc_Cons take_add)
          then have "filter ?P_enq (take k_enq_A' L') = 
                     filter ?P_enq (take k3 L') @ filter ?P_enq [L' ! k3] @ filter ?P_enq (take (k_enq_A' - k3 - 1) (drop (k3 + 1) L'))"
            by simp
          moreover have "?P_enq (L' ! k3)" using is_enq_B False by simp
          ultimately have "length (filter ?P_enq (take k_enq_A' L')) > ?rank_B"
            by simp
          then show ?thesis using k_enq_A'_def(3) by simp
        qed

        obtain k_enq_B_L where k_enq_B_L_def:
          "k_enq_B_L < length L"
          "L ! k_enq_B_L = L' ! k3"
          "length (filter ?P_enq (take k_enq_B_L L)) = ?rank_B"
          using enq_ord filter_nth_ex_rank[where P="?P_enq"  and i="k3"] is_enq_B False
          using \<open>k3 < k_enq_A'\<close> k_enq_A'_def(1) order.strict_trans
          by blast

        (* SMT *)
        have "k_enq_B_L < k_enq_A_L"
        proof (rule ccontr)
          assume "\<not> k_enq_B_L < k_enq_A_L"
          then have "k_enq_A_L \<le> k_enq_B_L" by simp
          hence "take k_enq_B_L L = take k_enq_A_L L @ drop k_enq_A_L (take k_enq_B_L L)"
            by (metis drop_take le_add_diff_inverse take_add)
          hence "filter ?P_enq (take k_enq_B_L L) = filter ?P_enq (take k_enq_A_L L) @ filter ?P_enq (drop k_enq_A_L (take k_enq_B_L L))"
            by (metis filter_append)
          hence "length (filter ?P_enq (take k_enq_A_L L)) \<le> length (filter ?P_enq (take k_enq_B_L L))"
            by simp
          then have "?rank_enq_A \<le> ?rank_B" using enq_A_L_props(2,3) k_enq_B_L_def(3) by simp
          then show False using `?rank_B < ?rank_enq_A` by simp
        qed

        obtain k_deq_B_L where deq_B_L:
             "k_enq_B_L < k_deq_B_L" "k_deq_B_L < k_deq_A_L"
             "op_name (L!k_deq_B_L) = deq" "op_val (L!k_deq_B_L) = ?B"
             using fifo_L[rule_format, of k_enq_B_L] k_enq_B_L_def(1,3) `k_enq_B_L < k_enq_A_L`
             using is_enq_B k_enq_B_L_def(2) by auto

        let ?rank_deq_B = "length (filter ?P_deq (take k_deq_B_L L))"
        
        obtain k4 where k4_def:
             "k4 < length L'"
             "L' ! k4 = L ! k_deq_B_L"
             "length (filter ?P_deq (take k4 L')) = ?rank_deq_B"
             using deq_ord filter_nth_ex_rank[where P="?P_deq"  and i="k_deq_B_L"] deq_B_L(3)
             by (metis (no_types, lifting) deq_B_L(2) k_deq_A_L_def(1) order_less_trans)

        have "k4 < k_deq_A'"
        proof -
          have "length (filter ?P_deq (take k_deq_B_L L)) < length (filter ?P_deq (take k_deq_A_L L))"
          proof -
            have "take (Suc k_deq_B_L) L = take (Suc k_deq_B_L) (take k_deq_A_L L)"
              using deq_B_L(2) by simp
            moreover have "take k_deq_A_L L = take (Suc k_deq_B_L) (take k_deq_A_L L) @ drop (Suc k_deq_B_L) (take k_deq_A_L L)"
              by (metis append_take_drop_id)
            ultimately have split: "take k_deq_A_L L = take (Suc k_deq_B_L) L @ drop (Suc k_deq_B_L) (take k_deq_A_L L)"
              by simp
            have "take (Suc k_deq_B_L) L = take k_deq_B_L L @ [L ! k_deq_B_L]"
              using deq_B_L(2) k_deq_A_L_def(1) by (simp add: take_Suc_conv_app_nth)
            have "filter ?P_deq (take k_deq_A_L L) = 
                  filter ?P_deq (take k_deq_B_L L) @ filter ?P_deq [L ! k_deq_B_L] @ 
                  filter ?P_deq (drop (Suc k_deq_B_L) (take k_deq_A_L L))"
              by (metis
                  \<open>take (Suc k_deq_B_L) L = take (Suc k_deq_B_L) (take k_deq_A_L L)\<close>
                  \<open>take (Suc k_deq_B_L) L = take k_deq_B_L L @ [L ! k_deq_B_L]\<close>
                  \<open>take k_deq_A_L L = take (Suc k_deq_B_L) (take k_deq_A_L L) @ drop (Suc k_deq_B_L) (take k_deq_A_L L)\<close>
                  append.assoc filter_append)
            moreover have "filter ?P_deq [L ! k_deq_B_L] = [L ! k_deq_B_L]"
              using deq_B_L(3) by simp
            ultimately show ?thesis by simp
          qed
          then have rank_rel: "length (filter ?P_deq (take k4 L')) < ?rank_deq"
            using k4_def(3) k_deq_A_L_def(3) by simp
            
          (* SMT : rank index *)
          show ?thesis
          proof (rule ccontr)
            assume "\<not> k4 < k_deq_A'"
            hence "k_deq_A' \<le> k4" by simp
            hence "take k4 L' = take k_deq_A' L' @ drop k_deq_A' (take k4 L')"
              by (metis add.commute le_Suc_ex take_add take_drop)
            hence "filter ?P_deq (take k4 L') = filter ?P_deq (take k_deq_A' L') @ filter ?P_deq (drop k_deq_A' (take k4 L'))"
              by (metis filter_append)
            hence "length (filter ?P_deq (take k_deq_A' L')) \<le> length (filter ?P_deq (take k4 L'))"
              by simp
            thus False using rank_rel by simp
          qed
        qed

        have "k3 < k4"
        proof -
          have op4: "op_name (L' ! k4) = deq" using k4_def(2) deq_B_L(3) by simp
          have val4: "op_val (L' ! k4) = ?B" using k4_def(2) deq_B_L(4) by simp
          have op3: "op_name (L' ! k3) = enq" using is_enq_B by simp
          have val3: "op_val (L' ! k3) = ?B" using is_enq_B by simp

          show ?thesis
            using struct_props k4_def(1) `k3 < k_enq_A'` k_enq_A'_def(1) order_less_trans
            using op4 val4 op3 val3 by blast
        qed

        show ?thesis
            apply (rule exI[where x=k4])
            using k4_def deq_B_L `k4 < k_deq_A'` `k3 < k4` by auto
      qed
    qed
  qed
qed


(* ----------------------------------------------------------------- *)
(* modify_lin Distance = 0 *)
(* ----------------------------------------------------------------- *)
lemma modify_lin_Distance_zero_internal:
  assumes "data_independent L"
  assumes "lI4_FIFO_Semantics_list L"
  assumes "lI5_SA_Prefix_list L"
  assumes "\<forall>k < length L. op_val (L!k) = v \<longrightarrow> op_name (L!k) \<noteq> deq"
  assumes "\<exists>k < length L. op_name (L!k) = enq \<and> op_val (L!k) = v"
  shows "Distance (modify_lin L H v) v = 0"
  using assms
proof (induction L H v rule: modify_lin.induct)
  case (1 L_curr H bt_val)
  (* Step 1: 1. *)
  note IH = 1(1)
  note DI_L = 1(2)
  note lI4_FIFO_Semantics_L = 1(3)
  note lI5_SA_Prefix_L = 1(4)
  note pending_L = 1(5)
  note exists_L = 1(6)

  have independent_L_curr: "data_independent L_curr" using "1.prems" by blast
  have lin_L_curr: "lI4_FIFO_Semantics_list L_curr" using "1.prems" by blast
  have lin_I5_curr: "lI5_SA_Prefix_list L_curr" using "1.prems" by blast
  have pending_L: "\<forall>k < length L_curr. op_val (L_curr!k) = bt_val \<longrightarrow> op_name (L_curr!k) \<noteq> deq" 
    using "1.prems" by blast
  have exists_L: "\<exists>k < length L_curr. op_name (L_curr!k) = enq \<and> op_val (L_curr!k) = bt_val" 
    using "1.prems" by blast

  show ?case
  proof (cases "should_modify L_curr H bt_val")
    (* ========================================================== *)
    (* Case False: , *)
    (* ========================================================== *)
    case False
    have res_eq: "modify_lin L_curr H bt_val = L_curr" 
      using False by (subst modify_lin.simps, simp)
      
    have "Distance L_curr bt_val = 0"
    proof (rule ccontr)
      assume dist_not_zero: "Distance L_curr bt_val \<noteq> 0"
      
      (* , Distance 0, should_modify True *)
      have "should_modify L_curr H bt_val"
        apply (rule should_modify_completeness)
        apply (simp add: independent_L_curr)
        apply (simp add: lin_I5_curr)
        apply (simp add: pending_L)
        apply (simp add: exists_L)
        by (simp add: dist_not_zero)
      
      (* should_modify True False *)
      thus False using False by contradiction
    qed
    
    thus ?thesis using res_eq by simp

  next
    (* ========================================================== *)
    (* Case True: , 6 *)
    (* ========================================================== *)
    case True
    note do_modify = True
    
        (* 2. ( mset ) *)
        define last_sa_pos where "last_sa_pos = find_last_SA L_curr"
        define remaining where "remaining = drop (nat (last_sa_pos + 1)) L_curr"
        
        have idx_exists: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
          using True unfolding should_modify_def last_sa_pos_def remaining_def by (metis option.simps(4))
        
        obtain bt_idx where bt_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
          using idx_exists by blast

        have bt_idx_valid: "bt_idx < length remaining"
          using bt_idx_def by (rule find_unique_index_Some_less_length)

        define l1 where "l1 = take (nat (last_sa_pos + 1)) L_curr"
        define l2 where "l2 = take bt_idx remaining"
        define l3 where "l3 = drop (bt_idx + 1) remaining"
        define bt_act where "bt_act = remaining ! bt_idx"

        (* 3. : l2 *)
        have l2_not_nil: "l2 \<noteq> []"
        proof (cases "l2 = []")
          case True
          have "remaining \<noteq> []"
            using bt_idx_def apply (cases remaining) apply (auto simp: find_unique_index_def)
            using bt_idx_def find_unique_index_Some_less_length by force
          have "bt_idx = 0" 
            using True l2_def `remaining \<noteq> []` by (metis take_eq_Nil)
          have False
            using do_modify unfolding should_modify_def find_last_enq_def
            unfolding last_sa_pos_def remaining_def l1_def l2_def
            using `bt_idx = 0` bt_idx_def True by (simp add: last_sa_pos_def remaining_def)
          then show ?thesis ..
        next
          case False then show ?thesis by simp
        qed

        define l2_last where "l2_last = last l2"

    show ?thesis
    proof (cases "op_name l2_last = enq")
      (* === Case c0: Enq === *)
      case True
      note c0 = True

      define new_L where "new_L = l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3"
      
      have mod_eq: "modify_lin L_curr H bt_val = modify_lin new_L H bt_val"
      proof -
        (* 2: new_L , SMT *)
        have "modify_lin L_curr H bt_val = modify_lin (l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3) H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def do_modify c0
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          by (simp add: l2_def l2_last_def last_sa_pos_def
              remaining_def)
        thus ?thesis unfolding new_L_def by simp
      qed


            (* Step 1: 1. *)
            let ?pre = "l1 @ butlast l2"
            let ?idx = "length ?pre"
            
            (* Step 2: 2. L_curr new_L *)
             have L_curr_eq: "L_curr = ?pre @ [l2_last, bt_act] @ l3"
            proof -
              have "l2 = butlast l2 @ [l2_last]" using l2_not_nil l2_last_def by simp
              moreover have "remaining = l2 @ [bt_act] @ l3" 
                unfolding l2_def l3_def bt_act_def using bt_idx_valid by (simp add: id_take_nth_drop)
              ultimately show ?thesis unfolding l1_def remaining_def
                by (metis Cons_eq_appendI append_assoc append_take_drop_id
                    eq_Nil_appendI) 
            qed
            
            have new_L_eq: "new_L = ?pre @ [bt_act, l2_last] @ l3"
              unfolding new_L_def by simp

            have len_eq: "length new_L = length L_curr"
              using L_curr_eq new_L_eq by simp
              
            have l2_last_enq: "op_name l2_last = enq"
              by (simp add: c0) 
            have bt_act_enq: "op_name bt_act = enq" 
              using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def
              by (simp add: c0)

            (* Step 1: 1. *)
            have mset_eq: "mset new_L = mset L_curr"
            proof -
              have "mset new_L = mset (?pre @ [bt_act, l2_last] @ l3)" using new_L_eq by simp
              also have "... = mset (?pre @ [l2_last, bt_act] @ l3)" by (simp add: union_ac)
              also have "... = mset L_curr" using L_curr_eq by simp
              finally show ?thesis .
            qed


      (* IH 5 ( ) *)
      have indep_new: "data_independent new_L" 
           by (metis data_independent_cong independent_L_curr mod_eq
                modify_preserves_mset) 

      have p_lI4_FIFO_Semantics: "lI4_FIFO_Semantics_list new_L" 
          proof -
            (* Step 3: 3. , Let_def *)
            show ?thesis unfolding lI4_FIFO_Semantics_list_def Let_def
            proof (intro allI impI)
              fix kD assume kD_len: "kD < length new_L" 
              assume kD_deq: "op_name (new_L ! kD) = deq"
              
              (* A. kD *)
              have kD_not_idx: "kD \<noteq> ?idx \<and> kD \<noteq> ?idx + 1"
              proof (rule ccontr)
                assume "\<not> (kD \<noteq> ?idx \<and> kD \<noteq> ?idx + 1)"
                then consider (is_bt) "kD = ?idx" | (is_l2) "kD = ?idx + 1" by linarith
                then show False proof cases
                  case is_bt
                  have "new_L ! kD = bt_act" using is_bt new_L_eq by (simp add: nth_append)
                  with kD_deq bt_act_enq show False by simp
                next
                  case is_l2
                  have "new_L ! kD = l2_last" using is_l2 new_L_eq by (simp add: nth_append)
                  with kD_deq l2_last_enq show False by simp
                qed
              qed
              
              (* B. SMT : kD, *)
              have L_new_kD: "L_curr ! kD = new_L ! kD"
              proof -
                (* kD \<noteq> ?idx kD \<noteq> ?idx + 1 *)
                consider (before) "kD < ?idx" | (after) "kD \<ge> ?idx + 2"
                  using kD_not_idx by linarith
                then show ?thesis
                proof cases
                  case before
                  (* 1: kD ?pre , *)
                  then show ?thesis 
                    using L_curr_eq new_L_eq
                    by (metis nth_append_left) 
                next
                  case after
                  (* 2: kD l3 . A @ (B @ C) *)
                  
                  have "L_curr ! kD = (?pre @ ([l2_last, bt_act] @ l3)) ! kD"
                    using L_curr_eq by simp
                  also have "... = ([l2_last, bt_act] @ l3) ! (kD - ?idx)"
                    using after by (auto simp add: nth_append)
                  also have "... = l3 ! (kD - ?idx - 2)"
                    using after by (auto simp add: nth_append)
                  finally have eq1: "L_curr ! kD = l3 ! (kD - ?idx - 2)" .
                  
                  have "new_L ! kD = (?pre @ ([bt_act, l2_last] @ l3)) ! kD"
                    using new_L_eq by simp
                  also have "... = ([bt_act, l2_last] @ l3) ! (kD - ?idx)"
                    using after by (auto simp add: nth_append)
                  also have "... = l3 ! (kD - ?idx - 2)"
                    using after by (auto simp add: nth_append)
                  finally have eq2: "new_L ! kD = l3 ! (kD - ?idx - 2)" .
                  
                  show ?thesis using eq1 eq2 by simp
                qed
              qed

                
              (* C. k2 ( 4 ) *)
              obtain k2 where k2_props: 
                "k2 < kD" 
                "op_name (L_curr ! k2) = enq" 
                "op_val (L_curr ! k2) = op_val (L_curr ! kD)"
                "\<forall>k3<k2. op_name (L_curr ! k3) = enq \<longrightarrow> 
                  (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (L_curr ! k4) = deq \<and> op_val (L_curr ! k4) = op_val (L_curr ! k3))"
                using lin_L_curr[unfolded lI4_FIFO_Semantics_list_def Let_def, THEN spec, of kD]
                using `kD < length new_L` len_eq L_new_kD kD_deq
                by auto
                
              (* D. : lI5_SA_Prefix k2 *)
              show "\<exists>k2<kD. op_name (new_L ! k2) = enq \<and> op_val (new_L ! k2) = op_val (new_L ! kD) \<and>
                      (\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow>
                        (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)))"
              proof -
                define a where "a = op_val (L_curr ! kD)"
                have a_eq: "op_val (new_L ! kD) = a" using L_new_kD a_def by simp
                
                have "in_SA a L_curr" 
                proof -
                  (* Proof note. *)
                  have k2_len: "k2 < length L_curr" using k2_props(1) kD_len len_eq by simp
                  have kD_len_curr: "kD < length L_curr" using kD_len len_eq by simp
                  
                  (* Step 1: 1. Enq *)
                  have enq_not_none: "find_unique_index (\<lambda>x. op_name x = enq \<and> op_val x = a) L_curr \<noteq> None"
                  proof -
                    have "op_val (L_curr ! k2) = a" using k2_props(3) a_def by simp
                    hence "find_indices (\<lambda>x. op_name x = enq \<and> op_val x = a) L_curr = [k2]"
                      using k2_props(2) k2_len independent_L_curr unique_enq_index by blast
                    thus ?thesis unfolding find_unique_index_def by simp
                  qed
                  
                  (* Step 2: 2. Deq *)
                  moreover have deq_not_none: "find_unique_index (\<lambda>x. op_name x = deq \<and> op_val x = a) L_curr \<noteq> None"
                  proof -
                    have kD_is_deq: "op_name (L_curr ! kD) = deq" using kD_deq L_new_kD by simp
                    have "find_indices (\<lambda>x. op_name x = deq \<and> op_val x = a) L_curr = [kD]"
                      using kD_is_deq kD_len_curr a_def independent_L_curr unique_deq_index by blast
                    thus ?thesis unfolding find_unique_index_def by simp
                  qed
                  
                  ultimately show ?thesis unfolding in_SA_def by (auto split: option.splits)
                qed      

                (* lI5_SA_Prefix_list *)
                have k2_bound: "int k2 \<le> find_last_SA L_curr"
                  using lin_I5_curr[unfolded lI5_SA_Prefix_list_def] `in_SA a L_curr` k2_props(2) k2_props(3) a_def
                  by (metis k2_props(1) kD_len len_eq order.strict_trans) 
                  
                have k2_before_swap: "k2 < ?idx"
                proof -
                  (* remaining bt_idx, drop , *)
                  have bound: "nat (find_last_SA L_curr + 1) \<le> length L_curr"
                    using bt_idx_valid unfolding remaining_def last_sa_pos_def by simp

                  have "?idx = length l1 + length (butlast l2)" by simp
                  (* bound min , nat (x + 1) *)
                  also have "... = nat (find_last_SA L_curr + 1) + length (butlast l2)" 
                    unfolding l1_def last_sa_pos_def using bound by simp
                  finally have "?idx \<ge> nat (find_last_SA L_curr + 1)" by simp
                  
                  (* k2 : SA , <= find_last_SA *)
                  moreover have "k2 \<le> nat (find_last_SA L_curr)" 
                    using k2_bound by linarith
                    
                  (* Step 0: 0 : nat (x) nat (x + 1) > 0 . SMT , linarith *)
                  ultimately show ?thesis 
                    using k2_bound by linarith
                qed
                
                have L_new_k2: "new_L ! k2 = L_curr ! k2"
                  using k2_before_swap L_curr_eq new_L_eq
                  by (metis nth_append_cases(1)) 
                  
                (* Proof note. *)
                show ?thesis
                proof (rule exI[where x=k2], intro conjI)
                  show "k2 < kD" using k2_props(1) .
                  show "op_name (new_L ! k2) = enq" using k2_props(2) L_new_k2 by simp
                  show "op_val (new_L ! k2) = op_val (new_L ! kD)" using k2_props(3) L_new_k2 L_new_kD by simp
                  
                  show "\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow>
                        (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3))"
                  proof (intro allI impI)
                    fix k3 assume "k3 < k2" and k3_enq: "op_name (new_L ! k3) = enq"
                    
                    have k3_before_swap: "k3 < ?idx" using `k3 < k2` k2_before_swap by simp
                    have L_new_k3: "new_L ! k3 = L_curr ! k3" using k3_before_swap L_curr_eq new_L_eq
                      by (metis nth_append_cases(1)) 
                    
                    have "op_name (L_curr ! k3) = enq" using k3_enq L_new_k3 by simp
                    
                    obtain k4 where k4_props: "k3 < k4" "k4 < kD" "op_name (L_curr ! k4) = deq" 
                                              "op_val (L_curr ! k4) = op_val (L_curr ! k3)"
                      using k2_props(4)[rule_format, OF `k3 < k2` `op_name (L_curr ! k3) = enq`] by blast
                      
                    have k4_not_idx: "k4 \<noteq> ?idx \<and> k4 \<noteq> ?idx + 1"
                    proof (rule ccontr)
                      assume "\<not> (k4 \<noteq> ?idx \<and> k4 \<noteq> ?idx + 1)"
                      then consider (is_l2) "k4 = ?idx" | (is_bt) "k4 = ?idx + 1" by linarith
                      then show False proof cases
                        case is_l2
                        have "L_curr ! k4 = l2_last" using is_l2 L_curr_eq by (simp add: nth_append)
                        with k4_props(3) l2_last_enq show False by simp
                      next
                        case is_bt
                        have "L_curr ! k4 = bt_act" using is_bt L_curr_eq by (simp add: nth_append)
                        with k4_props(3) bt_act_enq show False by simp
                      qed
                    qed
                    
                    have L_new_k4: "new_L ! k4 = L_curr ! k4"
                    proof -
                      consider (before) "k4 < ?idx" | (after) "k4 \<ge> ?idx + 2" using k4_not_idx by linarith
                      then show ?thesis
                      proof cases
                        case before then show ?thesis using L_curr_eq new_L_eq
                          by (metis nth_append_cases(1)) 
                      next
                        case after
                        have "L_curr ! k4 = l3 ! (k4 - ?idx - 2)" using L_curr_eq after by (auto simp add: nth_append)
                        moreover have "new_L ! k4 = l3 ! (k4 - ?idx - 2)" using new_L_eq after by (auto simp add: nth_append)
                        ultimately show ?thesis by simp
                      qed
                    qed
                    
                    show "\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)"
                    proof (rule exI[where x=k4], intro conjI)
                      show "k3 < k4" "k4 < kD" using k4_props by auto
                      show "op_name (new_L ! k4) = deq" using k4_props(3) L_new_k4 by simp
                      show "op_val (new_L ! k4) = op_val (new_L ! k3)" using k4_props(4) L_new_k4 L_new_k3 by simp
                    qed
                  qed
                qed
              qed
            qed
          qed

      have p_lI5_SA_Prefix: "lI5_SA_Prefix_list new_L" 
          proof -            
            (* Step 3: 3. last_sa_pos  *)
            have prefix_eq: "take (nat (last_sa_pos + 1)) new_L = take (nat (last_sa_pos + 1)) L_curr"
            proof -
              have "take (nat (last_sa_pos + 1)) L_curr = l1" unfolding l1_def by simp
              moreover have "take (nat (last_sa_pos + 1)) new_L = l1"
              proof -
                have "new_L = l1 @ (butlast l2 @ [bt_act, l2_last] @ l3)" using new_L_eq by simp
                hence "take (length l1) new_L = take (length l1) (l1 @ (butlast l2 @ [bt_act, l2_last] @ l3))" by simp
                also have "... = l1" by simp
                finally show ?thesis unfolding l1_def
                  by (metis add_left_imp_eq append_eq_append_conv append_take_drop_id
                      len_eq length_append length_drop)
              qed
              ultimately show ?thesis by simp
            qed

            (* Step 2: 2. in_SA *)
            have in_SA_eq: "\<And>a. in_SA a new_L = in_SA a L_curr"
              using in_SA_mset_eq mset_eq by blast
               
            (* Step 3: 3. find_last_SA : PureLib.thy *)
            have sa_eq: "find_last_SA new_L = find_last_SA L_curr"
            proof -
              let ?n = "nat (last_sa_pos + 1)"
              
              (* A. L_curr Enq *)
              have suffix_L_curr: "\<forall>i \<in> {?n..<length L_curr}. \<not> (op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr)"
              proof (intro ballI notI)
                fix i assume "i \<in> {?n..<length L_curr}"
                then have "i < length L_curr" and "int i > find_last_SA L_curr"
                  unfolding last_sa_pos_def by auto
                assume "op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr"
                then have "op_name (L_curr ! i) = enq" and in_sa: "in_SA (op_val (L_curr ! i)) L_curr" by auto
                
                (* PureLib enqs_after_last_sa_are_not_in_sa *)
                from enqs_after_last_sa_are_not_in_sa[OF `i < length L_curr` `int i > find_last_SA L_curr` `op_name (L_curr ! i) = enq`]
                show False using in_sa by simp
              qed

              (* B. new_L Enq ( , SMT) *)
              have suffix_new_L: "\<forall>i \<in> {?n..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
              proof (intro ballI notI)
                fix i assume "i \<in> {?n..<length new_L}"
                assume bad: "op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L"
                then have is_enq: "op_name (new_L ! i) = enq" and in_sa: "in_SA (op_val (new_L ! i)) new_L" by auto
                
                (* in_SA in_SA *)
                have in_sa_curr: "in_SA (op_val (new_L ! i)) L_curr"
                  using in_sa in_SA_eq by simp
                
                (* k_old *)
                have "\<exists>k_old \<ge> ?n. k_old < length L_curr \<and> L_curr ! k_old = new_L ! i"
                proof -
                  consider (before) "i < ?idx" | (at_bt) "i = ?idx" | (at_l2) "i = ?idx + 1" | (after) "i \<ge> ?idx + 2" by linarith
                  then show ?thesis
                  proof cases
                    case before
                    have "new_L ! i = L_curr ! i" using before L_curr_eq new_L_eq
                      by (metis nth_append_cases(1)) 
                    moreover have "i \<ge> ?n" using `i \<in> {?n..<length new_L}` by simp
                    moreover have "i < length L_curr" using `i \<in> {?n..<length new_L}` len_eq by simp
                    ultimately show ?thesis
                      by auto 
                  next
                    case at_bt
                    have "new_L ! i = bt_act" using at_bt new_L_eq by (simp add: nth_append)
                    moreover have "L_curr ! (?idx + 1) = bt_act" using L_curr_eq by (simp add: nth_append)
                    moreover have "?idx + 1 \<ge> ?n"
                      by (metis \<open>i \<in> {nat (last_sa_pos + 1)..<length new_L}\<close> add.commute
                          atLeastLessThan_iff at_bt trans_le_add2)
                    (* 1: L_curr_eq ?idx + 1 *)
                    moreover have "?idx + 1 < length L_curr" using L_curr_eq by simp
                    (* 2: SMT , *)
                    ultimately show ?thesis by (rule_tac x="?idx + 1" in exI, simp)
                  next
                    case at_l2
                    have "new_L ! i = l2_last" using at_l2 new_L_eq by (simp add: nth_append)
                    moreover have "L_curr ! ?idx = l2_last" using L_curr_eq by (simp add: nth_append)
                    moreover have "?idx \<ge> ?n"
                      by (metis L_curr_eq List.nth_append_length
                          \<open>i \<in> {nat (last_sa_pos + 1)..<length new_L}\<close> append_Cons in_sa is_enq
                          linorder_le_less_linear new_L_eq nth_take prefix_eq
                          suffix_L_curr) 
                    (* 3 *)
                    moreover have "?idx < length L_curr" using L_curr_eq by simp
                    ultimately show ?thesis by (rule_tac x="?idx" in exI, simp)
                  next
                    case after
                    have "new_L ! i = L_curr ! i"
                    proof -
                      have "new_L ! i = l3 ! (i - ?idx - 2)" using after new_L_eq by (auto simp add: nth_append)
                      moreover have "L_curr ! i = l3 ! (i - ?idx - 2)" using after L_curr_eq by (auto simp add: nth_append)
                      ultimately show ?thesis by simp
                    qed
                    moreover have "i \<ge> ?n" using `i \<in> {?n..<length new_L}` by simp
                    moreover have "i < length L_curr" using `i \<in> {?n..<length new_L}` len_eq by simp
                    ultimately show ?thesis
                      by auto 
                  qed
                qed
                then obtain k_old where k_old_props: "k_old < length L_curr" "k_old \<ge> ?n" "L_curr ! k_old = new_L ! i" by blast
                
                (* Proof note. *)
                have "k_old \<in> {?n..<length L_curr}" using k_old_props by simp
                with suffix_L_curr have "\<not> (op_name (L_curr ! k_old) = enq \<and> in_SA (op_val (L_curr ! k_old)) L_curr)" by blast
                moreover have "op_name (L_curr ! k_old) = enq" using is_enq k_old_props(3) by simp
                ultimately have "\<not> in_SA (op_val (L_curr ! k_old)) L_curr" by simp
                
                with in_sa_curr k_old_props(3) show False by simp
              qed
              
              (* C. PureLib.thy find_last_SA_stable_prefix *)
              show ?thesis
              proof (rule find_last_SA_stable_prefix[of new_L L_curr "?n"])
                show "length new_L = length L_curr" using len_eq .
                show "take ?n new_L = take ?n L_curr" using prefix_eq .
                show "\<forall>i\<in>{?n..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)" using suffix_new_L .
                show "\<forall>i\<in>{?n..<length L_curr}. \<not> (op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr)" using suffix_L_curr .
                show "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L_curr" using in_SA_eq by blast
              qed
            qed

            (* Step 4: 4. lI5_SA_Prefix_list_def (, 100%) *)
            show ?thesis unfolding lI5_SA_Prefix_list_def
            proof (intro allI impI)
              fix k assume k_len: "k < length new_L" 
              assume k_enq: "op_name (new_L ! k) = enq"
              
              show "in_SA (op_val (new_L ! k)) new_L \<longleftrightarrow> int k \<le> find_last_SA new_L"
              proof -
                (* new_L L_curr *)
                have lhs_eq: "in_SA (op_val (new_L ! k)) new_L = in_SA (op_val (new_L ! k)) L_curr" 
                  using in_SA_eq by simp
                  
                (* nat (last_sa_pos + 1) , -1 *)
                consider (in_prefix) "k < nat (last_sa_pos + 1)" | (in_suffix) "k \<ge> nat (last_sa_pos + 1)" by linarith
                then show ?thesis
                proof cases
                  case in_prefix
                  (* A: k , *)
                  have k_eq: "new_L ! k = L_curr ! k"
                  proof -
                    have "take (nat (last_sa_pos + 1)) new_L ! k = take (nat (last_sa_pos + 1)) L_curr ! k"
                      using prefix_eq by simp
                    thus ?thesis using in_prefix k_len len_eq by simp
                  qed
                  
                  (* k < nat (last_sa_pos + 1), last_sa_pos >= 0, int k <= last_sa_pos *)
                  have rhs_true: "int k \<le> last_sa_pos"
                    using in_prefix by linarith
                    
                  (* lI5_SA_Prefix lhs True *)
                  have "in_SA (op_val (L_curr ! k)) L_curr"
                    by (metis k_enq k_eq k_len last_sa_pos_def lI5_SA_Prefix_list_def lin_I5_curr
                        mset_eq rhs_true size_mset)
                    
                  thus ?thesis using lhs_eq k_eq rhs_true sa_eq last_sa_pos_def by simp
                  
                next
                  case in_suffix
                  (* B: k *)
                  (* Step 1: 1. False: k >= nat (last_sa_pos + 1), int k > last_sa_pos *)
                  have rhs_false: "\<not> (int k \<le> find_last_SA new_L)"
                    using in_suffix sa_eq last_sa_pos_def by linarith
                    
                  (* Step 2: 2. False: suffix_new_L *)
                  have lhs_false: "\<not> in_SA (op_val (new_L ! k)) new_L"
                  proof -
                    have "k \<in> {nat (last_sa_pos + 1)..<length new_L}" using in_suffix k_len by simp
                    with k_enq show ?thesis
                      using enqs_after_last_sa_are_not_in_sa k_enq k_len rhs_false
                        verit_comp_simplify1(3) by blast 
                  qed
                  
                  show ?thesis using rhs_false lhs_false by simp
                qed
              qed
            qed
          qed

      have p_pending: "\<forall>k<length new_L. op_val (new_L ! k) = bt_val \<longrightarrow> op_name (new_L ! k) \<noteq> deq"
        by (metis in_set_conv_nth mod_eq modify_preserves_mset pending_L set_mset_mset)
      have p_exists: "\<exists>k<length new_L. op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = bt_val"
        by (metis exists_L in_set_conv_nth mod_eq modify_preserves_mset set_mset_mset)

      (* 1(1) *)
      show ?thesis
        unfolding mod_eq
        using "1.IH"(1) do_modify True bt_idx_def
        by (metis bt_act_def indep_new l1_def l2_def l2_last_def l3_def
            last_sa_pos_def new_L_def option.sel p_exists p_lI4_FIFO_Semantics p_lI5_SA_Prefix
            p_pending remaining_def)

    next
      (* === Case c1/c2/c3: Deq === *)
      case False
      note not_enq = False
      
      have find_enq_valid: "find_last_enq l2 \<noteq> None"
        using do_modify False l2_not_nil 
        unfolding should_modify_def l2_def remaining_def last_sa_pos_def l2_last_def 
        using bt_idx_def
        by (smt (verit) last_sa_pos_def option.simps(4,5) remaining_def) 

      obtain l21 b_act l22 where l2_split: "find_last_enq l2 = Some (l21, b_act, l22)"
        using find_enq_valid by (cases "find_last_enq l2", auto)
        
      define o1 where "o1 = hd l22"

          have l22_not_nil: "l22 \<noteq> []"
            using do_modify not_enq l2_last_def l2_split l2_not_nil unfolding find_last_enq_def using l2_def remaining_def
            by (metis find_last_enq_props(1,2) l2_split last_snoc self_append_conv)       

          have l2_eq: "l2 = l21 @ [b_act] @ l22"
            using find_last_enq_props(1)[OF l2_split] by simp
            
          have l22_eq: "l22 = o1 # tl l22"
            using l22_not_nil o1_def by simp
            
          have l2_eq_expanded: "l2 = l21 @ [b_act, o1] @ tl l22"
            using l2_eq l22_eq by simp
            
          have b_act_enq: "op_name b_act = enq"
            using find_last_enq_props(2)[OF l2_split] by simp
            
          have o1_deq: "op_name o1 = deq"
          proof -
            have "\<forall>x\<in>set l22. op_name x = deq"
              using find_last_enq_props(3)[OF l2_split]
              using mname.exhaust by auto 
            moreover have "o1 \<in> set l22" using l22_not_nil o1_def by simp
            ultimately show ?thesis by simp
          qed
          
          have bt_act_enq: "op_name bt_act = enq" 
            using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by auto

          (* ?idx ( b_act) ?idx+1 ( o1) *)
          let ?pre = "l1 @ l21"
          let ?idx = "length ?pre"
          
          have L_curr_eq: "L_curr = ?pre @ [b_act, o1] @ tl l22 @ [bt_act] @ l3"
          proof -
            have "remaining = l2 @ [bt_act] @ l3" 
              unfolding l2_def l3_def bt_act_def using bt_idx_valid by (simp add: id_take_nth_drop)
            hence "L_curr = l1 @ l2 @ [bt_act] @ l3" unfolding l1_def remaining_def
              by (metis append_take_drop_id) 
            thus ?thesis using l2_eq_expanded by auto
          qed

              (* Enq Deq , data_independent *)
              have val_neq: "op_val b_act \<noteq> op_val o1"
              proof (rule ccontr)
                assume "\<not> (op_val b_act \<noteq> op_val o1)"
                hence val_eq: "op_val b_act = op_val o1" by simp
                
                (* Step 1: 1. b_act (Enq) *)
                have idx_b_bound: "?idx < length L_curr" using L_curr_eq by simp
                have idx_b_val: "L_curr ! ?idx = b_act" using L_curr_eq by (simp add: nth_append)
                have b_is_enq: "op_name (L_curr ! ?idx) = enq" using idx_b_val b_act_enq by simp
                
                (* Step 2: 2. b_act SA *)
                have idx_after_sa: "int ?idx > find_last_SA L_curr"
                proof -
                  have bound: "nat (last_sa_pos + 1) \<le> length L_curr" 
                    using bt_idx_valid unfolding remaining_def by auto
                  have "?idx = length l1 + length l21" by simp
                  also have "... = (nat (last_sa_pos + 1)) + length l21" 
                    unfolding l1_def using bound by simp
                  finally show ?thesis unfolding last_sa_pos_def by linarith
                qed
                
                (* Step 3: 3. PureLib , SA Enq SA *)
                have not_in_sa: "\<not> in_SA (op_val b_act) L_curr"
                  using enqs_after_last_sa_are_not_in_sa[OF idx_b_bound idx_after_sa b_is_enq]
                  using idx_b_val by simp
                  
                (* Step 4: 4. : o1 Deq , SA *)
                have "in_SA (op_val b_act) L_curr"
                proof -
                  (* a. Enq *)
                  have enq_indices: "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = op_val b_act) L_curr = [?idx]"
                    using unique_enq_index[OF independent_L_curr b_is_enq _ idx_b_bound] idx_b_val by simp
                  
                  (* b. Deq *)
                  have idx_o_bound: "?idx + 1 < length L_curr" using L_curr_eq by simp
                  have idx_o_val: "L_curr ! (?idx + 1) = o1" using L_curr_eq by (simp add: nth_append)
                  have o_is_deq: "op_name (L_curr ! (?idx + 1)) = deq" using idx_o_val o1_deq by simp
                  have o_val_match: "op_val (L_curr ! (?idx + 1)) = op_val b_act" using idx_o_val val_eq by simp
                  
                  have deq_indices: "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = op_val b_act) L_curr = [?idx + 1]"
                    using unique_deq_index[OF independent_L_curr o_is_deq o_val_match idx_o_bound] by simp
                    
                  (* c. in_SA , SA *)
                  show ?thesis 
                    unfolding in_SA_def find_unique_index_def Let_def
                    using enq_indices deq_indices by (auto split: option.splits if_splits)
                qed
                
                (* Step 5: 5. *)
                with not_in_sa show False by simp
              qed

      (* Step 3: 3 *)
      consider 
          (c1) "happens_before o1 bt_act H" 
        | (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H"
        | (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast

      then show ?thesis
      proof cases
        case c1 (* === c1 === *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"
        
            (* new_L L_curr , [o1, b_act] *)
            have new_L_eq: "new_L = ?pre @ [o1, b_act] @ tl l22 @ [bt_act] @ l3"
              unfolding new_L_def by simp
              
            have len_eq: "length new_L = length L_curr"
              using L_curr_eq new_L_eq by simp

            have mset_eq: "mset new_L = mset L_curr"
            proof -
              have "mset new_L = mset (?pre @ [o1, b_act] @ tl l22 @ [bt_act] @ l3)" using new_L_eq by simp
              also have "... = mset (?pre @ [b_act, o1] @ tl l22 @ [bt_act] @ l3)" by (simp add: union_ac)
              also have "... = mset L_curr" using L_curr_eq by simp
              finally show ?thesis .
            qed

        have mod_eq: "modify_lin L_curr H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c1 False do_modify o1_def  apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold) apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)


        have indep_new: "data_independent new_L"
          by (metis data_independent_cong independent_L_curr mod_eq modify_preserves_mset)

        have p_lI4_FIFO_Semantics: "lI4_FIFO_Semantics_list new_L" 
            proof -
              (* ?map *)
              show ?thesis unfolding lI4_FIFO_Semantics_list_def Let_def
              proof (intro allI impI)
                fix kD assume kD_len: "kD < length new_L" 
                assume kD_deq: "op_name (new_L ! kD) = deq"
                
                (* Proof note. *)
                let ?map = "\<lambda>k. if k = ?idx then ?idx + 1 else if k = ?idx + 1 then ?idx else k"
                
                have kD_not_idx1: "kD \<noteq> ?idx + 1"
                proof (rule ccontr)
                  assume "\<not> (kD \<noteq> ?idx + 1)"
                  hence "new_L ! kD = b_act" using new_L_eq by (simp add: nth_append)
                  with kD_deq b_act_enq show False by simp
                qed
                
                (* kD *)
                define kD_old where "kD_old = ?map kD"
                
                (* Auxiliary lemma L_new_kD *)
                have L_new_kD: "new_L ! kD = L_curr ! kD_old"
                  using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                  using L_curr_eq new_L_eq kD_old_def by simp
                  
                have kD_old_len: "kD_old < length L_curr"
                  using kD_len len_eq kD_old_def kD_not_idx1 L_curr_eq by auto

                have kD_old_deq: "op_name (L_curr ! kD_old) = deq" using L_new_kD kD_deq by simp
                
                obtain k2_old where k2_old_props: 
                  "k2_old < kD_old" "op_name (L_curr ! k2_old) = enq" "op_val (L_curr ! k2_old) = op_val (L_curr ! kD_old)"
                  "\<forall>k3<k2_old. op_name (L_curr ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD_old \<and> op_name (L_curr ! k4) = deq \<and> op_val (L_curr ! k4) = op_val (L_curr ! k3))"
                  using lin_L_curr[unfolded lI4_FIFO_Semantics_list_def Let_def, THEN spec, of kD_old] using kD_old_len kD_old_deq by blast

                have k2_old_not_idx1: "k2_old \<noteq> ?idx + 1"
                proof (rule ccontr)
                  assume "\<not> (k2_old \<noteq> ?idx + 1)"
                  hence "L_curr ! k2_old = o1" using L_curr_eq by (simp add: nth_append)
                  with k2_old_props(2) o1_deq show False by simp
                qed

                (* k2 *)
                define k2 where "k2 = ?map k2_old"
                
                (* Proof note. *)
                have L_new_k2: "new_L ! k2 = L_curr ! k2_old"
                  using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                  using L_curr_eq new_L_eq k2_def by simp

                show "\<exists>k2<kD. op_name (new_L ! k2) = enq \<and> op_val (new_L ! k2) = op_val (new_L ! kD) \<and>
                        (\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)))"
                proof (rule exI[where x=k2], intro conjI)
                  
                  show "k2 < kD"
                  proof -
                    have kD_old_not_idx: "kD_old \<noteq> ?idx"
                      using kD_old_def kD_not_idx1 by (auto split: if_splits)
                      
                    (* val_neq , *)
                    have "k2_old \<noteq> ?idx \<or> kD_old \<noteq> ?idx + 1"
                    proof (rule ccontr)
                      assume "\<not> (k2_old \<noteq> ?idx \<or> kD_old \<noteq> ?idx + 1)"
                      hence "k2_old = ?idx" and "kD_old = ?idx + 1" by auto
                      hence "L_curr ! k2_old = b_act" and "L_curr ! kD_old = o1" using L_curr_eq by (auto simp add: nth_append)
                      hence "op_val b_act = op_val o1" using k2_old_props(3) by simp
                      thus False using val_neq by simp
                    qed
                    
                    (* , auto *)
                    thus ?thesis using k2_old_props(1) k2_def kD_old_def kD_not_idx1 k2_old_not_idx1 kD_old_not_idx
                      by (metis Suc_eq_plus1 linorder_cases not_less_eq) 
                  qed
                  
                  show "op_name (new_L ! k2) = enq" using k2_old_props(2) L_new_k2 by simp
                  show "op_val (new_L ! k2) = op_val (new_L ! kD)" using k2_old_props(3) L_new_k2 L_new_kD by simp
                  
                  show "\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3))"
                  proof (intro allI impI)
                    fix k3 assume "k3 < k2" and k3_enq: "op_name (new_L ! k3) = enq"
                    
                    have k3_not_idx: "k3 \<noteq> ?idx"
                    proof (rule ccontr)
                      assume "\<not> (k3 \<noteq> ?idx)"
                      hence "new_L ! k3 = o1" using new_L_eq by (simp add: nth_append)
                      with k3_enq o1_deq show False by simp
                    qed
                    
                    (* k3 *)
                    define k3_old where "k3_old = ?map k3"
                    
                    have L_new_k3: "new_L ! k3 = L_curr ! k3_old"
                      using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                      using L_curr_eq new_L_eq k3_old_def by simp
                      
                    have "k3_old < k2_old"
                    proof -
                      have "k3_old \<noteq> ?idx \<or> k2_old \<noteq> ?idx + 1" using k2_old_not_idx1 by simp
                      thus ?thesis using `k3 < k2` k3_old_def k2_def k3_not_idx k2_old_not_idx1
                        by (metis le_antisym less_iff_succ_less_eq nat_less_le
                            nat_neq_iff) 
                    qed
                    
                    obtain k4_old where k4_old_props: "k3_old < k4_old" "k4_old < kD_old" "op_name (L_curr ! k4_old) = deq" 
                                              "op_val (L_curr ! k4_old) = op_val (L_curr ! k3_old)"
                      using L_new_k3 \<open>k3_old < k2_old\<close> k2_old_props(4) k3_enq by auto
                      
                    have k4_old_not_idx: "k4_old \<noteq> ?idx"
                    proof (rule ccontr)
                      assume "\<not> (k4_old \<noteq> ?idx)"
                      hence "L_curr ! k4_old = b_act" using L_curr_eq by (simp add: nth_append)
                      with k4_old_props(3) b_act_enq show False by simp
                    qed
                    
                    (* k4 *)
                    define k4 where "k4 = ?map k4_old"
                    
                    have L_new_k4: "new_L ! k4 = L_curr ! k4_old"
                      using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                      using L_curr_eq new_L_eq k4_def by simp
                      
                    show "\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)"
                    proof (rule exI[where x=k4], intro conjI)
                      show "k3 < k4"
                      proof -
                        (* k3_old k4_old *)
                        have no_reverse: "k3_old \<noteq> ?idx \<or> k4_old \<noteq> ?idx + 1"
                        proof (rule ccontr)
                          assume "\<not> (k3_old \<noteq> ?idx \<or> k4_old \<noteq> ?idx + 1)"
                          hence "k3_old = ?idx" and "k4_old = ?idx + 1" by auto
                          
                          (* Proof note. *)
                          hence "L_curr ! k3_old = b_act" and "L_curr ! k4_old = o1" 
                            using L_curr_eq by (auto simp add: nth_append)
                            
                          (* k4_old_props, *)
                          hence "op_val o1 = op_val b_act" 
                            using k4_old_props(4) by simp
                            
                          (* val_neq, *)
                          thus False using val_neq by auto
                        qed
                        
                        (* , , auto *)
                        thus ?thesis using k4_old_props(1) k3_old_def k4_def k3_not_idx k4_old_not_idx
                          by (metis Suc_eq_plus1 Suc_leI le_neq_implies_less less_SucE)
                      qed
                      show "k4 < kD"
                      proof -
                        have kD_old_not_idx: "kD_old \<noteq> ?idx" using kD_old_def kD_not_idx1 by (auto split: if_splits)
                        have "k4_old \<noteq> ?idx \<or> kD_old \<noteq> ?idx + 1" using k4_old_not_idx by simp
                        thus ?thesis using k4_old_props(2) k4_def kD_old_def k4_old_not_idx kD_old_not_idx kD_not_idx1
                          by (metis add.commute add_lessD1 less_SucE plus_1_eq_Suc) 
                      qed
                      show "op_name (new_L ! k4) = deq" using k4_old_props(3) L_new_k4 by simp
                      show "op_val (new_L ! k4) = op_val (new_L ! k3)" using k4_old_props(4) L_new_k4 L_new_k3 by simp
                    qed
                  qed
                qed
              qed
            qed

        have p_lI5_SA_Prefix: "lI5_SA_Prefix_list new_L" 
            proof -
              let ?n = "nat (last_sa_pos + 1)"
              let ?map = "\<lambda>k. if k = ?idx then ?idx + 1 else if k = ?idx + 1 then ?idx else k"
              
              (* Proof note. *)
              have sa_bound: "?n \<le> ?idx"
              proof -
                have bound: "?n \<le> length L_curr" using bt_idx_valid unfolding remaining_def by auto
                have "?idx = length l1 + length l21" by simp
                also have "... = ?n + length l21" unfolding l1_def using bound by simp
                finally show ?thesis by linarith
              qed

              (* Step 1: 1. *)
              have prefix_eq: "take ?n new_L = take ?n L_curr"
              proof -
                have "take ?n L_curr = l1" unfolding l1_def by simp
                moreover have "take ?n new_L = l1"
                proof -
                  have "new_L = l1 @ (l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3)" using new_L_eq by simp
                  hence "take (length l1) new_L = take (length l1) (l1 @ (l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3))" by simp
                  also have "... = l1" by simp
                  finally show ?thesis unfolding l1_def 
                    by (metis add_left_imp_eq append_eq_append_conv append_take_drop_id len_eq length_append length_drop)
                qed
                ultimately show ?thesis by simp
              qed

              (* Step 2: 2. in_SA *)
              have in_SA_eq: "\<And>a. in_SA a new_L = in_SA a L_curr"
              proof -
                fix a
                have eq1: "L_curr = l1 @ remaining" unfolding l1_def remaining_def by simp
                have eq2: "new_L = l1 @ (l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3)" unfolding new_L_def l1_def by simp
                have rem_not_nil: "remaining \<noteq> []" 
                proof (cases remaining)
                  case Nil with bt_idx_valid show ?thesis by simp
                next
                  case Cons thus ?thesis by simp
                qed
                have "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L_curr"
                  using L_and_new_L_have_same_SA[of L_curr l1 remaining new_L "l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3" last_sa_pos]
                  using independent_L_curr eq1 eq2 rem_not_nil mset_eq l1_def last_sa_pos_def
                  by metis 
                thus "in_SA a new_L = in_SA a L_curr" by simp
              qed

              (* Step 3: 3. find_last_SA *)
              have sa_eq: "find_last_SA new_L = find_last_SA L_curr"
              proof -
                have suffix_L_curr: "\<forall>i \<in> {?n..<length L_curr}. \<not> (op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr)"
                proof (intro ballI notI)
                  fix i assume "i \<in> {?n..<length L_curr}"
                  then have "i < length L_curr" and "int i > find_last_SA L_curr" unfolding last_sa_pos_def by auto
                  assume "op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr"
                  then have "op_name (L_curr ! i) = enq" and in_sa: "in_SA (op_val (L_curr ! i)) L_curr" by auto
                  from enqs_after_last_sa_are_not_in_sa[OF `i < length L_curr` `int i > find_last_SA L_curr` `op_name (L_curr ! i) = enq`]
                  show False using in_sa by simp
                qed

                have suffix_new_L: "\<forall>i \<in> {?n..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
                proof (intro ballI notI)
                  fix i assume "i \<in> {?n..<length new_L}"
                  assume bad: "op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L"
                  then have is_enq: "op_name (new_L ! i) = enq" and in_sa: "in_SA (op_val (new_L ! i)) new_L" by auto
                  have in_sa_curr: "in_SA (op_val (new_L ! i)) L_curr" using in_sa in_SA_eq by simp
                  
                  (* ?map L_curr *)
                  define k_old where "k_old = ?map i"
                  have "new_L ! i = L_curr ! k_old"
                    using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                    using L_curr_eq new_L_eq k_old_def by simp
                  moreover have "k_old \<ge> ?n" using `i \<in> {?n..<length new_L}` sa_bound k_old_def by auto
                  (* 【 】: L_curr_eq , Isabelle +1 *)
                  moreover have "k_old < length L_curr"
                  proof -
                    have "?idx + 1 < length L_curr" using L_curr_eq by simp
                    thus ?thesis using `i \<in> {?n..<length new_L}` len_eq k_old_def by auto
                  qed
                  ultimately have "k_old \<in> {?n..<length L_curr}" by simp
                  
                  with suffix_L_curr have "\<not> (op_name (L_curr ! k_old) = enq \<and> in_SA (op_val (L_curr ! k_old)) L_curr)" by blast
                  moreover have "op_name (L_curr ! k_old) = enq" using is_enq `new_L ! i = L_curr ! k_old` by simp
                  ultimately have "\<not> in_SA (op_val (L_curr ! k_old)) L_curr" by simp
                  with in_sa_curr `new_L ! i = L_curr ! k_old` show False by simp
                qed
                
                show ?thesis
                proof (rule find_last_SA_stable_prefix[of new_L L_curr "?n"])
                  show "length new_L = length L_curr" using len_eq .
                  show "take ?n new_L = take ?n L_curr" using prefix_eq .
                  show "\<forall>i\<in>{?n..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)" using suffix_new_L .
                  show "\<forall>i\<in>{?n..<length L_curr}. \<not> (op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr)" using suffix_L_curr .
                  show "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L_curr" using in_SA_eq by blast
                qed
              qed

              (* Step 4: 4. lI5_SA_Prefix_list_def  *)
              show ?thesis unfolding lI5_SA_Prefix_list_def
              proof (intro allI impI)
                fix k assume k_len: "k < length new_L" 
                assume k_enq: "op_name (new_L ! k) = enq"
                
                (* Proof note. *)
                define k_old where "k_old = ?map k"
                have L_new_k: "new_L ! k = L_curr ! k_old"
                  using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                  using L_curr_eq new_L_eq k_old_def by simp
                
                (* 【 】: , k_old *)
                have k_old_len: "k_old < length L_curr" 
                proof -
                  have "?idx + 1 < length L_curr" using L_curr_eq by simp
                  thus ?thesis using k_len len_eq k_old_def by auto
                qed
                
                have lhs_eq: "in_SA (op_val (new_L ! k)) new_L = in_SA (op_val (new_L ! k)) L_curr" using in_SA_eq by simp
                
                (* 【 】: nat (last_sa_pos + 1) *)
                consider (in_prefix) "k < nat (last_sa_pos + 1)" | (in_suffix) "k \<ge> nat (last_sa_pos + 1)" by linarith
                then show "in_SA (op_val (new_L ! k)) new_L \<longleftrightarrow> int k \<le> find_last_SA new_L"
                proof cases
                  case in_prefix
                  (* A: prefix , k ?idx, ?map k_old = k *)
                  have "k < ?idx" using in_prefix sa_bound by linarith
                  hence "k_old = k" using k_old_def by simp
                  hence "new_L ! k = L_curr ! k" using L_new_k by simp
                  
                  hence "op_name (L_curr ! k) = enq" using k_enq by simp
                  moreover have "k < length L_curr" using k_len len_eq by simp
                  (* int *)
                  moreover have rhs_true: "int k \<le> last_sa_pos" using in_prefix by linarith
                  ultimately have "in_SA (op_val (L_curr ! k)) L_curr"
                    using lin_I5_curr[unfolded lI5_SA_Prefix_list_def, THEN spec, of k] unfolding last_sa_pos_def by blast
                  thus ?thesis using `new_L ! k = L_curr ! k` lhs_eq sa_eq last_sa_pos_def rhs_true by simp
                  
                next
                  case in_suffix
                  (* B: suffix . swap, k_old >= *)
                  (* Step 1: 1. k_old >= nat (last_sa_pos + 1) *)
                  have k_old_ge_bound: "k_old \<ge> nat (last_sa_pos + 1)"
                  proof -
                    (* k >= , , *)
                    have "k \<ge> nat (last_sa_pos + 1)" using in_suffix by simp
                    moreover have "nat (last_sa_pos + 1) \<le> ?idx" using sa_bound by simp
                    ultimately show ?thesis unfolding k_old_def by auto
                  qed
                  
                  (* Step 2: 2. int , nat(-1)=0 *)
                  (* int k_old > last_sa_pos *)
                  have "int k_old > last_sa_pos"
                  proof -
                    (* 1: int (nat X) >= X *)
                    have "int (nat (last_sa_pos + 1)) \<ge> last_sa_pos + 1" by simp
                    (* 2 *)
                    moreover have "int k_old \<ge> int (nat (last_sa_pos + 1))" 
                      using k_old_ge_bound by linarith
                    (* linarith *)
                    ultimately show ?thesis by linarith
                  qed
                  
                  (* Step 3: 3. lI5_SA_Prefix *)
                  have "op_name (L_curr ! k_old) = enq" using k_enq L_new_k by simp
                  hence "\<not> in_SA (op_val (L_curr ! k_old)) L_curr"
                    using lin_I5_curr[unfolded lI5_SA_Prefix_list_def, THEN spec, of k_old] 
                    using `int k_old > last_sa_pos` k_old_len
                    by (simp add: last_sa_pos_def) 
                  hence "\<not> in_SA (op_val (new_L ! k)) new_L" using L_new_k lhs_eq by simp
                  
                  (* Step 4: 4. False ( int ) *)
                  moreover have "\<not> (int k \<le> find_last_SA new_L)" 
                  proof -
                    (* 1: int (nat X) >= X *)
                    have "int (nat (last_sa_pos + 1)) \<ge> last_sa_pos + 1" by simp
                    (* 2: in_suffix ( k >= nat (last_sa_pos + 1)) int *)
                    moreover have "int k \<ge> int (nat (last_sa_pos + 1))" 
                      using in_suffix by linarith
                    (* , linarith *)
                    ultimately have "int k > last_sa_pos" by linarith
                    (* Proof note. *)
                    thus ?thesis using sa_eq last_sa_pos_def by simp
                  qed
                  
                  ultimately show ?thesis by simp
                qed
              qed
            qed

        have p_pending: "\<forall>k<length new_L. op_val (new_L ! k) = bt_val \<longrightarrow> op_name (new_L ! k) \<noteq> deq"
          by (metis in_set_conv_nth mod_eq modify_preserves_mset pending_L set_mset_mset)
        have p_exists: "\<exists>k<length new_L. op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = bt_val"
          by (metis exists_L in_set_conv_nth mod_eq modify_preserves_mset set_mset_mset)

        (* === SMT === *)
        (* Step 1: 1. , 1.IH(2) AST 100% *)
        define L_inner where "L_inner = take (nat (find_last_SA L_curr + 1)) L_curr @ l21 @ [hd l22] @ [b_act] @ tl l22 @ [drop (nat (find_last_SA L_curr + 1)) L_curr ! bt_idx] @ drop (bt_idx + 1) (drop (nat (find_last_SA L_curr + 1)) L_curr)"
        
        have new_L_eq_L_inner: "new_L = L_inner"
          unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def o1_def L_inner_def by simp
          
        (* Step 2: 2. L_inner , new_L *)
        have p1_in: "data_independent L_inner" using indep_new unfolding new_L_eq_L_inner .
        have p2_in: "lI4_FIFO_Semantics_list L_inner" using p_lI4_FIFO_Semantics unfolding new_L_eq_L_inner .
        have p3_in: "lI5_SA_Prefix_list L_inner" using p_lI5_SA_Prefix unfolding new_L_eq_L_inner .
        have p4_in: "\<forall>k<length L_inner. op_val (L_inner ! k) = bt_val \<longrightarrow> op_name (L_inner ! k) \<noteq> deq" using p_pending unfolding new_L_eq_L_inner .
        have p5_in: "\<exists>k<length L_inner. op_name (L_inner ! k) = enq \<and> op_val (L_inner ! k) = bt_val" using p_exists unfolding new_L_eq_L_inner .

        (* Step 3: 3. IH 5 , *)
        have pre1: "should_modify L_curr H bt_val" using do_modify .
        have pre2: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L_curr + 1)) L_curr) = Some bt_idx"
          using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] .
        have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L_curr + 1)) L_curr))) \<noteq> enq"
          using False unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] .
        have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L_curr + 1)) L_curr)) = Some (l21, b_act, l22)"
          using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] .
        have pre5: "happens_before (hd l22) (drop (nat (find_last_SA L_curr + 1)) L_curr ! bt_idx) H"
          using c1 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] o1_def[symmetric] .

        (* Step 4: 4. simp , metis *)
        show ?thesis 
          unfolding mod_eq new_L_eq_L_inner
          unfolding L_inner_def
          using "1.IH"(2) pre1 pre2 pre3 pre4 pre5 p1_in p2_in p3_in p4_in p5_in
          unfolding L_inner_def
          by simp


      next
        case c2 (* === c2 === *)
        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"
        
            have new_L_eq: "new_L = ?pre @ [bt_act, b_act] @ l22 @ l3"
              unfolding new_L_def by simp
              
            have len_eq: "length new_L = length L_curr"
            proof -
              have "L_curr = ?pre @ [b_act] @ l22 @ [bt_act] @ l3"
                using L_curr_eq l22_eq by simp
              thus ?thesis using new_L_eq by simp
            qed

        have mod_eq: "modify_lin L_curr H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c2 False do_modify o1_def  apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold) apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def last_sa_pos_def new_L_def remaining_def)

            (* Step 3: 3. (, ) *)
            have indep_new: "data_independent new_L"
              by (metis data_independent_cong independent_L_curr mod_eq modify_preserves_mset)

        have p_lI4_FIFO_Semantics: "lI4_FIFO_Semantics_list new_L" 
            proof -
              let ?m_len = "length l22"
              
              (* Step 1: 1. (: -> ) *)
              let ?map_back = "\<lambda>k. if k < ?idx then k 
                                  else if k = ?idx then ?idx + ?m_len + 1 
                                  else if k \<le> ?idx + ?m_len + 1 then k - 1 
                                  else k"
                                  
              (* Step 2: 2. (: -> ) *)
              (* 3 & 4 : bt_act , deq l22 , *)
              let ?map_fwd = "\<lambda>k. if k < ?idx then k 
                                  else if k \<le> ?idx + ?m_len then k + 1 
                                  else k"

              (* bt_act *)
              have bt_act_old_pos: "L_curr ! (?idx + ?m_len + 1) = bt_act"
              proof -
                (* "bt_act " "bt_act " *)
                have "L_curr = (?pre @ [b_act] @ l22) @ (bt_act # l3)"
                  using L_curr_eq l22_eq by simp
                
                (* Proof note. *)
                moreover have "length (?pre @ [b_act] @ l22) = ?idx + ?m_len + 1"
                  by simp
                
                (* (A @ B) ! length A = B ! 0, *)
                ultimately show ?thesis 
                  by (simp add: nth_append)
              qed

              show ?thesis unfolding lI4_FIFO_Semantics_list_def Let_def
              proof (intro allI impI)
                fix kD assume kD_len: "kD < length new_L" 
                assume kD_deq: "op_name (new_L ! kD) = deq"
                
                (* kD bt_act *)
                have kD_not_idx: "kD \<noteq> ?idx" 
                  using kD_deq bt_act_enq new_L_eq by (auto simp: nth_append)

                define kD_old where "kD_old = ?map_back kD"
                
                have L_new_kD: "new_L ! kD = L_curr ! kD_old"
                proof -
                  have L_exp: "L_curr = ?pre @ [b_act] @ l22 @ [bt_act] @ l3" using L_curr_eq l22_eq by simp
                  have N_exp: "new_L = ?pre @ [bt_act] @ [b_act] @ l22 @ l3" using new_L_eq by simp
                  show ?thesis using jump_back_nth[OF L_exp N_exp refl refl, of kD] unfolding kD_old_def by simp
                qed

                have kD_old_len: "kD_old < length L_curr" using kD_len len_eq kD_old_def
                  using kD_not_idx by auto 
                have kD_old_deq: "op_name (L_curr ! kD_old) = deq" using L_new_kD kD_deq by simp
                
                obtain k2_old where k2_old_props: 
                  "k2_old < kD_old" "op_name (L_curr ! k2_old) = enq" 
                  "op_val (L_curr ! k2_old) = op_val (L_curr ! kD_old)"
                  "\<forall>k3<k2_old. op_name (L_curr ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD_old \<and> op_name (L_curr ! k4) = deq \<and> op_val (L_curr ! k4) = op_val (L_curr ! k3))"
                  using lin_L_curr[unfolded lI4_FIFO_Semantics_list_def Let_def, THEN spec, of kD_old] using kD_old_len L_new_kD kD_deq by auto

                (* ================================================================= *)
                (* 1: kD_old Enq SA, l1 *)
                (* ================================================================= *)
                have k2_old_in_SA: "k2_old < length l1"
                proof -
                  define V where "V = op_val (L_curr ! kD_old)"
                  have "in_SA V L_curr"
                  proof -
                    have e_idx: "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = V) L_curr = [k2_old]"
                      using unique_enq_index[OF independent_L_curr k2_old_props(2) _] using k2_old_props(1) kD_old_len k2_old_props(3) V_def by auto
                    have d_idx: "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = V) L_curr = [kD_old]"
                      using unique_deq_index[OF independent_L_curr kD_old_deq _ kD_old_len] using V_def by auto
                    show ?thesis unfolding in_SA_def find_unique_index_def Let_def using e_idx d_idx k2_old_props(1) by (auto split: option.splits)
                  qed
                  hence "int k2_old \<le> find_last_SA L_curr"
                    using lin_I5_curr[unfolded lI5_SA_Prefix_list_def, THEN spec, of k2_old] using k2_old_props(1,2) kD_old_len
                    using V_def k2_old_props(3) by auto
                  moreover have "find_last_SA L_curr = last_sa_pos"
                    by (simp add: last_sa_pos_def) 
                  moreover have "length l1 = nat (last_sa_pos + 1)"
                  proof -
                    have bound: "nat (last_sa_pos + 1) \<le> length L_curr" using bt_idx_valid unfolding remaining_def last_sa_pos_def
                      by simp 
                    show ?thesis unfolding l1_def using bound by (simp add: min_absorb2)
                  qed
                  ultimately show ?thesis by linarith
                qed

                (* k2_old k3 ?idx *)
                have k2_old_lt_idx: "k2_old < ?idx" using k2_old_in_SA by simp

                (* k2 , *)
                define k2 where "k2 = k2_old"

                have L_new_k2: "new_L ! k2 = L_curr ! k2_old"
                proof -
                  have L_exp: "L_curr = ?pre @ [b_act] @ l22 @ [bt_act] @ l3" using L_curr_eq l22_eq by simp
                  have N_exp: "new_L = ?pre @ [bt_act] @ [b_act] @ l22 @ l3" using new_L_eq by simp
                  show ?thesis using jump_back_nth[OF L_exp N_exp refl refl, of k2] unfolding k2_def using k2_old_lt_idx by simp
                qed

                show "\<exists>k2<kD. op_name (new_L ! k2) = enq \<and> op_val (new_L ! k2) = op_val (new_L ! kD) \<and>
                        (\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)))"
                proof (rule exI[where x=k2], intro conjI)
                  
                  show "k2 < kD"
                  proof -
                    have "kD_old > k2_old" using k2_old_props(1) .
                    thus ?thesis unfolding k2_def kD_old_def using k2_old_lt_idx kD_not_idx by (auto split: if_splits)
                  qed

                  show "op_name (new_L ! k2) = enq" using k2_old_props(2) L_new_k2 by simp
                  show "op_val (new_L ! k2) = op_val (new_L ! kD)" using k2_old_props(3) L_new_k2 L_new_kD by simp

                  (* ================================================================= *)
                  (* 2: SA , Deq *)
                  (* ================================================================= *)
                  show "\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3))"
                  proof (intro allI impI)
                    fix k3 assume "k3 < k2" and k3_enq: "op_name (new_L ! k3) = enq"
                    
                    (* , k3 *)
                    have k3_lt_idx: "k3 < ?idx" using `k3 < k2` k2_def k2_old_lt_idx by simp
                    define k3_old where "k3_old = k3"
                    
                    have L_new_k3: "new_L ! k3 = L_curr ! k3_old"
                    proof -
                      have L_exp: "L_curr = ?pre @ [b_act] @ l22 @ [bt_act] @ l3" using L_curr_eq l22_eq by simp
                      have N_exp: "new_L = ?pre @ [bt_act] @ [b_act] @ l22 @ l3" using new_L_eq by simp
                      show ?thesis using jump_back_nth[OF L_exp N_exp refl refl, of k3] unfolding k3_old_def using k3_lt_idx by simp
                    qed

                    have k3_old_enq: "op_name (L_curr ! k3_old) = enq" using k3_enq L_new_k3 by simp
                    have k3_old_lt_k2_old: "k3_old < k2_old" unfolding k3_old_def k2_def using `k3 < k2`
                      by (simp add: k2_def) 

                    (* Deq k4_old *)
                    obtain k4_old where k4_old_props: 
                      "k3_old < k4_old" "k4_old < kD_old" 
                      "op_name (L_curr ! k4_old) = deq" 
                      "op_val (L_curr ! k4_old) = op_val (L_curr ! k3_old)"
                      using k2_old_props(4)[rule_format, OF k3_old_lt_k2_old] k3_old_enq by blast

                    (* 3: , Deq *)
                    define k4 where "k4 = ?map_fwd k4_old"

                    (* k4_old bt_act, deq *)
                    have k4_old_not_bt: "k4_old \<noteq> ?idx + ?m_len + 1"
                    proof
                      assume "k4_old = ?idx + ?m_len + 1"
                      hence "L_curr ! k4_old = bt_act" using bt_act_old_pos by simp
                      with k4_old_props(3) bt_act_enq show False by simp
                    qed

                    have L_new_k4: "new_L ! k4 = L_curr ! k4_old"
                    proof -
                      have L_exp: "L_curr = ?pre @ [b_act] @ l22 @ [bt_act] @ l3" 
                        using L_curr_eq l22_eq by simp
                      have N_exp: "new_L = ?pre @ [bt_act] @ [b_act] @ l22 @ l3" 
                        using new_L_eq by simp
                      
                      (* Step 1: 1. k4 jump_back_nth *)
                      have "new_L ! k4 = L_curr ! (
                        if k4 < ?idx then k4
                        else if k4 = ?idx then ?idx + ?m_len + 1  
                        else if k4 \<le> ?idx + ?m_len + 1 then k4 - 1 
                        else k4)"
                        using jump_back_nth[OF L_exp N_exp refl refl, of k4] .
                        
                      (* Step 2: 2. : ?map_back (?map_fwd k4_old) = k4_old *)
                      (* k4_old_not_bt, auto *)
                      moreover have "(
                        if k4 < ?idx then k4
                        else if k4 = ?idx then ?idx + ?m_len + 1  
                        else if k4 \<le> ?idx + ?m_len + 1 then k4 - 1 
                        else k4) = k4_old"
                        unfolding k4_def using k4_old_not_bt by auto
                        
                      ultimately show ?thesis by simp
                    qed

                    show "\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)"
                    proof (rule exI[where x=k4], intro conjI)
                      
                      (* k3 < k4 *)
                      show "k3 < k4"
                      proof -
                        have "k3_old < k4_old" using k4_old_props(1) .
                        thus ?thesis unfolding k3_old_def k4_def using k3_lt_idx by (auto split: if_splits)
                      qed
                      
                      (* bt_act k4_old kD_old, *)
                      show "k4 < kD"
                      proof -
                        have kD_old_not_bt: "kD_old \<noteq> ?idx + ?m_len + 1"
                        proof
                          assume "kD_old = ?idx + ?m_len + 1"
                          hence "L_curr ! kD_old = bt_act" using bt_act_old_pos by simp
                          with kD_old_deq bt_act_enq show False by simp
                        qed

                        (* kD kD_old , ?map_fwd *)
                        have kD_is_fwd: "kD = ?map_fwd kD_old"
                          unfolding kD_old_def using kD_not_idx by (auto split: if_splits)

                        have "k4_old < kD_old" using k4_old_props(2) .
                        
                        (* , *)
                        thus ?thesis unfolding k4_def kD_is_fwd
                          using k4_old_not_bt kD_old_not_bt by (auto split: if_splits)
                      qed

                      show "op_name (new_L ! k4) = deq" using L_new_k4 k4_old_props(3) by simp
                      show "op_val (new_L ! k4) = op_val (new_L ! k3)" using L_new_k4 L_new_k3 k4_old_props(4) by simp
                    qed
                  qed
                qed
              qed
            qed


        have p_lI5_SA_Prefix: "lI5_SA_Prefix_list new_L" 
            proof -
              let ?m_len = "length l22"
              let ?map_back = "\<lambda>k. if k < ?idx then k 
                                  else if k = ?idx then ?idx + ?m_len + 1 
                                  else if k \<le> ?idx + ?m_len + 1 then k - 1 
                                  else k"

              (* Step 1: 1.  *)
              have mset_eq: "mset new_L = mset L_curr"
              proof -
                have "mset L_curr = mset ?pre + mset [b_act] + mset l22 + mset [bt_act] + mset l3"
                  by (metis L_curr_eq add.assoc l2_eq l2_eq_expanded
                      mset_append)
                also have "... = mset ?pre + mset [bt_act] + mset [b_act] + mset l22 + mset l3"
                  by (simp add: add.commute add.left_commute)
                also have "... = mset new_L"
                  by (simp add: new_L_def)
                finally show ?thesis by simp
              qed

              (* Step 2: 2. SA *)
              have sa_eq: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L_curr"
              proof -
                have L_split: "L_curr = l1 @ (l21 @ [b_act] @ l22 @ [bt_act] @ l3)" 
                  using L_curr_eq l1_def
                  using l2_eq l2_eq_expanded by fastforce 
                have N_split: "new_L = l1 @ (l21 @ [bt_act] @ [b_act] @ l22 @ l3)" 
                  using new_L_eq l1_def by auto
                have l1_take: "l1 = take (nat (last_sa_pos + 1)) L_curr" 
                  unfolding l1_def using bt_idx_valid remaining_def last_sa_pos_def 
                  by (metis drop_eq_Nil leI min_absorb2)
                show ?thesis
                  using in_SA_mset_eq mset_eq by blast
              qed

              (* Step 3: 3. SA last_sa_pos *)
              have boundary_eq: "find_last_SA new_L = find_last_SA L_curr"
              proof -
                let ?n = "nat (last_sa_pos + 1)"
                have len_eq: "length new_L = length L_curr" using mset_eq size_mset by metis
                
                have take_eq: "take ?n new_L = take ?n L_curr"
                proof -
                   have "?n \<le> ?idx"
                     using l1_def l2_def l2_not_nil remaining_def by auto
                   thus ?thesis using L_curr_eq new_L_eq by simp
                qed
                
                (* L_curr SA *)
                have no_sa_L: "\<forall>i \<in> {?n..<length L_curr}. \<not> (op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr)"
                  using enqs_after_last_sa_are_not_in_sa last_sa_pos_def by force
                  
                (* new_L SA ( ) *)
                have no_sa_N: "\<forall>k \<in> {?n..<length new_L}. \<not> (op_name (new_L ! k) = enq \<and> in_SA (op_val (new_L ! k)) new_L)"
                proof (intro ballI notI)
                  fix k assume "k \<in> {?n..<length new_L}"
                  assume asm: "op_name (new_L ! k) = enq \<and> in_SA (op_val (new_L ! k)) new_L"
                  
                  define k_old where "k_old = ?map_back k"
                  
                  (* , o1 *)
                  have L_exp: "L_curr = (l1 @ l21) @ [b_act] @ l22 @ [bt_act] @ l3" 
                    using L_curr_eq l22_eq by simp
                  have N_exp: "new_L = (l1 @ l21) @ [bt_act] @ [b_act] @ l22 @ l3" 
                    using new_L_eq by  simp
                  
                  (* , OF *)
                  have "new_L ! k = L_curr ! k_old" 
                    using jump_back_nth[OF L_exp N_exp refl refl, of k]
                    unfolding k_old_def by (auto split: if_splits)
                    
                  hence enq_old: "op_name (L_curr ! k_old) = enq" 
                    and sa_old: "in_SA (op_val (L_curr ! k_old)) L_curr"
                    using asm sa_eq by auto
                    
                  (* k , k_old *)
                  have "k_old \<ge> ?n"
                  proof -
                    (* Isabelle l1 ?n *)
                    have "length l1 = ?n"
                      unfolding l1_def using bt_idx_valid unfolding remaining_def last_sa_pos_def
                      by simp 
                    hence "?idx \<ge> ?n" by simp
                    
                    (* ?idx \<ge> ?n k > ?idx , k - 1 \<ge> ?n *)
                    thus ?thesis 
                      unfolding k_old_def using `k \<in> {?n..<length new_L}` 
                      by (auto split: if_splits)
                  qed
                  
                  moreover have "k_old < length L_curr" 
                  proof -
                    (* L_exp, L_curr *)
                    have "length L_curr = ?idx + 1 + ?m_len + 1 + length l3"
                      using L_exp by simp
                    
                    (* Isabelle length L_curr ?idx + ?m_len + 2, k_old *)
                    thus ?thesis 
                      unfolding k_old_def using `k \<in> {?n..<length new_L}` len_eq 
                      by (auto split: if_splits)
                  qed
                  
                  (* Proof note. *)
                  ultimately show False using no_sa_L enq_old sa_old by auto
                qed
                                    
                show ?thesis using find_last_SA_stable_prefix[OF len_eq take_eq no_sa_N no_sa_L sa_eq] by simp
              qed

              (* Step 4: 4. lI5_SA_Prefix  *)
              show ?thesis unfolding lI5_SA_Prefix_list_def Let_def
              proof (intro allI impI)
                fix k assume k_len: "k < length new_L"
                assume k_enq: "op_name (new_L ! k) = enq"
                
                show "in_SA (op_val (new_L ! k)) new_L = (int k \<le> find_last_SA new_L)"
                proof cases
                  assume "k < ?idx"
                  (* 1: . , *)
                  have L_exp_final: "L_curr = (l1 @ l21) @ [b_act] @ l22 @ [bt_act] @ l3" 
                    using L_curr_eq l22_eq by  simp
                  have N_exp_final: "new_L = (l1 @ l21) @ [bt_act] @ [b_act] @ l22 @ l3" 
                    using new_L_eq by simp
                  
                  have "new_L ! k = L_curr ! k" 
                    using jump_back_nth[OF L_exp_final N_exp_final refl refl, of k]
                    using `k < ?idx` by simp
                    
                  moreover have "in_SA (op_val (L_curr ! k)) L_curr = (int k \<le> find_last_SA L_curr)"
                  proof -
                    have "k < length L_curr" using k_len len_eq by simp
                    moreover have "op_name (L_curr ! k) = enq" using k_enq `new_L ! k = L_curr ! k` by simp
                    ultimately show ?thesis using lin_I5_curr[unfolded lI5_SA_Prefix_list_def Let_def, THEN spec, of k] by auto
                  qed
                  
                  ultimately show ?thesis using sa_eq boundary_eq by auto
                next
                  assume "\<not> k < ?idx"
                  hence "k \<ge> ?idx" by simp
                  
                  (* 2: . SA , False *)
                  
                  (* Proof note. *)
                  have len_l1: "length l1 = nat (last_sa_pos + 1)"
                    unfolding l1_def using bt_idx_valid unfolding remaining_def last_sa_pos_def by simp
                  hence idx_bound: "?idx \<ge> nat (last_sa_pos + 1)" by simp
                  
                  (* False: no_sa_N SA *)
                  have left_false: "\<not> in_SA (op_val (new_L ! k)) new_L"
                  proof -
                    let ?n = "nat (last_sa_pos + 1)"
                    have "k \<ge> ?n" using `k \<ge> ?idx` idx_bound by simp
                    hence "k \<in> {?n ..< length new_L}" using k_len by auto
                    
                    (* auto \<forall>k \<in> {...} *)
                    have "\<not> (op_name (new_L ! k) = enq \<and> in_SA (op_val (new_L ! k)) new_L)"
                      using \<open>nat (last_sa_pos + 1) \<le> k\<close> boundary_eq
                        enqs_after_last_sa_are_not_in_sa k_len last_sa_pos_def
                      by force 

                      
                    (* k_enq, in_SA False *)
                    thus ?thesis using k_enq by simp
                  qed
                  
                  (* False: k SA *)
                  have right_false: "\<not> (int k \<le> find_last_SA new_L)"
                  proof -
                    let ?n = "nat (last_sa_pos + 1)"
                    have "find_last_SA new_L = last_sa_pos" using boundary_eq last_sa_pos_def by simp
                    moreover have "int k \<ge> int ?n" using `k \<ge> ?idx` idx_bound by linarith
                    ultimately show ?thesis
                      by linarith 
                  qed
                  
                  (* False = False, *)
                  show ?thesis using left_false right_false by simp
                qed
              qed
            qed


        have p_pending: "\<forall>k<length new_L. op_val (new_L ! k) = bt_val \<longrightarrow> op_name (new_L ! k) \<noteq> deq"
          by (metis in_set_conv_nth mod_eq modify_preserves_mset pending_L set_mset_mset)
        have p_exists: "\<exists>k<length new_L. op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = bt_val"
          by (metis exists_L in_set_conv_nth mod_eq modify_preserves_mset set_mset_mset)

        (* === SMT (Case c2) === *)
        (* Step 1: 1. , 1.IH(3) AST 100% *)
        (* l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3 *)
        define L_inner where "L_inner = take (nat (find_last_SA L_curr + 1)) L_curr @ l21 @ [drop (nat (find_last_SA L_curr + 1)) L_curr ! bt_idx] @ [b_act] @ l22 @ drop (bt_idx + 1) (drop (nat (find_last_SA L_curr + 1)) L_curr)"
        
        have new_L_eq_L_inner: "new_L = L_inner"
          unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def L_inner_def by simp
          
        (* Step 2: 2. L_inner , new_L *)
        have p1_in: "data_independent L_inner" using indep_new unfolding new_L_eq_L_inner .
        have p2_in: "lI4_FIFO_Semantics_list L_inner" using p_lI4_FIFO_Semantics unfolding new_L_eq_L_inner .
        have p3_in: "lI5_SA_Prefix_list L_inner" using p_lI5_SA_Prefix unfolding new_L_eq_L_inner .
        have p4_in: "\<forall>k<length L_inner. op_val (L_inner ! k) = bt_val \<longrightarrow> op_name (L_inner ! k) \<noteq> deq" using p_pending unfolding new_L_eq_L_inner .
        have p5_in: "\<exists>k<length L_inner. op_name (L_inner ! k) = enq \<and> op_val (L_inner ! k) = bt_val" using p_exists unfolding new_L_eq_L_inner .

        (* Step 3: 3. IH 5+2 , *)
        have pre1: "should_modify L_curr H bt_val" using do_modify .
        have pre2: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L_curr + 1)) L_curr) = Some bt_idx"
          using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] .
        have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L_curr + 1)) L_curr))) \<noteq> enq"
          using False unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] .
        have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L_curr + 1)) L_curr)) = Some (l21, b_act, l22)"
          using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] .
        
        (* c2 HB : \<not> HB(o1, bt_act) HB(b_act, o1) *)
        have pre5_1: "\<not> happens_before (hd l22) (drop (nat (find_last_SA L_curr + 1)) L_curr ! bt_idx) H"
          using c2 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] o1_def[symmetric] by simp
        have pre5_2: "happens_before b_act (hd l22) H"
          using c2 unfolding o1_def[symmetric] by simp

        (* Step 4: 4. simp , metis *)
        show ?thesis 
          unfolding mod_eq new_L_eq_L_inner
          unfolding L_inner_def
          using "1.IH"(3) pre1 pre2 pre3 pre4 pre5_1 pre5_2 p1_in p2_in p3_in p4_in p5_in
          unfolding L_inner_def
          by simp

      next
        case c3 (* === c3 ( c1) === *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"
        
            (* new_L L_curr , [o1, b_act] *)
            have new_L_eq: "new_L = ?pre @ [o1, b_act] @ tl l22 @ [bt_act] @ l3"
              unfolding new_L_def by simp
              
            have len_eq: "length new_L = length L_curr"
              using L_curr_eq new_L_eq by simp

            have mset_eq: "mset new_L = mset L_curr"
            proof -
              have "mset new_L = mset (?pre @ [o1, b_act] @ tl l22 @ [bt_act] @ l3)" using new_L_eq by simp
              also have "... = mset (?pre @ [b_act, o1] @ tl l22 @ [bt_act] @ l3)" by (simp add: union_ac)
              also have "... = mset L_curr" using L_curr_eq by simp
              finally show ?thesis .
            qed

        have mod_eq: "modify_lin L_curr H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c3 False do_modify o1_def  apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold) apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)


        have indep_new: "data_independent new_L"
          by (metis data_independent_cong independent_L_curr mod_eq modify_preserves_mset)

        have p_lI4_FIFO_Semantics: "lI4_FIFO_Semantics_list new_L" 
            proof -
              (* ?map *)
              show ?thesis unfolding lI4_FIFO_Semantics_list_def Let_def
              proof (intro allI impI)
                fix kD assume kD_len: "kD < length new_L" 
                assume kD_deq: "op_name (new_L ! kD) = deq"
                
                (* Proof note. *)
                let ?map = "\<lambda>k. if k = ?idx then ?idx + 1 else if k = ?idx + 1 then ?idx else k"
                
                have kD_not_idx1: "kD \<noteq> ?idx + 1"
                proof (rule ccontr)
                  assume "\<not> (kD \<noteq> ?idx + 1)"
                  hence "new_L ! kD = b_act" using new_L_eq by (simp add: nth_append)
                  with kD_deq b_act_enq show False by simp
                qed
                
                (* kD *)
                define kD_old where "kD_old = ?map kD"
                
                (* Auxiliary lemma L_new_kD *)
                have L_new_kD: "new_L ! kD = L_curr ! kD_old"
                  using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                  using L_curr_eq new_L_eq kD_old_def by simp
                  
                have kD_old_len: "kD_old < length L_curr"
                  using kD_len len_eq kD_old_def kD_not_idx1 L_curr_eq by auto

                have kD_old_deq: "op_name (L_curr ! kD_old) = deq" using L_new_kD kD_deq by simp
                
                obtain k2_old where k2_old_props: 
                  "k2_old < kD_old" "op_name (L_curr ! k2_old) = enq" "op_val (L_curr ! k2_old) = op_val (L_curr ! kD_old)"
                  "\<forall>k3<k2_old. op_name (L_curr ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD_old \<and> op_name (L_curr ! k4) = deq \<and> op_val (L_curr ! k4) = op_val (L_curr ! k3))"
                  using lin_L_curr[unfolded lI4_FIFO_Semantics_list_def Let_def, THEN spec, of kD_old] using kD_old_len kD_old_deq by blast

                have k2_old_not_idx1: "k2_old \<noteq> ?idx + 1"
                proof (rule ccontr)
                  assume "\<not> (k2_old \<noteq> ?idx + 1)"
                  hence "L_curr ! k2_old = o1" using L_curr_eq by (simp add: nth_append)
                  with k2_old_props(2) o1_deq show False by simp
                qed

                (* k2 *)
                define k2 where "k2 = ?map k2_old"
                
                (* Proof note. *)
                have L_new_k2: "new_L ! k2 = L_curr ! k2_old"
                  using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                  using L_curr_eq new_L_eq k2_def by simp

                show "\<exists>k2<kD. op_name (new_L ! k2) = enq \<and> op_val (new_L ! k2) = op_val (new_L ! kD) \<and>
                        (\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)))"
                proof (rule exI[where x=k2], intro conjI)
                  
                  show "k2 < kD"
                  proof -
                    have kD_old_not_idx: "kD_old \<noteq> ?idx"
                      using kD_old_def kD_not_idx1 by (auto split: if_splits)
                      
                    (* val_neq , *)
                    have "k2_old \<noteq> ?idx \<or> kD_old \<noteq> ?idx + 1"
                    proof (rule ccontr)
                      assume "\<not> (k2_old \<noteq> ?idx \<or> kD_old \<noteq> ?idx + 1)"
                      hence "k2_old = ?idx" and "kD_old = ?idx + 1" by auto
                      hence "L_curr ! k2_old = b_act" and "L_curr ! kD_old = o1" using L_curr_eq by (auto simp add: nth_append)
                      hence "op_val b_act = op_val o1" using k2_old_props(3) by simp
                      thus False using val_neq by simp
                    qed
                    
                    (* , auto *)
                    thus ?thesis using k2_old_props(1) k2_def kD_old_def kD_not_idx1 k2_old_not_idx1 kD_old_not_idx
                      by (metis Suc_eq_plus1 linorder_cases not_less_eq) 
                  qed
                  
                  show "op_name (new_L ! k2) = enq" using k2_old_props(2) L_new_k2 by simp
                  show "op_val (new_L ! k2) = op_val (new_L ! kD)" using k2_old_props(3) L_new_k2 L_new_kD by simp
                  
                  show "\<forall>k3<k2. op_name (new_L ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3))"
                  proof (intro allI impI)
                    fix k3 assume "k3 < k2" and k3_enq: "op_name (new_L ! k3) = enq"
                    
                    have k3_not_idx: "k3 \<noteq> ?idx"
                    proof (rule ccontr)
                      assume "\<not> (k3 \<noteq> ?idx)"
                      hence "new_L ! k3 = o1" using new_L_eq by (simp add: nth_append)
                      with k3_enq o1_deq show False by simp
                    qed
                    
                    (* k3 *)
                    define k3_old where "k3_old = ?map k3"
                    
                    have L_new_k3: "new_L ! k3 = L_curr ! k3_old"
                      using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                      using L_curr_eq new_L_eq k3_old_def by simp
                      
                    have "k3_old < k2_old"
                    proof -
                      have "k3_old \<noteq> ?idx \<or> k2_old \<noteq> ?idx + 1" using k2_old_not_idx1 by simp
                      thus ?thesis using `k3 < k2` k3_old_def k2_def k3_not_idx k2_old_not_idx1
                        by (metis le_antisym less_iff_succ_less_eq nat_less_le
                            nat_neq_iff) 
                    qed
                    
                    obtain k4_old where k4_old_props: "k3_old < k4_old" "k4_old < kD_old" "op_name (L_curr ! k4_old) = deq" 
                                              "op_val (L_curr ! k4_old) = op_val (L_curr ! k3_old)"
                      using L_new_k3 \<open>k3_old < k2_old\<close> k2_old_props(4) k3_enq by auto
                      
                    have k4_old_not_idx: "k4_old \<noteq> ?idx"
                    proof (rule ccontr)
                      assume "\<not> (k4_old \<noteq> ?idx)"
                      hence "L_curr ! k4_old = b_act" using L_curr_eq by (simp add: nth_append)
                      with k4_old_props(3) b_act_enq show False by simp
                    qed
                    
                    (* k4 *)
                    define k4 where "k4 = ?map k4_old"
                    
                    have L_new_k4: "new_L ! k4 = L_curr ! k4_old"
                      using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                      using L_curr_eq new_L_eq k4_def by simp
                      
                    show "\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (new_L ! k4) = deq \<and> op_val (new_L ! k4) = op_val (new_L ! k3)"
                    proof (rule exI[where x=k4], intro conjI)
                      show "k3 < k4"
                      proof -
                        (* k3_old k4_old *)
                        have no_reverse: "k3_old \<noteq> ?idx \<or> k4_old \<noteq> ?idx + 1"
                        proof (rule ccontr)
                          assume "\<not> (k3_old \<noteq> ?idx \<or> k4_old \<noteq> ?idx + 1)"
                          hence "k3_old = ?idx" and "k4_old = ?idx + 1" by auto
                          
                          (* Proof note. *)
                          hence "L_curr ! k3_old = b_act" and "L_curr ! k4_old = o1" 
                            using L_curr_eq by (auto simp add: nth_append)
                            
                          (* k4_old_props, *)
                          hence "op_val o1 = op_val b_act" 
                            using k4_old_props(4) by simp
                            
                          (* val_neq, *)
                          thus False using val_neq by auto
                        qed
                        
                        (* , , auto *)
                        thus ?thesis using k4_old_props(1) k3_old_def k4_def k3_not_idx k4_old_not_idx
                          by (metis Suc_eq_plus1 Suc_leI le_neq_implies_less less_SucE)
                      qed
                      show "k4 < kD"
                      proof -
                        have kD_old_not_idx: "kD_old \<noteq> ?idx" using kD_old_def kD_not_idx1 by (auto split: if_splits)
                        have "k4_old \<noteq> ?idx \<or> kD_old \<noteq> ?idx + 1" using k4_old_not_idx by simp
                        thus ?thesis using k4_old_props(2) k4_def kD_old_def k4_old_not_idx kD_old_not_idx kD_not_idx1
                          by (metis add.commute add_lessD1 less_SucE plus_1_eq_Suc) 
                      qed
                      show "op_name (new_L ! k4) = deq" using k4_old_props(3) L_new_k4 by simp
                      show "op_val (new_L ! k4) = op_val (new_L ! k3)" using k4_old_props(4) L_new_k4 L_new_k3 by simp
                    qed
                  qed
                qed
              qed
            qed

        have p_lI5_SA_Prefix: "lI5_SA_Prefix_list new_L" 
            proof -
              let ?n = "nat (last_sa_pos + 1)"
              let ?map = "\<lambda>k. if k = ?idx then ?idx + 1 else if k = ?idx + 1 then ?idx else k"
              
              (* Proof note. *)
              have sa_bound: "?n \<le> ?idx"
              proof -
                have bound: "?n \<le> length L_curr" using bt_idx_valid unfolding remaining_def by auto
                have "?idx = length l1 + length l21" by simp
                also have "... = ?n + length l21" unfolding l1_def using bound by simp
                finally show ?thesis by linarith
              qed

              (* Step 1: 1. *)
              have prefix_eq: "take ?n new_L = take ?n L_curr"
              proof -
                have "take ?n L_curr = l1" unfolding l1_def by simp
                moreover have "take ?n new_L = l1"
                proof -
                  have "new_L = l1 @ (l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3)" using new_L_eq by simp
                  hence "take (length l1) new_L = take (length l1) (l1 @ (l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3))" by simp
                  also have "... = l1" by simp
                  finally show ?thesis unfolding l1_def 
                    by (metis add_left_imp_eq append_eq_append_conv append_take_drop_id len_eq length_append length_drop)
                qed
                ultimately show ?thesis by simp
              qed

              (* Step 2: 2. in_SA *)
              have in_SA_eq: "\<And>a. in_SA a new_L = in_SA a L_curr"
              proof -
                fix a
                have eq1: "L_curr = l1 @ remaining" unfolding l1_def remaining_def by simp
                have eq2: "new_L = l1 @ (l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3)" unfolding new_L_def l1_def by simp
                have rem_not_nil: "remaining \<noteq> []" 
                proof (cases remaining)
                  case Nil with bt_idx_valid show ?thesis by simp
                next
                  case Cons thus ?thesis by simp
                qed
                have "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L_curr"
                  using L_and_new_L_have_same_SA[of L_curr l1 remaining new_L "l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3" last_sa_pos]
                  using independent_L_curr eq1 eq2 rem_not_nil mset_eq l1_def last_sa_pos_def
                  by metis 
                thus "in_SA a new_L = in_SA a L_curr" by simp
              qed

              (* Step 3: 3. find_last_SA *)
              have sa_eq: "find_last_SA new_L = find_last_SA L_curr"
              proof -
                have suffix_L_curr: "\<forall>i \<in> {?n..<length L_curr}. \<not> (op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr)"
                proof (intro ballI notI)
                  fix i assume "i \<in> {?n..<length L_curr}"
                  then have "i < length L_curr" and "int i > find_last_SA L_curr" unfolding last_sa_pos_def by auto
                  assume "op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr"
                  then have "op_name (L_curr ! i) = enq" and in_sa: "in_SA (op_val (L_curr ! i)) L_curr" by auto
                  from enqs_after_last_sa_are_not_in_sa[OF `i < length L_curr` `int i > find_last_SA L_curr` `op_name (L_curr ! i) = enq`]
                  show False using in_sa by simp
                qed

                have suffix_new_L: "\<forall>i \<in> {?n..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
                proof (intro ballI notI)
                  fix i assume "i \<in> {?n..<length new_L}"
                  assume bad: "op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L"
                  then have is_enq: "op_name (new_L ! i) = enq" and in_sa: "in_SA (op_val (new_L ! i)) new_L" by auto
                  have in_sa_curr: "in_SA (op_val (new_L ! i)) L_curr" using in_sa in_SA_eq by simp
                  
                  (* ?map L_curr *)
                  define k_old where "k_old = ?map i"
                  have "new_L ! i = L_curr ! k_old"
                    using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                    using L_curr_eq new_L_eq k_old_def by simp
                  moreover have "k_old \<ge> ?n" using `i \<in> {?n..<length new_L}` sa_bound k_old_def by auto
                  (* 【 】: L_curr_eq , Isabelle +1 *)
                  moreover have "k_old < length L_curr"
                  proof -
                    have "?idx + 1 < length L_curr" using L_curr_eq by simp
                    thus ?thesis using `i \<in> {?n..<length new_L}` len_eq k_old_def by auto
                  qed
                  ultimately have "k_old \<in> {?n..<length L_curr}" by simp
                  
                  with suffix_L_curr have "\<not> (op_name (L_curr ! k_old) = enq \<and> in_SA (op_val (L_curr ! k_old)) L_curr)" by blast
                  moreover have "op_name (L_curr ! k_old) = enq" using is_enq `new_L ! i = L_curr ! k_old` by simp
                  ultimately have "\<not> in_SA (op_val (L_curr ! k_old)) L_curr" by simp
                  with in_sa_curr `new_L ! i = L_curr ! k_old` show False by simp
                qed
                
                show ?thesis
                proof (rule find_last_SA_stable_prefix[of new_L L_curr "?n"])
                  show "length new_L = length L_curr" using len_eq .
                  show "take ?n new_L = take ?n L_curr" using prefix_eq .
                  show "\<forall>i\<in>{?n..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)" using suffix_new_L .
                  show "\<forall>i\<in>{?n..<length L_curr}. \<not> (op_name (L_curr ! i) = enq \<and> in_SA (op_val (L_curr ! i)) L_curr)" using suffix_L_curr .
                  show "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L_curr" using in_SA_eq by blast
                qed
              qed

              (* Step 4: 4. lI5_SA_Prefix_list_def  *)
              show ?thesis unfolding lI5_SA_Prefix_list_def
              proof (intro allI impI)
                fix k assume k_len: "k < length new_L" 
                assume k_enq: "op_name (new_L ! k) = enq"
                
                (* Proof note. *)
                define k_old where "k_old = ?map k"
                have L_new_k: "new_L ! k = L_curr ! k_old"
                  using swap_adjacent_nth[of L_curr ?pre b_act o1 "tl l22 @ [bt_act] @ l3" new_L ?idx]
                  using L_curr_eq new_L_eq k_old_def by simp
                
                (* 【 】: , k_old *)
                have k_old_len: "k_old < length L_curr" 
                proof -
                  have "?idx + 1 < length L_curr" using L_curr_eq by simp
                  thus ?thesis using k_len len_eq k_old_def by auto
                qed
                
                have lhs_eq: "in_SA (op_val (new_L ! k)) new_L = in_SA (op_val (new_L ! k)) L_curr" using in_SA_eq by simp
                
                (* 【 】: nat (last_sa_pos + 1) *)
                consider (in_prefix) "k < nat (last_sa_pos + 1)" | (in_suffix) "k \<ge> nat (last_sa_pos + 1)" by linarith
                then show "in_SA (op_val (new_L ! k)) new_L \<longleftrightarrow> int k \<le> find_last_SA new_L"
                proof cases
                  case in_prefix
                  (* A: prefix , k ?idx, ?map k_old = k *)
                  have "k < ?idx" using in_prefix sa_bound by linarith
                  hence "k_old = k" using k_old_def by simp
                  hence "new_L ! k = L_curr ! k" using L_new_k by simp
                  
                  hence "op_name (L_curr ! k) = enq" using k_enq by simp
                  moreover have "k < length L_curr" using k_len len_eq by simp
                  (* int *)
                  moreover have rhs_true: "int k \<le> last_sa_pos" using in_prefix by linarith
                  ultimately have "in_SA (op_val (L_curr ! k)) L_curr"
                    using lin_I5_curr[unfolded lI5_SA_Prefix_list_def, THEN spec, of k] unfolding last_sa_pos_def by blast
                  thus ?thesis using `new_L ! k = L_curr ! k` lhs_eq sa_eq last_sa_pos_def rhs_true by simp
                  
                next
                  case in_suffix
                  (* B: suffix . swap, k_old >= *)
                  (* Step 1: 1. k_old >= nat (last_sa_pos + 1) *)
                  have k_old_ge_bound: "k_old \<ge> nat (last_sa_pos + 1)"
                  proof -
                    (* k >= , , *)
                    have "k \<ge> nat (last_sa_pos + 1)" using in_suffix by simp
                    moreover have "nat (last_sa_pos + 1) \<le> ?idx" using sa_bound by simp
                    ultimately show ?thesis unfolding k_old_def by auto
                  qed
                  
                  (* Step 2: 2. int , nat(-1)=0 *)
                  (* int k_old > last_sa_pos *)
                  have "int k_old > last_sa_pos"
                  proof -
                    (* 1: int (nat X) >= X *)
                    have "int (nat (last_sa_pos + 1)) \<ge> last_sa_pos + 1" by simp
                    (* 2 *)
                    moreover have "int k_old \<ge> int (nat (last_sa_pos + 1))" 
                      using k_old_ge_bound by linarith
                    (* linarith *)
                    ultimately show ?thesis by linarith
                  qed
                  
                  (* Step 3: 3. lI5_SA_Prefix *)
                  have "op_name (L_curr ! k_old) = enq" using k_enq L_new_k by simp
                  hence "\<not> in_SA (op_val (L_curr ! k_old)) L_curr"
                    using lin_I5_curr[unfolded lI5_SA_Prefix_list_def, THEN spec, of k_old] 
                    using `int k_old > last_sa_pos` k_old_len
                    by (simp add: last_sa_pos_def) 
                  hence "\<not> in_SA (op_val (new_L ! k)) new_L" using L_new_k lhs_eq by simp
                  
                  (* Step 4: 4. False ( int ) *)
                  moreover have "\<not> (int k \<le> find_last_SA new_L)" 
                  proof -
                    (* 1: int (nat X) >= X *)
                    have "int (nat (last_sa_pos + 1)) \<ge> last_sa_pos + 1" by simp
                    (* 2: in_suffix ( k >= nat (last_sa_pos + 1)) int *)
                    moreover have "int k \<ge> int (nat (last_sa_pos + 1))" 
                      using in_suffix by linarith
                    (* , linarith *)
                    ultimately have "int k > last_sa_pos" by linarith
                    (* Proof note. *)
                    thus ?thesis using sa_eq last_sa_pos_def by simp
                  qed
                  
                  ultimately show ?thesis by simp
                qed
              qed
            qed

        have p_pending: "\<forall>k<length new_L. op_val (new_L ! k) = bt_val \<longrightarrow> op_name (new_L ! k) \<noteq> deq"
          by (metis in_set_conv_nth mod_eq modify_preserves_mset pending_L set_mset_mset)
        have p_exists: "\<exists>k<length new_L. op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = bt_val"
          by (metis exists_L in_set_conv_nth mod_eq modify_preserves_mset set_mset_mset)

        (* === SMT === *)
        (* Step 1: 1. , 1.IH(4) AST 100% *)
        define L_inner where "L_inner = take (nat (find_last_SA L_curr + 1)) L_curr @ l21 @ [hd l22] @ [b_act] @ tl l22 @ [drop (nat (find_last_SA L_curr + 1)) L_curr ! bt_idx] @ drop (bt_idx + 1) (drop (nat (find_last_SA L_curr + 1)) L_curr)"
        
        have new_L_eq_L_inner: "new_L = L_inner"
          unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def o1_def L_inner_def by simp
          
        (* Step 2: 2. L_inner , new_L *)
        have p1_in: "data_independent L_inner" using indep_new unfolding new_L_eq_L_inner .
        have p2_in: "lI4_FIFO_Semantics_list L_inner" using p_lI4_FIFO_Semantics unfolding new_L_eq_L_inner .
        have p3_in: "lI5_SA_Prefix_list L_inner" using p_lI5_SA_Prefix unfolding new_L_eq_L_inner .
        have p4_in: "\<forall>k<length L_inner. op_val (L_inner ! k) = bt_val \<longrightarrow> op_name (L_inner ! k) \<noteq> deq" using p_pending unfolding new_L_eq_L_inner .
        have p5_in: "\<exists>k<length L_inner. op_name (L_inner ! k) = enq \<and> op_val (L_inner ! k) = bt_val" using p_exists unfolding new_L_eq_L_inner .

        (* Step 3: 3. IH 5 , *)
        have pre1: "should_modify L_curr H bt_val" using do_modify .
        have pre2: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L_curr + 1)) L_curr) = Some bt_idx"
          using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] .
        have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L_curr + 1)) L_curr))) \<noteq> enq"
          using False unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] .
        have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L_curr + 1)) L_curr)) = Some (l21, b_act, l22)"
          using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] .
        (* 【 】: c3 HB : if , if *)
        have pre5_1: "\<not> happens_before (hd l22) (drop (nat (find_last_SA L_curr + 1)) L_curr ! bt_idx) H"
          using c3 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] o1_def[symmetric] by simp
        have pre5_2: "\<not> happens_before b_act (hd l22) H"
          using c3 unfolding o1_def[symmetric] by simp

        (* Step 4: 4. simp , metis *)
        show ?thesis 
          unfolding mod_eq new_L_eq_L_inner
          unfolding L_inner_def
          using "1.IH"(4) pre1 pre2 pre3 pre4 pre5_1 pre5_2 p1_in p2_in p3_in p4_in p5_in
          unfolding L_inner_def
          by simp
      qed
    qed
  qed
qed


(* ==================================================================== *)
(* Auxiliary lemma: Distance = 0 , Deq lI4_FIFO_Semantics (Enq-Deq) *)
(* ==================================================================== *)
lemma lI4_FIFO_Semantics_append_deq_success:
  fixes L :: "OpRec list" and deq_act :: "OpRec" and v :: nat
  assumes I4: "lI4_FIFO_Semantics_list L"
  assumes DI: "data_independent L"
  assumes deq_op: "op_name deq_act = deq"
  assumes deq_val: "op_val deq_act = v"
  assumes enq_exists: "\<exists>k < length L. op_name (L ! k) = enq \<and> op_val (L ! k) = v"
  assumes not_sa: "\<not> in_SA v L"
  assumes dist_zero: "Distance L v = 0"
  shows "lI4_FIFO_Semantics_list (L @ [deq_act])"
proof -
  let ?L' = "L @ [deq_act]"

  (* Step 1: 1. k_v, Distance=0 Enq SA *)
  obtain k_v where kv_props: "k_v < length L" "op_name (L ! k_v) = enq" "op_val (L ! k_v) = v"
    using enq_exists by blast
    
  have all_before_in_sa: "\<forall>k < k_v. op_name (L ! k) = enq \<longrightarrow> in_SA (op_val (L ! k)) L"
  proof (intro allI impI)
    fix k assume "k < k_v" and k_enq: "op_name (L ! k) = enq"
    show "in_SA (op_val (L ! k)) L"
    proof (rule ccontr)
      assume not_in: "\<not> in_SA (op_val (L ! k)) L"
      define x where "x = op_val (L ! k)"
      
      have x_idx: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L = Some k"
        using unique_enq_index[OF DI] k_enq `k < k_v` kv_props(1) x_def 
        unfolding find_unique_index_def by force

      have v_idx: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some k_v"
        using unique_enq_index[OF DI] kv_props 
        unfolding find_unique_index_def by force

      have dist_x_v: "distance_func x v L > 0"
        unfolding distance_func_def using not_in[folded x_def] x_idx v_idx `k < k_v` by simp
      
      have "Distance L v > 0"
      proof -
        let ?all_enqs = "filter (\<lambda>a. op_name a = enq) L"
        let ?vals = "set (map op_val ?all_enqs)"
        have "x \<in> ?vals" 
          using `k < k_v` kv_props(1) k_enq unfolding x_def by auto
        hence in_sorted: "x \<in> set (sorted_list_of_set ?vals)" by simp
        thus ?thesis unfolding Distance_def Let_def using dist_x_v
          using sum_list_map_ge_element[OF in_sorted, of "\<lambda>v'. distance_func v' v L"]
          by force
      qed
      thus False using dist_zero by simp
    qed
  qed

  (* Step 2: 2. lI4_FIFO_Semantics_list *)
  show ?thesis unfolding lI4_FIFO_Semantics_list_def Let_def
  proof (intro allI impI)
    fix kD assume kD_len: "kD < length ?L'"
    assume kD_deq: "op_name (?L' ! kD) = deq"
    
    (* , *)
    consider (old) "kD < length L" | (new) "kD = length L"
      using kD_len
      by force 
    then show "\<exists>k2<kD. op_name (?L' ! k2) = enq \<and> op_val (?L' ! k2) = op_val (?L' ! kD) \<and>
              (\<forall>k3<k2. op_name (?L' ! k3) = enq \<longrightarrow> 
                (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (?L' ! k4) = deq \<and> op_val (?L' ! k4) = op_val (?L' ! k3)))"
    proof cases
      case old
      (* A: kD L , lI4_FIFO_Semantics *)
      have "L ! kD = ?L' ! kD" using old by (simp add: nth_append)
      hence "op_name (L ! kD) = deq" using kD_deq by simp
      
      obtain k2 where k2_props: "k2 < kD" "op_name (L ! k2) = enq" "op_val (L ! k2) = op_val (L ! kD)"
         "\<forall>k3<k2. op_name (L ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (L ! k4) = deq \<and> op_val (L ! k4) = op_val (L ! k3))"
        using I4[unfolded lI4_FIFO_Semantics_list_def Let_def, THEN spec, of kD] old `op_name (L ! kD) = deq` by blast
        
      show ?thesis
      proof (rule exI[where x=k2], intro conjI)
        show "k2 < kD" using k2_props(1) .
        show "op_name (?L' ! k2) = enq" using k2_props(2) `k2 < kD` old by (simp add: nth_append)
        show "op_val (?L' ! k2) = op_val (?L' ! kD)" using k2_props(3) `k2 < kD` old by (simp add: nth_append)
        
        show "\<forall>k3<k2. op_name (?L' ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (?L' ! k4) = deq \<and> op_val (?L' ! k4) = op_val (?L' ! k3))"
        proof (intro allI impI)
          fix k3 assume "k3 < k2" and "op_name (?L' ! k3) = enq"
          have "k3 < length L" using `k3 < k2` `k2 < kD` old by simp
          hence "op_name (L ! k3) = enq" using `op_name (?L' ! k3) = enq` by (simp add: nth_append)
          
          obtain k4 where k4_props: "k3 < k4" "k4 < kD" "op_name (L ! k4) = deq" "op_val (L ! k4) = op_val (L ! k3)"
            using k2_props(4)[rule_format, OF `k3 < k2` `op_name (L ! k3) = enq`] by blast
            
          have "k4 < length L" using `k4 < kD` old by simp
          
          show "\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (?L' ! k4) = deq \<and> op_val (?L' ! k4) = op_val (?L' ! k3)"
          proof (rule exI[where x=k4], intro conjI)
            show "k3 < k4" "k4 < kD" using k4_props by auto
            show "op_name (?L' ! k4) = deq" using k4_props(3) `k4 < length L` by (simp add: nth_append)
            show "op_val (?L' ! k4) = op_val (?L' ! k3)" using k4_props(4) `k3 < length L` `k4 < length L` by (simp add: nth_append)
          qed
        qed
      qed
      
    next
      case new
      (* B: kD Deq_act *)
      have kD_eq: "kD = length L" using new by simp
      hence val_kD: "op_val (?L' ! kD) = v" using deq_val by (simp add: nth_append)
      
      (* Enq k_v *)
      show ?thesis
      proof (rule exI[where x=k_v], intro conjI)
        show "k_v < kD" using kv_props(1) kD_eq by simp
        show "op_name (?L' ! k_v) = enq" using kv_props(2) kv_props(1) by (simp add: nth_append)
        show "op_val (?L' ! k_v) = op_val (?L' ! kD)" using kv_props(3) val_kD kv_props(1) by (simp add: nth_append)
        
        (* k_v Enq, Deq, Deq kD *)
        show "\<forall>k3<k_v. op_name (?L' ! k3) = enq \<longrightarrow> (\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (?L' ! k4) = deq \<and> op_val (?L' ! k4) = op_val (?L' ! k3))"
        proof (intro allI impI)
          fix k3 assume "k3 < k_v" and k3_enq_L': "op_name (?L' ! k3) = enq"
          have k3_len: "k3 < length L" using `k3 < k_v` kv_props(1) by simp
          have k3_enq: "op_name (L ! k3) = enq" using k3_enq_L' k3_len by (simp add: nth_append)
          
          (* Distance=0 : SA *)
          have "in_SA (op_val (L ! k3)) L" using all_before_in_sa `k3 < k_v` k3_enq by simp
          
          define x where "x = op_val (L ! k3)"
          have "in_SA x L" using `in_SA (op_val (L ! k3)) L` x_def by simp
          
          (* SA , L deq *)
          obtain k4 where k4_idx: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) L = Some k4"
            using `in_SA x L` unfolding in_SA_def by (auto split: option.splits)
            
          have k4_props: "k4 < length L" "op_name (L ! k4) = deq" "op_val (L ! k4) = x"
            using find_unique_index_prop[OF k4_idx] by auto
            
          (* lI4_FIFO_Semantics k3 < k4 *)
          have "k3 < k4"
          proof -
            (* k4 lI4_FIFO_Semantics *)
            obtain k2_x where k2_x_props: "k2_x < k4" "op_name (L ! k2_x) = enq" "op_val (L ! k2_x) = op_val (L ! k4)"
              using I4[unfolded lI4_FIFO_Semantics_list_def Let_def, THEN spec, of k4] k4_props(1,2) by blast
              
            (* data_independent Enq , k2_x k3 *)
            have "op_val (L ! k2_x) = x" using k2_x_props(3) k4_props(3) by simp
            
            (* Step 1: 1. , unique_enq_index *)
            have "k2_x < length L" using k2_x_props(1) `k4 < length L` by simp
            
            (* Step 2: 2. find_indices *)
            have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x) L = [k2_x]"
              using unique_enq_index[OF DI] k2_x_props(2) `op_val (L ! k2_x) = x` `k2_x < length L` 
              by blast
              
            (* Step 3: 3. find_unique_index , *)
            hence "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L = Some k2_x"
              unfolding find_unique_index_def by simp
              
            moreover have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L = Some k3"
              using unique_enq_index[OF DI] k3_len k3_enq x_def
              using DI \<open>op_val (L ! k2_x) = x\<close> \<open>k2_x < length L\<close> calculation
                k2_x_props(2) unique_enq_value by blast
              
            ultimately have "k2_x = k3" by simp
            thus ?thesis using k2_x_props(1) by simp
          qed
          
          show "\<exists>k4. k3 < k4 \<and> k4 < kD \<and> op_name (?L' ! k4) = deq \<and> op_val (?L' ! k4) = op_val (?L' ! k3)"
          proof (rule exI[where x=k4], intro conjI)
            show "k3 < k4" using `k3 < k4` .
            show "k4 < kD" using k4_props(1) kD_eq by simp
            show "op_name (?L' ! k4) = deq" using k4_props(2,1) by (simp add: nth_append)
            show "op_val (?L' ! k4) = op_val (?L' ! k3)" using k4_props(3,1) x_def k3_len by (simp add: nth_append)
          qed
        qed
      qed
    qed
  qed
qed


(* ----------------------------------------------------------------- *)
(* Deq lI5_SA_Prefix *)
(* ----------------------------------------------------------------- *)
lemma lI5_SA_Prefix_append_deq_success:
  fixes L :: "OpRec list" and deq_act :: "OpRec" and v :: nat
  assumes I5: "lI5_SA_Prefix_list L"
  assumes DI: "data_independent L"
  assumes deq_op: "op_name deq_act = deq"
  assumes deq_val: "op_val deq_act = v"
  assumes enq_exists: "\<exists>k < length L. op_name (L ! k) = enq \<and> op_val (L ! k) = v"
  assumes not_sa: "\<not> in_SA v L"
  assumes dist_zero: "Distance L v = 0"
  shows "lI5_SA_Prefix_list (L @ [deq_act])"
proof -
  let ?L' = "L @ [deq_act]"

  (* Step 1: 1. v Enq k_v *)
  obtain k_v where kv_props: "k_v < length L" "op_name (L ! k_v) = enq" "op_val (L ! k_v) = v"
    using enq_exists by blast

  (* Step 2: 2. SA : Deq v SA *)
  have sa_evolve: "\<And>x. in_SA x ?L' \<longleftrightarrow> in_SA x L \<or> x = v"
  proof -
    fix x
    let ?P_enq = "\<lambda>a. op_name a = enq \<and> op_val a = x"
    let ?P_deq = "\<lambda>a. op_name a = deq \<and> op_val a = x"
    
    (* Proof note. *)
    have list_upt: "[0..<length ?L'] = [0..<length L] @ [length L]" by simp
    
    (* ========================================== *)
    (* Enq *)
    (* ========================================== *)
    have enq_idx_eq: "find_indices ?P_enq ?L' = find_indices ?P_enq L"
    proof -
      (* Step 1: 1. : filter_cong , nth_append if-else *)
      have part1: "filter (\<lambda>i. ?P_enq (?L' ! i)) [0..<length L] = filter (\<lambda>i. ?P_enq (L ! i)) [0..<length L]"
        by (intro filter_cong refl) (auto simp: nth_append)
      (* Step 2: 2. : deq, enq *)
      have part2: "filter (\<lambda>i. ?P_enq (?L' ! i)) [length L] = []"
        using deq_op by (auto simp: nth_append)
        
      show ?thesis unfolding find_indices_def list_upt using part1 part2 by simp
    qed
    
    have enq_uniq_eq: "find_unique_index ?P_enq ?L' = find_unique_index ?P_enq L"
      unfolding find_unique_index_def enq_idx_eq by simp
      
    (* ========================================== *)
    (* SA *)
    (* ========================================== *)
    show "in_SA x ?L' \<longleftrightarrow> in_SA x L \<or> x = v"
    proof (cases "x = v")
      case True
      (* x = v , ( v) True *)
      
      (* A. Enq(v) L *)
      have enq_v_exists: "find_unique_index ?P_enq L \<noteq> None"
      proof -
        have "find_indices ?P_enq L = [k_v]"
          using unique_enq_index[OF DI] kv_props True by auto
        thus ?thesis unfolding find_unique_index_def by simp
      qed
      
      (* B. Deq(v) L *)
      have deq_v_empty: "find_indices ?P_deq L = []"
      proof (rule ccontr)
        assume "find_indices ?P_deq L \<noteq> []"
        then obtain k_d where "k_d < length L" "op_name (L ! k_d) = deq" "op_val (L ! k_d) = v"
          unfolding find_indices_def
          by (smt (verit, ccfv_SIG) True
              \<open>find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x) L \<noteq> []\<close>
              find_unique_index_def find_unique_index_prop) 
        hence "find_indices ?P_deq L = [k_d]"
          using unique_deq_index[OF DI] True by auto
        hence "find_unique_index ?P_deq L = Some k_d" unfolding find_unique_index_def by simp
        with enq_v_exists have "in_SA v L" unfolding in_SA_def Let_def True by auto
        thus False using not_sa by simp
      qed
      
      (* C. Deq(v) *)
      have deq_v_L': "find_indices ?P_deq ?L' = [length L]"
      proof -
        (* filter_cong *)
        have part1: "filter (\<lambda>i. ?P_deq (?L' ! i)) [0..<length L] = filter (\<lambda>i. ?P_deq (L ! i)) [0..<length L]"
          by (intro filter_cong refl) (auto simp: nth_append)
        (* Proof note. *)
        have part2: "filter (\<lambda>i. ?P_deq (?L' ! i)) [length L] = [length L]"
          using deq_op deq_val True by (auto simp: nth_append)
          
        show ?thesis 
          unfolding find_indices_def list_upt 
          using part1 part2 deq_v_empty[unfolded find_indices_def] by simp
      qed
      hence deq_v_uniq: "find_unique_index ?P_deq ?L' = Some (length L)"
        unfolding find_unique_index_def by simp
        
      (* D. *)
      show ?thesis unfolding in_SA_def Let_def using enq_uniq_eq enq_v_exists deq_v_uniq True by auto
    next
      case False
      (* x \<noteq> v , , L *)
      have deq_idx_eq: "find_indices ?P_deq ?L' = find_indices ?P_deq L"
      proof -
        (* filter_cong *)
        have part1: "filter (\<lambda>i. ?P_deq (?L' ! i)) [0..<length L] = filter (\<lambda>i. ?P_deq (L ! i)) [0..<length L]"
          by (intro filter_cong refl) (auto simp: nth_append)
        (* , *)
        have part2: "filter (\<lambda>i. ?P_deq (?L' ! i)) [length L] = []"
          using False
          by (simp add: deq_val)
          
        show ?thesis unfolding find_indices_def list_upt using part1 part2 by simp
      qed
      
      have deq_uniq_eq: "find_unique_index ?P_deq ?L' = find_unique_index ?P_deq L"
        unfolding find_unique_index_def deq_idx_eq by simp
        
      (* Enq Deq *)
      show ?thesis unfolding in_SA_def Let_def using enq_uniq_eq deq_uniq_eq False
        by presburger
    qed
  qed

(* Step 3: 3. 0 : k_v Enq ( SA ) *)
  have all_before_in_sa: "\<forall>k < k_v. op_name (L ! k) = enq \<longrightarrow> in_SA (op_val (L ! k)) L"
  proof (intro allI impI)
    fix k assume "k < k_v" and k_enq: "op_name (L ! k) = enq"
    
    show "in_SA (op_val (L ! k)) L"
    proof (rule ccontr)
      assume not_in: "\<not> in_SA (op_val (L ! k)) L"
      define x where "x = op_val (L ! k)"
      
      (* x *)
      have x_idx: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L = Some k"
        using unique_enq_index[OF DI] k_enq `k < k_v` kv_props(1) x_def 
        unfolding find_unique_index_def by force

      (* v ( k_v) *)
      have v_idx: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some k_v"
        using unique_enq_index[OF DI] kv_props 
        unfolding find_unique_index_def by force

      (* x SA , v (k < k_v), x v 0 *)
      have dist_x_v: "distance_func x v L > 0"
      proof -
        have "distance_func x v L = (if k < k_v then k_v - k else 0)"
          unfolding distance_func_def
          using not_in[folded x_def] x_idx v_idx by simp
        thus ?thesis using `k < k_v` by simp
      qed
      
      (* Proof note. *)
      (* distance_func , > 0, > 0 *)
      have "Distance L v > 0"
      proof -
        (* x *)
        let ?all_enqs = "filter (\<lambda>a. op_name a = enq) L"
        let ?vals = "set (map op_val ?all_enqs)"
        
        have "x \<in> ?vals" 
        proof -
          have "L ! k \<in> set L" using `k < k_v` kv_props(1) by simp
          with k_enq have "L ! k \<in> set ?all_enqs" by simp
          thus ?thesis unfolding x_def
            by auto 
        qed
        
        (* x , >= 0, >= x *)
        hence "sum_list (map (\<lambda>v'. distance_func v' v L) (sorted_list_of_set ?vals)) \<ge> distance_func x v L"
        proof -
          (* Step 1: 1. x *)
          have in_sorted: "x \<in> set (sorted_list_of_set ?vals)" 
            using `x \<in> ?vals` by simp
            
          (* Step 2: 2. *)
          (* [OF in_sorted] x xs, *)
          show ?thesis 
            using sum_list_map_ge_element[OF in_sorted] .
        qed
        
        thus ?thesis unfolding Distance_def Let_def using dist_x_v by linarith
      qed
      
      (* Distance L v = 0 *)
      thus False using dist_zero by simp
    qed
  qed

  (* Step 4: 4. : v , SA k_v *)
  have new_sa_bound: "find_last_SA ?L' = int k_v"
  proof -
    let ?P = "\<lambda>i. op_name (?L' ! i) = enq \<and> in_SA (op_val (?L' ! i)) ?L'"
    
    (* 1: k_v SA ( ) *)
    have kv_valid: "k_v < length ?L' \<and> ?P k_v"
    proof -
      have "k_v < length ?L'" using kv_props(1) by simp
      moreover have "?L' ! k_v = L ! k_v" using kv_props(1) by (simp add: nth_append)
      hence "op_name (?L' ! k_v) = enq" and "op_val (?L' ! k_v) = v" 
        using kv_props by auto
      moreover have "in_SA v ?L'" using sa_evolve[of v] by simp
      ultimately show ?thesis by auto
    qed
    
    (* 2: k_v SA ( ) *)
    have no_sa_after_kv: "\<forall>i \<in> {k_v+1..<length ?L'}. \<not> ?P i"
    proof (intro ballI notI)
      fix i assume "i \<in> {k_v+1..<length ?L'}"
      assume P_i: "?P i"
      hence is_enq: "op_name (?L' ! i) = enq" and in_sa_L': "in_SA (op_val (?L' ! i)) ?L'" by auto
      
      (* deq_act *)
      have "i < length L"
      proof (rule ccontr)
        assume "\<not> i < length L"
        hence "i = length L" using `i \<in> {k_v+1..<length ?L'}` by simp
        hence "?L' ! i = deq_act" by simp
        with is_enq deq_op show False by simp
      qed
      
      hence L_i_eq: "?L' ! i = L ! i" by (simp add: nth_append)
      
      (* a) a *)
      define a where "a = op_val (L ! i)"
      have val_i: "op_val (?L' ! i) = a" using L_i_eq a_def by simp
      
      (* b) a \<noteq> v, v Enq k_v, i > k_v *)
      have "a \<noteq> v"
      proof (rule ccontr)
        assume "\<not> a \<noteq> v"
        hence "a = v" by simp
        have "op_name (L ! i) = enq" using is_enq L_i_eq by simp
        (* i k_v enq v, *)
        with `i < length L` kv_props(1,2,3) `a = v` a_def 
        have "i = k_v" 
          using unique_enq_value[of L i k_v] DI
          using \<open>\<not> a \<noteq> v\<close> \<open>op_name (L ! i) = enq\<close> \<open>i < length L\<close> a_def
            kv_props(1,2,3) by auto 
        thus False using `i \<in> {k_v+1..<length ?L'}` by simp
      qed
      
      (* c) a \<noteq> v, sa_evolve , a L SA *)
      have in_sa_L: "in_SA a L"
        using in_sa_L' val_i sa_evolve[of a] `a \<noteq> v` by simp
        
      (* d) : k_v SA *)
      (* v SA , SA k_v *)
      have old_bound: "find_last_SA L < int k_v"
      proof (rule ccontr)
        assume "\<not> (find_last_SA L < int k_v)"
        hence "int k_v \<le> find_last_SA L" by simp
        with I5[unfolded lI5_SA_Prefix_list_def] kv_props(1,2) 
        have "in_SA (op_val (L ! k_v)) L" by auto
        with kv_props(3) not_sa show False by simp
      qed
      
      have "int i > find_last_SA L"
        using `i \<in> {k_v+1..<length ?L'}` old_bound
        by fastforce 
        
      have "\<not> in_SA (op_val (L ! i)) L"
        by (metis L_i_eq P_i \<open>find_last_SA L < int i\<close> \<open>i < length L\<close>
            enqs_after_last_sa_are_not_in_sa) 
      thus False using in_sa_L a_def by simp
    qed
    
    (* Step 3: 3. : k_v , k_v , k_v *)
    show ?thesis
    proof -
      (* find_indices : ?P *)
      let ?indices = "find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) ?L') ?L'"
      
      have "k_v \<in> set ?indices"
        unfolding find_indices_def using kv_valid
        by (metis (mono_tags, lifting) atLeastLessThan_iff atLeastLessThan_upt
            le0 mem_Collect_eq set_filter) 
      hence "?indices \<noteq> []" by auto
      
      (* k_v , k_v *)
      have "last ?indices = k_v"
      proof (rule ccontr)
        assume "last ?indices \<noteq> k_v"
        
      (* ?indices k_v, , last k_v, k_v *)
      have "last ?indices > k_v"
      proof -
        (* Step 1: 1. indices ( filter ) *)
        have "sorted ?indices" 
          unfolding find_indices_def
          by (meson sorted_upt sorted_wrt_filter) 
          
        (* Step 2: 2. k_v <= last ?indices *)
        have "k_v \<le> last ?indices"
        proof -
          (* k_v *)
          obtain i where i_props: "i < length ?indices" "?indices ! i = k_v"
            using `k_v \<in> set ?indices`
            by (meson in_set_conv_nth) 
            
          (* . i <= length - 1 *)
          have "i \<le> length ?indices - 1" 
            using i_props(1) by linarith
            
          (* indices!i <= indices!(length - 1) *)
          have "?indices ! i \<le> ?indices ! (length ?indices - 1)"
            using `sorted ?indices` `i \<le> length ?indices - 1` i_props(1)
            by (simp add: sorted_iff_nth_mono)
            
          (* last last xs = xs ! (len - 1) *)
          thus ?thesis 
            using i_props(2) `?indices \<noteq> []` last_conv_nth 
            by fastforce
        qed
        
        (* Step 3: 3. last != k_v, *)
        thus ?thesis using `last ?indices \<noteq> k_v` by simp
      qed  

        (* > k_v ?P , no_sa_after_kv *)
        (* Step 1: 1. : last *)
        have last_in: "last ?indices \<in> set ?indices"
          using `?indices \<noteq> []` by simp
          
        (* Step 2: 2. *)
        have "last ?indices < length ?L'"
          using last_in unfolding find_indices_def by auto
          
        (* Step 3: 3. P *)
        have "?P (last ?indices)" 
          using last_in unfolding find_indices_def by auto
          
        have "last ?indices \<in> {k_v+1..<length ?L'}"
          using `last ?indices > k_v` `last ?indices < length ?L'` by simp
          
        thus False using no_sa_after_kv `?P (last ?indices)` by blast
      qed
      
      thus ?thesis unfolding find_last_SA_def Let_def
        using `?indices \<noteq> []` by simp
    qed
  qed

  (* Step 5: 5. : lI5_SA_Prefix_list , *)
  show ?thesis unfolding lI5_SA_Prefix_list_def
  proof (intro allI impI)
    fix k assume k_len: "k < length ?L'" 
    assume k_enq: "op_name (?L' ! k) = enq"
    
    (* deq, enq L *)
    have "k < length L" 
    proof (rule ccontr)
      assume "\<not> k < length L"
      hence "k = length L" using k_len by simp
      hence "?L' ! k = deq_act" by simp
      with k_enq deq_op show False by simp
    qed

    hence L_k_eq: "?L' ! k = L ! k" by (simp add: nth_append)
    have is_enq: "op_name (L ! k) = enq" using k_enq L_k_eq by simp
    have val_k: "op_val (?L' ! k) = op_val (L ! k)" using L_k_eq by simp

    (* k_v *)
    show "in_SA (op_val (?L' ! k)) ?L' \<longleftrightarrow> int k \<le> find_last_SA ?L'"
    proof cases
      assume "k < k_v"
      (* Case A: k k_v . Distance=0 SA *)
      have "in_SA (op_val (L ! k)) L" using all_before_in_sa `k < k_v` is_enq by simp
      hence "in_SA (op_val (?L' ! k)) ?L'" using sa_evolve val_k by simp
      moreover have "int k \<le> find_last_SA ?L'" using `k < k_v` new_sa_bound by simp
      ultimately show ?thesis by simp
    next
      assume "\<not> k < k_v"
      then consider (eq) "k = k_v" | (gt) "k > k_v" by linarith
      then show ?thesis
      proof cases
        case eq
        (* Case B: k k_v. v *)
        have "op_val (L ! k) = v" using eq kv_props(3) by simp
        hence "in_SA (op_val (?L' ! k)) ?L'" using sa_evolve val_k by simp
        moreover have "int k \<le> find_last_SA ?L'" using eq new_sa_bound by simp
        ultimately show ?thesis by simp
      next
        case gt
        (* C: k k_v . lI5_SA_Prefix, SA *)
        have "op_val (L ! k) \<noteq> v"
        proof
          assume "op_val (L ! k) = v"
          (* , , , gt (k > k_v) *)
          have "k = k_v" 
            using same_enq_value_same_index[OF DI `k < length L` kv_props(1) is_enq kv_props(2)]
            using `op_val (L ! k) = v` kv_props(3) by simp
          with gt show False by simp
        qed
        
        (* v SA , SA k_v *)
        have "int k_v > find_last_SA L" 
          using I5[unfolded lI5_SA_Prefix_list_def, THEN spec, of k_v] kv_props not_sa by auto
          
        (* k k_v , k SA *)
        hence "int k > find_last_SA L" using gt by simp
        hence "\<not> in_SA (op_val (L ! k)) L" 
          using I5[unfolded lI5_SA_Prefix_list_def, THEN spec, of k] `k < length L` is_enq by auto
        
        (* , k SA , v, SA *)
        hence "\<not> in_SA (op_val (?L' ! k)) ?L'" 
          using sa_evolve val_k `op_val (L ! k) \<noteq> v` by simp
        
        (* k_v *)
        moreover have "\<not> (int k \<le> find_last_SA ?L')" 
          using gt new_sa_bound by simp
          
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

(* ----------------------------------------------------------------- *)
(* Auxiliary lemma: D3 lI4_FIFO_Semantics (FIFO) *)
(* ----------------------------------------------------------------- *)
lemma lI4_FIFO_Semantics_deq_step_preservation:
  assumes INV: "system_invariant s"
  assumes q_in_SetB: "q_val \<in> SetB s"
  assumes q_not_bot: "q_val \<noteq> BOT"
  assumes base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val 
                                 then modify_lin (lin_seq s) (his_seq s) q_val 
                                 else lin_seq s)"
  (* Revision note 1: mk_op sn *)
  assumes s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p sn]"
  shows "lI4_FIFO_Semantics s'"
proof -
  (* Step 1: 1. *)
  have di_s: "data_independent (lin_seq s)" using INV unfolding system_invariant_def by simp
  have lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" using INV unfolding system_invariant_def by simp
  have lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics_list (lin_seq s)" using INV unfolding system_invariant_def lI4_FIFO_Semantics_def by blast 
  have lI5_SA_Prefix_s: "lI5_SA_Prefix_list (lin_seq s)" using INV unfolding system_invariant_def lI5_SA_Prefix_def by simp

  (* Revision note 2: Key simplification, lI2_Op_Cardinality q_val , PureLib *)
  have card_deq: "card (DeqIdxs s q_val) = 0" using lI2_Op_Cardinality_s q_in_SetB unfolding lI2_Op_Cardinality_def by blast
  have finite_deq: "finite (DeqIdxs s q_val)" unfolding DeqIdxs_def by simp
  have q_deq_empty: "DeqIdxs s q_val = {}" using card_deq finite_deq by auto
  
  have pending_q: "\<forall>k < length (lin_seq s). op_val (lin_seq s ! k) = q_val \<longrightarrow> op_name (lin_seq s ! k) \<noteq> deq"
    using q_deq_empty unfolding DeqIdxs_def by blast

  have card_enq: "card (EnqIdxs s q_val) = 1" using lI2_Op_Cardinality_s q_in_SetB unfolding lI2_Op_Cardinality_def by blast
  have exists_q: "\<exists>k < length (lin_seq s). op_name (lin_seq s ! k) = enq \<and> op_val (lin_seq s ! k) = q_val"
    using card_enq unfolding EnqIdxs_def
    by (simp add: INV SetB_implies_enq_in_lin q_in_SetB)


  (* Step 2: 2. base_lin *)
  have mset_base_eq: "mset base_lin = mset (lin_seq s)"
    unfolding base_def using modify_preserves_mset by presburger 

  (* Step 3: 3. base_lin lI4_FIFO_Semantics_list *)
  have lI4_FIFO_Semantics_base: "lI4_FIFO_Semantics_list base_lin"
  proof (cases "should_modify (lin_seq s) (his_seq s) q_val")
    case True
    then have base_eq: "base_lin = modify_lin (lin_seq s) (his_seq s) q_val" using base_def by meson 
    show ?thesis 
      using move_pending_enq_preserves_lI4_FIFO_Semantics[OF lI4_FIFO_Semantics_s base_eq di_s lI5_SA_Prefix_s pending_q] .
  next
    case False
    then show ?thesis using base_def lI4_FIFO_Semantics_s by simp
  qed

  (* Step 4: 4. base_lin Distance 0 *)
  have dist_zero_base: "Distance base_lin q_val = 0"
  proof (cases "should_modify (lin_seq s) (his_seq s) q_val")
    case True
    then have base_eq: "base_lin = modify_lin (lin_seq s) (his_seq s) q_val" using base_def by simp
    show ?thesis 
      using modify_lin_Distance_zero_internal[OF di_s _ lI5_SA_Prefix_s pending_q exists_q] base_eq lI4_FIFO_Semantics_s by auto
  next
    case False
    note not_modify = False 
    
    (* Proof note. *)
    have "Distance (lin_seq s) q_val = 0"
    proof (rule ccontr)
      assume dist_not_zero: "Distance (lin_seq s) q_val \<noteq> 0"
      
      (* , 0, *)
      have "should_modify (lin_seq s) (his_seq s) q_val"
        using should_modify_completeness[OF di_s lI5_SA_Prefix_s pending_q exists_q dist_not_zero] .
      
      (* False (not_modify) *)
      with not_modify show False by contradiction
    qed
    
    (* base_lin *)
    thus ?thesis using base_def False by simp
  qed

  (* Step 5: 5. : Append *)
  let ?deq_act = "mk_op deq q_val p sn"
  have "lI4_FIFO_Semantics_list (base_lin @ [?deq_act])"
  proof (rule lI4_FIFO_Semantics_append_deq_success[where v="q_val"])
    show "lI4_FIFO_Semantics_list base_lin" using lI4_FIFO_Semantics_base .
    show "data_independent base_lin" using di_s data_independent_cong mset_base_eq by blast
    
    (* Revision note 3: mk_op *)
    show "op_name ?deq_act = deq" by (simp add: mk_op_def op_name_def)
    show "op_val ?deq_act = q_val" by (simp add: mk_op_def op_val_def)
    
    show "\<exists>k<length base_lin. op_name (base_lin ! k) = enq \<and> op_val (base_lin ! k) = q_val"
    proof -
      have "\<exists>act \<in> set (lin_seq s). op_name act = enq \<and> op_val act = q_val"
        using exists_q by (metis nth_mem)
      with mset_base_eq show ?thesis by (metis in_set_conv_nth set_mset_mset)
    qed
    show "\<not> in_SA q_val base_lin"
    proof -
      have "\<forall>act \<in> set (lin_seq s). op_val act = q_val \<longrightarrow> op_name act \<noteq> deq"
        using pending_q by (metis in_set_conv_nth)
      with mset_base_eq have "\<forall>act \<in> set base_lin. op_val act = q_val \<longrightarrow> op_name act \<noteq> deq"
        by (metis set_mset_mset)
      thus ?thesis unfolding in_SA_def find_unique_index_def by (auto simp: filter_empty_conv find_indices_def)
    qed
    show "Distance base_lin q_val = 0" using dist_zero_base .
  qed

  (* Step 6: 6. *)
  thus ?thesis unfolding lI4_FIFO_Semantics_def s'_lin_def by simp
qed

(* ----------------------------------------------------------------- *)
(* Auxiliary lemma: D3 lI5_SA_Prefix (SA) *)
(* ----------------------------------------------------------------- *)
lemma lI5_SA_Prefix_deq_step_preservation:
  assumes INV: "system_invariant s"
  assumes q_in_SetB: "q_val \<in> SetB s"
  assumes q_not_bot: "q_val \<noteq> BOT"
  assumes base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val 
                                 then modify_lin (lin_seq s) (his_seq s) q_val 
                                 else lin_seq s)"
  (* Revision note 1: mk_op sn *)
  assumes s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p sn]"
  shows "lI5_SA_Prefix s'"
proof -
  let ?L = "lin_seq s"
  let ?H = "his_seq s"
  
  (* Step 1: 1. *)
  have di_s: "data_independent ?L" 
    using INV unfolding system_invariant_def by simp
  have lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" 
    using INV unfolding system_invariant_def by simp
  have lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics_list ?L" 
    using INV unfolding system_invariant_def lI4_FIFO_Semantics_def by simp
  have lI5_SA_Prefix_s: "lI5_SA_Prefix_list ?L" 
    using INV unfolding system_invariant_def lI5_SA_Prefix_def by simp

  (* Revision note 2: Key simplification, lI2_Op_Cardinality , *)
  have card_deq: "card (DeqIdxs s q_val) = 0" using lI2_Op_Cardinality_s q_in_SetB unfolding lI2_Op_Cardinality_def by blast
  have finite_deq: "finite (DeqIdxs s q_val)" unfolding DeqIdxs_def by simp
  have q_deq_empty: "DeqIdxs s q_val = {}" using card_deq finite_deq by auto
  
  have pending_q: "\<forall>k < length ?L. op_val (?L ! k) = q_val \<longrightarrow> op_name (?L ! k) \<noteq> deq"
    using q_deq_empty unfolding DeqIdxs_def by blast

  have card_enq: "card (EnqIdxs s q_val) = 1" using lI2_Op_Cardinality_s q_in_SetB unfolding lI2_Op_Cardinality_def by blast
  have exists_q: "\<exists>k < length ?L. op_name (?L ! k) = enq \<and> op_val (?L ! k) = q_val"
    using card_enq unfolding EnqIdxs_def
    using INV SetB_implies_enq_in_lin q_in_SetB by blast 


  (* Step 2: 2. base_lin lI5_SA_Prefix_list *)
  have lI5_SA_Prefix_base: "lI5_SA_Prefix_list base_lin"
  proof (cases "should_modify ?L ?H q_val")
    case True
    then have base_eq: "base_lin = modify_lin ?L ?H q_val" using base_def by meson 
    show ?thesis 
      using modify_preserves_lI5_SA_Prefix[OF lI4_FIFO_Semantics_s base_eq di_s lI5_SA_Prefix_s pending_q] .
  next
    case False
    then show ?thesis using base_def lI5_SA_Prefix_s by simp
  qed

  (* Step 3: 3. ( mset) *)
  have mset_base_eq: "mset base_lin = mset ?L"
    unfolding base_def using modify_preserves_mset q_not_bot by presburger 
  have di_base: "data_independent base_lin"
    using di_s data_independent_cong mset_base_eq by blast

  (* Step 4: 4. Distance *)
  have dist_zero: "Distance base_lin q_val = 0"
  proof (cases "should_modify ?L ?H q_val")
    case True
    then have base_eq: "base_lin = modify_lin ?L ?H q_val" using base_def by simp
    show ?thesis 
      using modify_lin_Distance_zero_internal[OF di_s lI4_FIFO_Semantics_s lI5_SA_Prefix_s pending_q exists_q] base_eq by auto
  next
    case False
    note not_mod = False
    have "Distance ?L q_val = 0"
    proof (rule ccontr)
      assume "Distance ?L q_val \<noteq> 0"
      have "should_modify ?L ?H q_val"
        using should_modify_completeness[OF di_s lI5_SA_Prefix_s pending_q exists_q `Distance ?L q_val \<noteq> 0`] .
      with not_mod show False by contradiction
    qed
    thus ?thesis using base_def False by simp
  qed

  (* Step 5: 5. *)
  let ?deq_act = "mk_op deq q_val p sn"
  have "lI5_SA_Prefix_list (base_lin @ [?deq_act])"
  proof (rule lI5_SA_Prefix_append_deq_success)
    show "lI5_SA_Prefix_list base_lin" using lI5_SA_Prefix_base .
    show "data_independent base_lin" using di_base .
    
    (* Revision note 3: mk_op *)
    show "op_name ?deq_act = deq" by (simp add: mk_op_def op_name_def)
    show "op_val ?deq_act = q_val" by (simp add: mk_op_def op_val_def)
    
    show "\<exists>k < length base_lin. op_name (base_lin ! k) = enq \<and> op_val (base_lin ! k) = q_val"
    proof -
      have "\<exists>act \<in> set ?L. op_name act = enq \<and> op_val act = q_val"
        using exists_q by (metis nth_mem)
      with mset_base_eq show ?thesis by (metis set_mset_mset in_set_conv_nth)
    qed
    
    show "\<not> in_SA q_val base_lin"
    proof -
      have "\<forall>act \<in> set ?L. op_val act = q_val \<longrightarrow> op_name act \<noteq> deq"
        using pending_q by (metis in_set_conv_nth)
      with mset_base_eq have "\<forall>act \<in> set base_lin. op_val act = q_val \<longrightarrow> op_name act \<noteq> deq"
        by (metis set_mset_mset)
      thus ?thesis unfolding in_SA_def find_unique_index_def by (auto simp: find_indices_def filter_empty_conv)
    qed
    show "Distance base_lin q_val = 0" using dist_zero .
  qed

  (* Step 6: 6. *)
  thus ?thesis unfolding lI5_SA_Prefix_def s'_lin_def by simp
qed

(* ----------------------------------------------------------------- *)
(* Auxiliary lemma: D3 preserves under the successful transition hI16_BO_BT_No_HB (SetBO vs SetBT) *)
(* ----------------------------------------------------------------- *)
lemma D3_preserves_hI16_BO_BT_No_HB:
  assumes INV: "system_invariant s"
  assumes pc_D3: "program_counter s p = ''D3''"
  assumes q_not_bot: "Q_arr s (j_var s p) \<noteq> BOT"
  defines "s' \<equiv> Sys_D3_success_update s p"
  shows "hI16_BO_BT_No_HB s'"
proof -
  (* === 1. === *)
  have hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s" using INV unfolding system_invariant_def by auto
  have hI18_Idx_Order_No_Rev_HB_s: "hI18_Idx_Order_No_Rev_HB s" using INV unfolding system_invariant_def by auto
  have hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s" using INV unfolding system_invariant_def by auto
  have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" using INV unfolding system_invariant_def by auto
  have sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s" using INV unfolding system_invariant_def by auto

  define jp where "jp = j_var s p"

  (* === 1.5. state transport , SMT === *)
  have s'_fields: 
    "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    "x_var s' = (\<lambda>x. if x = p then Q_arr s jp else x_var s x)"
    "Q_arr s' = (\<lambda>x. if x = jp then BOT else Q_arr s x)"
    "Qback_arr s' = Qback_arr s"
    "his_seq s' = his_seq s"
    "s_var s' = s_var s"
    "j_var s' = j_var s"
    "l_var s' = l_var s"
    "v_var s' = v_var s"
    "i_var s' = i_var s"
    using assms unfolding s'_def Sys_D3_success_update_def Let_def jp_def
          program_counter_def x_var_def Q_arr_def Qback_arr_def his_seq_def 
          s_var_def j_var_def l_var_def v_var_def i_var_def
    by auto

  have HB_eq: "\<And>x y. HB_EnqRetCall s' x y \<longleftrightarrow> HB_EnqRetCall s x y"
    using s'_fields(5) unfolding HB_EnqRetCall_def HB_Act_def by simp

  show ?thesis
    unfolding hI16_BO_BT_No_HB_def
  proof (intro allI impI notI)
    (* nat *)
    fix a b :: nat
    assume asm: "a \<in> SetBO s' \<and> b \<in> SetBT s'"
    assume HB_s'_ab: "HB_EnqRetCall s' a b"
    
    have a_BO': "a \<in> SetBO s'" and b_BT': "b \<in> SetBT s'" using asm by auto
    have HB_ab: "HB_EnqRetCall s a b" using HB_s'_ab HB_eq by simp
    
    (* === 3. a b T , Idx === *)
    have b_in_T: "InQBack s b"
    proof -
      have "InQBack s' b" using b_BT' unfolding SetBT_def TypeBT_def by auto
      thus ?thesis using s'_fields(4) unfolding InQBack_def by auto
    qed
    
    have a_in_T: "InQBack s a"
      using HB_implies_InQBack[OF INV HB_ab] .
    
    let ?idx_a = "Idx s a"
    let ?idx_b = "Idx s b"
    
    have a_neq_b: "a \<noteq> b" 
      using a_BO' b_BT' unfolding SetBO_def SetBT_def TypeBO_def by blast 

    have idx_neq: "?idx_a \<noteq> ?idx_b"
    proof
      assume same_idx: "?idx_a = ?idx_b"
      have val_a: "Qback_arr s ?idx_a = a"
        using Idx_implies_AtIdx[OF INV a_in_T] AtIdx_implies_Qback_eq by simp
      have val_b: "Qback_arr s ?idx_b = b"
        using Idx_implies_AtIdx[OF INV b_in_T] AtIdx_implies_Qback_eq by simp
      have "a = b" using same_idx val_a val_b by presburger
      thus False using a_neq_b by simp
    qed

    (* === 4. : Idx_a Idx_b === *)
    show False
    proof (cases "?idx_b < ?idx_a")
      case True
      have "\<not> HB_EnqRetCall s a b"
        using hI18_Idx_Order_No_Rev_HB_s True a_in_T b_in_T unfolding hI18_Idx_Order_No_Rev_HB_def by blast
      thus False using HB_ab by simp
    next
      case False
      with idx_neq have a_lt_b: "?idx_a < ?idx_b" by simp

      (* Proof note. *)
      have TypeOK_s': "TypeOK s'"
        using Sys_D3_success_phys_invariants[OF INV pc_D3 q_not_bot] unfolding s'_def by blast
        
      have a_in_B': "a \<in> SetB s'" using a_BO' unfolding SetBO_def by (simp add: SetB_def TypeBO_def) 
      
      have a_not_BOT: "a \<noteq> BOT" 
      proof -
        have "a \<in> Val" 
          using a_in_B' TypeOK_s' unfolding TypeOK_def SetB_def TypeB_def QHas_def Val_def BOT_def by blast
        thus ?thesis unfolding Val_def BOT_def by simp
      qed

      (* Auxiliary lemma *)
      have SetB'_to_TypeB_s: "\<And>x. x \<in> SetB s' \<Longrightarrow> TypeB s x"
      proof -
        fix x assume "x \<in> SetB s'"
        hence TypeB_x': "TypeB s' x" unfolding SetB_def by simp
        have x_not_BOT: "x \<noteq> BOT" using `x \<in> SetB s'` unfolding SetB_def Val_def BOT_def by auto
        show "TypeB s x"
        proof (cases "QHas s' x")
          case True
          then obtain k where "Q_arr s' k = x" unfolding QHas_def by blast
          have "k \<noteq> jp"
          proof
            assume "k = jp"
            hence "Q_arr s' k = BOT" using s'_fields(3) by simp
            with `Q_arr s' k = x` have "x = BOT" by simp
            thus False using x_not_BOT by simp
          qed
          hence "Q_arr s k = x" using `Q_arr s' k = x` s'_fields(3) by simp
          thus ?thesis unfolding TypeB_def QHas_def by blast
        next
          case False
          hence "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x" using TypeB_x' unfolding TypeB_def by auto
          then obtain q where "program_counter s' q = ''E2''" "v_var s' q = x" by blast
          have "q \<noteq> p" using `program_counter s' q = ''E2''` s'_fields(1)
            by auto 
          have "program_counter s q = ''E2''" using `program_counter s' q = ''E2''` `q \<noteq> p` s'_fields(1) by auto
          moreover have "v_var s q = x" using `v_var s' q = x` `q \<noteq> p` s'_fields(9) by auto
          ultimately show ?thesis unfolding TypeB_def by auto
        qed
      qed

      (* Q_arr s' (?idx_a) = a \<noteq> BOT *)
      have Q_idx_a: "Q_arr s' ?idx_a = a"
      proof -
        let ?q_val = "Q_arr s jp"
        have sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s"
          using INV unfolding system_invariant_def by auto

        have qback_a: "Qback_arr s ?idx_a = a" using Idx_implies_AtIdx[OF INV a_in_T] AtIdx_implies_Qback_eq by simp
        have a_in_Val: "a \<in> Val" using a_not_BOT unfolding Val_def BOT_def by simp
        have a_in_B_s: "a \<in> SetB s" using a_in_B' SetB'_to_TypeB_s SetB_def a_in_Val by auto

        have Q_s_idx_a: "Q_arr s ?idx_a = a"
        proof (rule ccontr)
          assume neq_a: "Q_arr s ?idx_a \<noteq> a"
          have "Q_arr s ?idx_a = BOT" using sI8_Q_Qback_Sync_s qback_a neq_a unfolding sI8_Q_Qback_Sync_def by metis 
          have not_in_Q: "\<not> QHas s a"
          proof
            assume "QHas s a"
            then obtain k where "Q_arr s k = a" unfolding QHas_def by blast
            have "Qback_arr s k = a" using sI8_Q_Qback_Sync_s `Q_arr s k = a` a_not_BOT unfolding sI8_Q_Qback_Sync_def by metis 
            show False
            proof (cases "k = ?idx_a")
              case True with `Q_arr s k = a` `Q_arr s ?idx_a = BOT` a_not_BOT show False by simp
            next
              case False
              with sI10_Qback_Unique_Vals_s `Qback_arr s k = a` qback_a a_not_BOT have "Qback_arr s k \<noteq> Qback_arr s ?idx_a" unfolding sI10_Qback_Unique_Vals_def by force
              thus False using `Qback_arr s k = a` qback_a by simp
            qed
          qed
          have "a \<in> SetA s" unfolding SetA_def TypeA_def InQBack_def using qback_a not_in_Q a_in_Val by blast
          have "card (DeqIdxs s a) = 1" using lI2_Op_Cardinality_s `a \<in> SetA s` unfolding lI2_Op_Cardinality_def by blast
          moreover have "card (DeqIdxs s a) = 0" using lI2_Op_Cardinality_s a_in_B_s unfolding lI2_Op_Cardinality_def by blast
          ultimately show False by simp
        qed

        have idx_a_neq_jp: "?idx_a \<noteq> jp"
        proof
          assume "?idx_a = jp"
          with Q_s_idx_a have "a = ?q_val" by simp
          have "TypeB s' ?q_val" using a_in_B' `a = ?q_val` unfolding SetB_def by simp
          thus False
          proof (cases "QHas s' ?q_val")
            case True
            then obtain k where k_def: "Q_arr s' k = ?q_val" unfolding QHas_def by blast
            have "k \<noteq> jp" using s'_fields(3) k_def q_not_bot jp_def by auto
            hence "Q_arr s k = ?q_val" using k_def s'_fields(3) by simp
            have "Qback_arr s k = ?q_val" using sI8_Q_Qback_Sync_s `Q_arr s k = ?q_val` q_not_bot unfolding sI8_Q_Qback_Sync_def
              by (metis jp_def)
            have "Qback_arr s jp = ?q_val" using sI8_Q_Qback_Sync_s q_not_bot unfolding sI8_Q_Qback_Sync_def
              using \<open>Idx s a = jp\<close> \<open>a = Model.Q_arr s jp\<close> qback_a
              by fastforce
            with sI10_Qback_Unique_Vals_s `Qback_arr s k = ?q_val` `k \<noteq> jp` q_not_bot show False unfolding sI10_Qback_Unique_Vals_def
              by (metis jp_def) 
          next
            case False
            hence "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = ?q_val" using `TypeB s' ?q_val` unfolding TypeB_def by auto
            then obtain q where "program_counter s' q = ''E2''" "v_var s' q = ?q_val" by blast
            have "q \<noteq> p" using `program_counter s' q = ''E2''` s'_fields(1)
              by fastforce 
            have pc_E2: "program_counter s q = ''E2''" using `program_counter s' q = ''E2''` `q \<noteq> p` s'_fields(1) by auto
            have v_qval: "v_var s q = ?q_val" using `v_var s' q = ?q_val` `q \<noteq> p` s'_fields(9) by auto
            have pending: "HasPendingEnq s q ?q_val" using hI1_E_Phase_Pending_Enq_s pc_E2 v_qval unfolding hI1_E_Phase_Pending_Enq_def by (metis E2_implies_HasPendingEnq INV) 
            have "Q_arr s (i_var s q) = BOT" using sI3_E2_Slot_Exclusive_s pc_E2 unfolding sI3_E2_Slot_Exclusive_def by blast
            hence "jp \<noteq> i_var s q" using q_not_bot
              using jp_def by auto
            have "Qback_arr s jp = ?q_val" using sI8_Q_Qback_Sync_s q_not_bot unfolding sI8_Q_Qback_Sync_def
              using \<open>Idx s a = jp\<close> \<open>a = Model.Q_arr s jp\<close> qback_a by auto 
            have "\<not> (\<exists>k. Qback_arr s k = ?q_val \<and> k \<noteq> i_var s q)" using hI14_Pending_Enq_Qback_Exclusivity_s pending pc_E2 unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
            thus False using `Qback_arr s jp = ?q_val` `jp \<noteq> i_var s q` by blast
          qed
        qed
        show ?thesis using Q_s_idx_a idx_a_neq_jp s'_fields(3) by simp
      qed

      (* b s' TypeBT , hI19_Scanner_Catches_Later_Enq *)
      have "((\<forall>k < ?idx_b. Q_arr s' k = BOT) \<or>
             (\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> ?idx_b \<and> ?idx_b < l_var s' q \<and>
                  (\<forall>k. j_var s' q \<le> k \<and> k < ?idx_b \<longrightarrow> Q_arr s' k = BOT)))"
        using b_BT' s'_fields(4) unfolding SetBT_def TypeBT_def Idx_def AtIdx_def by auto
        
      thus False
      proof (elim disjE exE conjE)
        assume "\<forall>k < ?idx_b. Q_arr s' k = BOT"
        hence "Q_arr s' ?idx_a = BOT" using a_lt_b by simp
        thus False using Q_idx_a a_not_BOT by auto
      next
        fix q
        assume pc_q: "program_counter s' q = ''D3''"
           and j_le: "j_var s' q \<le> ?idx_b"
           and idx_lt: "?idx_b < l_var s' q"
           and bot_range: "\<forall>k. j_var s' q \<le> k \<and> k < ?idx_b \<longrightarrow> Q_arr s' k = BOT"
           
        have "?idx_a < j_var s' q"
        proof (rule ccontr)
          assume "\<not> ?idx_a < j_var s' q"
          hence "j_var s' q \<le> ?idx_a" by simp
          with a_lt_b bot_range have "Q_arr s' ?idx_a = BOT" by simp
          thus False using Q_idx_a a_not_BOT by auto
        qed
        
        have q_neq_p: "q \<noteq> p" using pc_q s'_fields(1)
          by auto 
        have pc_q_s: "program_counter s q = ''D3''" using pc_q q_neq_p s'_fields(1) by auto
        have j_q_s: "j_var s q = j_var s' q" using q_neq_p s'_fields(7) by simp
        have l_q_s: "l_var s q = l_var s' q" using q_neq_p s'_fields(8) by simp
          
        (* hI12_D_Phase_Pending_Deq D3 Dequeue *)
        have pending_q: "HasPendingDeq s q"
          using INV pc_q_s unfolding system_invariant_def hI12_D_Phase_Pending_Deq_def by auto
          
        have TypeB_a_s: "TypeB s a" using a_in_B' SetB'_to_TypeB_s by simp
        have TypeB_b_s: "TypeB s b" using b_BT' unfolding SetBT_def by (simp add: SetB_def TypeBT_implies_TypeB SetB'_to_TypeB_s)

        (* Step 1: 1. q , metis *)
        have ex_q_s: "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and> 
                          Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
          using pending_q pc_q_s `?idx_a < j_var s' q` j_le idx_lt j_q_s l_q_s by auto

        (* Step 2: 2. hI19_Scanner_Catches_Later_Enq_s a_in_T b_in_T *)
        have "\<not> HB_EnqRetCall s a b"
          using hI19_Scanner_Catches_Later_Enq_s a_in_T b_in_T TypeB_a_s TypeB_b_s a_lt_b ex_q_s
          unfolding hI19_Scanner_Catches_Later_Enq_def by blast
          
        (* Step 3: 3. *)
        thus False using HB_ab by simp
      qed
    qed
  qed
qed


lemma D3_preserves_hI17_BT_BT_No_HB:
  assumes INV: "system_invariant s"
  assumes pc_D3: "program_counter s p = ''D3''"
  assumes q_not_bot: "Q_arr s (j_var s p) \<noteq> BOT"
  defines "s' \<equiv> Sys_D3_success_update s p"
  shows "hI17_BT_BT_No_HB s'"
proof -
  (* === 1. === *)
  have hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s" using INV unfolding system_invariant_def by auto
  have hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s" using INV unfolding system_invariant_def by auto
  have hI18_Idx_Order_No_Rev_HB_s: "hI18_Idx_Order_No_Rev_HB s" using INV unfolding system_invariant_def by auto
  have hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s" using INV unfolding system_invariant_def by auto
  have hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s" using INV unfolding system_invariant_def by auto
  have his_wf: "hI7_His_WF s" using INV unfolding system_invariant_def by auto
  have hI23_Deq_Call_Ret_Balanced_s: "hI23_Deq_Call_Ret_Balanced s" using INV unfolding system_invariant_def by auto
  have sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" using INV unfolding system_invariant_def by auto
  have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" using INV unfolding system_invariant_def by auto
  have sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s" using INV unfolding system_invariant_def by auto
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by auto
  have hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" using INV unfolding system_invariant_def by auto
  have lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" using INV unfolding system_invariant_def by auto

  (* === 2. state transport === *)
  have his_eq: "his_seq s' = his_seq s"
    unfolding s'_def Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by simp
  have T_eq: "Qback_arr s' = Qback_arr s"
    unfolding s'_def Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by simp
  have HB_eq: "\<And>a b. HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
    using his_eq unfolding HB_EnqRetCall_def HB_Act_def by simp

  have sI2_X_var_Upper_Bound_s': "sI2_X_var_Upper_Bound s'" and sI8_Q_Qback_Sync_s': "sI8_Q_Qback_Sync s'" and sI9_Qback_Discrepancy_E3_s': "sI9_Qback_Discrepancy_E3 s'" and TypeOK_s': "TypeOK s'"
    using Sys_D3_success_phys_invariants[OF INV pc_D3 q_not_bot] s'_def by auto

  (* === 3. Auxiliary lemma: SetB s' TypeB s === *)
  have SetB'_to_TypeB_s: "\<And>x. x \<in> SetB s' \<Longrightarrow> TypeB s x"
  proof -
    fix x assume "x \<in> SetB s'"
    hence TypeB_x': "TypeB s' x" unfolding SetB_def by simp
    have x_not_BOT: "x \<noteq> BOT" 
      using `x \<in> SetB s'` unfolding SetB_def Val_def BOT_def by auto
      
    show "TypeB s x"
    proof (cases "QHas s' x")
      case True
      then obtain k where "Q_arr s' k = x" unfolding QHas_def by blast
      have "k \<noteq> j_var s p"
      proof
        assume "k = j_var s p"
        hence "Q_arr s' k = BOT" using s'_def 
          unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def fun_upd_def by simp
        with `Q_arr s' k = x` have "x = BOT" by simp
        thus False using x_not_BOT by simp
      qed
      hence "Q_arr s k = x" 
        using `Q_arr s' k = x` s'_def 
        unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def fun_upd_def by simp
      thus ?thesis unfolding TypeB_def QHas_def by blast
    next
      case False
      hence "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x"
        using TypeB_x' unfolding TypeB_def by auto
      then obtain q where "program_counter s' q = ''E2''" "v_var s' q = x" by blast
      
      have "q \<noteq> p"
      proof
        assume "q = p"
        hence "program_counter s' q = ''D4''" 
          using s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
        with `program_counter s' q = ''E2''` show False by simp
      qed
      
      have "program_counter s q = ''E2''" 
        using `program_counter s' q = ''E2''` `q \<noteq> p` s'_def 
        unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
      moreover have "v_var s q = x"
        using `v_var s' q = x` s'_def 
        unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
      ultimately show ?thesis unfolding TypeB_def by auto
    qed
  qed

  (* === 4. : a, b hI17_BT_BT_No_HB s' === *)
  show ?thesis
    unfolding hI17_BT_BT_No_HB_def
  proof (intro allI impI)
    fix a b
    assume asm_s': "a \<in> SetBT s' \<and> b \<in> SetBT s'"
    
    show "\<not> HB_EnqRetCall s' a b"
    proof
      (* Happen-Before *)
      assume HB_s'_ab: "HB_EnqRetCall s' a b"
      hence HB_ab: "HB_EnqRetCall s a b" using HB_eq by simp

      have a_in_B': "a \<in> SetB s'" and b_in_B': "b \<in> SetB s'" 
        using asm_s' unfolding SetBT_def TypeBT_def
        apply (simp add: SetB_def)
        by (simp add: SetB_partition asm_s') 
        
      have a_not_BOT: "a \<noteq> BOT" 
      proof -
        have "a \<in> Val" using a_in_B' TypeOK_s' 
          unfolding TypeOK_def SetB_def TypeB_def QHas_def Val_def BOT_def by blast
        thus ?thesis unfolding Val_def BOT_def by simp
      qed

      have TypeB_a_s: "TypeB s a" using a_in_B' SetB'_to_TypeB_s by simp
      have TypeB_b_s: "TypeB s b" using b_in_B' SetB'_to_TypeB_s by simp

      have a_in_T: "InQBack s a" using HB_implies_InQBack[OF INV HB_ab] .
      have b_in_T: "InQBack s b"
      proof -
        have "InQBack s' b" using asm_s' unfolding SetBT_def TypeBT_def by auto
        thus ?thesis using T_eq unfolding InQBack_def by auto
      qed

      let ?idx_a = "Idx s a"
      let ?idx_b = "Idx s b"

      (* ============================================================== *)
      (* idx_a < idx_b, a=b *)
      (* ============================================================== *)
      have a_lt_b: "?idx_a < ?idx_b"
      proof (rule ccontr)
        assume not_lt: "\<not> ?idx_a < ?idx_b"
        show False
        proof (cases "?idx_a = ?idx_b")
          case True
          (* Step 1: 1. , T , a = b *)
          have val_a: "Qback_arr s ?idx_a = a"
            using Idx_implies_AtIdx[OF INV a_in_T] AtIdx_implies_Qback_eq by simp
          have val_b: "Qback_arr s ?idx_b = b"
            using Idx_implies_AtIdx[OF INV b_in_T] AtIdx_implies_Qback_eq by simp
          have a_eq_b: "a = b" using True val_a val_b by presburger
          
          (* Step 2: 2. : , Happens-Before *)
          have "\<not> HB_EnqRetCall s a a" using HB_irrefl[OF INV] .
          
          (* Step 3: 3. *)
          thus False using HB_ab a_eq_b by simp
        next
          case False
          (* idx_b < idx_a, hI18_Idx_Order_No_Rev_HB *)
          with not_lt have "?idx_b < ?idx_a" by simp
          with hI18_Idx_Order_No_Rev_HB_s TypeB_a_s TypeB_b_s have "\<not> HB_EnqRetCall s a b" 
            unfolding hI18_Idx_Order_No_Rev_HB_def by (metis a_in_T b_in_T)
          thus False using HB_ab by simp
        qed
      qed

      (* ============================================================== *)
      (* Q_arr s' (?idx_a) = a \<noteq> BOT ( hI16_BO_BT_No_HB ) *)
      (* ============================================================== *)
      have Q_idx_a: "Q_arr s' ?idx_a = a"
      proof -
        let ?jp = "j_var s p"
        let ?q_val = "Q_arr s ?jp"
        have qback_a: "Qback_arr s ?idx_a = a" 
          using Idx_implies_AtIdx[OF INV a_in_T] AtIdx_implies_Qback_eq by simp
        have a_in_Val: "a \<in> Val" using a_not_BOT unfolding Val_def BOT_def by simp
        
        have a_in_B_s: "a \<in> SetB s" unfolding SetB_def using TypeB_a_s a_in_Val by simp

        have Q_s_idx_a: "Q_arr s ?idx_a = a"
        proof (rule ccontr)
          assume neq_a: "Q_arr s ?idx_a \<noteq> a"
          have "Q_arr s ?idx_a = BOT"
          proof (rule ccontr)
            assume "Q_arr s ?idx_a \<noteq> BOT"
            with sI8_Q_Qback_Sync_s have "Qback_arr s ?idx_a = Q_arr s ?idx_a" unfolding sI8_Q_Qback_Sync_def by metis 
            with qback_a neq_a show False by simp
          qed
          have not_in_Q: "\<not> QHas s a"
          proof
            assume "QHas s a"
            then obtain k where "Q_arr s k = a" unfolding QHas_def by blast
            have "Qback_arr s k = a" using sI8_Q_Qback_Sync_s `Q_arr s k = a` a_not_BOT unfolding sI8_Q_Qback_Sync_def by metis 
            show False
            proof (cases "k = ?idx_a")
              case True with `Q_arr s k = a` `Q_arr s ?idx_a = BOT` a_not_BOT show False by simp
            next
              case False
              with sI10_Qback_Unique_Vals_s `Qback_arr s k = a` qback_a a_not_BOT have "Qback_arr s k \<noteq> Qback_arr s ?idx_a" 
                unfolding sI10_Qback_Unique_Vals_def by force
              thus False using `Qback_arr s k = a` qback_a by simp
            qed
          qed
          
          have "a \<in> SetA s" unfolding SetA_def TypeA_def InQBack_def
            using qback_a not_in_Q a_in_Val by blast
          have "card (DeqIdxs s a) = 1" using lI2_Op_Cardinality_s `a \<in> SetA s` unfolding lI2_Op_Cardinality_def by blast
          moreover have "card (DeqIdxs s a) = 0" using lI2_Op_Cardinality_s a_in_B_s unfolding lI2_Op_Cardinality_def by blast
          ultimately show False by simp
        qed

        have idx_a_neq_jp: "?idx_a \<noteq> ?jp"
        proof
          assume "?idx_a = ?jp"
          with Q_s_idx_a have a_eq_qval: "a = ?q_val" by simp
          have "TypeB s' ?q_val" using a_in_B' a_eq_qval unfolding SetB_def by simp
          thus False
          proof (cases "QHas s' ?q_val")
            case True
            then obtain k where k_def: "Q_arr s' k = ?q_val" unfolding QHas_def by blast
            have "k \<noteq> ?jp" 
              using s'_def k_def q_not_bot unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def fun_upd_def by auto
            hence "Q_arr s k = ?q_val" 
              using k_def s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def fun_upd_def by simp
            have "Qback_arr s k = ?q_val" 
              using sI8_Q_Qback_Sync_s `Q_arr s k = ?q_val` q_not_bot unfolding sI8_Q_Qback_Sync_def by metis 
            have "Qback_arr s ?jp = ?q_val" 
              using sI8_Q_Qback_Sync_s q_not_bot unfolding sI8_Q_Qback_Sync_def by metis 
            with sI10_Qback_Unique_Vals_s `Qback_arr s k = ?q_val` `k \<noteq> ?jp` q_not_bot show False unfolding sI10_Qback_Unique_Vals_def by force
          next
            case False
            hence "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = ?q_val" 
              using `TypeB s' ?q_val` unfolding TypeB_def by auto
            then obtain q where "program_counter s' q = ''E2''" "v_var s' q = ?q_val" by blast
            
            have "q \<noteq> p"
            proof
              assume "q = p"
              hence "program_counter s' q = ''D4''" 
                using s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
              with `program_counter s' q = ''E2''` show False by simp
            qed
            
            have pc_E2: "program_counter s q = ''E2''" 
              using `program_counter s' q = ''E2''` `q \<noteq> p` s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
            have v_qval: "v_var s q = ?q_val" 
              using `v_var s' q = ?q_val` s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
            
            have pending: "HasPendingEnq s q ?q_val" 
              using hI1_E_Phase_Pending_Enq_s pc_E2 v_qval unfolding hI1_E_Phase_Pending_Enq_def by (metis E2_implies_HasPendingEnq INV) 
              
            have "Q_arr s (i_var s q) = BOT" 
              using sI3_E2_Slot_Exclusive_s pc_E2 unfolding sI3_E2_Slot_Exclusive_def by blast
            hence "?jp \<noteq> i_var s q" 
              using q_not_bot by auto
              
            have "Qback_arr s ?jp = ?q_val" 
              using sI8_Q_Qback_Sync_s q_not_bot unfolding sI8_Q_Qback_Sync_def by force
            have "\<not> (\<exists>k. Qback_arr s k = ?q_val \<and> k \<noteq> i_var s q)" 
              using hI14_Pending_Enq_Qback_Exclusivity_s pending pc_E2 unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
              
            thus False using `Qback_arr s ?jp = ?q_val` `?jp \<noteq> i_var s q` by blast
          qed
        qed

        show ?thesis 
          using Q_s_idx_a idx_a_neq_jp s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def fun_upd_def by simp
      qed

      (* ============================================================== *)
      (* b s' TypeBT, hI19_Scanner_Catches_Later_Enq *)
      (* ============================================================== *)
      have "((\<forall>k < ?idx_b. Q_arr s' k = BOT) \<or>
             (\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> ?idx_b \<and> ?idx_b < l_var s' q \<and>
                  (\<forall>k. j_var s' q \<le> k \<and> k < ?idx_b \<longrightarrow> Q_arr s' k = BOT)))"
        using asm_s' T_eq unfolding SetBT_def TypeBT_def Idx_def AtIdx_def by auto
        
      thus False
      proof (elim disjE exE conjE)
        (* 1: b . , a b , a *)
        assume "\<forall>k < ?idx_b. Q_arr s' k = BOT"
        hence "Q_arr s' ?idx_a = BOT" using a_lt_b by simp
        thus False using Q_idx_a a_not_BOT by auto
      next
        (* 2: b q *)
        fix q
        assume pc_q: "program_counter s' q = ''D3''"
           and j_le: "j_var s' q \<le> ?idx_b"
           and idx_lt: "?idx_b < l_var s' q"
           and bot_range: "\<forall>k. j_var s' q \<le> k \<and> k < ?idx_b \<longrightarrow> Q_arr s' k = BOT"
           
        (* Q_arr s' ?idx_a \<noteq> BOT, a *)
        have "?idx_a < j_var s' q"
        proof (rule ccontr)
          assume "\<not> ?idx_a < j_var s' q"
          hence "j_var s' q \<le> ?idx_a" by simp
          with a_lt_b bot_range have "Q_arr s' ?idx_a = BOT" by simp
          thus False using Q_idx_a a_not_BOT by auto
        qed
        
        (* q s *)
        have q_neq_p: "q \<noteq> p"
          using pc_q s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
        have pc_q_s: "program_counter s q = ''D3''"
          using pc_q q_neq_p s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
        have j_q_s: "j_var s q = j_var s' q"
          using q_neq_p s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto
        have l_q_s: "l_var s q = l_var s' q"
          using q_neq_p s'_def unfolding Sys_D3_success_update_def Let_def 
                  program_counter_def Q_arr_def x_var_def lin_seq_def Qback_arr_def 
                  X_var_def V_var_def v_var_def i_var_def j_var_def l_var_def his_seq_def by auto

        (* ========================================================== *)
        (* 【 】 hI12_D_Phase_Pending_Deq, *)
        (* ========================================================== *)
        have pending_q: "HasPendingDeq s q"
          using INV pc_q_s unfolding system_invariant_def hI12_D_Phase_Pending_Deq_def by auto

        (* ========================================================== *)
        (* 【 】 hI12_D_Phase_Pending_Deq, *)
        (* ========================================================== *)
        have pending_q: "HasPendingDeq s q"
          using INV pc_q_s unfolding system_invariant_def hI12_D_Phase_Pending_Deq_def by auto

        (* ?idx_a < j_var s q \<le> ?idx_b < l_var s q *)
        (* Step 1: 1. q , *)
        have ex_q_s: "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and> 
                          Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
          using pending_q pc_q_s `?idx_a < j_var s' q` j_le idx_lt j_q_s l_q_s by auto

        (* Step 2: 2. hI19_Scanner_Catches_Later_Enq. : a_in_T b_in_T TypeB hI19_Scanner_Catches_Later_Enq *)
        have "\<not> HB_EnqRetCall s a b"
          using hI19_Scanner_Catches_Later_Enq_s a_in_T b_in_T TypeB_a_s TypeB_b_s a_lt_b ex_q_s
          unfolding hI19_Scanner_Catches_Later_Enq_def by blast
          
        (* Step 3: 3. , a Happen-Before b *)
        thus False using HB_ab by simp
      qed
    qed
  qed
qed

(* Auxiliary lemma: D3 Q (BOT) , sI4_E3_Qback_Written *)
lemma sI4_E3_Qback_Written_preserved_under_D3_BOT:
  fixes s s' :: SysState and p :: nat and jp lp :: nat
  assumes INV: "system_invariant s"
  assumes Q_jp_bot: "Q_arr s jp = BOT"
  assumes s'_def: "s' = (
    (fst s)\<lparr>
      c_program_counter := (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else CState.c_program_counter (fst s) x),
      Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
      j_var := (\<lambda>x. if x = p then (if jp \<noteq> lp - 1 then jp + 1 else jp) else CState.j_var (fst s) x),
      x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
    \<rparr>,
    snd s
  )"
  shows "sI4_E3_Qback_Written s'"
proof -
  (* Step 1: 1. *)
  note bridges = program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def

  (* Step 2: 2. ( sI4_E3_Qback_Written) *)
  have sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s" using INV unfolding system_invariant_def by auto
  
  (* Step 3: 3. s'_def *)
  have pc_update: "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
    using s'_def by (auto simp: bridges)
    
  have s'_simple_props: 
    "\<forall>q. i_var s' q = i_var s q" 
    "X_var s' = X_var s"
    "\<forall>k. Qback_arr s' k = Qback_arr s k"
    "\<forall>q. v_var s' q = v_var s q"
    using s'_def by (auto simp: bridges)
    
  have Q_update: "\<forall>k. Q_arr s' k = (if k = jp then BOT else Q_arr s k)"
    using s'_def by (auto simp: bridges)

  (* Step 4: 4. *)
  show ?thesis
    unfolding sI4_E3_Qback_Written_def
  proof (intro allI impI)
    fix pa :: nat
    assume pc_pa: "program_counter s' pa = ''E3''"
    
    have pa_not_p: "pa \<noteq> p"
    proof
      assume "pa = p"
      hence "program_counter s' p = ''E3''" using pc_pa by simp
      moreover have "program_counter s' p = ''D1'' \<or> program_counter s' p = ''D3''"
        using pc_update by auto
      ultimately show False by auto
    qed

    have pc_pa_old: "program_counter s pa = ''E3''"
      using pc_pa pc_update pa_not_p by (auto split: if_splits)

    (* Step 5: 5. pa : \<or> BOT *)
    have pa_props: 
      "i_var s pa \<in> Val" 
      "Q_arr s (i_var s pa) = v_var s pa \<or> Q_arr s (i_var s pa) = BOT"
      "Qback_arr s (i_var s pa) = v_var s pa"
      using sI4_E3_Qback_Written_s pc_pa_old unfolding sI4_E3_Qback_Written_def bridges by auto

    (* Step 6: 6. : BOT, BOT Q_arr *)
    have Q_eq_all: "\<forall>k. Q_arr s' k = Q_arr s k"
      using Q_update Q_jp_bot by auto

    (* Step 7: 7. *)
    have eq_facts: 
      "i_var s' pa = i_var s pa" 
      "X_var s' = X_var s"
      "Qback_arr s' (i_var s' pa) = Qback_arr s (i_var s pa)"
      "v_var s' pa = v_var s pa"
      using pa_not_p s'_simple_props by auto

    (* Step 8: 8. *)
    have prop1: "i_var s' pa \<in> Val" using pa_props(1) eq_facts by simp
      
    have prop2: "i_var s' pa < X_var s'" using sI4_E3_Qback_Written_s pc_pa_old eq_facts s'_simple_props unfolding sI4_E3_Qback_Written_def by auto
      
    (* Q_eq_all , \<or> BOT *)
    have prop3: "Q_arr s' (i_var s' pa) = v_var s' pa \<or> Q_arr s' (i_var s' pa) = BOT" 
      using pa_props(2) eq_facts Q_eq_all by auto
      
    have prop4: "Qback_arr s' (i_var s' pa) = v_var s' pa" 
      using pa_props(3) eq_facts by simp
      
    have prop5: "\<forall>q. q \<noteq> pa \<and> program_counter s' q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' pa \<noteq> i_var s' q"
    proof (intro allI impI)
      fix q
      assume q_prems: "q \<noteq> pa \<and> program_counter s' q \<in> {''E2'', ''E3''}"
      have q_not_p: "q \<noteq> p" using q_prems pc_update by (auto split: if_splits)
      have i_q_eq: "i_var s' q = i_var s q" using q_not_p s'_simple_props by auto
      have pc_q_old: "program_counter s q \<in> {''E2'', ''E3''}"
        using q_prems q_not_p pc_update by (auto split: if_splits)
      show "i_var s' pa \<noteq> i_var s' q"
        using sI4_E3_Qback_Written_s pc_pa_old eq_facts i_q_eq pc_q_old q_prems
        unfolding sI4_E3_Qback_Written_def by auto
    qed

    (* Step 9: 9. ( sI4_E3_Qback_Written) *)
    show "i_var s' pa \<in> Val \<and> i_var s' pa < X_var s' \<and> (Q_arr s' (i_var s' pa) = v_var s' pa \<or> Q_arr s' (i_var s' pa) = BOT) \<and> Qback_arr s' (i_var s' pa) = v_var s' pa \<and> (\<forall>q. q \<noteq> pa \<and> program_counter s' q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' pa \<noteq> i_var s' q)"
      using prop1 prop2 prop3 prop4 prop5 by blast
  qed
qed


(* Auxiliary lemma: D3 Q , sI4_E3_Qback_Written *)
lemma sI4_E3_Qback_Written_preserved_under_D3_success:
  fixes s s' :: SysState and p :: nat and jp :: nat
  assumes INV: "system_invariant s"
  assumes jp_def: "jp = j_var s p"
  assumes pc_update: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
  assumes Q_update: "\<forall>k. Q_arr s' k = (if k = jp then BOT else Q_arr s k)"
  assumes simple_props: 
    "\<forall>q. i_var s' q = i_var s q"
    "X_var s' = X_var s"
    "\<forall>k. Qback_arr s' k = Qback_arr s k"
    "\<forall>q. v_var s' q = v_var s q"
  shows "sI4_E3_Qback_Written s'"
proof -
  note bridges = program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def
  have sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s" using INV unfolding system_invariant_def by auto

  show ?thesis
    unfolding sI4_E3_Qback_Written_def
  proof (intro allI impI)
    fix pa :: nat
    assume pc_pa: "program_counter s' pa = ''E3''"
    
    have pa_not_p: "pa \<noteq> p"
    proof
      assume "pa = p"
      hence "program_counter s' p = ''E3''" using pc_pa by simp
      moreover have "program_counter s' p = ''D4''" using pc_update by simp
      ultimately show False by simp
    qed

    have pc_pa_old: "program_counter s pa = ''E3''"
      using pc_pa pc_update pa_not_p by (auto split: if_splits)

    have pa_props: 
      "i_var s pa \<in> Val" 
      "Qback_arr s (i_var s pa) = v_var s pa"
      "(Q_arr s (i_var s pa) = v_var s pa \<or> Q_arr s (i_var s pa) = BOT)"
      using sI4_E3_Qback_Written_s pc_pa_old unfolding sI4_E3_Qback_Written_def bridges by auto

    have eq_facts: 
      "i_var s' pa = i_var s pa" 
      "X_var s' = X_var s"
      "Qback_arr s' (i_var s' pa) = Qback_arr s (i_var s pa)"
      "v_var s' pa = v_var s pa"
      using pa_not_p simple_props by auto

    have prop1: "i_var s' pa \<in> Val" using pa_props(1) eq_facts(1) by simp
    have prop2: "i_var s' pa < X_var s'" using sI4_E3_Qback_Written_s pc_pa_old eq_facts(1) simple_props unfolding sI4_E3_Qback_Written_def by auto
    
    (* , Q_arr BOT, \<or> BOT *)
    have prop3: "Q_arr s' (i_var s' pa) = v_var s' pa \<or> Q_arr s' (i_var s' pa) = BOT"
    proof (cases "i_var s pa = jp")
      case True
      hence "Q_arr s' (i_var s' pa) = BOT" using Q_update eq_facts(1) by simp
      thus ?thesis by simp
    next
      case False
      hence "Q_arr s' (i_var s' pa) = Q_arr s (i_var s pa)" using Q_update eq_facts(1) by simp
      thus ?thesis using pa_props(3) eq_facts(4) by simp
    qed

    have prop4: "Qback_arr s' (i_var s' pa) = v_var s' pa" using pa_props(2) eq_facts(3,4) by simp
    
    have prop5: "\<forall>q. q \<noteq> pa \<and> program_counter s' q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' pa \<noteq> i_var s' q"
    proof (intro allI impI)
      fix q
      assume q_prems: "q \<noteq> pa \<and> program_counter s' q \<in> {''E2'', ''E3''}"
      have q_not_p: "q \<noteq> p" using q_prems pc_update by (auto split: if_splits)
      have i_q_eq: "i_var s' q = i_var s q" using q_not_p simple_props by auto
      have pc_q_old: "program_counter s q \<in> {''E2'', ''E3''}"
        using q_prems q_not_p pc_update by (auto split: if_splits)
      show "i_var s' pa \<noteq> i_var s' q"
        using sI4_E3_Qback_Written_s pc_pa_old eq_facts(1) i_q_eq pc_q_old q_prems(1)
        unfolding sI4_E3_Qback_Written_def by auto
    qed

    show "i_var s' pa \<in> Val \<and> i_var s' pa < X_var s' \<and> (Q_arr s' (i_var s' pa) = v_var s' pa \<or> Q_arr s' (i_var s' pa) = BOT) \<and> Qback_arr s' (i_var s' pa) = v_var s' pa \<and> (\<forall>q. q \<noteq> pa \<and> program_counter s' q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' pa \<noteq> i_var s' q)"
      using prop1 prop2 prop3 prop4 prop5 by blast
  qed
qed


(* ========================================================================= *)
(* modify_lin lI7_D4_Deq_Deq_HB (Pending ) *)
(* ========================================================================= *)

(* Proof note. *)
lemma lI7_D4_Deq_Deq_HB_implies_list:
  assumes "lI7_D4_Deq_Deq_HB s"
  shows "lI7_D4_Deq_Deq_HB_list (lin_seq s) (his_seq s) (program_counter s) (x_var s) (s_var s)"
  using assms unfolding lI7_D4_Deq_Deq_HB_list_def lI7_D4_Deq_Deq_HB_def
  by meson

(* , *)
lemma list_implies_lI7_D4_Deq_Deq_HB:
  assumes "lI7_D4_Deq_Deq_HB_list (lin_seq s) (his_seq s) (program_counter s) (x_var s) (s_var s)"
  shows "lI7_D4_Deq_Deq_HB s"
  using assms unfolding lI7_D4_Deq_Deq_HB_list_def lI7_D4_Deq_Deq_HB_def
  by blast 

(* ========================================================================= *)
(* deq , q \<noteq> p ( k1,k2 ) *)
(* ========================================================================= *)
lemma lI7_D4_Deq_Deq_HB_append_deq_other:
  assumes list: "lI7_D4_Deq_Deq_HB_list L H pc xv sv"  (* 5 *)
    and q_neq_p: "q \<noteq> p"
    and pc': "pc' = pc(p := ''D4'')"
    (* mk_op 4 (oper, val, pid, ssn) *)
    and L': "L' = L @ [mk_op deq v p sn]" 
    and H': "H' = H"
    and k1_old: "k1 < length L"
    and k2_old: "k2 < length L"
    (* \<exists>h1 h2, lI7_D4_Deq_Deq_HB_list 5 *)
    and prems: "op_name (L' ! k1) = deq" 
               "L' ! k2 = mk_op deq (xv q) q (sv q)" 
               "\<forall>k3>k2. k3 < length L' \<longrightarrow> op_name (L' ! k3) \<noteq> deq \<or> op_pid (L' ! k3) \<noteq> q"
               "pc' q = ''D4''"
               "HB H' (L' ! k1) (L' ! k2)"
  shows "k1 < k2"
proof -
  (* Step 1: 1. L' L *)
  have eq1: "L' ! k1 = L ! k1" using k1_old L' by (simp add: nth_append)
  have eq2: "L' ! k2 = L ! k2" using k2_old L' by (simp add: nth_append)
  
  (* Step 2: 2. pc' pc *)
  have pc_q_D4: "pc q = ''D4''" using prems(4) pc' q_neq_p by auto

  (* Step 3: 3. prems L' L, H' H *)
  have oper_L_k1: "op_name (L ! k1) = deq" using prems(1) eq1 by simp 
  have match_L_k2: "L ! k2 = mk_op deq (xv q) q (sv q)" using prems(2) eq2 by simp
  
  (* , L *)
  have term_cond_L: "\<forall>k3>k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> q"
  proof (intro allI impI)
    fix k3 assume "k3 > k2" "k3 < length L"
    hence "k3 < length L'" using L' by simp
    with prems(3) `k3 > k2` have "op_name (L' ! k3) \<noteq> deq \<or> op_pid (L' ! k3) \<noteq> q" by simp
    thus "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> q" using L' `k3 < length L` by (simp add: nth_append)
  qed

  have hb_cond: "HB H (L ! k1) (L ! k2)"
    using prems(5) eq1 eq2 H' by simp 

  (* Step 4: 4. , list , *)
  show ?thesis
    using list[unfolded lI7_D4_Deq_Deq_HB_list_def, rule_format, of k1 k2 q]
    using k1_old k2_old oper_L_k1 match_L_k2 term_cond_L pc_q_D4 hb_cond
    by blast
qed


(* ========================================================================= *)
(* modify_lin lI7_D4_Deq_Deq_HB_list (SSN ) *)
(* \<Longrightarrow> , new_L 7 *)
(* ========================================================================= *)
lemma lI7_D4_Deq_Deq_HB_list_modify:
  assumes sys_inv: "system_invariant s"
  shows "H = his_seq s \<Longrightarrow> 
         TypeBT s bt_val \<Longrightarrow> 
         data_independent L \<Longrightarrow> 
         HB_consistent L H \<Longrightarrow> 
         lI7_D4_Deq_Deq_HB_list L H pc (x_var s) (s_var s) \<Longrightarrow> 
         mset L = mset (lin_seq s) \<Longrightarrow> 
         (\<forall>v. in_SA v L \<longleftrightarrow> in_SA v (lin_seq s)) \<Longrightarrow> 
         pc = program_counter s \<Longrightarrow>  
         lI7_D4_Deq_Deq_HB_list (modify_lin L H bt_val) H pc (x_var s) (s_var s)"
proof (induct L H bt_val rule: modify_lin.induct)
  case (1 L H bt_val)
  note ih = this
  
  from sys_inv have wf_s: "hI7_His_WF s" and order_s: "hI6_SSN_Order s" and unique_s: "hI5_SSN_Unique s" 
    unfolding system_invariant_def by auto

  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    have "modify_lin L H bt_val = L" 
      using False by (subst modify_lin.simps, auto simp: Let_def)
    thus ?thesis using "1.prems"(5) by simp
  next
    case True
    note do_modify = True
    
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define remaining where "remaining = drop (nat (last_sa_pos + 1)) L"
    
    have search_not_none: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
      using do_modify unfolding should_modify_def Let_def remaining_def last_sa_pos_def
      by (metis option.simps(4))
      
    then obtain bt_idx where bt_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx" 
      by auto
      
    have bt_idx_valid: "bt_idx < length remaining"
      by (rule find_unique_index_Some_less_length[OF bt_idx_def])
      
    define l1 where "l1 = take (nat (last_sa_pos + 1)) L"
    define l2 where "l2 = take bt_idx remaining"
    define l3 where "l3 = drop (bt_idx + 1) remaining"
    define bt_act where "bt_act = remaining ! bt_idx"
    define l2_last where "l2_last = last l2"

    have l2_not_nil: "l2 \<noteq> []"
    proof
      assume eq_nil: "l2 = []"
      have "remaining \<noteq> []" using bt_idx_valid by auto
      with eq_nil l2_def have "bt_idx = 0" by (metis take_eq_Nil)
      with do_modify show False 
        unfolding should_modify_def Let_def l2_def remaining_def last_sa_pos_def
        using bt_idx_def last_sa_pos_def remaining_def by force 
    qed

    have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
      using bt_idx_valid l2_def l3_def bt_act_def
      using id_take_nth_drop by fastforce
      
    have L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
      unfolding l1_def remaining_def using remaining_decomp
      using remaining_def by force 

    have bt_in_L: "bt_act \<in> set L"
      using L_decomp by auto

    show ?thesis
    proof (cases "op_name l2_last = enq")
      (* =================================================================== *)
      case True (* === c0: Enq Case === *)
      (* =================================================================== *)
      define ll2 where "ll2 = butlast l2"
      define new_L where "new_L = l1 @ ll2 @ [bt_act] @ [l2_last] @ l3"
      
      have l2_struct: "l2 = ll2 @ [l2_last]" using l2_not_nil ll2_def
        using l2_last_def by auto 
      
      have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
        using do_modify True bt_idx_def l2_not_nil
        unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        apply (subst modify_lin.simps)
        apply (auto simp: Let_def split: option.splits if_splits)
        done
        
      have mset_new: "mset new_L = mset L"
        using L_decomp l2_not_nil ll2_def new_L_def by (metis case1 l2_last_def)
        
      have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
      have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto
      
      have bt_type: "TypeBT s (op_val bt_act)" 
        using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def 
        using "1.prems"(2) by auto
      
      have hb_new: "HB_consistent new_L H"
        unfolding new_L_def
      proof (rule modify_step_c0_consistent[where s=s and L=L and H=H])
        show "system_invariant s" using sys_inv by simp
        show "HB_consistent L H" using "1.prems"(4) by blast
        show "H = his_seq s" using "1.prems"(1) by simp
        show "data_independent L" using "1.prems"(3) by blast
        show "mset L = mset (lin_seq s)" using "1.prems"(6) by blast
        show "\<forall>v. in_SA v L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) by blast
        show "L = l1 @ l2 @ [bt_act] @ l3" using L_decomp by simp
        show "l2 = ll2 @ [l2_last]" using l2_struct by simp
        show "last_sa_pos = find_last_SA L" using last_sa_pos_def by simp
        show "l1 = take (nat (last_sa_pos + 1)) L" using l1_def by simp
        show "op_name l2_last = enq" using True by simp
        show "op_name bt_act = enq" 
          using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
        show "TypeBT s (op_val bt_act)" using bt_type by simp
      qed

      (* 🛡️ 2: , \<exists>h1 h2 *)
      have lI7_D4_Deq_Deq_HB_new: "lI7_D4_Deq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
      proof (unfold lI7_D4_Deq_Deq_HB_list_def, intro allI impI, elim conjE)
        fix k1 k2 p
        assume prems: "k1 < length new_L" "k2 < length new_L"
           "op_name (new_L ! k1) = deq" 
           "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
           "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
           "pc p = ''D4''" 
           "HB H (new_L ! k1) (new_L ! k2)"

        have op_new_k2: "op_name (new_L ! k2) = deq" 
          using prems(4) by (simp add: mk_op_def op_name_def)
          
        have pid_new_k2: "op_pid (new_L ! k2) = p" 
          using prems(4) by (simp add: mk_op_def op_pid_def)

        let ?k = "length l1 + length ll2"
        let ?f = "\<lambda>i. if i = ?k then ?k + 1 else if i = ?k + 1 then ?k else i"
        
        have L_exp: "L = l1 @ ll2 @ l2_last # bt_act # l3" using L_decomp l2_struct by auto
        have new_L_exp: "new_L = l1 @ ll2 @ bt_act # l2_last # l3" using new_L_def by auto
        
        have len_L: "length L = length l1 + length ll2 + 2 + length l3" using L_exp by simp
        have len_eq: "length new_L = length L" using mset_new by (metis mset_eq_length)
        
        have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (?f i)"
        proof -
          fix i assume i_lt: "i < length new_L"
          consider (lt) "i < ?k" | (eq1) "i = ?k" | (eq2) "i = ?k + 1" | (gt) "i > ?k + 1" by linarith
          then show "new_L ! i = L ! (?f i)"
          proof cases
            case lt
            hence fi_eq: "?f i = i" by simp
            have "new_L ! i = L ! i"
            proof (cases "i < length l1")
              case True thus ?thesis unfolding L_exp new_L_exp by (simp add: nth_append)
            next
              case False
              hence "i - length l1 < length ll2" using lt by linarith
              thus ?thesis unfolding L_exp new_L_exp using False by (simp add: nth_append)
            qed
            thus ?thesis using fi_eq by simp
          next
            case eq1
            have f_val: "?f i = ?k + 1" using eq1 by simp
            have a1: "\<not> i < length l1" "i - length l1 = length ll2" using eq1 by linarith+
            have part1: "new_L ! i = bt_act" unfolding new_L_exp using a1 by (simp add: nth_append)
            have b1: "\<not> ?f i < length l1" "?f i - length l1 = Suc (length ll2)" using f_val by linarith+
            have part2: "L ! (?f i) = bt_act" unfolding L_exp using b1 by (simp add: nth_append)
            show ?thesis using part1 part2 by simp
          next
            case eq2
            have f_val: "?f i = ?k" using eq2 by simp
            have a1: "\<not> i < length l1" "i - length l1 = Suc (length ll2)" using eq2 by linarith+
            have part1: "new_L ! i = l2_last" unfolding new_L_exp using a1 by (simp add: nth_append)
            have b1: "\<not> ?f i < length l1" "?f i - length l1 = length ll2" using f_val by linarith+
            have part2: "L ! (?f i) = l2_last" unfolding L_exp using b1 by (simp add: nth_append)
            show ?thesis using part1 part2 by simp
          next
            case gt
            hence fi_eq: "?f i = i" by simp
            have a1: "\<not> i < length l1" "\<not> i - length l1 < length ll2" using gt by linarith+
            define m where "m = i - length l1 - length ll2 - 2"
            have idx_eq: "i - length l1 - length ll2 = Suc (Suc m)" unfolding m_def using gt by linarith
            have part1: "new_L ! i = l3 ! m" unfolding new_L_exp using a1 idx_eq by (simp add: nth_append)
            have part2: "L ! i = l3 ! m" unfolding L_exp using a1 idx_eq by (simp add: nth_append)
            show ?thesis using part1 part2 fi_eq by simp
          qed
        qed
        
        have valid_f1: "?f k1 < length L" using prems(1) len_eq len_L by auto
        have valid_f2: "?f k2 < length L" using prems(2) len_eq len_L by auto
        
        have oper_f1: "op_name (L ! (?f k1)) = deq" using prems(3) eq_nth[OF prems(1)] by simp
        have match_f2: "L ! (?f k2) = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
        
        have f2_not_swapped: "?f k2 \<noteq> ?k \<and> ?f k2 \<noteq> ?k + 1"
        proof (rule ccontr)
          assume "\<not> (?f k2 \<noteq> ?k \<and> ?f k2 \<noteq> ?k + 1)"
          hence "?f k2 = ?k \<or> ?f k2 = ?k + 1" by auto
          thus False
          proof
            assume "?f k2 = ?k"
            have "L ! ?k = l2_last" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! (?f k2)) = enq" using True `?f k2 = ?k` by simp
            thus False using match_f2
              using op_new_k2 prems(4) by auto 
          next
            assume "?f k2 = ?k + 1"
            have "L ! (?k + 1) = bt_act" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! (?f k2)) = enq" using find_unique_index_prop[OF bt_idx_def] `?f k2 = ?k + 1`
              using bt_act_def by fastforce 
            thus False using match_f2
              using op_new_k2 prems(4) by auto
          qed
        qed
        hence f2_eq_k2: "?f k2 = k2" by (auto split: if_splits)
        
        have term_cond_L: "\<forall>k3>?f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
        proof (intro allI impI)
          fix k3 assume "k3 > ?f k2" and "k3 < length L"
          hence "k3 > k2" using f2_eq_k2 by simp
          have "k3 = ?k \<or> k3 = ?k + 1 \<or> (?f k3 = k3)" by auto
          then show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
          proof (elim disjE)
            assume "k3 = ?k"
            have "L ! ?k = l2_last" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! k3) = enq" using `k3 = ?k` True by simp
            thus ?thesis by simp
          next
            assume "k3 = ?k + 1"
            have "L ! (?k + 1) = bt_act" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! k3) = enq" using find_unique_index_prop[OF bt_idx_def] `k3 = ?k + 1` bt_act_def by simp
            thus ?thesis by simp
          next
            assume f_k3_eq: "?f k3 = k3"
            hence "k3 < length new_L" using `k3 < length L` len_eq by simp
            with `k3 > k2` prems(5) have "op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p" by simp
            moreover have "new_L ! k3 = L ! k3" using eq_nth[OF `k3 < length new_L`] f_k3_eq by simp
            ultimately show ?thesis by simp
          qed
        qed

        have hb_cond: "HB H (L ! (?f k1)) (L ! (?f k2))"
          using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp 

        have f1_lt_f2: "?f k1 < ?f k2"
          using "1.prems"(5)[unfolded lI7_D4_Deq_Deq_HB_list_def, rule_format, of "?f k1" "?f k2" p]
          using valid_f1 valid_f2 oper_f1 match_f2 term_cond_L prems(6) hb_cond
          by blast
        
        show "k1 < k2"
        proof -
          have "k2 > ?f k1" using f1_lt_f2 f2_eq_k2 by simp
          consider "k1 < ?k" | "k1 = ?k" | "k1 = ?k + 1" | "k1 > ?k + 1" by linarith
          then show ?thesis
          proof cases
            case 1 then show ?thesis using `k2 > ?f k1` by simp
          next
            case 2 then have "?f k1 = ?k + 1" by simp
                 hence "k2 > ?k + 1" using `k2 > ?f k1` by simp
                 thus ?thesis using 2 by simp
          next
            case 3 then have "?f k1 = ?k" by simp
                 hence "k2 > ?k" using `k2 > ?f k1` by simp
                 have "k2 \<noteq> ?k + 1" using f2_not_swapped f2_eq_k2 by simp
                 thus ?thesis using `k2 > ?k` 3 by simp
          next
            case 4 then show ?thesis using `k2 > ?f k1` by simp
          qed
        qed
      qed
      
      have mset_new_full: "mset new_L = mset (lin_seq s)" 
        using mset_new "1.prems"(6) by simp

      have ih_app: "lI7_D4_Deq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        using ih(1) do_modify True bt_idx_def
        using "1.prems"(1) "1.prems"(2) di_new hb_new lI7_D4_Deq_Deq_HB_new mset_new_full in_SA_new
        unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        by (metis (no_types, lifting) ih(12) not_None_eq option.collapse option.inject)
        
      thus ?thesis using step1 by simp

    next
      (* =================================================================== *)
      case False (* === Deq Cases === *)
      (* =================================================================== *)
      note not_enq = False

      have find_enq_valid: "find_last_enq l2 \<noteq> None"
        using do_modify False l2_not_nil unfolding should_modify_def l2_def remaining_def last_sa_pos_def l2_last_def
        using bt_idx_def case_optionE last_sa_pos_def remaining_def
        by fastforce
        
      then obtain l21 b_act l22 where l2_split: "find_last_enq l2 = Some (l21, b_act, l22)"
        by (cases "find_last_enq l2") auto
        
      define o1 where "o1 = hd l22"
      define ou where "ou = last l22"
      
      have l22_not_nil: "l22 \<noteq> []" using find_enq_valid l2_split False l2_not_nil
        unfolding find_last_enq_def
        using find_last_enq_props(1,2) l2_last_def l2_split
        by fastforce 
        
      have b_act_enq: "op_name b_act = enq"
        using l2_split by (simp add: find_last_enq_props(2)) 
        
      have o1_deq: "op_name o1 = deq"
        using l22_are_all_deq[OF l2_split l22_not_nil] o1_def l22_not_nil by (metis hd_in_set)
        
      have l22_deqs: "\<forall>x \<in> set l22. op_name x = deq"
        using l22_are_all_deq[OF l2_split l22_not_nil] by simp

      have L_split_c1: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
        using L_decomp find_last_enq_props(1)[OF l2_split] by auto 
        
      have c1_decomp: "L = (l1 @ l21) @ [b_act] @ [o1] @ (tl l22 @ [bt_act] @ l3)"
        using L_split_c1 l22_not_nil o1_def by (metis append.assoc append_Cons append_Nil hd_Cons_tl)

      define b_idx where "b_idx = length l1 + length l21"
      have b_idx_props: "L ! b_idx = b_act" "b_idx \<ge> length l1" "b_idx < length L"
        unfolding b_idx_def using L_split_c1 by (auto simp: nth_append)

      have all_after_l1_not_sa: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
      proof -
        have l1_fmt: "l1 = take (nat (last_sa_pos + 1)) L" using l1_def by simp
        define rest where "rest = remaining"
        have L_split_lemma: "L = l1 @ rest" unfolding rest_def remaining_def l1_def using append_take_drop_id by simp
        have rest_not_nil: "rest \<noteq> []" unfolding rest_def using bt_idx_valid bt_idx_def by auto 
        show ?thesis
          apply (rule l1_contains_all_SA_in_L)
          apply (rule "1.prems"(3)) apply (rule L_split_lemma) apply (rule rest_not_nil)
          apply (rule l1_fmt) apply (rule last_sa_pos_def) done
      qed

      have b_act_not_sa: "\<not> in_SA (op_val b_act) L"
        using all_after_l1_not_sa b_idx_props b_act_enq by auto

      have b_neq_bt: "b_act \<noteq> bt_act"
      proof
        assume eq: "b_act = bt_act"
        let ?idx_b = "length l1 + length l21"
        let ?idx_bt = "length l1 + length l21 + 1 + length l22"
        
        have valid_b: "?idx_b < length L" using L_split_c1 by auto
        have valid_bt: "?idx_bt < length L" using L_split_c1 by auto
        
        have nth_b: "L ! ?idx_b = b_act" using L_split_c1 by (auto simp: nth_append)
        have nth_bt: "L ! ?idx_bt = bt_act" using L_split_c1 by (auto simp: nth_append)
        
        have oper_bt: "op_name bt_act = enq"
          using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
          
        have "?idx_b = ?idx_bt"
        proof (rule same_enq_value_same_index[OF "1.prems"(3)])
          show "?idx_b < length L" using valid_b .
          show "?idx_bt < length L" using valid_bt .
          show "op_name (L ! ?idx_b) = enq" using nth_b b_act_enq by simp
          show "op_name (L ! ?idx_bt) = enq" using nth_bt oper_bt by simp
          show "op_val (L ! ?idx_b) = op_val (L ! ?idx_bt)" using nth_b nth_bt eq by simp
        qed
        
        thus False by simp
      qed

      have b_val_sets: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"
      proof -
        have "\<not> in_SA (op_val b_act) (lin_seq s)" using b_act_not_sa "1.prems"(7) by simp 
        moreover have "b_act \<in> set (lin_seq s)" using b_idx_props(3) b_idx_props(1) "1.prems"(6) by (metis nth_mem set_mset_mset) 
        ultimately show ?thesis using LinSeq_Enq_State_Mapping[OF sys_inv] b_act_enq SetA_implies_in_SA[OF sys_inv] by blast
      qed

      have b_act_active: "b_act \<in> active_enqs s"
      proof -
        have b_in_s: "b_act \<in> set (lin_seq s)" using b_idx_props(3) b_idx_props(1) "1.prems"(6) by (metis nth_mem set_mset_mset) 
        have not_sa_s: "\<not> in_SA (op_val b_act) (lin_seq s)" using b_act_not_sa "1.prems"(7) by simp
        show ?thesis using b_in_s b_act_enq not_sa_s non_SA_enqs_are_active sys_inv unfolding system_invariant_def by blast
      qed

      consider (c1) "HB H o1 bt_act"
             | (c2) "\<not> HB H o1 bt_act \<and> HB H b_act o1"
             | (c3) "\<not> HB H o1 bt_act \<and> \<not> HB H b_act o1"
        by blast
        
      then show ?thesis
      proof cases
        (* ----------------------------------------------------------------- *)
        case c1 (* === c1 === *)
        (* ----------------------------------------------------------------- *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"
        
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          using do_modify False c1 l2_split o1_def bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
          apply (subst modify_lin.simps)
          apply (simp add: Let_def case_prod_unfold)
          done
          
        have mset_new: "mset new_L = mset L"
          unfolding new_L_def c1_decomp by (simp add: ac_simps)
          
        have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
        have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto
        
        have hb_new: "HB_consistent new_L H"
        proof -
          have struct_match: "new_L = (l1 @ l21) @ [o1] @ [b_act] @ (tl l22 @ [bt_act] @ l3)"
            unfolding new_L_def by simp
          have "HB_consistent ((l1 @ l21) @ [o1] @ [b_act] @ (tl l22 @ [bt_act] @ l3)) H"
          proof (rule modify_step_c1_consistent[where s=s and L=L and H=H])
            show "system_invariant s" using sys_inv by simp
            show "HB_consistent L H" using "1.prems"(4) by blast
            show "H = his_seq s" using "1.prems"(1) by simp
            show "mset L = mset (lin_seq s)" using "1.prems"(6) by blast
            show "L = (l1 @ l21) @ [b_act] @ [o1] @ (tl l22 @ [bt_act] @ l3)" using c1_decomp by simp
            show "op_name b_act = enq" using b_act_enq by simp
            show "op_name o1 = deq" using o1_deq by simp
            show "bt_act \<in> set L" using bt_in_L by simp
            show "op_name bt_act = enq" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
            show "TypeBT s (op_val bt_act)" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def using "1.prems"(2) by auto
            show "happens_before o1 bt_act H" using c1 by (simp add: HB_def)
            show "b_act \<in> active_enqs s" using b_act_active by simp
            show "b_act \<noteq> bt_act" using b_neq_bt by simp
            show "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s" using b_val_sets by simp
          qed
          thus ?thesis using struct_match by simp
        qed

(* 🛡️ 2: , \<exists>h1 h2 *)
        have lI7_D4_Deq_Deq_HB_new: "lI7_D4_Deq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
        proof (unfold lI7_D4_Deq_Deq_HB_list_def, intro allI impI, elim conjE)
          fix k1 k2 p
          assume prems: "k1 < length new_L" "k2 < length new_L"
               "op_name (new_L ! k1) = deq" 
               "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
               "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
               "pc p = ''D4''" 
               "HB H (new_L ! k1) (new_L ! k2)"

          have op_new_k2: "op_name (new_L ! k2) = deq" using prems(4) by (simp add: mk_op_def op_name_def)
          have pid_new_k2: "op_pid (new_L ! k2) = p" using prems(4) by (simp add: mk_op_def op_pid_def)

          (* c1 : ?k ?k+1 *)
          let ?k = "length l1 + length l21"
          define f where "f i = (if i = ?k then ?k + 1 else if i = ?k + 1 then ?k else i)" for i
          
          have L_exp: "L = l1 @ l21 @ [b_act, o1] @ tl l22 @ [bt_act] @ l3" using c1_decomp by simp
          have new_L_exp: "new_L = l1 @ l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3" unfolding new_L_def by simp
          have len_eq: "length new_L = length L" using mset_new mset_eq_length by auto

          have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (f i)"
          proof -
            fix i assume i_lt: "i < length new_L"
            consider (lt) "i < ?k" | (eq1) "i = ?k" | (eq2) "i = ?k + 1" | (gt) "i > ?k + 1" by linarith
            then show "new_L ! i = L ! (f i)"
            proof cases
              case lt hence "f i = i" unfolding f_def by simp
              thus ?thesis using lt unfolding L_exp new_L_exp
                by (metis append_assoc length_append nth_append_left) 
            next
              case eq1 hence "f i = ?k + 1" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq1 by (simp add: nth_append)
            next
              case eq2 hence "f i = ?k" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq2 by (simp add: nth_append)
            next
              case gt hence "f i = i" unfolding f_def by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using gt by linarith+
              show ?thesis unfolding L_exp new_L_exp using a1 gt `f i = i` by (simp add: nth_append)
            qed
          qed

          (* c1 k1 < k2 *)
          show "k1 < k2"
          proof (cases "k2 = ?k")
            case True
            hence k2_is_o1: "new_L ! k2 = o1" using new_L_exp by (simp add: nth_append)
            have f2: "f k2 = ?k + 1" unfolding f_def using True by simp

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L"
              proof -
                have bnd: "?k + 1 < length L" using L_exp by simp
                have orig: "k1 < length L" using prems(1) len_eq by simp
                show ?thesis unfolding f_def using bnd orig by auto
              qed
              have v2: "f k2 < length L" using True f2 L_exp by simp
              have oper_f1: "op_name (L ! f k1) = deq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              
              have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (intro allI impI)
                fix k3 assume "f k2 < k3" "k3 < length L"
                hence "k3 > ?k + 1" using f2 by simp
                hence "f k3 = k3" unfolding f_def by simp
                thus "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
                  using prems(5) `k3 < length L` len_eq `k3 > ?k + 1` `k2 = ?k` eq_nth
                  by (metis add_lessD1)
              qed

              have hb_match: "HB H (L ! f k1) (L ! f k2)"
                using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp

              show ?thesis
                using "1.prems"(5)[unfolded lI7_D4_Deq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            have f1_bound: "f k1 < ?k + 1" using f1_lt_f2 f2 by simp

            show "k1 < k2"
            proof (cases "k1 < ?k")
              case True thus ?thesis using `k2 = ?k` by simp
            next
              case False
              have "k1 = ?k \<or> k1 = ?k + 1 \<or> k1 > ?k + 1" using False by linarith
              moreover
              { assume "k1 = ?k"
                hence "f k1 = ?k + 1" unfolding f_def by simp
                with f1_bound have False by simp
                hence ?thesis by simp }
              moreover
              { assume "k1 > ?k + 1"
                hence "f k1 = k1" unfolding f_def by simp
                with f1_bound have "k1 < ?k + 1" by simp
                with `k1 > ?k + 1` have False by simp
                hence ?thesis by simp }
              moreover
              { assume k1_is: "k1 = ?k + 1"
                have k1_is_b: "new_L ! k1 = b_act" using k1_is new_L_exp by (simp add: nth_append)
                have "op_name (new_L ! k1) = enq" using k1_is_b b_act_enq by simp
                with prems(3) have False by simp 
                hence ?thesis by simp }
              ultimately show ?thesis by blast
            qed

          next
            case False
            have k2_not_kp1: "k2 \<noteq> ?k + 1"
            proof
              assume "k2 = ?k + 1"
              hence "new_L ! k2 = b_act" using new_L_exp by (simp add: nth_append)
              hence "op_name (new_L ! k2) = enq" using b_act_enq by simp
              thus False using op_new_k2 by simp
            qed
            
            have f2_eq_k2: "f k2 = k2" unfolding f_def using False k2_not_kp1 by simp
            
            have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
            proof (intro allI impI)
              fix k3 assume "f k2 < k3" "k3 < length L"
              show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (cases "k3 = ?k")
                case True
                hence "L ! k3 = b_act" using L_exp by (simp add: nth_append)
                hence "op_name (L ! k3) = enq" using b_act_enq by simp
                thus ?thesis by simp
              next
                case False_inner: False
                have f_k3_valid: "f k3 < length new_L" using `k3 < length L` len_eq unfolding f_def
                  by (simp add: False_inner) 
                have "k2 < f k3"
                proof -
                  have "k2 < k3" using `f k2 < k3` f2_eq_k2 by simp
                  thus ?thesis using False_inner k2_not_kp1 unfolding f_def
                    using False by auto 
                qed
                have "L ! k3 = new_L ! (f k3)" using eq_nth[OF f_k3_valid] unfolding f_def by (auto split: if_splits)
                with prems(5)[rule_format, of "f k3"] f_k3_valid `k2 < f k3` 
                show ?thesis by simp
              qed
            qed

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L" using prems(1) len_eq L_exp unfolding f_def by (auto split: if_splits)              
              have v2: "f k2 < length L" using prems(2) len_eq L_exp unfolding f_def by (auto split: if_splits)
              have oper_f1: "op_name (L ! f k1) = deq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              have hb_match: "HB H (L ! f k1) (L ! f k2)" using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp
              show ?thesis
                using "1.prems"(5)[unfolded lI7_D4_Deq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            show "k1 < k2" using f1_lt_f2 f2_eq_k2 unfolding f_def using False k2_not_kp1 prems(2) by (auto split: if_splits)
          qed
        qed
        
        have mset_new_full: "mset new_L = mset (lin_seq s)" using mset_new "1.prems"(6) by simp

        have ih_app: "lI7_D4_Deq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        proof -
          define L_inner where "L_inner = take (nat (find_last_SA L + 1)) L @ l21 @ [hd l22] @ [b_act] @ tl l22 @ [drop (nat (find_last_SA L + 1)) L ! bt_idx] @ drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L)"
          
          have hd_l22: "hd l22 = o1" using l2_split by (simp add: o1_def)
          
          have new_L_eq_L_inner: "new_L = L_inner"
            unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def L_inner_def
            using hd_l22 by simp
            
          have p1_in: "data_independent L_inner" using di_new unfolding new_L_eq_L_inner .
          have p2_in: "HB_consistent L_inner H" using hb_new unfolding new_L_eq_L_inner .
          have p3_in: "lI7_D4_Deq_Deq_HB_list L_inner H pc (x_var s) (s_var s)" using lI7_D4_Deq_Deq_HB_new unfolding new_L_eq_L_inner .
          have p4_in: "mset L_inner = mset (lin_seq s)" using mset_new_full unfolding new_L_eq_L_inner .
          have p5_in: "\<forall>v. in_SA v L_inner = in_SA v (lin_seq s)" using in_SA_new unfolding new_L_eq_L_inner .

          have pre1: "should_modify L H bt_val" using do_modify .
          
          have pre2: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L + 1)) L)) = bt_idx"
            using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
            
          have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L + 1)) L))) \<noteq> enq"
            using c1 unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric]
            by (simp add: False)
            
          have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L)) = Some (l21, b_act, l22)"
            using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
            
          have pre5: "happens_before (hd l22) (drop (nat (find_last_SA L + 1)) L ! bt_idx) H"
            using c1 hd_l22 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp

          show ?thesis 
            unfolding new_L_eq_L_inner
            unfolding L_inner_def
            using ih(2) pre1 pre2 pre3 pre4 pre5 p1_in p2_in p3_in p4_in p5_in "1.prems"(1) "1.prems"(2) "1.prems"(8)
            unfolding L_inner_def
            by simp
        qed
          
        thus ?thesis using step1 by simp
        
      next
        (* ----------------------------------------------------------------- *)
        case c2 (* === c2 === *)
        (* ----------------------------------------------------------------- *)
        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"
        
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          using do_modify False c2 l2_split o1_def bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
          apply (subst modify_lin.simps)
          apply (simp add: Let_def case_prod_unfold)
          done
          
        have mset_new: "mset new_L = mset L"
          unfolding new_L_def L_split_c1 by (simp add: ac_simps)
          
        have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
        have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto

        have hb_new: "HB_consistent new_L H"
        proof -
          have "HB_consistent (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) H"
          proof (rule modify_step_c2_consistent[where s=s and L=L and H=H])
            show "system_invariant s" using sys_inv by simp
            show "HB_consistent L H" using "1.prems"(4) by blast
            show "H = his_seq s" using "1.prems"(1) by simp
            show "mset L = mset (lin_seq s)" using "1.prems"(6) by blast
            show "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3" using L_split_c1 by simp
            show "l22 \<noteq> []" using l22_not_nil by simp
            show "op_name bt_act = enq" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
            show "TypeBT s (op_val bt_act)" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def using "1.prems"(2) by auto
            show "bt_act \<in> set L" using bt_in_L by simp
            show "o1 = hd l22" using o1_def by simp
            show "op_name b_act = enq" using b_act_enq by simp
            show "b_act \<in> active_enqs s" using b_act_active by simp
            show "b_act \<noteq> bt_act" using b_neq_bt by simp
            show "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s" using b_val_sets by simp
            show "\<not> happens_before o1 bt_act H" using c2 by (simp add: HB_def)
            show "happens_before b_act o1 H" using c2 by (simp add: HB_def)
            show "\<forall>x\<in>set l22. op_name x = deq" using l22_deqs by simp
          qed
          thus ?thesis unfolding new_L_def by simp
        qed
          
        have lI7_D4_Deq_Deq_HB_new: "lI7_D4_Deq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
        proof (unfold lI7_D4_Deq_Deq_HB_list_def, intro allI impI, elim conjE)
          fix k1 k2 p
          assume prems: "k1 < length new_L" "k2 < length new_L"
               "op_name (new_L ! k1) = deq"
               "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
               "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
               "pc p = ''D4''" 
               "HB H (new_L ! k1) (new_L ! k2)"

          have op_new_k2: "op_name (new_L ! k2) = deq" using prems(4) by (simp add: mk_op_def op_name_def)
          have pid_new_k2: "op_pid (new_L ! k2) = p" using prems(4) by (simp add: mk_op_def op_pid_def)

          let ?k1 = "length l1 + length l21"
          let ?k2 = "?k1 + 1 + length l22"
          let ?f = "\<lambda>i. if i = ?k1 then ?k2 else if ?k1 < i \<and> i \<le> ?k2 then i - 1 else i"

          have L_exp: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3" using L_split_c1 by simp
          have new_L_exp: "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3" unfolding new_L_def by simp
          have len_eq: "length new_L = length L" using mset_new mset_eq_length by auto
          have bt_enq: "op_name bt_act = enq" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp

          have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (?f i)"
          proof -
            fix i assume i_lt: "i < length new_L"
            consider (lt) "i < ?k1" | (eq1) "i = ?k1" | (eq2) "i = ?k1 + 1" | (mid) "?k1 + 1 < i \<and> i \<le> ?k2" | (gt) "i > ?k2" by linarith
            then show "new_L ! i = L ! (?f i)"
            proof cases
              case lt
              hence fi_eq: "?f i = i" by simp
              have "new_L ! i = L ! i"
              proof (cases "i < length l1")
                case True thus ?thesis unfolding L_exp new_L_exp by (simp add: nth_append)
              next
                case False
                hence "i - length l1 < length l21" using lt by linarith
                thus ?thesis unfolding L_exp new_L_exp using False by (simp add: nth_append)
              qed
              thus ?thesis using fi_eq by simp
            next
              case eq1
              have f_val: "?f i = ?k2" using eq1 by simp
              have a1: "\<not> i < length l1" "i - length l1 = length l21" using eq1 by linarith+
              have part1: "new_L ! i = bt_act" unfolding new_L_exp using a1 by (simp add: nth_append)
              
              have b1: "\<not> ?f i < length l1" "\<not> ?f i - length l1 < length l21" "?f i - length l1 - length l21 = Suc (length l22)" using f_val by linarith+
              have part2: "L ! (?f i) = bt_act" unfolding L_exp using b1 by (simp add: nth_append)
              
              show ?thesis using part1 part2 by simp
            next
              case eq2
              have f_val: "?f i = ?k1" using eq2 by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" "i - length l1 - length l21 = Suc 0" using eq2 by linarith+
              have part1: "new_L ! i = b_act" unfolding new_L_exp using a1 by (simp add: nth_append)
              
              have b1: "\<not> ?f i < length l1" "?f i - length l1 = length l21" using f_val by linarith+
              have part2: "L ! (?f i) = b_act" unfolding L_exp using b1 by (simp add: nth_append)
              
              show ?thesis using part1 part2 by simp
            next
              case mid
              have f_val: "?f i = i - 1" using mid by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using mid by linarith+
              define m where "m = i - length l1 - length l21 - 2"
              have idx1: "i - length l1 - length l21 = Suc (Suc m)" unfolding m_def using mid by linarith
              have m_lt: "m < length l22" unfolding m_def using mid by linarith
              have part1: "new_L ! i = l22 ! m" unfolding new_L_exp using a1 idx1 m_lt by (simp add: nth_append)
              
              have b1: "\<not> ?f i < length l1" "\<not> ?f i - length l1 < length l21" using f_val mid by linarith+
              have idx2: "?f i - length l1 - length l21 = Suc m" unfolding m_def f_val using mid by linarith
              have part2: "L ! (?f i) = l22 ! m" unfolding L_exp using b1 idx2 m_lt by (simp add: nth_append)
              
              show ?thesis using part1 part2 by simp
            next
              case gt
              hence fi_eq: "?f i = i" by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using gt by linarith+
              define m where "m = i - length l1 - length l21 - length l22 - 2"
              have idx1: "i - length l1 - length l21 = Suc (Suc (length l22 + m))" unfolding m_def using gt by linarith
              have part1: "new_L ! i = l3 ! m" unfolding new_L_exp using a1 idx1 by (simp add: nth_append)
              
              have b1: "\<not> ?f i < length l1" "\<not> ?f i - length l1 < length l21" using gt fi_eq by linarith+
              have idx2: "?f i - length l1 - length l21 = Suc (length l22 + Suc m)" unfolding m_def fi_eq using gt by linarith
              have part2: "L ! (?f i) = l3 ! m" unfolding L_exp using b1 idx2 by (simp add: nth_append)
              
              show ?thesis using part1 part2 fi_eq by simp
            qed
          qed

          have k2_neq_k1: "k2 \<noteq> ?k1"
          proof
            assume "k2 = ?k1"
            hence "new_L ! k2 = bt_act" using new_L_exp by (simp add: nth_append)
            with op_new_k2 bt_enq show False by simp
          qed

          have L_last_deq: "\<forall>k3>?f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
          proof (intro allI impI)
            fix k3 assume k3_gt: "?f k2 < k3" and k3_len: "k3 < length L"
            show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
            proof (cases "k3 = ?k1 \<or> k3 = ?k2")
              case True
              thus ?thesis
              proof (cases "k3 = ?k1")
                case True hence "L ! k3 = b_act" using L_exp by (simp add: nth_append)
                thus ?thesis using b_act_enq by simp
              next
                case False with True have "k3 = ?k2" by simp
                hence "L ! k3 = bt_act" using L_exp by (simp add: nth_append)
                thus ?thesis using bt_enq by simp
              qed
            next
              case False
              define k3_new where "k3_new = (if ?k1 < k3 \<and> k3 < ?k2 then k3 + 1 else k3)"
              have k3_new_len: "k3_new < length new_L"
              proof -
                have k2_bound: "?k2 < length L" unfolding L_exp by simp
                show ?thesis 
                  unfolding k3_new_def using k3_len len_eq k2_bound False
                  by auto 
              qed
              have f_k3_new: "?f k3_new = k3" using False unfolding k3_new_def by auto
              have L_k3_eq: "L ! k3 = new_L ! k3_new" using eq_nth[OF k3_new_len] f_k3_new by simp

              have "k2 < k3_new"
              proof (cases "k2 < ?k1")
                case True
                hence f2: "?f k2 = k2" by auto
                from f2 k3_gt have "k2 < k3" by simp
                thus ?thesis unfolding k3_new_def using True by auto
              next
                case False_outer: False
                have k2_ge: "k2 > ?k1" using False_outer k2_neq_k1 by simp
                
                show ?thesis
                proof (cases "k2 \<le> ?k2")
                  case True
                  hence f2_shift: "?f k2 = k2 - 1" using k2_ge by auto
                  from f2_shift k3_gt have "k2 - 1 < k3" by simp
                  hence k3_ge: "k2 \<le> k3" by simp
                  
                  show ?thesis
                  proof (cases "k3_new = k3 + 1")
                    case True thus ?thesis using k3_ge by simp
                  next
                    case False_inner: False
                    have k3_no_shift: "k3_new = k3" using False_inner k3_new_def by auto 
                    
                    from `\<not> (k3 = ?k1 \<or> k3 = ?k2)` have k3_neq: "k3 \<noteq> ?k1" "k3 \<noteq> ?k2" by auto
                    hence "\<not> (?k1 < k3 \<and> k3 < ?k2)" 
                      using k3_no_shift unfolding k3_new_def by (auto split: if_splits)
                    with k3_ge k2_ge True have "k3 \<ge> ?k2" by simp
                    with k3_neq(2) have "k3 > ?k2" by simp
                    thus ?thesis unfolding k3_new_def using k2_ge True by auto
                  qed
                next
                  case False_gt: False
                  have k2_gt_k2: "k2 > ?k2" using False_gt by auto 
                  hence "?f k2 = k2" by auto
                  with k3_gt have "k2 < k3" by simp
                  thus ?thesis unfolding k3_new_def using False_gt by auto
                qed
              qed               
              thus ?thesis using prems(5)[rule_format, OF `k2 < k3_new` k3_new_len] L_k3_eq by simp
            qed
          qed

          have v1: "?f k1 < length L"
          proof -
             have bnd: "?k2 < length L" using L_exp by simp
             have orig: "k1 < length L" using prems(1) len_eq by simp
             show ?thesis using bnd orig by auto
          qed

          have v2: "?f k2 < length L"
          proof -
             have bnd: "?k2 < length L" using L_exp by simp
             have orig: "k2 < length L" using prems(2) len_eq by simp
             show ?thesis using bnd orig by auto
          qed

          have oper_f1: "op_name (L ! ?f k1) = deq" using prems(3) eq_nth[OF prems(1)] by simp
          have match_f2: "L ! ?f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
          
          have hb_match: "HB H (L ! ?f k1) (L ! ?f k2)"
            using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp 

          have f1_lt_f2: "?f k1 < ?f k2"
          proof -
            show ?thesis
              using "1.prems"(5)[unfolded lI7_D4_Deq_Deq_HB_list_def, rule_format, of "?f k1" "?f k2" p]
              using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match
              by blast
          qed

          show "k1 < k2"
          proof (cases "k2 < ?k1")
            case True
            hence "?f k2 = k2" by auto
            with f1_lt_f2 have "?f k1 < k2" by simp
            show ?thesis
            proof (cases "k1 = ?k1")
              case True hence "?f k1 = ?k2" by auto
              with `?f k1 < k2` have "?k2 < k2" by simp
              with True `k2 < ?k1` show ?thesis by simp
            next
              case False
              hence "?f k1 \<ge> k1 - 1" by auto
              with `?f k1 < k2` have "k1 - 1 < k2" by simp
              hence "k1 \<le> k2" by simp
              moreover have "k1 \<noteq> k2" using f1_lt_f2 by auto
              ultimately show ?thesis by simp
            qed
          next
            case False
            hence k2_ge: "k2 > ?k1" using k2_neq_k1 by simp
            show ?thesis
            proof (cases "k2 \<le> ?k2")
              case True
              hence f2_eq: "?f k2 = k2 - 1" using k2_ge by auto
              with f1_lt_f2 have f1_lt: "?f k1 < k2 - 1" by simp
              show ?thesis
              proof (cases "k1 = ?k1")
                case True hence "?f k1 = ?k2" by auto
                with f1_lt have "?k2 < k2 - 1" by simp
                with True show ?thesis by simp
              next
                case False
                hence "?f k1 \<ge> k1 - 1" by auto
                with f1_lt have "k1 - 1 < k2 - 1" by simp
                thus ?thesis by simp
              qed
            next
              case False
              hence "?f k2 = k2" by auto
              with f1_lt_f2 have f1_lt: "?f k1 < k2" by simp
              show ?thesis
              proof (cases "k1 = ?k1")
                case True
                hence "?f k1 = ?k2" by auto
                with f1_lt have "?k2 < k2" by simp
                thus ?thesis using True by simp
              next
                case False
                hence "?f k1 \<ge> k1 - 1" by auto
                with f1_lt have "k1 - 1 < k2" by simp
                hence "k1 \<le> k2" by simp
                moreover have "k1 \<noteq> k2" using f1_lt_f2 by auto
                ultimately show ?thesis by simp
              qed
            qed
          qed
        qed
        
        have mset_new_full: "mset new_L = mset (lin_seq s)" using mset_new "1.prems"(6) by simp

        have ih_app: "lI7_D4_Deq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        proof -
          (* c2 AST bt_act b_act *)
          define L_inner where "L_inner = take (nat (find_last_SA L + 1)) L @ l21 @ [drop (nat (find_last_SA L + 1)) L ! bt_idx] @ [b_act] @ l22 @ drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L)"
          
          have new_L_eq_L_inner: "new_L = L_inner"
            unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def L_inner_def
            by simp
            
          have p1_in: "data_independent L_inner" using di_new unfolding new_L_eq_L_inner .
          have p2_in: "HB_consistent L_inner H" using hb_new unfolding new_L_eq_L_inner .
          have p3_in: "lI7_D4_Deq_Deq_HB_list L_inner H pc (x_var s) (s_var s)" using lI7_D4_Deq_Deq_HB_new unfolding new_L_eq_L_inner .
          have p4_in: "mset L_inner = mset (lin_seq s)" using mset_new_full unfolding new_L_eq_L_inner .
          have p5_in: "\<forall>v. in_SA v L_inner = in_SA v (lin_seq s)" using in_SA_new unfolding new_L_eq_L_inner .

          have pre1: "\<not> \<not> should_modify L H bt_val" using do_modify by simp
          
          have pre2: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L + 1)) L)) = bt_idx"
            using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
            
          have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L + 1)) L))) \<noteq> enq"
            using False unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
            
          have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L)) = Some (l21, b_act, l22)"
            using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
            
          have hd_l22: "hd l22 = o1" using l2_split by (simp add: o1_def)
          
          have pre5: "\<not> happens_before (hd l22) (drop (nat (find_last_SA L + 1)) L ! bt_idx) H"
            using c2 hd_l22 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by (simp add: HB_def)
            
          have pre6: "happens_before b_act (hd l22) H"
            using c2 hd_l22 by (simp add: HB_def)

          show ?thesis 
            unfolding new_L_eq_L_inner
            unfolding L_inner_def
            using ih(3) pre1 pre2 pre3 pre4 pre5 pre6 p1_in p2_in p3_in p4_in p5_in "1.prems"(1) "1.prems"(2) "1.prems"(8)
            unfolding L_inner_def
            by simp
        qed
          
        thus ?thesis using step1 by simp
        
      next
        (* ----------------------------------------------------------------- *)
        case c3 (* === c3 === *)
        (* ----------------------------------------------------------------- *)
        define new_L where "new_L = l1 @ l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3"
        
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          using do_modify False c3 l2_split o1_def bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
          apply (subst modify_lin.simps)
          apply (simp add: Let_def case_prod_unfold)
          done
          
        have mset_new: "mset new_L = mset L"
          unfolding new_L_def c1_decomp by (simp add: ac_simps)
          
        have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
        have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto

        have hb_new: "HB_consistent new_L H"
        proof -
          have "HB_consistent (l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3) H"
          proof -
            note step_thm = modify_step_c3_new_consistent[where s=s and L=L and H=H]
            show ?thesis
              using sys_inv "1.prems"(4) "1.prems"(1) "1.prems"(6) c1_decomp
              using b_act_enq o1_deq bt_in_L find_unique_index_prop[OF bt_idx_def]
              using b_act_active b_neq_bt b_val_sets c3
              by (metis append_assoc bt_act_def ih(6) step_thm)
          qed
          thus ?thesis unfolding new_L_def by simp
        qed

        have lI7_D4_Deq_Deq_HB_new: "lI7_D4_Deq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
        proof (unfold lI7_D4_Deq_Deq_HB_list_def, intro allI impI, elim conjE)
          fix k1 k2 p
          assume prems: "k1 < length new_L" "k2 < length new_L"
               "op_name (new_L ! k1) = deq" 
               "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
               "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
               "pc p = ''D4'' " 
               "HB H (new_L ! k1) (new_L ! k2)"

          have op_new_k2: "op_name (new_L ! k2) = deq" using prems(4) by (simp add: mk_op_def op_name_def)
          have pid_new_k2: "op_pid (new_L ! k2) = p" using prems(4) by (simp add: mk_op_def op_pid_def)

          let ?k = "length l1 + length l21"
          define f where "f i = (if i = ?k then ?k + 1 else if i = ?k + 1 then ?k else i)" for i
          
          have L_exp: "L = l1 @ l21 @ [b_act, o1] @ tl l22 @ [bt_act] @ l3" using c1_decomp by simp
          have new_L_exp: "new_L = l1 @ l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3" unfolding new_L_def by simp
          have len_eq: "length new_L = length L" using mset_new mset_eq_length by auto

          have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (f i)"
          proof -
            fix i assume i_lt: "i < length new_L"
            consider (lt) "i < ?k" | (eq1) "i = ?k" | (eq2) "i = ?k + 1" | (gt) "i > ?k + 1" by linarith
            then show "new_L ! i = L ! (f i)"
            proof cases
              case lt hence "f i = i" unfolding f_def by simp
              thus ?thesis using lt unfolding L_exp new_L_exp
                by (metis append_assoc length_append nth_append_left) 
            next
              case eq1 hence "f i = ?k + 1" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq1 by (simp add: nth_append)
            next
              case eq2 hence "f i = ?k" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq2 by (simp add: nth_append)
            next
              case gt hence "f i = i" unfolding f_def by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using gt by linarith+
              show ?thesis unfolding L_exp new_L_exp using a1 gt `f i = i` by (simp add: nth_append)
            qed
          qed

          show "k1 < k2"
          proof (cases "k2 = ?k")
            case True
            hence k2_is_o1: "new_L ! k2 = o1" using new_L_exp by (simp add: nth_append)
            have f2: "f k2 = ?k + 1" unfolding f_def using True by simp

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L"
              proof -
                 have bnd: "?k + 1 < length L" using L_exp by simp
                 have orig: "k1 < length L" using prems(1) len_eq by simp
                 show ?thesis unfolding f_def using bnd orig by auto
              qed
              
              have v2: "f k2 < length L" using True f2 L_exp by simp
              have oper_f1: "op_name (L ! f k1) = deq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              
              have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (intro allI impI)
                fix k3 assume "f k2 < k3" "k3 < length L"
                hence "k3 > ?k + 1" using f2 by simp
                hence "f k3 = k3" unfolding f_def by simp
                thus "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
                  using prems(5) `k3 < length L` len_eq `k3 > ?k + 1` `k2 = ?k` eq_nth
                  by (metis add_lessD1) 
              qed

              have hb_match: "HB H (L ! f k1) (L ! f k2)"
                using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp 

              show ?thesis
                using "1.prems"(5)[unfolded lI7_D4_Deq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            have f1_bound: "f k1 < ?k + 1" using f1_lt_f2 f2 by simp

            show "k1 < k2"
            proof (cases "k1 < ?k")
              case True thus ?thesis using `k2 = ?k` by simp
            next
              case False
              have "k1 = ?k \<or> k1 = ?k + 1 \<or> k1 > ?k + 1" using False by linarith
              moreover
              { assume "k1 = ?k"
                hence "f k1 = ?k + 1" unfolding f_def by simp
                with f1_bound have False by simp
                hence ?thesis by simp }
              moreover
              { assume "k1 > ?k + 1"
                hence "f k1 = k1" unfolding f_def by simp
                with f1_bound have "k1 < ?k + 1" by simp
                with `k1 > ?k + 1` have False by simp
                hence ?thesis by simp }
              moreover
              { assume k1_is: "k1 = ?k + 1"
                have k1_is_b: "new_L ! k1 = b_act" using k1_is new_L_exp by (simp add: nth_append)
                have "op_name (new_L ! k1) = enq" using k1_is_b b_act_enq by simp
                with prems(3) have False by simp 
                hence ?thesis by simp }
              ultimately show ?thesis by blast
            qed

          next
            case False
            have k2_not_kp1: "k2 \<noteq> ?k + 1"
            proof
              assume "k2 = ?k + 1"
              hence "new_L ! k2 = b_act" using new_L_exp by (simp add: nth_append)
              hence "op_name (new_L ! k2) = enq" using b_act_enq by simp
              thus False using op_new_k2 by simp
            qed
            
            have f2_eq_k2: "f k2 = k2" unfolding f_def using False k2_not_kp1 by simp
            
            have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
            proof (intro allI impI)
              fix k3 assume "f k2 < k3" "k3 < length L"
              show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (cases "k3 = ?k")
                case True
                hence "L ! k3 = b_act" using L_exp by (simp add: nth_append)
                hence "op_name (L ! k3) = enq" using b_act_enq by simp
                thus ?thesis by simp
              next
                case False_inner: False
                have f_k3_valid: "f k3 < length new_L" using `k3 < length L` len_eq unfolding f_def
                  using False_inner by auto 
                have "k2 < f k3"
                proof -
                  have "k2 < k3" using `f k2 < k3` f2_eq_k2 by simp
                  thus ?thesis using False_inner k2_not_kp1 unfolding f_def
                    using False by auto 
                qed
                have "L ! k3 = new_L ! (f k3)" using eq_nth[OF f_k3_valid] unfolding f_def by (auto split: if_splits)
                with prems(5)[rule_format, of "f k3"] f_k3_valid `k2 < f k3` 
                show ?thesis by simp
              qed
            qed

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L" using prems(1) len_eq L_exp unfolding f_def by (auto split: if_splits)
              have v2: "f k2 < length L" using prems(2) len_eq L_exp unfolding f_def by (auto split: if_splits)
              have oper_f1: "op_name (L ! f k1) = deq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              have hb_match: "HB H (L ! f k1) (L ! f k2)" using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp
              show ?thesis
                using "1.prems"(5)[unfolded lI7_D4_Deq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            show "k1 < k2" using f1_lt_f2 f2_eq_k2 unfolding f_def using False k2_not_kp1 prems(2) by (auto split: if_splits)
          qed
        qed

        have mset_new_full: "mset new_L = mset (lin_seq s)" using mset_new "1.prems"(6) by simp

        have ih_app: "lI7_D4_Deq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        proof -
          define L_inner where "L_inner = take (nat (find_last_SA L + 1)) L @ l21 @ [hd l22] @ [b_act] @ tl l22 @ [drop (nat (find_last_SA L + 1)) L ! bt_idx] @ drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L)"
          
          have hd_l22: "hd l22 = o1" using l2_split by (simp add: o1_def)
          
          have new_L_eq_L_inner: "new_L = L_inner"
            unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def L_inner_def
            using hd_l22 by simp
            
          have p1_in: "data_independent L_inner" using di_new unfolding new_L_eq_L_inner .
          have p2_in: "HB_consistent L_inner H" using hb_new unfolding new_L_eq_L_inner .
          have p3_in: "lI7_D4_Deq_Deq_HB_list L_inner H pc (x_var s) (s_var s)" using lI7_D4_Deq_Deq_HB_new unfolding new_L_eq_L_inner .
          have p4_in: "mset L_inner = mset (lin_seq s)" using mset_new_full unfolding new_L_eq_L_inner .
          have p5_in: "\<forall>v. in_SA v L_inner = in_SA v (lin_seq s)" using in_SA_new unfolding new_L_eq_L_inner .

          have pre1: "\<not> \<not> should_modify L H bt_val" using do_modify by simp
          have pre2: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L + 1)) L)) = bt_idx"
            using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L + 1)) L))) \<noteq> enq"
            using False unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L)) = Some (l21, b_act, l22)"
            using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          
          have pre5: "\<not> happens_before (hd l22) (drop (nat (find_last_SA L + 1)) L ! bt_idx) H"
            using c3 hd_l22 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by (simp add: HB_def)
          have pre6: "\<not> happens_before b_act (hd l22) H"
            using c3 hd_l22 by (simp add: HB_def)

          have fact_o1: "o1 = hd l22"
            using o1_def by simp

          have fact_the_enq: "the (find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L))) = (l21, b_act, l22)"
            using pre4 by simp

          have fact_list_align: "drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L) = drop (Suc (bt_idx + nat (find_last_SA L + 1))) L"
            by auto

          show ?thesis
            unfolding new_L_eq_L_inner L_inner_def fact_o1
            using ih(4) pre1 pre2 pre3 pre4 pre5 pre6
            using p1_in[unfolded L_inner_def fact_o1] 
            using p2_in[unfolded L_inner_def fact_o1] 
            using p3_in[unfolded L_inner_def fact_o1] 
            using p4_in[unfolded L_inner_def fact_o1] 
            using p5_in[unfolded L_inner_def fact_o1] 
            using "1.prems"(1) "1.prems"(2) "1.prems"(8)
            using fact_the_enq fact_list_align hd_l22
            by simp
        qed
          
        thus ?thesis using step1 by simp
      qed
    qed
  qed
qed

(* ========================================================================= *)
(* 🚀 Sorry : modify_preserves_lI7_D4_Deq_Deq_HB (5 ) *)
(* ========================================================================= *)
lemma modify_preserves_lI7_D4_Deq_Deq_HB:
  assumes INV: "system_invariant s"
    and q_in_SetB_raw: "q_val \<in> SetB s"
    and q_not_bot: "q_val \<noteq> BOT"
    and q_val_def: "q_val = Q_arr s (j_var s p)"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                                then modify_lin (lin_seq s) (his_seq s) q_val
                                else lin_seq s)"
    and s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and his_eq: "his_seq s' = his_seq s"
    and pc_s': "program_counter s' = (program_counter s)(p := ''D4'')"
    and pc_s: "program_counter s p = ''D3''"
    and lI8_D3_Deq_Returned_s: "\<forall>p. program_counter s p = ''D3'' \<longrightarrow> 
                    (\<forall>k < length (lin_seq s). 
                      (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = p) \<longrightarrow> 
                      DeqRetInHis s p (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))"
    (* , q \<noteq> p *)
    and x_eq: "\<forall>q. q \<noteq> p \<longrightarrow> x_var s' q = x_var s q"
    and sn_eq: "\<forall>q. q \<noteq> p \<longrightarrow> s_var s' q = s_var s q"
  shows "lI7_D4_Deq_Deq_HB s'"
proof -
  (* Step 1: 1. basic facts ( 5 ) *)
  let ?L = "lin_seq s" let ?H = "his_seq s" 
  let ?pc = "\<lambda>p. program_counter s p"
  let ?xv = "\<lambda>p. x_var s p" let ?sv = "\<lambda>p. s_var s p"
  
  have di: "data_independent ?L" using INV unfolding system_invariant_def by auto
  have hb_cons: "HB_consistent ?L ?H" using INV unfolding system_invariant_def lI3_HB_Ret_Lin_Sync_def
    by (meson HB_Act_def HB_consistent_def) 
  have orig_list: "lI7_D4_Deq_Deq_HB_list ?L ?H ?pc ?xv ?sv" using INV lI7_D4_Deq_Deq_HB_implies_list unfolding system_invariant_def lI7_D4_Deq_Deq_HB_def by auto
  have hI15_Deq_Result_Exclusivity: "hI15_Deq_Result_Exclusivity s" using INV unfolding system_invariant_def by auto

  (* Step 2: 2. q_in_SetB *)
  have q_in_SetB: "q_val \<in> SetB s"
  proof -
    define jp where "jp = j_var s p"
    have jp_less: "jp < l_var s p" using INV pc_s unfolding system_invariant_def sI6_D3_Scan_Pointers_def
      using jp_def by blast 
    hence q_val_sym: "Q_arr s jp = q_val" using q_val_def jp_def by simp
    with q_not_bot have "Q_arr s jp \<noteq> BOT" by simp
    hence "InQBack s q_val" using INV jp_less unfolding system_invariant_def sI8_Q_Qback_Sync_def jp_def
      by (metis InQBack_def q_val_def)
    thus ?thesis 
      unfolding SetB_def TypeB_def using q_val_sym pc_s q_not_bot
      using InQBack_non_BOT_implies_Val
      using QHas_def SetB_def q_in_SetB_raw by blast 
  qed

  (* Step 3: 3. base_lin lI7_D4_Deq_Deq_HB_list *)
  have base_list_prop: "lI7_D4_Deq_Deq_HB_list base_lin ?H ?pc ?xv ?sv"
  proof (cases "should_modify ?L ?H q_val")
    case False thus ?thesis using orig_list base_def by simp
  next
    case True
    have bt: "TypeBT s q_val"
    proof -
      define jp where "jp = j_var s p"
      have idx_is_jp: "Idx s q_val = jp"
        using q_in_SetB q_val_def jp_def unfolding SetB_def TypeB_def
        by (metis sI10_Qback_Unique_Vals_def AtIdx_def D3_Q_at_j INV Idx_implies_AtIdx
            InQBack_def pc_s q_not_bot system_invariant_def) 
      have q_in_back: "\<exists>k. Qback_arr s k = q_val"
        using q_in_SetB unfolding SetB_def TypeB_def InQBack_def QHas_def
        by (metis D3_Q_at_j INV pc_s q_not_bot q_val_def) 
      have path_bot: "\<forall>k < Idx s q_val. k \<ge> j_var s p \<longrightarrow> Q_arr s k = BOT"
        using idx_is_jp jp_def by auto 
      show ?thesis
        unfolding TypeBT_def
        using q_in_SetB q_not_bot pc_s q_val_def q_in_back idx_is_jp
        unfolding SetB_def TypeB_def InQBack_def
        by (metis sI6_D3_Scan_Pointers_def INV QHas_def jp_def order_refl path_bot system_invariant_def)
    qed

    have eq_facts: "?H = his_seq s" "mset ?L = mset (lin_seq s)" 
                   "\<forall>v. in_SA v ?L = in_SA v (lin_seq s)" "?pc = (\<lambda>p. program_counter s p)" 
      by simp_all

    have final_list: "lI7_D4_Deq_Deq_HB_list (modify_lin ?L ?H q_val) ?H ?pc ?xv ?sv"
      by (rule lI7_D4_Deq_Deq_HB_list_modify[OF INV eq_facts(1) bt di hb_cons orig_list eq_facts(2-4)])

    show ?thesis using True final_list base_def by simp
  qed

  (* Step 4: 4.  *)
  show "lI7_D4_Deq_Deq_HB s'" unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
    apply (intro allI impI)
    subgoal premises prems for k1 k2 q
    proof -
      (* , *)
      have k1_bound: "k1 < length (lin_seq s')" and
           k2_bound: "k2 < length (lin_seq s')" and
           k1_deq: "op_name (lin_seq s' ! k1) = deq" and
           k2_match: "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)" and
           k2_last_deq: "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q" and
           q_D4: "program_counter s' q = ''D4''" and
           hb_k1_k2: "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
        using prems by auto

      show ?thesis
      proof (cases "q = p")
        case True
        (* \<forall>k3>k2 k2 lI8_D3_Deq_Returned *)
        have k2_is_last: "k2 = length base_lin"
        proof (rule ccontr)
          assume "k2 \<noteq> length base_lin"
          with k2_bound s'_lin_def have k2_less: "k2 < length base_lin" by auto
          let ?k3 = "length base_lin"
          have "?k3 > k2" using k2_less by simp
          have "?k3 < length (lin_seq s')" using s'_lin_def by simp
          have "lin_seq s' ! ?k3 = mk_op deq q_val p (s_var s p)"
            using s'_lin_def by (simp add: nth_append)
          hence "op_name (lin_seq s' ! ?k3) = deq \<and> op_pid (lin_seq s' ! ?k3) = p"
            unfolding mk_op_def op_name_def op_pid_def by simp
          with k2_last_deq `?k3 > k2` `?k3 < length (lin_seq s')` True show False
            by auto 
        qed

        have k1_not_last: "k1 < length base_lin"
        proof (rule ccontr)
          assume "\<not> k1 < length base_lin"
          hence k1_last: "k1 = length base_lin" using k1_bound s'_lin_def by auto
          have act_props: "op_val (lin_seq s' ! k1) = q_val" 
                          "op_pid (lin_seq s' ! k1) = p"
                          "op_name (lin_seq s' ! k1) = deq"
                          "op_ssn (lin_seq s' ! k1) = s_var s p"
            using k1_last s'_lin_def mk_op_def by (auto simp: op_val_def op_pid_def op_name_def op_ssn_def)
            
          have "DeqRetInHis s p q_val (s_var s p)" 
            using hb_k1_k2 k1_last s'_lin_def True his_eq act_props
            unfolding DeqRetInHis_def match_ret_def HB_Act_def HB_def Let_def by force
            
          with hI15_Deq_Result_Exclusivity q_in_SetB show False 
            unfolding hI15_Deq_Result_Exclusivity_def SetB_def InQBack_def using q_val_def by blast
        qed

        from k1_not_last k2_is_last show ?thesis by simp
        
      next
        case False
        (* q \<noteq> p *)
        have k2_old: "k2 < length base_lin"
        proof (rule ccontr)
          assume "\<not> k2 < length base_lin"
          hence k2_last: "k2 = length base_lin" using k2_bound s'_lin_def by auto
          have "op_pid (lin_seq s' ! k2) = p"
            using k2_last s'_lin_def mk_op_def by (simp add: nth_append op_pid_def)
          moreover have "op_pid (lin_seq s' ! k2) = q"
            using k2_match mk_op_def by (simp add: op_pid_def)
          ultimately show False using False by simp
        qed

        have k1_old: "k1 < length base_lin"
        proof (rule ccontr)
          assume "\<not> k1 < length base_lin"
          hence k1_last: "k1 = length base_lin" using k1_bound s'_lin_def by auto
          have act_props: "op_val (lin_seq s' ! k1) = q_val" 
                          "op_pid (lin_seq s' ! k1) = p"
                          "op_name (lin_seq s' ! k1) = deq"
                          "op_ssn (lin_seq s' ! k1) = s_var s p"
            using k1_last s'_lin_def mk_op_def by (auto simp: op_val_def op_pid_def op_name_def op_ssn_def)
            
          have "DeqRetInHis s p q_val (s_var s p)" 
            using hb_k1_k2 k1_last s'_lin_def False his_eq act_props
            unfolding DeqRetInHis_def match_ret_def HB_Act_def HB_def Let_def by force
            
          with hI15_Deq_Result_Exclusivity q_in_SetB show False 
            unfolding hI15_Deq_Result_Exclusivity_def SetB_def InQBack_def using q_val_def by blast 
        qed

        (* 2: lI7_D4_Deq_Deq_HB_append_deq_other, , *)
        have "k1 < k2"
        proof -
          have base_unfold: "\<forall>k1' k2' q'. k1' < length base_lin \<and> k2' < length base_lin \<and>
                op_name (base_lin ! k1') = deq \<and> 
                base_lin ! k2' = mk_op deq (x_var s q') q' (s_var s q') \<and>
                (\<forall>k3>k2'. k3 < length base_lin \<longrightarrow> op_name (base_lin ! k3) \<noteq> deq \<or> op_pid (base_lin ! k3) \<noteq> q') \<and> 
                program_counter s q' = ''D4'' \<and>
                HB ?H (base_lin ! k1') (base_lin ! k2') \<longrightarrow> k1' < k2'"
            using base_list_prop unfolding lI7_D4_Deq_Deq_HB_list_def by blast
          
          have "k1 < length base_lin" using k1_old .
          have "k2 < length base_lin" using k2_old .
          have "op_name (base_lin ! k1) = deq" 
            using k1_deq k1_old s'_lin_def by (simp add: nth_append)
            
          have "base_lin ! k2 = mk_op deq (x_var s q) q (s_var s q)"
          proof -
            have "lin_seq s' ! k2 = base_lin ! k2" using k2_old s'_lin_def by (simp add: nth_append)
            moreover have "x_var s' q = x_var s q" using x_eq False by simp
            moreover have "s_var s' q = s_var s q" using sn_eq False by simp
            ultimately show ?thesis using k2_match by simp
          qed

          have "\<forall>k3>k2. k3 < length base_lin \<longrightarrow> op_name (base_lin ! k3) \<noteq> deq \<or> op_pid (base_lin ! k3) \<noteq> q"
          proof (intro allI impI)
            fix k3 assume "k2 < k3" "k3 < length base_lin"
            hence "k3 < length (lin_seq s')" using s'_lin_def by auto
            moreover have "base_lin ! k3 = lin_seq s' ! k3" using `k3 < length base_lin` s'_lin_def by (simp add: nth_append)
            ultimately show "op_name (base_lin ! k3) \<noteq> deq \<or> op_pid (base_lin ! k3) \<noteq> q"
              using k2_last_deq `k2 < k3` by auto
          qed

          have "program_counter s q = ''D4''" using pc_s' False q_D4 by auto
          
          have "HB ?H (base_lin ! k1) (base_lin ! k2)"
            using hb_k1_k2 his_eq s'_lin_def k1_old k2_old by (simp add: nth_append)
            
          with base_unfold show ?thesis 
            using `k1 < length base_lin` `k2 < length base_lin` 
                  `op_name (base_lin ! k1) = deq`
                  `base_lin ! k2 = mk_op deq (x_var s q) q (s_var s q)`
                  `\<forall>k3>k2. k3 < length base_lin \<longrightarrow> op_name (base_lin ! k3) \<noteq> deq \<or> op_pid (base_lin ! k3) \<noteq> q`
                  `program_counter s q = ''D4''`
            by blast
        qed
        thus ?thesis .
      qed
    qed
    done
qed

(* Proof note. *)
lemma lI10_D4_Enq_Deq_HB_implies_list:
  assumes "lI10_D4_Enq_Deq_HB s"
  shows "lI10_D4_Enq_Deq_HB_list (lin_seq s) (his_seq s) (program_counter s) (x_var s) (s_var s)"
  using assms unfolding lI10_D4_Enq_Deq_HB_list_def lI10_D4_Enq_Deq_HB_def
  by blast 

(* , *)
lemma list_implies_lI10_D4_Enq_Deq_HB:
  assumes "lI10_D4_Enq_Deq_HB_list (lin_seq s) (his_seq s) (program_counter s) (x_var s) (s_var s)"
  shows "lI10_D4_Enq_Deq_HB s"
  using assms unfolding lI10_D4_Enq_Deq_HB_list_def lI10_D4_Enq_Deq_HB_def
  by blast 

(* ========================================================================= *)
(* modify_lin lI10_D4_Enq_Deq_HB_list (SSN ) *)
(* lI7_D4_Deq_Deq_HB_list 100% , enq D4 deq *)
(* ========================================================================= *)
lemma lI10_D4_Enq_Deq_HB_list_modify:
  assumes sys_inv: "system_invariant s"
  shows "H = his_seq s \<Longrightarrow> 
         TypeBT s bt_val \<Longrightarrow> 
         data_independent L \<Longrightarrow> 
         HB_consistent L H \<Longrightarrow> 
         lI10_D4_Enq_Deq_HB_list L H pc (x_var s) (s_var s) \<Longrightarrow> 
         mset L = mset (lin_seq s) \<Longrightarrow> 
         (\<forall>v. in_SA v L \<longleftrightarrow> in_SA v (lin_seq s)) \<Longrightarrow> 
         pc = program_counter s \<Longrightarrow>  
         lI10_D4_Enq_Deq_HB_list (modify_lin L H bt_val) H pc (x_var s) (s_var s)"
proof (induct L H bt_val rule: modify_lin.induct)
  case (1 L H bt_val)
  note ih = this
  
  from sys_inv have wf_s: "hI7_His_WF s" and order_s: "hI6_SSN_Order s" and unique_s: "hI5_SSN_Unique s" 
    unfolding system_invariant_def by auto

  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    have "modify_lin L H bt_val = L" 
      using False by (subst modify_lin.simps, auto simp: Let_def)
    thus ?thesis using "1.prems"(5) by simp
  next
    case True
    note do_modify = True
    
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define remaining where "remaining = drop (nat (last_sa_pos + 1)) L"
    
    have search_not_none: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
      using do_modify unfolding should_modify_def Let_def remaining_def last_sa_pos_def
      by (metis option.simps(4))
      
    then obtain bt_idx where bt_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx" 
      by auto
      
    have bt_idx_valid: "bt_idx < length remaining"
      by (rule find_unique_index_Some_less_length[OF bt_idx_def])
      
    define l1 where "l1 = take (nat (last_sa_pos + 1)) L"
    define l2 where "l2 = take bt_idx remaining"
    define l3 where "l3 = drop (bt_idx + 1) remaining"
    define bt_act where "bt_act = remaining ! bt_idx"
    define l2_last where "l2_last = last l2"

    have l2_not_nil: "l2 \<noteq> []"
    proof
      assume eq_nil: "l2 = []"
      have "remaining \<noteq> []" using bt_idx_valid by auto
      with eq_nil l2_def have "bt_idx = 0" by (metis take_eq_Nil)
      with do_modify show False 
        unfolding should_modify_def Let_def l2_def remaining_def last_sa_pos_def
        using bt_idx_def last_sa_pos_def remaining_def by force 
    qed

    have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
      using bt_idx_valid l2_def l3_def bt_act_def
      using id_take_nth_drop by fastforce
      
    have L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
      unfolding l1_def remaining_def using remaining_decomp
      using remaining_def by force 

    have bt_in_L: "bt_act \<in> set L"
      using L_decomp by auto

    show ?thesis
    proof (cases "op_name l2_last = enq")
      (* =================================================================== *)
      case True (* === c0: Enq Case === *)
      (* =================================================================== *)
      define ll2 where "ll2 = butlast l2"
      define new_L where "new_L = l1 @ ll2 @ [bt_act] @ [l2_last] @ l3"
      
      have l2_struct: "l2 = ll2 @ [l2_last]" using l2_not_nil ll2_def
        using l2_last_def by auto 
      
      have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
        using do_modify True bt_idx_def l2_not_nil
        unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        apply (subst modify_lin.simps)
        apply (auto simp: Let_def split: option.splits if_splits)
        done
        
      have mset_new: "mset new_L = mset L"
        using L_decomp l2_not_nil ll2_def new_L_def by (metis case1 l2_last_def)
        
      have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
      have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto
      
      have bt_type: "TypeBT s (op_val bt_act)" 
        using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def 
        using "1.prems"(2) by auto
      
      have hb_new: "HB_consistent new_L H"
        unfolding new_L_def
      proof (rule modify_step_c0_consistent[where s=s and L=L and H=H])
        show "system_invariant s" using sys_inv by simp
        show "HB_consistent L H" using "1.prems"(4) by blast
        show "H = his_seq s" using "1.prems"(1) by simp
        show "data_independent L" using "1.prems"(3) by blast
        show "mset L = mset (lin_seq s)" using "1.prems"(6) by blast
        show "\<forall>v. in_SA v L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) by blast
        show "L = l1 @ l2 @ [bt_act] @ l3" using L_decomp by simp
        show "l2 = ll2 @ [l2_last]" using l2_struct by simp
        show "last_sa_pos = find_last_SA L" using last_sa_pos_def by simp
        show "l1 = take (nat (last_sa_pos + 1)) L" using l1_def by simp
        show "op_name l2_last = enq" using True by simp
        show "op_name bt_act = enq" 
          using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
        show "TypeBT s (op_val bt_act)" using bt_type by simp
      qed

      have lI10_D4_Enq_Deq_HB_new: "lI10_D4_Enq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
      proof (unfold lI10_D4_Enq_Deq_HB_list_def, intro allI impI, elim conjE)
        fix k1 k2 p
        assume prems: "k1 < length new_L" "k2 < length new_L"
           "op_name (new_L ! k1) = enq" 
           "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
           "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
           "pc p = ''D4''" 
           "HB H (new_L ! k1) (new_L ! k2)"

        have op_new_k2: "op_name (new_L ! k2) = deq" using prems(4) by (simp add: mk_op_def op_name_def)
        have pid_new_k2: "op_pid (new_L ! k2) = p" using prems(4) by (simp add: mk_op_def op_pid_def)

        let ?k = "length l1 + length ll2"
        define f where "f i = (if i = ?k then ?k + 1 else if i = ?k + 1 then ?k else i)" for i
        
        have L_exp: "L = l1 @ ll2 @ l2_last # bt_act # l3" using L_decomp l2_struct by auto
        have new_L_exp: "new_L = l1 @ ll2 @ bt_act # l2_last # l3" using new_L_def by auto
        
        have len_L: "length L = length l1 + length ll2 + 2 + length l3" using L_exp by simp
        have len_eq: "length new_L = length L" using mset_new by (metis mset_eq_length)
        
        have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (f i)"
        proof -
          fix i assume i_lt: "i < length new_L"
          consider (lt) "i < ?k" | (eq1) "i = ?k" | (eq2) "i = ?k + 1" | (gt) "i > ?k + 1" by linarith
          then show "new_L ! i = L ! (f i)"
          proof cases
            case lt
            hence fi_eq: "f i = i" unfolding f_def by simp
            have "new_L ! i = L ! i"
            proof (cases "i < length l1")
              case True thus ?thesis unfolding L_exp new_L_exp by (simp add: nth_append)
            next
              case False
              hence "i - length l1 < length ll2" using lt by linarith
              thus ?thesis unfolding L_exp new_L_exp using False by (simp add: nth_append)
            qed
            thus ?thesis using fi_eq by simp
          next
            case eq1
            have f_val: "f i = ?k + 1" unfolding f_def using eq1 by simp
            have a1: "\<not> i < length l1" "i - length l1 = length ll2" using eq1 by linarith+
            have part1: "new_L ! i = bt_act" unfolding new_L_exp using a1 by (simp add: nth_append)
            have b1: "\<not> f i < length l1" "f i - length l1 = Suc (length ll2)" using f_val by linarith+
            have part2: "L ! (f i) = bt_act" unfolding L_exp using b1 by (simp add: nth_append)
            show ?thesis using part1 part2 by simp
          next
            case eq2
            have f_val: "f i = ?k" unfolding f_def using eq2 by simp
            have a1: "\<not> i < length l1" "i - length l1 = Suc (length ll2)" using eq2 by linarith+
            have part1: "new_L ! i = l2_last" unfolding new_L_exp using a1 by (simp add: nth_append)
            have b1: "\<not> f i < length l1" "f i - length l1 = length ll2" using f_val by linarith+
            have part2: "L ! (f i) = l2_last" unfolding L_exp using b1 by (simp add: nth_append)
            show ?thesis using part1 part2 by simp
          next
            case gt
            hence fi_eq: "f i = i" unfolding f_def by simp
            have a1: "\<not> i < length l1" "\<not> i - length l1 < length ll2" using gt by linarith+
            define m where "m = i - length l1 - length ll2 - 2"
            have idx_eq: "i - length l1 - length ll2 = Suc (Suc m)" unfolding m_def using gt by linarith
            have part1: "new_L ! i = l3 ! m" unfolding new_L_exp using a1 idx_eq by (simp add: nth_append)
            have part2: "L ! i = l3 ! m" unfolding L_exp using a1 idx_eq by (simp add: nth_append)
            show ?thesis using part1 part2 fi_eq by simp
          qed
        qed
        
        have valid_f1: "f k1 < length L" using prems(1) len_eq len_L unfolding f_def by auto
        have valid_f2: "f k2 < length L" using prems(2) len_eq len_L unfolding f_def by auto
        
        have oper_f1: "op_name (L ! (f k1)) = enq" using prems(3) eq_nth[OF prems(1)] by simp
        have match_f2: "L ! (f k2) = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
        
        have f2_not_swapped: "f k2 \<noteq> ?k \<and> f k2 \<noteq> ?k + 1"
        proof (rule ccontr)
          assume "\<not> (f k2 \<noteq> ?k \<and> f k2 \<noteq> ?k + 1)"
          hence "f k2 = ?k \<or> f k2 = ?k + 1" by auto
          thus False
          proof
            assume "f k2 = ?k"
            have "L ! ?k = l2_last" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! (f k2)) = enq" using True `f k2 = ?k` by simp
            thus False using match_f2 by (simp add: mk_op_def op_name_def)
          next
            assume "f k2 = ?k + 1"
            have "L ! (?k + 1) = bt_act" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! (f k2)) = enq" using find_unique_index_prop[OF bt_idx_def] `f k2 = ?k + 1`
              using bt_act_def by fastforce 
            thus False using match_f2 by (simp add: mk_op_def op_name_def)
          qed
        qed
        hence f2_eq_k2: "f k2 = k2" unfolding f_def by (auto split: if_splits)
        
        have term_cond_L: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
        proof (intro allI impI)
          fix k3 assume "k3 > f k2" and "k3 < length L"
          hence "k3 > k2" using f2_eq_k2 by simp
          have "k3 = ?k \<or> k3 = ?k + 1 \<or> (f k3 = k3)" unfolding f_def by auto
          then show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
          proof (elim disjE)
            assume "k3 = ?k"
            have "L ! ?k = l2_last" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! k3) = enq" using `k3 = ?k` True by simp
            thus ?thesis by simp
          next
            assume "k3 = ?k + 1"
            have "L ! (?k + 1) = bt_act" using L_decomp l2_struct by (simp add: nth_append)
            hence "op_name (L ! k3) = enq" using find_unique_index_prop[OF bt_idx_def] `k3 = ?k + 1` bt_act_def by simp
            thus ?thesis by simp
          next
            assume f_k3_eq: "f k3 = k3"
            hence "k3 < length new_L" using `k3 < length L` len_eq by simp
            with `k3 > k2` prems(5) have "op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p" by simp
            moreover have "new_L ! k3 = L ! k3" using eq_nth[OF `k3 < length new_L`] f_k3_eq by simp
            ultimately show ?thesis by simp
          qed
        qed

        have hb_cond: "HB H (L ! (f k1)) (L ! (f k2))"
          using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp

        have f1_lt_f2: "f k1 < f k2"
          using "1.prems"(5)[unfolded lI10_D4_Enq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
          using valid_f1 valid_f2 oper_f1 match_f2 term_cond_L prems(6) hb_cond
          by blast
        
        show "k1 < k2"
        proof -
          have "k2 > f k1" using f1_lt_f2 f2_eq_k2 by simp
          consider "k1 < ?k" | "k1 = ?k" | "k1 = ?k + 1" | "k1 > ?k + 1" by linarith
          then show ?thesis
          proof cases
            case 1 then show ?thesis using `k2 > f k1` unfolding f_def by simp
          next
            case 2 then have "f k1 = ?k + 1" unfolding f_def by simp
                 hence "k2 > ?k + 1" using `k2 > f k1` by simp
                 thus ?thesis using 2 by simp
          next
            case 3 then have "f k1 = ?k" unfolding f_def by simp
                 hence "k2 > ?k" using `k2 > f k1` by simp
                 have "k2 \<noteq> ?k + 1" using f2_not_swapped f2_eq_k2 by simp
                 thus ?thesis using `k2 > ?k` 3 by simp
          next
            case 4 then show ?thesis using `k2 > f k1` unfolding f_def by simp
          qed
        qed
      qed
      
      have mset_new_full: "mset new_L = mset (lin_seq s)" 
        using mset_new "1.prems"(6) by simp

      have ih_app: "lI10_D4_Enq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        using ih(1) do_modify True bt_idx_def
        using "1.prems"(1) "1.prems"(2) di_new hb_new lI10_D4_Enq_Deq_HB_new mset_new_full in_SA_new
        unfolding new_L_def ll2_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        by (metis (no_types, lifting) ih(12) not_None_eq option.collapse option.inject)
        
      thus ?thesis using step1 by simp

    next
      (* =================================================================== *)
      case False (* === Deq Cases === *)
      (* =================================================================== *)
      note not_enq = False

      have find_enq_valid: "find_last_enq l2 \<noteq> None"
        using do_modify False l2_not_nil unfolding should_modify_def l2_def remaining_def last_sa_pos_def l2_last_def
        using bt_idx_def case_optionE last_sa_pos_def remaining_def
        by fastforce
        
      then obtain l21 b_act l22 where l2_split: "find_last_enq l2 = Some (l21, b_act, l22)"
        by (cases "find_last_enq l2") auto
        
      define o1 where "o1 = hd l22"
      define ou where "ou = last l22"
      
      have l22_not_nil: "l22 \<noteq> []" using find_enq_valid l2_split False l2_not_nil
        unfolding find_last_enq_def
        using find_last_enq_props(1,2) l2_last_def l2_split
        by fastforce 
        
      have b_act_enq: "op_name b_act = enq"
        using l2_split by (simp add: find_last_enq_props(2)) 
        
      have o1_deq: "op_name o1 = deq"
        using l22_are_all_deq[OF l2_split l22_not_nil] o1_def l22_not_nil by (metis hd_in_set)
        
      have l22_deqs: "\<forall>x \<in> set l22. op_name x = deq"
        using l22_are_all_deq[OF l2_split l22_not_nil] by simp

      have L_split_c1: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
        using L_decomp find_last_enq_props(1)[OF l2_split] by auto 
        
      have c1_decomp: "L = (l1 @ l21) @ [b_act] @ [o1] @ (tl l22 @ [bt_act] @ l3)"
        using L_split_c1 l22_not_nil o1_def by (metis append.assoc append_Cons append_Nil hd_Cons_tl)

      define b_idx where "b_idx = length l1 + length l21"
      have b_idx_props: "L ! b_idx = b_act" "b_idx \<ge> length l1" "b_idx < length L"
        unfolding b_idx_def using L_split_c1 by (auto simp: nth_append)

      have all_after_l1_not_sa: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
      proof -
        have l1_fmt: "l1 = take (nat (last_sa_pos + 1)) L" using l1_def by simp
        define rest where "rest = remaining"
        have L_split_lemma: "L = l1 @ rest" unfolding rest_def remaining_def l1_def using append_take_drop_id by simp
        have rest_not_nil: "rest \<noteq> []" unfolding rest_def using bt_idx_valid bt_idx_def by auto 
        show ?thesis
          apply (rule l1_contains_all_SA_in_L)
          apply (rule "1.prems"(3)) apply (rule L_split_lemma) apply (rule rest_not_nil)
          apply (rule l1_fmt) apply (rule last_sa_pos_def) done
      qed

      have b_act_not_sa: "\<not> in_SA (op_val b_act) L"
        using all_after_l1_not_sa b_idx_props b_act_enq by auto

      have b_neq_bt: "b_act \<noteq> bt_act"
      proof
        assume eq: "b_act = bt_act"
        let ?idx_b = "length l1 + length l21"
        let ?idx_bt = "length l1 + length l21 + 1 + length l22"
        
        have valid_b: "?idx_b < length L" using L_split_c1 by auto
        have valid_bt: "?idx_bt < length L" using L_split_c1 by auto
        
        have nth_b: "L ! ?idx_b = b_act" using L_split_c1 by (auto simp: nth_append)
        have nth_bt: "L ! ?idx_bt = bt_act" using L_split_c1 by (auto simp: nth_append)
        
        have oper_bt: "op_name bt_act = enq"
          using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
          
        have "?idx_b = ?idx_bt"
        proof (rule same_enq_value_same_index[OF "1.prems"(3)])
          show "?idx_b < length L" using valid_b .
          show "?idx_bt < length L" using valid_bt .
          show "op_name (L ! ?idx_b) = enq" using nth_b b_act_enq by simp
          show "op_name (L ! ?idx_bt) = enq" using nth_bt oper_bt by simp
          show "op_val (L ! ?idx_b) = op_val (L ! ?idx_bt)" using nth_b nth_bt eq by simp
        qed
        
        thus False by simp
      qed

      have b_val_sets: "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s"
      proof -
        have "\<not> in_SA (op_val b_act) (lin_seq s)" using b_act_not_sa "1.prems"(7) by simp 
        moreover have "b_act \<in> set (lin_seq s)" using b_idx_props(3) b_idx_props(1) "1.prems"(6) by (metis nth_mem set_mset_mset) 
        ultimately show ?thesis using LinSeq_Enq_State_Mapping[OF sys_inv] b_act_enq SetA_implies_in_SA[OF sys_inv] by blast
      qed

      have b_act_active: "b_act \<in> active_enqs s"
      proof -
        have b_in_s: "b_act \<in> set (lin_seq s)" using b_idx_props(3) b_idx_props(1) "1.prems"(6) by (metis nth_mem set_mset_mset) 
        have not_sa_s: "\<not> in_SA (op_val b_act) (lin_seq s)" using b_act_not_sa "1.prems"(7) by simp
        show ?thesis using b_in_s b_act_enq not_sa_s non_SA_enqs_are_active sys_inv unfolding system_invariant_def by blast
      qed

      consider (c1) "HB H o1 bt_act"
             | (c2) "\<not> HB H o1 bt_act \<and> HB H b_act o1"
             | (c3) "\<not> HB H o1 bt_act \<and> \<not> HB H b_act o1"
        by blast
        
      then show ?thesis
      proof cases
        (* ----------------------------------------------------------------- *)
        case c1 (* === c1 === *)
        (* ----------------------------------------------------------------- *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"
        
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          using do_modify False c1 l2_split o1_def bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
          apply (subst modify_lin.simps)
          apply (simp add: Let_def case_prod_unfold)
          done
          
        have mset_new: "mset new_L = mset L"
          unfolding new_L_def c1_decomp by (simp add: ac_simps)
          
        have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
        have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto
        
        have hb_new: "HB_consistent new_L H"
        proof -
          have struct_match: "new_L = (l1 @ l21) @ [o1] @ [b_act] @ (tl l22 @ [bt_act] @ l3)"
            unfolding new_L_def by simp
          have "HB_consistent ((l1 @ l21) @ [o1] @ [b_act] @ (tl l22 @ [bt_act] @ l3)) H"
          proof (rule modify_step_c1_consistent[where s=s and L=L and H=H])
            show "system_invariant s" using sys_inv by simp
            show "HB_consistent L H" using "1.prems"(4) by blast
            show "H = his_seq s" using "1.prems"(1) by simp
            show "mset L = mset (lin_seq s)" using "1.prems"(6) by blast
            show "L = (l1 @ l21) @ [b_act] @ [o1] @ (tl l22 @ [bt_act] @ l3)" using c1_decomp by simp
            show "op_name b_act = enq" using b_act_enq by simp
            show "op_name o1 = deq" using o1_deq by simp
            show "bt_act \<in> set L" using bt_in_L by simp
            show "op_name bt_act = enq" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
            show "TypeBT s (op_val bt_act)" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def using "1.prems"(2) by auto
            show "happens_before o1 bt_act H" using c1 by (simp add: HB_def)
            show "b_act \<in> active_enqs s" using b_act_active by simp
            show "b_act \<noteq> bt_act" using b_neq_bt by simp
            show "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s" using b_val_sets by simp
          qed
          thus ?thesis using struct_match by simp
        qed

        have lI10_D4_Enq_Deq_HB_new: "lI10_D4_Enq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
        proof (unfold lI10_D4_Enq_Deq_HB_list_def, intro allI impI, elim conjE)
          fix k1 k2 p
          assume prems: "k1 < length new_L" "k2 < length new_L"
               "op_name (new_L ! k1) = enq" 
               "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
               "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
               "pc p = ''D4'' " 
               "HB H (new_L ! k1) (new_L ! k2)"

          have op_new_k2: "op_name (new_L ! k2) = deq" using prems(4) by (simp add: mk_op_def op_name_def)
          have pid_new_k2: "op_pid (new_L ! k2) = p" using prems(4) by (simp add: mk_op_def op_pid_def)

          let ?k = "length l1 + length l21"
          define f where "f i = (if i = ?k then ?k + 1 else if i = ?k + 1 then ?k else i)" for i
          
          have L_exp: "L = l1 @ l21 @ [b_act, o1] @ tl l22 @ [bt_act] @ l3" using c1_decomp by simp
          have new_L_exp: "new_L = l1 @ l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3" unfolding new_L_def by simp
          have len_eq: "length new_L = length L" using mset_new mset_eq_length by auto

          have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (f i)"
          proof -
            fix i assume i_lt: "i < length new_L"
            consider (lt) "i < ?k" | (eq1) "i = ?k" | (eq2) "i = ?k + 1" | (gt) "i > ?k + 1" by linarith
            then show "new_L ! i = L ! (f i)"
            proof cases
              case lt hence "f i = i" unfolding f_def by simp
              thus ?thesis using lt unfolding L_exp new_L_exp
                by (metis append_assoc length_append nth_append_left) 
            next
              case eq1 hence "f i = ?k + 1" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq1 by (simp add: nth_append)
            next
              case eq2 hence "f i = ?k" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq2 by (simp add: nth_append)
            next
              case gt hence "f i = i" unfolding f_def by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using gt by linarith+
              show ?thesis unfolding L_exp new_L_exp using a1 gt `f i = i` by (simp add: nth_append)
            qed
          qed

          show "k1 < k2"
          proof (cases "k2 = ?k")
            case True
            hence k2_is_o1: "new_L ! k2 = o1" using new_L_exp by (simp add: nth_append)
            have f2: "f k2 = ?k + 1" unfolding f_def using True by simp

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L"
              proof -
                have bnd: "?k + 1 < length L" using L_exp by simp
                have orig: "k1 < length L" using prems(1) len_eq by simp
                show ?thesis unfolding f_def using bnd orig by auto
              qed
              have v2: "f k2 < length L" using True f2 L_exp by simp
              have oper_f1: "op_name (L ! f k1) = enq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              
              have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (intro allI impI)
                fix k3 assume "f k2 < k3" "k3 < length L"
                hence "k3 > ?k + 1" using f2 by simp
                hence "f k3 = k3" unfolding f_def by simp
                thus "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
                  using prems(5) `k3 < length L` len_eq `k3 > ?k + 1` `k2 = ?k` eq_nth
                  by (metis add_lessD1)
              qed

              have hb_match: "HB H (L ! f k1) (L ! f k2)"
                using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp

              show ?thesis
                using "1.prems"(5)[unfolded lI10_D4_Enq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            have f1_bound: "f k1 < ?k + 1" using f1_lt_f2 f2 by simp

            show "k1 < k2"
            proof (cases "k1 < ?k")
              case True thus ?thesis using `k2 = ?k` by simp
            next
              case False
              have "k1 = ?k \<or> k1 = ?k + 1 \<or> k1 > ?k + 1" using False by linarith
              moreover
              { assume "k1 = ?k"
                hence "f k1 = ?k + 1" unfolding f_def by simp
                with f1_bound have False by simp
                hence ?thesis by simp }
              moreover
              { assume "k1 > ?k + 1"
                hence "f k1 = k1" unfolding f_def by simp
                with f1_bound have "k1 < ?k + 1" by simp
                with `k1 > ?k + 1` have False by simp
                hence ?thesis by simp }
              moreover
              { assume k1_is: "k1 = ?k + 1"
                have "k2 < k1" using k1_is `k2 = ?k` by simp
                hence False using hb_new prems(7) prems(1) prems(2)
                  unfolding HB_consistent_def HB_def
                  using False True by blast 
                hence ?thesis by simp }
              ultimately show ?thesis by blast
            qed

          next
            case False
            have k2_not_kp1: "k2 \<noteq> ?k + 1"
            proof
              assume "k2 = ?k + 1"
              hence "new_L ! k2 = b_act" using new_L_exp by (simp add: nth_append)
              hence "op_name (new_L ! k2) = enq" using b_act_enq by simp
              thus False using op_new_k2 by simp
            qed
            
            have f2_eq_k2: "f k2 = k2" unfolding f_def using False k2_not_kp1 by simp
            
            have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
            proof (intro allI impI)
              fix k3 assume "f k2 < k3" "k3 < length L"
              show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (cases "k3 = ?k")
                case True
                hence "L ! k3 = b_act" using L_exp by (simp add: nth_append)
                hence "op_name (L ! k3) = enq" using b_act_enq by simp
                thus ?thesis by simp
              next
                case False_inner: False
                have f_k3_valid: "f k3 < length new_L" using `k3 < length L` len_eq unfolding f_def
                  by (simp add: False_inner) 
                have "k2 < f k3"
                proof -
                  have "k2 < k3" using `f k2 < k3` f2_eq_k2 by simp
                  thus ?thesis using False_inner k2_not_kp1 unfolding f_def
                    using False by auto 
                qed
                have "L ! k3 = new_L ! (f k3)" using eq_nth[OF f_k3_valid] unfolding f_def by (auto split: if_splits)
                with prems(5)[rule_format, of "f k3"] f_k3_valid `k2 < f k3` 
                show ?thesis by simp
              qed
            qed

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L" using prems(1) len_eq L_exp unfolding f_def by (auto split: if_splits)              
              have v2: "f k2 < length L" using prems(2) len_eq L_exp unfolding f_def by (auto split: if_splits)
              have oper_f1: "op_name (L ! f k1) = enq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              have hb_match: "HB H (L ! f k1) (L ! f k2)" using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp
              show ?thesis
                using "1.prems"(5)[unfolded lI10_D4_Enq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            show "k1 < k2" using f1_lt_f2 f2_eq_k2 unfolding f_def using False k2_not_kp1 prems(2) by (auto split: if_splits)
          qed
        qed
        
        have mset_new_full: "mset new_L = mset (lin_seq s)" using mset_new "1.prems"(6) by simp

        have ih_app: "lI10_D4_Enq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        proof -
          define L_inner where "L_inner = take (nat (find_last_SA L + 1)) L @ l21 @ [hd l22] @ [b_act] @ tl l22 @ [drop (nat (find_last_SA L + 1)) L ! bt_idx] @ drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L)"
          
          have hd_l22: "hd l22 = o1" using l2_split by (simp add: o1_def)
          
          have new_L_eq_L_inner: "new_L = L_inner"
            unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def L_inner_def
            using hd_l22 by simp
            
          have p1_in: "data_independent L_inner" using di_new unfolding new_L_eq_L_inner .
          have p2_in: "HB_consistent L_inner H" using hb_new unfolding new_L_eq_L_inner .
          have p3_in: "lI10_D4_Enq_Deq_HB_list L_inner H pc (x_var s) (s_var s)" using lI10_D4_Enq_Deq_HB_new unfolding new_L_eq_L_inner .
          have p4_in: "mset L_inner = mset (lin_seq s)" using mset_new_full unfolding new_L_eq_L_inner .
          have p5_in: "\<forall>v. in_SA v L_inner = in_SA v (lin_seq s)" using in_SA_new unfolding new_L_eq_L_inner .

          have pre1: "\<not> \<not> should_modify L H bt_val" using do_modify by simp
          have pre2: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L + 1)) L)) = bt_idx"
            using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L + 1)) L))) \<noteq> enq"
            using c1 unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric]
            by (simp add: False)
          have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L)) = Some (l21, b_act, l22)"
            using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre5: "happens_before (hd l22) (drop (nat (find_last_SA L + 1)) L ! bt_idx) H"
            using c1 hd_l22 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp

          (* 3 , simp *)
          have fact_o1: "o1 = hd l22" using o1_def by simp
          have fact_the_enq: "the (find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L))) = (l21, b_act, l22)"
            using pre4 by simp
          have fact_list_align: "drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L) = drop (Suc (bt_idx + nat (find_last_SA L + 1))) L"
            by auto

          show ?thesis 
            unfolding new_L_eq_L_inner L_inner_def fact_o1
            using ih(2) pre1 pre2 pre3 pre4 pre5
            using p1_in[unfolded L_inner_def fact_o1] 
            using p2_in[unfolded L_inner_def fact_o1] 
            using p3_in[unfolded L_inner_def fact_o1] 
            using p4_in[unfolded L_inner_def fact_o1] 
            using p5_in[unfolded L_inner_def fact_o1] 
            using "1.prems"(1) "1.prems"(2) "1.prems"(8)
            using fact_the_enq fact_list_align hd_l22
            by simp
        qed
          
        thus ?thesis using step1 by simp
        
      next
        (* ----------------------------------------------------------------- *)
        case c2 (* === c2 === *)
        (* ----------------------------------------------------------------- *)
        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"
        
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          using do_modify False c2 l2_split o1_def bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
          apply (subst modify_lin.simps)
          apply (simp add: Let_def case_prod_unfold)
          done
          
        have mset_new: "mset new_L = mset L"
          unfolding new_L_def L_split_c1 by (simp add: ac_simps)
          
        have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
        have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto

        have hb_new: "HB_consistent new_L H"
        proof -
          have "HB_consistent (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) H"
          proof (rule modify_step_c2_consistent[where s=s and L=L and H=H])
            show "system_invariant s" using sys_inv by simp
            show "HB_consistent L H" using "1.prems"(4) by blast
            show "H = his_seq s" using "1.prems"(1) by simp
            show "mset L = mset (lin_seq s)" using "1.prems"(6) by blast
            show "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3" using L_split_c1 by simp
            show "l22 \<noteq> []" using l22_not_nil by simp
            show "op_name bt_act = enq" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp
            show "TypeBT s (op_val bt_act)" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def using "1.prems"(2) by auto
            show "bt_act \<in> set L" using bt_in_L by simp
            show "o1 = hd l22" using o1_def by simp
            show "op_name b_act = enq" using b_act_enq by simp
            show "b_act \<in> active_enqs s" using b_act_active by simp
            show "b_act \<noteq> bt_act" using b_neq_bt by simp
            show "op_val b_act \<in> SetBO s \<or> op_val b_act \<in> SetBT s" using b_val_sets by simp
            show "\<not> happens_before o1 bt_act H" using c2 by (simp add: HB_def)
            show "happens_before b_act o1 H" using c2 by (simp add: HB_def)
            show "\<forall>x\<in>set l22. op_name x = deq" using l22_deqs by simp
          qed
          thus ?thesis unfolding new_L_def by simp
        qed
          
        have lI10_D4_Enq_Deq_HB_new: "lI10_D4_Enq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
        proof (unfold lI10_D4_Enq_Deq_HB_list_def, intro allI impI, elim conjE)
          fix k1 k2 p
          assume prems: "k1 < length new_L" "k2 < length new_L"
               "op_name (new_L ! k1) = enq"
               "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
               "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
               "pc p = ''D4''" 
               "HB H (new_L ! k1) (new_L ! k2)"

          have op_new_k2: "op_name (new_L ! k2) = deq" using prems(4) by (simp add: mk_op_def op_name_def)
          have pid_new_k2: "op_pid (new_L ! k2) = p" using prems(4) by (simp add: mk_op_def op_pid_def)

          let ?k1 = "length l1 + length l21"
          let ?k2 = "?k1 + 1 + length l22"
          define f where "f i = (if i = ?k1 then ?k2 else if ?k1 < i \<and> i \<le> ?k2 then i - 1 else i)" for i

          have L_exp: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3" using L_split_c1 by simp
          have new_L_exp: "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3" unfolding new_L_def by simp
          have len_eq: "length new_L = length L" using mset_new mset_eq_length by auto
          have bt_enq: "op_name bt_act = enq" using find_unique_index_prop[OF bt_idx_def] unfolding bt_act_def by simp

          have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (f i)"
          proof -
            fix i assume i_lt: "i < length new_L"
            consider (lt) "i < ?k1" | (eq1) "i = ?k1" | (eq2) "i = ?k1 + 1" | (mid) "?k1 + 1 < i \<and> i \<le> ?k2" | (gt) "i > ?k2" by linarith
            then show "new_L ! i = L ! (f i)"
            proof cases
              case lt
              hence fi_eq: "f i = i" unfolding f_def by simp
              have "new_L ! i = L ! i"
              proof (cases "i < length l1")
                case True thus ?thesis unfolding L_exp new_L_exp by (simp add: nth_append)
              next
                case False
                hence "i - length l1 < length l21" using lt by linarith
                thus ?thesis unfolding L_exp new_L_exp using False by (simp add: nth_append)
              qed
              thus ?thesis using fi_eq by simp
            next
              case eq1
              have f_val: "f i = ?k2" unfolding f_def using eq1 by simp
              have a1: "\<not> i < length l1" "i - length l1 = length l21" using eq1 by linarith+
              have part1: "new_L ! i = bt_act" unfolding new_L_exp using a1 by (simp add: nth_append)
              
              have b1: "\<not> f i < length l1" "\<not> f i - length l1 < length l21" "f i - length l1 - length l21 = Suc (length l22)" using f_val by linarith+
              have part2: "L ! (f i) = bt_act" unfolding L_exp using b1 by (simp add: nth_append)
              
              show ?thesis using part1 part2 by simp
            next
              case eq2
              have f_val: "f i = ?k1" unfolding f_def using eq2 by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" "i - length l1 - length l21 = Suc 0" using eq2 by linarith+
              have part1: "new_L ! i = b_act" unfolding new_L_exp using a1 by (simp add: nth_append)
              
              have b1: "\<not> f i < length l1" "f i - length l1 = length l21" using f_val by linarith+
              have part2: "L ! (f i) = b_act" unfolding L_exp using b1 by (simp add: nth_append)
              
              show ?thesis using part1 part2 by simp
            next
              case mid
              have f_val: "f i = i - 1" unfolding f_def using mid by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using mid by linarith+
              define m where "m = i - length l1 - length l21 - 2"
              have idx1: "i - length l1 - length l21 = Suc (Suc m)" unfolding m_def using mid by linarith
              have m_lt: "m < length l22" unfolding m_def using mid by linarith
              have part1: "new_L ! i = l22 ! m" unfolding new_L_exp using a1 idx1 m_lt by (simp add: nth_append)
              
              have b1: "\<not> f i < length l1" "\<not> f i - length l1 < length l21" using f_val mid by linarith+
              have idx2: "f i - length l1 - length l21 = Suc m" unfolding m_def f_val using mid by linarith
              have part2: "L ! (f i) = l22 ! m" unfolding L_exp using b1 idx2 m_lt by (simp add: nth_append)
              
              show ?thesis using part1 part2 by simp
            next
              case gt
              hence fi_eq: "f i = i" unfolding f_def by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using gt by linarith+
              define m where "m = i - length l1 - length l21 - length l22 - 2"
              have idx1: "i - length l1 - length l21 = Suc (Suc (length l22 + m))" unfolding m_def using gt by linarith
              have part1: "new_L ! i = l3 ! m" unfolding new_L_exp using a1 idx1 by (simp add: nth_append)
              
              have b1: "\<not> f i < length l1" "\<not> f i - length l1 < length l21" using gt fi_eq by linarith+
              have idx2: "f i - length l1 - length l21 = Suc (length l22 + Suc m)" unfolding m_def fi_eq using gt by linarith
              have part2: "L ! (f i) = l3 ! m" unfolding L_exp using b1 idx2 by (simp add: nth_append)
              
              show ?thesis using part1 part2 fi_eq by simp
            qed
          qed

          have k2_neq_k1: "k2 \<noteq> ?k1"
          proof
            assume "k2 = ?k1"
            hence "new_L ! k2 = bt_act" using new_L_exp by (simp add: nth_append)
            with op_new_k2 bt_enq show False by simp
          qed

          have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
          proof (intro allI impI)
            fix k3 assume k3_gt: "f k2 < k3" and k3_len: "k3 < length L"
            show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
            proof (cases "k3 = ?k1 \<or> k3 = ?k2")
              case True
              thus ?thesis
              proof (cases "k3 = ?k1")
                case True hence "L ! k3 = b_act" using L_exp by (simp add: nth_append)
                thus ?thesis using b_act_enq by simp
              next
                case False with True have "k3 = ?k2" by simp
                hence "L ! k3 = bt_act" using L_exp by (simp add: nth_append)
                thus ?thesis using bt_enq by simp
              qed
            next
              case False
              define k3_new where "k3_new = (if ?k1 < k3 \<and> k3 < ?k2 then k3 + 1 else k3)"
              have k3_new_len: "k3_new < length new_L"
              proof -
                have k2_bound: "?k2 < length L" unfolding L_exp by simp
                show ?thesis 
                  unfolding k3_new_def using k3_len len_eq k2_bound False
                  by auto 
              qed
              have f_k3_new: "f k3_new = k3" using False unfolding k3_new_def f_def by auto
              have L_k3_eq: "L ! k3 = new_L ! k3_new" using eq_nth[OF k3_new_len] f_k3_new by simp

              have "k2 < k3_new"
              proof (cases "k2 < ?k1")
                case True
                hence f2: "f k2 = k2" unfolding f_def by auto
                from f2 k3_gt have "k2 < k3" by simp
                thus ?thesis unfolding k3_new_def using True by auto
              next
                case False_outer: False
                have k2_ge: "k2 > ?k1" using False_outer k2_neq_k1 by simp
                
                show ?thesis
                proof (cases "k2 \<le> ?k2")
                  case True
                  hence f2_shift: "f k2 = k2 - 1" unfolding f_def using k2_ge by auto
                  from f2_shift k3_gt have "k2 - 1 < k3" by simp
                  hence k3_ge: "k2 \<le> k3" by simp
                  
                  show ?thesis
                  proof (cases "k3_new = k3 + 1")
                    case True thus ?thesis using k3_ge by simp
                  next
                    case False_inner: False
                    have k3_no_shift: "k3_new = k3" using False_inner k3_new_def by auto 
                    
                    from `\<not> (k3 = ?k1 \<or> k3 = ?k2)` have k3_neq: "k3 \<noteq> ?k1" "k3 \<noteq> ?k2" by auto
                    hence "\<not> (?k1 < k3 \<and> k3 < ?k2)" 
                      using k3_no_shift unfolding k3_new_def by (auto split: if_splits)
                    with k3_ge k2_ge True have "k3 \<ge> ?k2" by simp
                    with k3_neq(2) have "k3 > ?k2" by simp
                    thus ?thesis unfolding k3_new_def using k2_ge True by auto
                  qed
                next
                  case False_gt: False
                  have k2_gt_k2: "k2 > ?k2" using False_gt by auto 
                  hence "f k2 = k2" unfolding f_def by auto
                  with k3_gt have "k2 < k3" by simp
                  thus ?thesis unfolding k3_new_def using False_gt by auto
                qed
              qed               
              thus ?thesis using prems(5)[rule_format, OF `k2 < k3_new` k3_new_len] L_k3_eq by simp
            qed
          qed

          have v1: "f k1 < length L"
          proof -
             have bnd: "?k2 < length L" using L_exp by simp
             have orig: "k1 < length L" using prems(1) len_eq by simp
             show ?thesis unfolding f_def using bnd orig by auto
          qed

          have v2: "f k2 < length L"
          proof -
             have bnd: "?k2 < length L" using L_exp by simp
             have orig: "k2 < length L" using prems(2) len_eq by simp
             show ?thesis unfolding f_def using bnd orig by auto
          qed

          have oper_f1: "op_name (L ! f k1) = enq" using prems(3) eq_nth[OF prems(1)] by simp
          have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
          have hb_match: "HB H (L ! f k1) (L ! f k2)" using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp
          
          have f1_lt_f2: "f k1 < f k2"
          proof -
            show ?thesis
              using "1.prems"(5)[unfolded lI10_D4_Enq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
              using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match
              by blast
          qed

          show "k1 < k2"
          proof (cases "k2 < ?k1")
            case True
            hence "f k2 = k2" unfolding f_def by auto
            with f1_lt_f2 have "f k1 < k2" by simp
            show ?thesis
            proof (cases "k1 = ?k1")
              case True hence "f k1 = ?k2" unfolding f_def by auto
              with `f k1 < k2` have "?k2 < k2" by simp
              with True `k2 < ?k1` show ?thesis by simp
            next
              case False
              hence "f k1 \<ge> k1 - 1" unfolding f_def by auto
              with `f k1 < k2` have "k1 - 1 < k2" by simp
              hence "k1 \<le> k2" by simp
              moreover have "k1 \<noteq> k2" using f1_lt_f2 by auto
              ultimately show ?thesis by simp
            qed
          next
            case False
            hence k2_ge: "k2 > ?k1" using k2_neq_k1 by simp
            show ?thesis
            proof (cases "k2 \<le> ?k2")
              case True
              hence f2_eq: "f k2 = k2 - 1" unfolding f_def using k2_ge by auto
              with f1_lt_f2 have f1_lt: "f k1 < k2 - 1" by simp
              show ?thesis
              proof (cases "k1 = ?k1")
                case True hence "f k1 = ?k2" unfolding f_def by auto
                with f1_lt have "?k2 < k2 - 1" by simp
                with True show ?thesis by simp
              next
                case False
                hence "f k1 \<ge> k1 - 1" unfolding f_def by auto
                with f1_lt have "k1 - 1 < k2 - 1" by simp
                thus ?thesis by simp
              qed
            next
              case False
              hence "f k2 = k2" unfolding f_def by auto
              with f1_lt_f2 have f1_lt: "f k1 < k2" by simp
              show ?thesis
              proof (cases "k1 = ?k1")
                case True
                hence "f k1 = ?k2" unfolding f_def by auto
                with f1_lt have "?k2 < k2" by simp
                thus ?thesis using True by simp
              next
                case False
                hence "f k1 \<ge> k1 - 1" unfolding f_def by auto
                with f1_lt have "k1 - 1 < k2" by simp
                hence "k1 \<le> k2" by simp
                moreover have "k1 \<noteq> k2" using f1_lt_f2 by auto
                ultimately show ?thesis by simp
              qed
            qed
          qed
        qed
        
        have mset_new_full: "mset new_L = mset (lin_seq s)" using mset_new "1.prems"(6) by simp

        have ih_app: "lI10_D4_Enq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        proof -
          define L_inner where "L_inner = take (nat (find_last_SA L + 1)) L @ l21 @ [drop (nat (find_last_SA L + 1)) L ! bt_idx] @ [b_act] @ l22 @ drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L)"
          
          have new_L_eq_L_inner: "new_L = L_inner"
            unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def L_inner_def
            by simp
            
          have p1_in: "data_independent L_inner" using di_new unfolding new_L_eq_L_inner .
          have p2_in: "HB_consistent L_inner H" using hb_new unfolding new_L_eq_L_inner .
          have p3_in: "lI10_D4_Enq_Deq_HB_list L_inner H pc (x_var s) (s_var s)" using lI10_D4_Enq_Deq_HB_new unfolding new_L_eq_L_inner .
          have p4_in: "mset L_inner = mset (lin_seq s)" using mset_new_full unfolding new_L_eq_L_inner .
          have p5_in: "\<forall>v. in_SA v L_inner = in_SA v (lin_seq s)" using in_SA_new unfolding new_L_eq_L_inner .

          have pre1: "\<not> \<not> should_modify L H bt_val" using do_modify by simp
          have pre2: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L + 1)) L)) = bt_idx"
            using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L + 1)) L))) \<noteq> enq"
            using False unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L)) = Some (l21, b_act, l22)"
            using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          
          have hd_l22: "hd l22 = o1" using l2_split by (simp add: o1_def)
          have pre5: "\<not> happens_before (hd l22) (drop (nat (find_last_SA L + 1)) L ! bt_idx) H"
            using c2 hd_l22 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by (simp add: HB_def)
          have pre6: "happens_before b_act (hd l22) H"
            using c2 hd_l22 by (simp add: HB_def)

          show ?thesis 
            unfolding new_L_eq_L_inner
            unfolding L_inner_def
            using ih(3) pre1 pre2 pre3 pre4 pre5 pre6 p1_in p2_in p3_in p4_in p5_in "1.prems"(1) "1.prems"(2) "1.prems"(8)
            unfolding L_inner_def
            by simp
        qed
          
        thus ?thesis using step1 by simp
        
      next
        (* ----------------------------------------------------------------- *)
        case c3 (* === c3 === *)
        (* ----------------------------------------------------------------- *)
        define new_L where "new_L = l1 @ l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3"
        
        have step1: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          using do_modify False c3 l2_split o1_def bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
          apply (subst modify_lin.simps)
          apply (simp add: Let_def case_prod_unfold)
          done
          
        have mset_new: "mset new_L = mset L"
          unfolding new_L_def c1_decomp by (simp add: ac_simps)
          
        have di_new: "data_independent new_L" using "1.prems"(3) data_independent_cong mset_new by blast
        have in_SA_new: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v (lin_seq s)" using "1.prems"(7) in_SA_mset_eq[OF mset_new] by auto

        have hb_new: "HB_consistent new_L H"
        proof -
          have "HB_consistent (l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3) H"
          proof -
            note step_thm = modify_step_c3_new_consistent[where s=s and L=L and H=H]
            show ?thesis
              using sys_inv "1.prems"(4) "1.prems"(1) "1.prems"(6) c1_decomp
              using b_act_enq o1_deq bt_in_L find_unique_index_prop[OF bt_idx_def]
              using b_act_active b_neq_bt b_val_sets c3
              by (metis append_assoc bt_act_def ih(6) step_thm)
          qed
          thus ?thesis unfolding new_L_def by simp
        qed

        have lI10_D4_Enq_Deq_HB_new: "lI10_D4_Enq_Deq_HB_list new_L H pc (x_var s) (s_var s)"
        proof (unfold lI10_D4_Enq_Deq_HB_list_def, intro allI impI, elim conjE)
          fix k1 k2 p
          assume prems: "k1 < length new_L" "k2 < length new_L"
               "op_name (new_L ! k1) = enq" 
               "new_L ! k2 = mk_op deq (x_var s p) p (s_var s p)"
               "\<forall>k3>k2. k3 < length new_L \<longrightarrow> op_name (new_L ! k3) \<noteq> deq \<or> op_pid (new_L ! k3) \<noteq> p"
               "pc p = ''D4'' " 
               "HB H (new_L ! k1) (new_L ! k2)"

          have op_new_k2: "op_name (new_L ! k2) = deq" using prems(4) by (simp add: mk_op_def op_name_def)
          have pid_new_k2: "op_pid (new_L ! k2) = p" using prems(4) by (simp add: mk_op_def op_pid_def)

          let ?k = "length l1 + length l21"
          define f where "f i = (if i = ?k then ?k + 1 else if i = ?k + 1 then ?k else i)" for i
          
          have L_exp: "L = l1 @ l21 @ [b_act, o1] @ tl l22 @ [bt_act] @ l3" using c1_decomp by simp
          have new_L_exp: "new_L = l1 @ l21 @ [o1, b_act] @ tl l22 @ [bt_act] @ l3" unfolding new_L_def by simp
          have len_eq: "length new_L = length L" using mset_new mset_eq_length by auto

          have eq_nth: "\<And>i. i < length new_L \<Longrightarrow> new_L ! i = L ! (f i)"
          proof -
            fix i assume i_lt: "i < length new_L"
            consider (lt) "i < ?k" | (eq1) "i = ?k" | (eq2) "i = ?k + 1" | (gt) "i > ?k + 1" by linarith
            then show "new_L ! i = L ! (f i)"
            proof cases
              case lt hence "f i = i" unfolding f_def by simp
              thus ?thesis using lt unfolding L_exp new_L_exp
                by (metis append_assoc length_append nth_append_left) 
            next
              case eq1 hence "f i = ?k + 1" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq1 by (simp add: nth_append)
            next
              case eq2 hence "f i = ?k" unfolding f_def by simp
              thus ?thesis unfolding L_exp new_L_exp using eq2 by (simp add: nth_append)
            next
              case gt hence "f i = i" unfolding f_def by simp
              have a1: "\<not> i < length l1" "\<not> i - length l1 < length l21" using gt by linarith+
              show ?thesis unfolding L_exp new_L_exp using a1 gt `f i = i` by (simp add: nth_append)
            qed
          qed

          show "k1 < k2"
          proof (cases "k2 = ?k")
            case True
            hence k2_is_o1: "new_L ! k2 = o1" using new_L_exp by (simp add: nth_append)
            have f2: "f k2 = ?k + 1" unfolding f_def using True by simp

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L"
              proof -
                 have bnd: "?k + 1 < length L" using L_exp by simp
                 have orig: "k1 < length L" using prems(1) len_eq by simp
                 show ?thesis unfolding f_def using bnd orig by auto
              qed
              
              have v2: "f k2 < length L" using True f2 L_exp by simp
              have oper_f1: "op_name (L ! f k1) = enq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              
              have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (intro allI impI)
                fix k3 assume "f k2 < k3" "k3 < length L"
                hence "k3 > ?k + 1" using f2 by simp
                hence "f k3 = k3" unfolding f_def by simp
                thus "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
                  using prems(5) `k3 < length L` len_eq `k3 > ?k + 1` `k2 = ?k` eq_nth
                  by (metis add_lessD1) 
              qed

              have hb_match: "HB H (L ! f k1) (L ! f k2)"
                using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp 

              show ?thesis
                using "1.prems"(5)[unfolded lI10_D4_Enq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            have f1_bound: "f k1 < ?k + 1" using f1_lt_f2 f2 by simp

            show "k1 < k2"
            proof (cases "k1 < ?k")
              case True thus ?thesis using `k2 = ?k` by simp
            next
              case False
              have "k1 = ?k \<or> k1 = ?k + 1 \<or> k1 > ?k + 1" using False by linarith
              moreover
              { assume "k1 = ?k"
                hence "f k1 = ?k + 1" unfolding f_def by simp
                with f1_bound have False by simp
                hence ?thesis by simp }
              moreover
              { assume "k1 > ?k + 1"
                hence "f k1 = k1" unfolding f_def by simp
                with f1_bound have "k1 < ?k + 1" by simp
                with `k1 > ?k + 1` have False by simp
                hence ?thesis by simp }
              moreover
              { assume k1_is: "k1 = ?k + 1"
                have "k2 < k1" using k1_is `k2 = ?k` by simp
                hence False using hb_new prems(7) prems(1) prems(2)
                  unfolding HB_consistent_def HB_def
                  using False True by blast 
                hence ?thesis by simp }
              ultimately show ?thesis by blast
            qed

          next
            case False
            have k2_not_kp1: "k2 \<noteq> ?k + 1"
            proof
              assume "k2 = ?k + 1"
              hence "new_L ! k2 = b_act" using new_L_exp by (simp add: nth_append)
              hence "op_name (new_L ! k2) = enq" using b_act_enq by simp
              thus False using op_new_k2 by simp
            qed
            
            have f2_eq_k2: "f k2 = k2" unfolding f_def using False k2_not_kp1 by simp
            
            have L_last_deq: "\<forall>k3>f k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
            proof (intro allI impI)
              fix k3 assume "f k2 < k3" "k3 < length L"
              show "op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p"
              proof (cases "k3 = ?k")
                case True
                hence "L ! k3 = b_act" using L_exp by (simp add: nth_append)
                hence "op_name (L ! k3) = enq" using b_act_enq by simp
                thus ?thesis by simp
              next
                case False_inner: False
                have f_k3_valid: "f k3 < length new_L" using `k3 < length L` len_eq unfolding f_def
                  using False_inner by auto 
                have "k2 < f k3"
                proof -
                  have "k2 < k3" using `f k2 < k3` f2_eq_k2 by simp
                  thus ?thesis using False_inner k2_not_kp1 unfolding f_def
                    using False by auto 
                qed
                have "L ! k3 = new_L ! (f k3)" using eq_nth[OF f_k3_valid] unfolding f_def by (auto split: if_splits)
                with prems(5)[rule_format, of "f k3"] f_k3_valid `k2 < f k3` 
                show ?thesis by simp
              qed
            qed

            have f1_lt_f2: "f k1 < f k2"
            proof -
              have v1: "f k1 < length L" using prems(1) len_eq L_exp unfolding f_def by (auto split: if_splits)              
              have v2: "f k2 < length L" using prems(2) len_eq L_exp unfolding f_def by (auto split: if_splits)
              have oper_f1: "op_name (L ! f k1) = enq" using prems(3) eq_nth[OF prems(1)] by simp
              have match_f2: "L ! f k2 = mk_op deq (x_var s p) p (s_var s p)" using prems(4) eq_nth[OF prems(2)] by simp
              have hb_match: "HB H (L ! f k1) (L ! f k2)" using prems(7) eq_nth[OF prems(1)] eq_nth[OF prems(2)] by simp
              show ?thesis
                using "1.prems"(5)[unfolded lI10_D4_Enq_Deq_HB_list_def, rule_format, of "f k1" "f k2" p]
                using v1 v2 oper_f1 match_f2 L_last_deq prems(6) hb_match by blast
            qed

            show "k1 < k2" using f1_lt_f2 f2_eq_k2 unfolding f_def using False k2_not_kp1 prems(2) by (auto split: if_splits)
          qed
        qed
        
        have mset_new_full: "mset new_L = mset (lin_seq s)" using mset_new "1.prems"(6) by simp

        have ih_app: "lI10_D4_Enq_Deq_HB_list (modify_lin new_L H bt_val) H pc (x_var s) (s_var s)"
        proof -
          define L_inner where "L_inner = take (nat (find_last_SA L + 1)) L @ l21 @ [o1] @ [b_act] @ tl l22 @ [drop (nat (find_last_SA L + 1)) L ! bt_idx] @ drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L)"
          
          have hd_l22: "hd l22 = o1" using l2_split by (simp add: o1_def)
          
          have new_L_eq_L_inner: "new_L = L_inner"
            unfolding new_L_def l1_def l3_def bt_act_def remaining_def last_sa_pos_def L_inner_def
            using hd_l22 by simp
            
          have p1_in: "data_independent L_inner" using di_new unfolding new_L_eq_L_inner .
          have p2_in: "HB_consistent L_inner H" using hb_new unfolding new_L_eq_L_inner .
          have p3_in: "lI10_D4_Enq_Deq_HB_list L_inner H pc (x_var s) (s_var s)" using lI10_D4_Enq_Deq_HB_new unfolding new_L_eq_L_inner .
          have p4_in: "mset L_inner = mset (lin_seq s)" using mset_new_full unfolding new_L_eq_L_inner .
          have p5_in: "\<forall>v. in_SA v L_inner = in_SA v (lin_seq s)" using in_SA_new unfolding new_L_eq_L_inner .

          have pre1: "\<not> \<not> should_modify L H bt_val" using do_modify by simp
          have pre2: "the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) (drop (nat (find_last_SA L + 1)) L)) = bt_idx"
            using bt_idx_def unfolding remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre3: "op_name (last (take bt_idx (drop (nat (find_last_SA L + 1)) L))) \<noteq> enq"
            using False unfolding l2_def[symmetric] l2_last_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          have pre4: "find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L)) = Some (l21, b_act, l22)"
            using l2_split unfolding l2_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by simp
          
          have pre5: "\<not> happens_before (hd l22) (drop (nat (find_last_SA L + 1)) L ! bt_idx) H"
            using c3 hd_l22 unfolding bt_act_def[symmetric] remaining_def[symmetric] last_sa_pos_def[symmetric] by (simp add: HB_def)
          have pre6: "\<not> happens_before b_act (hd l22) H"
            using c3 hd_l22 by (simp add: HB_def)

          have fact_o1: "o1 = hd l22" using o1_def by simp
          have fact_the_enq: "the (find_last_enq (take bt_idx (drop (nat (find_last_SA L + 1)) L))) = (l21, b_act, l22)"
            using pre4 by simp
          have fact_list_align: "drop (bt_idx + 1) (drop (nat (find_last_SA L + 1)) L) = drop (Suc (bt_idx + nat (find_last_SA L + 1))) L"
            by auto

          show ?thesis 
            unfolding new_L_eq_L_inner L_inner_def fact_o1
            using ih(4) pre1 pre2 pre3 pre4 pre5 pre6
            using p1_in[unfolded L_inner_def fact_o1] 
            using p2_in[unfolded L_inner_def fact_o1] 
            using p3_in[unfolded L_inner_def fact_o1] 
            using p4_in[unfolded L_inner_def fact_o1] 
            using p5_in[unfolded L_inner_def fact_o1] 
            using "1.prems"(1) "1.prems"(2) "1.prems"(8)
            using fact_the_enq fact_list_align hd_l22
            by simp
        qed
          
        thus ?thesis using step1 by simp
      qed
    qed
  qed
qed


(* ========================================================================= *)
(* 🚀 Sorry : modify_preserves_lI10_D4_Enq_Deq_HB (SSN + ) *)
(* ========================================================================= *)
lemma modify_preserves_lI10_D4_Enq_Deq_HB:
  assumes INV: "system_invariant s"
    and q_in_SetB_raw: "q_val \<in> SetB s"
    and q_not_bot: "q_val \<noteq> BOT"
    and q_val_def: "q_val = Model.Q_arr s (Model.j_var s p)"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                                then modify_lin (lin_seq s) (his_seq s) q_val
                                else lin_seq s)"
    (* SSN : mk_op 4 , xv / sv *)
    and s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and xv_s': "x_var s' = (x_var s)(p := q_val)"
    and sv_s': "s_var s' = s_var s"
    and his_eq: "his_seq s' = his_seq s"
    and pc_s': "program_counter s' = (program_counter s)(p := ''D4'')"
    and pc_s: "program_counter s p = ''D3'' "
    and lI8_D3_Deq_Returned_s: "\<forall>p. program_counter s p = ''D3'' \<longrightarrow> 
                     (\<forall>k < length (lin_seq s). 
                       (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = p) \<longrightarrow> 
                       DeqRetInHis s p (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))"
  shows "lI10_D4_Enq_Deq_HB s'"
proof -
  (* Step 1: 1. basic facts *)
  let ?L = "lin_seq s" let ?H = "his_seq s" let ?pc = "program_counter s"
  
  have di: "data_independent ?L" using INV unfolding system_invariant_def by auto
  have hb_cons: "HB_consistent ?L ?H" using INV unfolding system_invariant_def lI3_HB_Ret_Lin_Sync_def
    by (meson HB_Act_def HB_consistent_def) 
    
  have orig_list: "lI10_D4_Enq_Deq_HB_list ?L ?H ?pc (x_var s) (s_var s)" 
    using INV lI10_D4_Enq_Deq_HB_implies_list unfolding system_invariant_def by auto

  (* Step 2: 2. q_in_SetB ( lI7_D4_Deq_Deq_HB ) *)
  have q_in_SetB: "q_val \<in> SetB s"
  proof -
    define jp where "jp = j_var s p"
    have "jp < l_var s p" using INV pc_s unfolding system_invariant_def sI6_D3_Scan_Pointers_def
      using jp_def by blast 
    hence "Q_arr s jp = q_val" using q_val_def jp_def by simp
    with q_not_bot have "Q_arr s jp \<noteq> BOT" by simp
    hence "InQBack s q_val" using INV `jp < l_var s p` unfolding system_invariant_def sI8_Q_Qback_Sync_def jp_def
      by (metis InQBack_def q_val_def)
    thus ?thesis 
      unfolding SetB_def TypeB_def using `Q_arr s jp = q_val` pc_s q_not_bot
      using InQBack_non_BOT_implies_Val
      using QHas_def SetB_def q_in_SetB_raw by blast 
  qed

  (* Step 3: 3. base_lin lI10_D4_Enq_Deq_HB_list *)
  have base_list_prop: "lI10_D4_Enq_Deq_HB_list base_lin ?H ?pc (x_var s) (s_var s)"
  proof (cases "should_modify ?L ?H q_val")
    case False thus ?thesis using orig_list base_def by simp
  next
    case True
    have bt: "TypeBT s q_val"
    proof -
      define jp where "jp = j_var s p"
      have idx_is_jp: "Idx s q_val = jp"
        using q_in_SetB q_val_def jp_def unfolding SetB_def TypeB_def
        by (metis sI10_Qback_Unique_Vals_def AtIdx_def D3_Q_at_j INV Idx_implies_AtIdx
            InQBack_def pc_s q_not_bot system_invariant_def) 
      have q_in_back: "\<exists>k. Qback_arr s k = q_val"
        using q_in_SetB unfolding SetB_def TypeB_def InQBack_def QHas_def
        by (metis D3_Q_at_j INV pc_s q_not_bot q_val_def) 
      have path_bot: "\<forall>k < Idx s q_val. k \<ge> j_var s p \<longrightarrow> Q_arr s k = BOT"
        using idx_is_jp jp_def by auto 
      show ?thesis
        unfolding TypeBT_def
        using q_in_SetB q_not_bot pc_s q_val_def q_in_back idx_is_jp
        unfolding SetB_def TypeB_def InQBack_def
        by (metis sI6_D3_Scan_Pointers_def INV QHas_def jp_def order_refl path_bot
            system_invariant_def)
    qed
      
    have mset_eq: "mset ?L = mset (lin_seq s)" by simp
    have sa_eq: "(\<forall>v. in_SA v ?L \<longleftrightarrow> in_SA v (lin_seq s))" by simp
    show ?thesis
      using lI10_D4_Enq_Deq_HB_list_modify[OF INV refl bt di hb_cons orig_list mset_eq sa_eq refl] True base_def
      by metis 
  qed

  (* ========================================================================= *)
  (* lI10_D4_Enq_Deq_HB: (Key simplification ) *)
  (* ========================================================================= *)
  show "lI10_D4_Enq_Deq_HB s'" unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
  apply (intro allI impI, elim conjE) (* elim conjE *)
  subgoal premises prems for k1 k2 q
  proof (cases "q = p")
    case True
    (* --------------------------------------------------------------------- *)
    (* 1: q = p. : k1 enq, deq, *)
    (* --------------------------------------------------------------------- *)
    then show "k1 < k2"
    proof (cases "k2 = length base_lin")
      case True (* Case A: k2 *)
      have "k1 < length base_lin"
      proof (rule ccontr)
        assume "\<not> k1 < length base_lin"
        hence "k1 = length base_lin" using prems(1) s'_lin_def by auto
        hence "op_name (lin_seq s' ! k1) = deq" 
          using s'_lin_def by (simp add: nth_append mk_op_def op_name_def)
        moreover have "op_name (lin_seq s' ! k1) = enq" using prems(3) by blast
        ultimately show False by simp
      qed
      thus ?thesis using True by simp
    next
      case False (* Case B: k2 *)
      hence k2_old: "k2 < length base_lin" using prems(2) s'_lin_def by auto
      
      define k3 where "k3 = length base_lin"
      have "k3 > k2" using k2_old k3_def by simp
      
      moreover have "k3 < length (lin_seq s')" by (simp add: k3_def s'_lin_def)
      moreover have "op_name (lin_seq s' ! k3) = deq" 
        using s'_lin_def k3_def unfolding mk_op_def op_name_def by (auto simp: nth_append)
      moreover have "op_pid (lin_seq s' ! k3) = p"
        using s'_lin_def k3_def unfolding mk_op_def op_pid_def by (auto simp: nth_append)

      ultimately show ?thesis using prems(5)[rule_format, of k3] True by (auto simp: s'_lin_def)
    qed

  next
    case False (* --------------------------------------------------------- *)
    (* 2: q \<noteq> p. q , base_list_prop *)
    (* --------------------------------------------------------------------- *)
    have q_not_p: "q \<noteq> p" by (rule False)
    
    (* Step 1: 1. k2 *)
    have k2_old: "k2 < length base_lin"
    proof (rule ccontr)
      assume "\<not> k2 < length base_lin"
      hence "k2 = length base_lin" using prems(2) s'_lin_def by auto
      hence "op_pid (lin_seq s' ! k2) = p" using s'_lin_def by (auto simp: mk_op_def op_pid_def nth_append)
      moreover have "op_pid (lin_seq s' ! k2) = q" 
        using prems(4) by (simp add: mk_op_def op_pid_def)
      ultimately show False using q_not_p by auto
    qed
    
    (* Step 2: 2. k1 *)
    have k1_old: "k1 < length base_lin"
    proof (rule ccontr)
      assume "\<not> k1 < length base_lin"
      hence "k1 = length base_lin" using prems(1) s'_lin_def by auto
      hence "op_name (lin_seq s' ! k1) = deq" using s'_lin_def by (auto simp: mk_op_def op_name_def nth_append)
      moreover have "op_name (lin_seq s' ! k1) = enq" using prems(3) by blast
      ultimately show False by auto
    qed

    (* Step 3: 3. : q \<noteq> p, xv / sv *)
    have pc_q: "program_counter s q = ''D4'' "
      using prems(6) q_not_p pc_s' by (metis fun_upd_other)
    
    have last_deq_old: "\<forall>k3>k2. k3 < length base_lin \<longrightarrow> 
                             op_name (base_lin ! k3) \<noteq> deq \<or> op_pid (base_lin ! k3) \<noteq> q"
    proof (intro allI impI)
      fix k3 assume "k2 < k3" and "k3 < length base_lin"
      hence "k3 < length (lin_seq s')" and "base_lin ! k3 = lin_seq s' ! k3"
        using s'_lin_def by (auto simp: nth_append)
      with prems(5)[rule_format, of k3] show "op_name (base_lin ! k3) \<noteq> deq \<or> op_pid (base_lin ! k3) \<noteq> q"
        using `k2 < k3` by presburger
    qed

    from base_list_prop [unfolded lI10_D4_Enq_Deq_HB_list_def, rule_format, of k1 k2 q]
    show "k1 < k2"
    proof -
      have cond1: "k1 < length base_lin" by (rule k1_old)
      have cond2: "k2 < length base_lin" by (rule k2_old)
      have cond3: "op_name (base_lin ! k1) = enq" 
        using k1_old s'_lin_def prems(3) by (auto simp: nth_append)
        
      have "x_var s' q = x_var s q" using xv_s' q_not_p by simp
      moreover have "s_var s' q = s_var s q" using sv_s' by simp
      ultimately have cond4: "base_lin ! k2 = mk_op deq (x_var s q) q (s_var s q)"
        using k2_old s'_lin_def prems(4) by (auto simp: nth_append)
        
      have cond5: "\<forall>k3>k2. k3 < length base_lin \<longrightarrow> op_name (base_lin ! k3) \<noteq> deq \<or> op_pid (base_lin ! k3) \<noteq> q"
        by (rule last_deq_old)
      have cond6: "program_counter s q = ''D4''" by (rule pc_q)
      
      have cond7: "HB ?H (base_lin ! k1) (base_lin ! k2)"
        using prems(7) his_eq k1_old k2_old s'_lin_def by (auto simp: nth_append)
      
      show ?thesis 
        using base_list_prop[unfolded lI10_D4_Enq_Deq_HB_list_def]
        using cond1 cond2 cond3 cond4 cond5 cond6 cond7 by blast
    qed
  qed
  done
qed

(* ========================================================================= *)
(* Auxiliary lemma: D3 lI11_D4_Deq_Unique (SSN + 4) *)
(* ========================================================================= *)
lemma modify_preserves_lI11_D4_Deq_Unique:
  assumes sys_inv: "system_invariant s"
    and type_bt: "TypeBT s q_val"
    and q_val_not_bot: "q_val \<noteq> BOT"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val 
                               then modify_lin (lin_seq s) (his_seq s) q_val 
                               else lin_seq s)"
    (* 4 mk_op *)
    and s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and his_eq: "his_seq s' = his_seq s"
    and pc_s': "program_counter s' = (program_counter s)(p := ''D4'')"
    and pc_s: "program_counter s p = ''D3''"
    (* Proof note. *)
    and xv_s': "x_var s' = (x_var s)(p := q_val)"
    and sv_s': "s_var s' = s_var s"
    (* DeqRetInHis SSN *)
    and lI8_D3_Deq_Returned_s: "\<forall>p. program_counter s p = ''D3'' \<longrightarrow> 
                     (\<forall>k < length (lin_seq s). 
                       (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = p) \<longrightarrow> 
                       DeqRetInHis s p (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))"
  shows "lI11_D4_Deq_Unique s'"
  unfolding lI11_D4_Deq_Unique_def
proof (intro allI impI)
  fix q
  assume pc_q_s': "program_counter s' q = ''D4''"
  
  (* Proof note. *)
  have L_def: "lin_seq s = lin_seq s" by simp
  have inv_lI11_D4_Deq_Unique: "lI11_D4_Deq_Unique s" using sys_inv unfolding system_invariant_def by auto
  
  show "\<exists>k2 < length (lin_seq s').
          lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
          (\<forall>k3 < length (lin_seq s'). op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
             k3 < k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3)))"
  proof (cases "q = p")
    case True
    (* --------------------------------------------------------------------- *)
    (* 1: D3 p *)
    (* --------------------------------------------------------------------- *)
    let ?new_k2 = "length base_lin"
    
    (* 4 mk_op *)
    have k2_props: "?new_k2 < length (lin_seq s') \<and> 
                    lin_seq s' ! ?new_k2 = mk_op deq (x_var s' p) p (s_var s' p)"
      using s'_lin_def xv_s' sv_s' by (simp add: nth_append)
      
    have other_k3_props: "\<forall>k3 < length (lin_seq s'). 
          op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = p \<and> k3 \<noteq> ?new_k2 \<longrightarrow>
          k3 < ?new_k2 \<and> DeqRetInHis s' p (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
    proof (intro allI impI)
      fix k3
      assume k3_bound: "k3 < length (lin_seq s')"
      assume cond3: "op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = p \<and> k3 \<noteq> ?new_k2"
      
      have k3_lt: "k3 < length base_lin" 
        using k3_bound cond3 s'_lin_def by auto
        
      (* k3 *)
      have mset_eq: "mset base_lin = mset (lin_seq s)"
        using base_def modify_preserves_mset by presburger 
        
      have "lin_seq s' ! k3 \<in> set base_lin"
        using k3_lt s'_lin_def by (simp add: nth_append)
      hence "lin_seq s' ! k3 \<in> set (lin_seq s)"
        using mset_eq by (metis mset_eq_setD)
      then obtain old_k3 where old_k3_def: 
        "old_k3 < length (lin_seq s)" 
        "lin_seq s ! old_k3 = lin_seq s' ! k3" 
        by (metis in_set_conv_nth)
        
      (* p D3, lI8_D3_Deq_Returned, *)
      have "DeqRetInHis s p (op_val (lin_seq s ! old_k3)) (op_ssn (lin_seq s ! old_k3))"
        using lI8_D3_Deq_Returned_s pc_s old_k3_def(1) cond3 old_k3_def(2) by metis 
        
      show "k3 < ?new_k2 \<and> DeqRetInHis s' p (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
        using `DeqRetInHis s p (op_val (lin_seq s ! old_k3)) (op_ssn (lin_seq s ! old_k3))` 
        using k3_lt old_k3_def(2) his_eq unfolding DeqRetInHis_def Let_def by auto
    qed
    
    show ?thesis using True k2_props other_k3_props by blast
    
  next
    case False
    (* --------------------------------------------------------------------- *)
    (* 2: D4 q *)
    (* --------------------------------------------------------------------- *)
    have pc_q_s: "program_counter s q = ''D4''" 
      using pc_q_s' pc_s' False by (metis fun_upd_other)
      
    (* q ( mk_op) *)
    obtain old_k2 where old_props:
      "old_k2 < length (lin_seq s)"
      "lin_seq s ! old_k2 = mk_op deq (x_var s q) q (s_var s q)"
      "\<forall>k3 < length (lin_seq s). op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = q \<and> k3 \<noteq> old_k2 \<longrightarrow>
         k3 < old_k2 \<and> DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
      using inv_lI11_D4_Deq_Unique pc_q_s unfolding lI11_D4_Deq_Unique_def by blast
      
    let ?P = "\<lambda>act. op_name act = deq \<and> op_pid act = q"
    
    (* modify_lin, deq *)
    have filter_eq: "filter ?P base_lin = filter ?P (lin_seq s)"
      using base_def modify_preserves_deq_filter[OF sys_inv L_def type_bt] by presburger 
      
    (* Proof note. *)
    have mset_eq: "mset base_lin = mset (lin_seq s)"
      using base_def modify_preserves_mset by metis 
      
    have "lin_seq s ! old_k2 \<in> set base_lin"
      using old_props(1) mset_eq by (metis in_set_conv_nth mset_eq_setD)
    then obtain new_k2 where new_k2_props:
      "new_k2 < length base_lin" "base_lin ! new_k2 = lin_seq s ! old_k2"
      by (metis in_set_conv_nth)
      
    (* base_lin distinct *)
    have di: "data_independent (lin_seq s)" using sys_inv unfolding system_invariant_def by auto

    have distinct_lin: "distinct (lin_seq s)"
    proof (unfold distinct_conv_nth, intro allI impI)
      fix i j 
      assume i_lt: "i < length (lin_seq s)" 
      assume j_lt: "j < length (lin_seq s)" 
      assume i_neq_j: "i \<noteq> j"
      
      show "lin_seq s ! i \<noteq> lin_seq s ! j"
      proof
        assume eq: "lin_seq s ! i = lin_seq s ! j"
        let ?v = "op_val (lin_seq s ! i)"
        have val_j: "op_val (lin_seq s ! j) = ?v" using eq by simp
        
        have "i = j"
        proof (cases "op_name (lin_seq s ! i)")
          case enq
          have oper_j: "op_name (lin_seq s ! j) = enq" using eq enq by simp
          have idx_i: "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = ?v) (lin_seq s) = [i]"
            using unique_enq_index[OF di] enq i_lt by simp
          have idx_j: "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = ?v) (lin_seq s) = [j]"
            using unique_enq_index[OF di] oper_j val_j j_lt by simp
          show ?thesis using idx_i idx_j by simp
        next
          case deq
          have oper_j: "op_name (lin_seq s ! j) = deq" using eq deq by simp
          have idx_i: "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = ?v) (lin_seq s) = [i]"
            using unique_deq_index[OF di] deq i_lt by simp
          have idx_j: "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = ?v) (lin_seq s) = [j]"
            using unique_deq_index[OF di] oper_j val_j j_lt by simp
          show ?thesis using idx_i idx_j by simp
        qed
        thus False using i_neq_j by simp
      qed
    qed

    hence dist_base: "distinct base_lin" using mset_eq distinct_lin by (metis mset_eq_imp_distinct_iff)
      
    (* q mk_op *)
    have q_props_s': 
      "new_k2 < length (lin_seq s')"
      "lin_seq s' ! new_k2 = mk_op deq (x_var s' q) q (s_var s' q)"
    proof -
      show "new_k2 < length (lin_seq s')" using new_k2_props(1) s'_lin_def by simp
      have "x_var s' q = x_var s q" using xv_s' False by simp
      moreover have "s_var s' q = s_var s q" using sv_s' by simp
      ultimately show "lin_seq s' ! new_k2 = mk_op deq (x_var s' q) q (s_var s' q)" 
        using new_k2_props s'_lin_def old_props(2) by (simp add: nth_append)
    qed
    
    have q_order_s': "\<forall>new_k3 < length (lin_seq s'). op_name (lin_seq s' ! new_k3) = deq \<and> op_pid (lin_seq s' ! new_k3) = q \<and> new_k3 \<noteq> new_k2 \<longrightarrow>
             new_k3 < new_k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! new_k3)) (op_ssn (lin_seq s' ! new_k3))"
    proof (intro allI impI)
      fix new_k3
      assume k3_bound: "new_k3 < length (lin_seq s')"
      assume cond3: "op_name (lin_seq s' ! new_k3) = deq \<and> op_pid (lin_seq s' ! new_k3) = q \<and> new_k3 \<noteq> new_k2"
                     
      have new_k3_lt: "new_k3 < length base_lin"
      proof (rule ccontr)
        assume "\<not> new_k3 < length base_lin"
        hence "new_k3 = length base_lin" using k3_bound s'_lin_def by auto
        hence "op_pid (lin_seq s' ! new_k3) = p" using s'_lin_def by (simp add: nth_append mk_op_def op_pid_def)
        thus False using cond3 False by simp
      qed
      
      have "base_lin ! new_k3 \<in> set (lin_seq s)"
        using new_k3_lt mset_eq by (metis in_set_conv_nth mset_eq_setD)
      then obtain old_k3 where old_k3_props:
        "old_k3 < length (lin_seq s)" "lin_seq s ! old_k3 = base_lin ! new_k3"
        by (metis in_set_conv_nth)
        
      have "base_lin ! new_k3 \<noteq> base_lin ! new_k2"
        using dist_base new_k3_lt new_k2_props(1) cond3 by (metis nth_eq_iff_index_eq)
      hence old_k3_neq: "old_k3 \<noteq> old_k2"
        using old_k3_props(2) new_k2_props(2) by auto
        
      have P_old_k3: "?P (lin_seq s ! old_k3)"
        using cond3 old_k3_props(2) s'_lin_def new_k3_lt by (simp add: nth_append)
        
      (* 1: 、 old_k2 P , *)
      have P_old_k2: "?P (lin_seq s ! old_k2)"
        using old_props(2) by (simp add: mk_op_def op_name_def op_pid_def)
        
      have old_lt: "old_k3 < old_k2" 
        using old_props(3) old_k3_props(1) P_old_k3 old_k3_neq by blast
        
      have "new_k3 < new_k2"
        using filter_order_preserved filter_eq old_lt old_props(1) P_old_k3 P_old_k2 
              old_k3_props(2) new_k2_props(2) new_k3_lt new_k2_props(1) dist_base
        by (smt (verit, ccfv_SIG) distinct_filter
            filter_order_preserved)
        
      moreover have "DeqRetInHis s' q (op_val (lin_seq s' ! new_k3)) (op_ssn (lin_seq s' ! new_k3))"
      proof -
        have "DeqRetInHis s q (op_val (lin_seq s ! old_k3)) (op_ssn (lin_seq s ! old_k3))"
          using old_props(3) old_k3_props(1) P_old_k3 old_k3_neq by blast
          
        moreover have "op_val (lin_seq s' ! new_k3) = op_val (lin_seq s ! old_k3)"
          using s'_lin_def new_k3_lt old_k3_props(2) by (simp add: nth_append)
          
        moreover have "op_ssn (lin_seq s' ! new_k3) = op_ssn (lin_seq s ! old_k3)"
          using s'_lin_def new_k3_lt old_k3_props(2) by (simp add: nth_append)
          
        ultimately show ?thesis
          using his_eq unfolding DeqRetInHis_def Let_def by auto
      qed     

      ultimately show "new_k3 < new_k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! new_k3)) (op_ssn (lin_seq s' ! new_k3))" by simp
    qed
    
    show ?thesis using q_props_s' q_order_s' False by blast
  qed
qed


(* ========================================================================= *)
(* Auxiliary lemma: D3 hI24_HB_Implies_Idx_Order *)
(* ========================================================================= *)
lemma hI24_HB_Implies_Idx_Order_D3_success_update:
  assumes inv_hI24_HB_Implies_Idx_Order: "hI24_HB_Implies_Idx_Order s"
      and inv_hI20_Enq_Val_Valid: "hI20_Enq_Val_Valid s"
      and update: "s' = Sys_D3_success_update s p"
      and his_eq: "his_seq s' = his_seq s"
  shows "hI24_HB_Implies_Idx_Order s'"
  unfolding hI24_HB_Implies_Idx_Order_def
proof (intro allI impI, elim conjE)
  fix u1 u2 v1 v2 idx1 idx2 sn1 sn2
  assume hb_prime: "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
     and arr1_prime: "CState.Q_arr (fst s') idx1 = v1"
     and arr2_prime: "CState.Q_arr (fst s') idx2 = v2"

  (* Step 1: 1. HB *)
  have hb_s: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
    using hb_prime his_eq unfolding HB_Act_def by simp

  (* Step 2: 2. , v1, v2 \<in> Val *)
  obtain k1 k2 where
    m1: "match_ret (his_seq s) k1 (mk_op enq v2 u2 sn2)" and
    m2: "match_call (his_seq s) k2 (mk_op enq v1 u1 sn1)"
    using hb_s unfolding HB_Act_def HB_def by blast

  have v2_val: "v2 \<in> Val"
  proof -
    have "v2 = act_val (his_seq s ! k1)" using m1 unfolding match_ret_def Let_def
      by (simp add: op_val_def mk_op_def) 
    moreover have "k1 < length (his_seq s)" using m1 unfolding match_ret_def
      by auto 
    moreover have "act_name (his_seq s ! k1) = enq" using m1 unfolding match_ret_def Let_def
      by (simp add: op_name_def mk_op_def) 
    ultimately show "v2 \<in> Val" using inv_hI20_Enq_Val_Valid unfolding hI20_Enq_Val_Valid_def by auto
  qed

  have v1_val: "v1 \<in> Val"
  proof -
    have "v1 = act_val (his_seq s ! k2)" using m2 unfolding match_call_def Let_def
      by (simp add: op_name_def op_val_def mk_op_def) 
    moreover have "k2 < length (his_seq s)" using m2 unfolding match_call_def by simp
    moreover have "act_name (his_seq s ! k2) = enq" using m2 unfolding match_call_def Let_def
      by (simp add: op_name_def mk_op_def) 
    ultimately show "v1 \<in> Val" using inv_hI20_Enq_Val_Valid unfolding hI20_Enq_Val_Valid_def by auto
  qed

  (* Step 3: 3. idx1, idx2 jp *)
  let ?jp = "CState.j_var (fst s) p"
  have Q_jp_bot: "CState.Q_arr (fst s') ?jp = BOT"
    using update unfolding Sys_D3_success_update_def Let_def
    by (auto simp: fun_eq_iff)

  have idx_not_jp: "idx1 \<noteq> ?jp" "idx2 \<noteq> ?jp"
    using arr1_prime arr2_prime Q_jp_bot v1_val v2_val unfolding Val_def BOT_def by auto

  (* Step 4: 4. *)
  have arr_s: "CState.Q_arr (fst s) idx1 = v1" "CState.Q_arr (fst s) idx2 = v2"
    using update arr1_prime arr2_prime idx_not_jp
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: fun_eq_iff)

  (* Step 5: 5. hI24_HB_Implies_Idx_Order *)
  from inv_hI24_HB_Implies_Idx_Order[unfolded hI24_HB_Implies_Idx_Order_def] hb_s arr_s show "idx2 < idx1" by blast
qed


(* ========================================================================= *)
(* hI21_D3_step_helper *)
(* D3 BOT , E2 HB . *)
(* ========================================================================= *)
lemma hI21_D3_step_helper:
  assumes INV: "system_invariant s"
      and STEP: "Sys_D3 p s s'"
      and q_val: "Q_arr s (j_var s p) = BOT"
  shows "hI29_E2_Scanner_Immunity s'"
proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI, goal_cases)
  case (1 p_enq a q)
  
  (* goal_cases , *)
  have asm_1: "program_counter s' p_enq = ''E2''" using 1(1) by blast
  have asm_2: "TypeB s' a"  by (simp add: "1") 
  have asm_3: "HasPendingDeq s' q" by (simp add: "1") 
  have asm_4: "program_counter s' q = ''D3''"  by (simp add: "1") 
  have asm_5: "Idx s' a < j_var s' q"  by (simp add: "1") 
  have asm_6: "j_var s' q \<le> i_var s' p_enq"  by (simp add: "1") 
  have asm_7: "i_var s' p_enq < l_var s' q"  by (simp add: "1") 

  (* 1. *)
  note bridge_defs = program_counter_def j_var_def l_var_def Q_arr_def x_var_def
                     Qback_arr_def i_var_def v_var_def s_var_def his_seq_def

  (* 2. *)
  have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast
  have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by blast

  (* 3. D3 BOT *)
  from STEP have pc_s_p: "program_counter s p = ''D3'' " 
    unfolding Sys_D3_def C_D3_def bridge_defs by auto

  from STEP q_val have pc_s'_p: "program_counter s' p = (if j_var s p = l_var s p - 1 then ''D1'' else ''D3'')"
    unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)

  from STEP q_val have j_var_inc: "j_var s' p = (if j_var s p = l_var s p - 1 then j_var s p else j_var s p + 1)"
    unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)

  (* 4. *)
  have conservations: 
    "his_seq s' = his_seq s" 
    "Qback_arr s' = Qback_arr s"
    "i_var s' = i_var s"
    "v_var s' = v_var s"
    "s_var s' = s_var s"
  proof -
    from STEP q_val show 
      "his_seq s' = his_seq s" 
      "Qback_arr s' = Qback_arr s"
      "i_var s' = i_var s"
      "v_var s' = v_var s"
      "s_var s' = s_var s"
      unfolding Sys_D3_def C_D3_def Let_def bridge_defs
      by (auto split: if_splits)
  qed

  hence his_eq: "his_seq s' = his_seq s" 
    and qback_eq: "Qback_arr s' = Qback_arr s"
    and i_var_eq: "i_var s' = i_var s"
    and v_var_eq: "v_var s' = v_var s"
    and s_var_eq: "s_var s' = s_var s" by auto

  have Q_arr_eq: "Q_arr s' = Q_arr s"
  proof (rule ext)
    fix k
    note accessors = Q_arr_def j_var_def 
    show "Q_arr s' k = Q_arr s k"
    proof (cases "k = j_var s p", goal_cases)
      case 1
      thus ?thesis using STEP q_val unfolding Sys_D3_def C_D3_def Let_def accessors by auto
    next
      case 2
      thus ?thesis using STEP q_val unfolding Sys_D3_def C_D3_def Let_def accessors by auto
    qed
  qed

  (* 5. *)
  have hb_eq: "HB_EnqRetCall s' a (v_var s' p_enq) = HB_EnqRetCall s a (v_var s p_enq)"
    unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def using his_eq
    by (simp add: v_var_eq) 
  
  have idx_a_eq: "Idx s' a = Idx s a" unfolding Idx_def AtIdx_def using qback_eq by simp

  have pc_E2_eq: "\<forall>p_any. (program_counter s' p_any = ''E2'') \<longleftrightarrow> (program_counter s p_any = ''E2'')"
  proof
    fix x
    show "program_counter s' x = ''E2'' \<longleftrightarrow> program_counter s x = ''E2'' "
    proof (cases "x = p", goal_cases)
      case 1
      have old: "program_counter s x = ''D3'' " using pc_s_p 1 by simp
      have new: "program_counter s' x \<noteq> ''E2'' "
        using STEP q_val 1 unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)
      thus ?thesis using old by auto
    next
      case 2
      have "program_counter s' x = program_counter s x"
        using STEP 2 unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)
      then show ?thesis by simp
    qed
  qed

  have tb_a_s: "TypeB s a" 
  proof -
    from asm_2 have "QHas s' a \<or> (\<exists>px. program_counter s' px = ''E2'' \<and> v_var s' px = a)"
      unfolding TypeB_def by simp
    thus ?thesis
    proof (elim disjE, goal_cases)
      case 1
      hence "QHas s a" unfolding QHas_def using Q_arr_eq by simp
      thus ?thesis unfolding TypeB_def by blast
    next
      case 2
      then obtain px where "program_counter s' px = ''E2''" and "v_var s' px = a" by blast
      hence "program_counter s px = ''E2''" and "v_var s px = a" using pc_E2_eq v_var_eq by auto
      thus ?thesis unfolding TypeB_def by blast
    qed
  qed

  have pc_e_s: "program_counter s p_enq = ''E2''" using asm_1 pc_E2_eq by auto
  have p_enq_neq_p: "p_enq \<noteq> p" using pc_e_s pc_s_p by auto

  (* 4. : q D3 p *)
  show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
  proof (cases "q = p")
    case True (* q = p  *)
    
    have l_p_eq: "l_var s' p = l_var s p"
      using STEP unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)

    have pc_p_D3: "program_counter s' p = ''D3''" using asm_4 True by simp

    have j_neq_l: "j_var s p \<noteq> l_var s p - 1"
    proof
      assume "j_var s p = l_var s p - 1"
      hence "program_counter s' p = ''D1''" using pc_s'_p by simp
      with pc_p_D3 show False by simp
    qed

    have j_inc: "j_var s' p = j_var s p + 1" 
      using j_var_inc j_neq_l by simp

    have pend_p_s: "HasPendingDeq s p" 
      using INV pc_s_p unfolding system_invariant_def hI12_D_Phase_Pending_Deq_def by auto

    have idx_lt_j_next: "Idx s a < j_var s p + 1" using asm_5 True j_inc idx_a_eq by simp
    hence a_cmp_j: "Idx s a < j_var s p \<or> Idx s a = j_var s p" by linarith

    show ?thesis
    proof (cases "Idx s a < j_var s p")
      case True (* A: a *)
      
      have cond1: "Idx s a < j_var s p" using True by simp
      
      have cond2: "j_var s p \<le> i_var s p_enq" 
      proof -
        from asm_6 \<open>q = p\<close> have "j_var s' p \<le> i_var s' p_enq" by simp
        moreover have "j_var s' p = j_var s p + 1" using j_inc by simp
        moreover have "i_var s' p_enq = i_var s p_enq" using i_var_eq by simp
        ultimately show ?thesis by linarith
      qed
        
      have cond3: "i_var s p_enq < l_var s p"
      proof -
        from asm_7 \<open>q = p\<close> have "i_var s' p_enq < l_var s' p" by simp
        moreover have "i_var s' p_enq = i_var s p_enq" using i_var_eq by simp
        moreover have "l_var s' p = l_var s p" using l_p_eq by simp
        ultimately show ?thesis by linarith
      qed

      have "\<not> HB_EnqRetCall s a (v_var s p_enq)"
        using hI21_s[unfolded hI29_E2_Scanner_Immunity_def, rule_format, of p_enq a p]
        using pc_e_s tb_a_s pend_p_s pc_s_p cond1 cond2 cond3
        using HB_implies_InQBack INV by blast 
        
      thus ?thesis using hb_eq by simp
    next
      case False (* B: Idx s a = j_var s p  *)
      hence idx_is_j: "Idx s a = j_var s p" using a_cmp_j by linarith
      have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" using INV unfolding system_invariant_def by blast
      
      show ?thesis
      proof (cases "a = BOT")
        case True (* hI20_Enq_Val_Valid *)
        show ?thesis
        proof (* notI *)
          assume hb: "HB_EnqRetCall s' a (v_var s' p_enq)"

          (* op_name_def op_val_def, force *)
          have "\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = BOT"
            using hb True his_eq 
            unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def op_name_def op_val_def
            by auto

          then obtain k where k_len: "k < length (his_seq s)" 
                          and k_op: "act_name (his_seq s ! k) = enq" 
                          and k_val: "act_val (his_seq s ! k) = BOT" by blast
          from hI20_Enq_Val_Valid_s k_len k_op have "act_val (his_seq s ! k) \<in> Val" unfolding hI20_Enq_Val_Valid_def by blast
          with k_val have "BOT \<in> Val" by simp
          thus False by (simp add: BOT_def Val_def)  
        qed
      next
        case False (* sI8_Q_Qback_Sync TypeB *)
        hence a_not_bot: "a \<noteq> BOT" by simp
        
        from tb_a_s[unfolded TypeB_def] show ?thesis
        proof (elim disjE)
          assume "QHas s a"
          then obtain k where k_idx: "Q_arr s k = a" unfolding QHas_def by blast
          
          from INV have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" unfolding system_invariant_def by blast
          have "Qback_arr s k = a" using sI8_Q_Qback_Sync_s k_idx a_not_bot unfolding sI8_Q_Qback_Sync_def by force
          hence "k = Idx s a" unfolding Idx_def AtIdx_def
            using INV Idx_eq_j_and_Q_BOT_implies_not_TypeB InQBack_def a_not_bot
              idx_is_j q_val tb_a_s by blast 
          with idx_is_j have "Q_arr s (j_var s p) = a" using k_idx by simp
          
          with q_val a_not_bot show ?thesis by simp
        next
          assume "\<exists>p_o. program_counter s p_o = ''E2'' \<and> v_var s p_o = a"
          then obtain p_o where po: "program_counter s p_o = ''E2'' \<and> v_var s p_o = a" by blast
          
          show ?thesis 
          proof (* notI *)
            assume hb_s': "HB_EnqRetCall s' a (v_var s' p_enq)"
            hence hb_s: "HB_EnqRetCall s a (v_var s p_enq)" using hb_eq by simp
            
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
              
            have pending_po: "HasPendingEnq s p_o a" using hI1_E_Phase_Pending_Enq_s po unfolding hI1_E_Phase_Pending_Enq_def by blast
            have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and> 
                                                act_val (his_seq s ! j_call) = a \<and> 
                                                act_cr (his_seq s ! j_call) = call \<and> 
                                                act_pid (his_seq s ! j_call) = p_o \<and> 
                                                act_ssn (his_seq s ! j_call) = s_var s p_o"
              using pending_po unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
              by (metis in_set_conv_nth) 
            then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                                 and j_call_op: "act_name (his_seq s ! j_call) = enq"
                                 and j_call_val: "act_val (his_seq s ! j_call) = a"
                                 and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                                 and j_call_pid: "act_pid (his_seq s ! j_call) = p_o"
                                 and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s p_o" by blast
                                 
            from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
            have "k_call = j_call"
              using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
              unfolding hI8_Val_Unique_def by blast
              
            hence "act_pid (his_seq s ! k_ret) = p_o" and "act_ssn (his_seq s ! k_ret) = s_var s p_o"
              using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all
              
            moreover have "\<not> (\<exists>k < length (his_seq s). act_pid (his_seq s ! k) = p_o \<and> act_ssn (his_seq s ! k) = s_var s p_o \<and> act_cr (his_seq s ! k) = ret)"
              using pending_po unfolding HasPendingEnq_def EnqRetInHis_def Let_def match_ret_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
              by force
              
            ultimately show False using k_ret_len k_ret_cr by blast
          qed
        qed
      qed
    qed

  next
    case False (* q \<noteq> p (q ) *)
    
    have pc_q_eq: "program_counter s' q = program_counter s q"
      using False STEP unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)
    have j_q_eq: "j_var s' q = j_var s q"
      using False STEP unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)
    have l_q_eq: "l_var s' q = l_var s q"
      using False STEP unfolding Sys_D3_def C_D3_def Let_def bridge_defs by (auto split: if_splits)

    have pc_q_s: "program_counter s q = ''D3''" using asm_4 pc_q_eq by simp
    have pend_q_s: "HasPendingDeq s q" 
      using asm_3 s_var_eq his_eq 
      unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def by auto
    
    have cond1: "Idx s a < j_var s q" using asm_5 idx_a_eq j_q_eq by simp
    have cond2: "j_var s q \<le> i_var s p_enq" using asm_6 j_q_eq i_var_eq by simp
    have cond3: "i_var s p_enq < l_var s q" using asm_7 i_var_eq l_q_eq by simp

    have "\<not> HB_EnqRetCall s a (v_var s p_enq)"
      using hI21_s[unfolded hI29_E2_Scanner_Immunity_def, rule_format, of p_enq a q]
      using pc_e_s tb_a_s pend_q_s pc_q_s cond1 cond2 cond3
      using HB_implies_InQBack INV by blast 
      
    thus ?thesis using hb_eq by simp
  qed
qed

(* ********************Auxiliary lemma********************** *)
lemma D3_step_unfolded:
  fixes s s' :: SysState and p jp lp q_val current_lin current_his base_lin
  assumes STEP: "Sys_D3 p s s'"
    and jp_def: "jp = j_var s p"
    and lp_def: "lp = l_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and current_lin_def: "current_lin = lin_seq s"
    and current_his_def: "current_his = his_seq s"
    and base_lin_def: "base_lin =
      (if q_val = BOT then current_lin
       else if should_modify current_lin current_his q_val
            then modify_lin current_lin current_his q_val
            else current_lin)"
  shows
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
proof -
  show "program_counter s p = ''D3''"
    using STEP
    unfolding Sys_D3_def C_D3_def program_counter_def Q_arr_def
    by simp

  show "s' = (
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
    using STEP
    unfolding Sys_D3_def C_D3_def U_D2_def Let_def
              jp_def lp_def q_val_def base_lin_def current_lin_def current_his_def
    by (auto simp: prod_eq_iff Q_arr_def j_var_def l_var_def x_var_def s_var_def
                   program_counter_def lin_seq_def his_seq_def fun_eq_iff)
qed

lemma D3_bot_branch_simp:
  fixes s s' :: SysState and p jp lp q_val current_lin current_his base_lin
  assumes STEP: "Sys_D3 p s s'"
    and jp_def: "jp = j_var s p"
    and lp_def: "lp = l_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and current_lin_def: "current_lin = lin_seq s"
    and current_his_def: "current_his = his_seq s"
    and base_lin_def: "base_lin =
      (if q_val = BOT then current_lin
       else if should_modify current_lin current_his q_val
            then modify_lin current_lin current_his q_val
            else current_lin)"
    and q_is_bot: "q_val = BOT"
  shows
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
proof -
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

  show "lin_seq s' = lin_seq s"
    using D3_unfolded(2) q_is_bot
    by (simp add: lin_seq_def)

  show "his_seq s' = his_seq s"
    using D3_unfolded(2) q_is_bot
    by (simp add: his_seq_def)

  show "base_lin = lin_seq s"
    unfolding base_lin_def current_lin_def
    using q_is_bot
    by simp

  show "s' = (
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
    using D3_unfolded(2) q_is_bot
    by (auto simp: fun_eq_iff)
qed

lemma D3_bot_preserves_basic_invariants:
  fixes s s' :: SysState and p jp lp
  assumes INV: "system_invariant s"
    and TypeOK_s: "TypeOK s"
    and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s"
    and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s"
    and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s"
    and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s"
    and jp_def: "jp = j_var s p"
    and lp_def: "lp = l_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and q_is_bot: "q_val = BOT"
    and D3_pc: "program_counter s p = ''D3''"
    and s'_simple: "s' = (
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
  shows
    "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
    "Q_arr s jp = BOT"
    "TypeOK s'"
    "sI1_Zero_Index_BOT s'"
    "sI2_X_var_Upper_Bound s'"
    "sI3_E2_Slot_Exclusive s'"
    "sI4_E3_Qback_Written s'"
    "sI5_D2_Local_Bound s'"
    "sI6_D3_Scan_Pointers s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def

  have pc_update:
    "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
    using s'_simple unfolding program_counter_def
    by (auto simp: fun_eq_iff)

  have Q_jp_bot: "Q_arr s jp = BOT"
    using q_is_bot q_val_def by (simp add: bridge_defs)

  show "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
    using pc_update .

  show "Q_arr s jp = BOT"
    using Q_jp_bot .

  show "TypeOK s'"
    using TypeOK_s s'_simple q_is_bot
    by (auto simp: TypeOK_def Val_def BOT_def
                   program_counter_def X_var_def V_var_def
                   Q_arr_def Qback_arr_def i_var_def j_var_def
                   l_var_def x_var_def v_var_def s_var_def)

  show "sI1_Zero_Index_BOT s'"
    using sI1_Zero_Index_BOT_s s'_simple q_is_bot
    by (auto simp: sI1_Zero_Index_BOT_def bridge_defs)

  show "sI2_X_var_Upper_Bound s'"
    using sI2_X_var_Upper_Bound_s s'_simple q_is_bot
    by (auto simp: sI2_X_var_Upper_Bound_def bridge_defs)

  show "sI3_E2_Slot_Exclusive s'"
    using sI3_E2_Slot_Exclusive_s s'_simple D3_pc
    by (auto simp: sI3_E2_Slot_Exclusive_def bridge_defs)

  show "sI4_E3_Qback_Written s'"
    using sI4_E3_Qback_Written_preserved_under_D3_BOT[OF INV Q_jp_bot s'_simple] .

  show "sI5_D2_Local_Bound s'"
    using sI5_D2_Local_Bound_s s'_simple D3_pc
    by (auto simp: sI5_D2_Local_Bound_def bridge_defs)

  show "sI6_D3_Scan_Pointers s'"
  proof -
    have p_props_s:
      "j_var s p \<in> Val"
      "l_var s p \<in> Val"
      "1 \<le> j_var s p"
      "j_var s p < l_var s p"
      "l_var s p \<le> X_var s"
      using sI6_D3_Scan_Pointers_s D3_pc
      unfolding sI6_D3_Scan_Pointers_def
      by auto

    show ?thesis
      unfolding sI6_D3_Scan_Pointers_def
    proof (intro allI impI)
      fix q
      assume asm_D3: "program_counter s' q = ''D3''"

      show "j_var s' q \<in> Val \<and> l_var s' q \<in> Val \<and> 1 \<le> j_var s' q \<and>
            j_var s' q < l_var s' q \<and> l_var s' q \<le> X_var s'"
      proof (cases "q = p")
        case False
        have pc_s: "program_counter s q = ''D3''"
          using asm_D3 s'_simple False bridge_defs by auto

        have vars_same:
          "j_var s' q = j_var s q"
          "l_var s' q = l_var s q"
          "X_var s' = X_var s"
          using s'_simple False bridge_defs by auto

        have "j_var s q \<in> Val \<and> l_var s q \<in> Val \<and> 1 \<le> j_var s q \<and>
              j_var s q < l_var s q \<and> l_var s q \<le> X_var s"
          using sI6_D3_Scan_Pointers_s pc_s
          unfolding sI6_D3_Scan_Pointers_def by blast

        then show ?thesis
          using vars_same by simp
      next
        case True
        have not_boundary: "jp \<noteq> lp - 1"
        proof (rule ccontr)
          assume "\<not> (jp \<noteq> lp - 1)"
          then have "jp = lp - 1" by simp
          then have "program_counter s' p = ''D1''"
            using s'_simple True bridge_defs by simp
          then show False
            using asm_D3 True by simp
        qed

        have jp_lt_lp: "jp < lp"
          using p_props_s unfolding jp_def lp_def by simp

        have arithmetic_hold: "jp + 1 < lp"
          using jp_lt_lp not_boundary by linarith

        have j_new: "j_var s' p = jp + 1"
          using s'_simple True not_boundary
          unfolding jp_def lp_def bridge_defs by auto

        have others_new:
          "l_var s' p = lp"
          "X_var s' = X_var s"
          using s'_simple True unfolding lp_def bridge_defs by auto

        have "jp \<in> Val"
          using p_props_s unfolding jp_def by simp
        then have val_jp_plus_1: "jp + 1 \<in> Val"
          unfolding Val_def by auto

        show ?thesis
          using j_new others_new arithmetic_hold p_props_s val_jp_plus_1
          unfolding jp_def lp_def Val_def
          using True le_add2 by presburger
      qed
    qed
  qed
qed

lemma D3_bot_preserves_more_invariants:
  fixes s s' :: SysState and p jp lp
  assumes INV: "system_invariant s"
    and s'_simple: "s' = (
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
    and his_seq_eq: "his_seq s' = his_seq s"
    and D3_pc: "program_counter s p = ''D3''"
    and sI4_s': "sI4_E3_Qback_Written s'"
    and Q_jp_bot: "Q_arr s jp = BOT"
    and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s"
    and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
    and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s"
    and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s"
    and sI11_x_var_Scope_s: "sI11_x_var_Scope s"
  shows
    "sI7_D4_Deq_Result s'"
    "hI3_L0_E_Phase_Bounds s'"
    "sI8_Q_Qback_Sync s'"
    "sI9_Qback_Discrepancy_E3 s'"
    "sI10_Qback_Unique_Vals s'"
    "hI2_SSN_Bounds s'"
    "sI11_x_var_Scope s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  show "sI7_D4_Deq_Result s'"
    using sI7_D4_Deq_Result_s s'_simple D3_pc
    by (auto simp: sI7_D4_Deq_Result_def bridge_defs)

  show "hI3_L0_E_Phase_Bounds s'"
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    have q_ne_p: "q \<noteq> p"
      using 1 s'_simple unfolding bridge_defs by (auto split: if_splits)
    have old_L0: "program_counter s q = ''L0''"
      using 1 q_ne_p s'_simple unfolding bridge_defs by (auto split: if_splits)

    have pend_enq_eq: "HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a" for a
      using his_seq_eq s'_simple unfolding HasPendingEnq_def Let_def bridge_defs
      by (auto simp: EnqCallInHis_def)

    have pend_deq_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
      using his_seq_eq s'_simple unfolding HasPendingDeq_def Let_def bridge_defs
      by (simp add: DeqCallInHis_def)

    show ?case
      using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s old_L0]
            pend_enq_eq pend_deq_eq
      by simp
  next
    case (2 q)
    have q_ne_p: "q \<noteq> p"
      using 2 s'_simple unfolding bridge_defs by (auto split: if_splits)
    have old_L0: "program_counter s q = ''L0''"
      using 2 q_ne_p s'_simple unfolding bridge_defs by (auto split: if_splits)

    show ?case
      using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s old_L0]
            his_seq_eq
      by simp
  next
    case (3 q)
    have q_ne_p: "q \<noteq> p"
      using 3 s'_simple unfolding bridge_defs by (auto split: if_splits)
    have old_E: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using 3 q_ne_p s'_simple unfolding bridge_defs by (auto split: if_splits)

    show ?case
      using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s old_E]
            s'_simple
      unfolding bridge_defs
      by (auto split: if_splits)
  next
    case (4 k)
    show ?case
      using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s] 4 his_seq_eq s'_simple
      unfolding bridge_defs
      by (auto split: if_splits)
  next
    case (5 k)
    show ?case
      using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s] s'_simple
      unfolding bridge_defs
      by (auto split: if_splits)
  qed

  show "sI8_Q_Qback_Sync s'"
    using sI8_Q_Qback_Sync_s s'_simple
    by (auto simp: sI8_Q_Qback_Sync_def bridge_defs)

  show "sI9_Qback_Discrepancy_E3 s'"
  proof -
    have Q_unchanged: "Q_arr s' = Q_arr s"
      using s'_simple Q_jp_bot
      by (auto simp: fun_eq_iff bridge_defs)

    have T_unchanged: "Qback_arr s' = Qback_arr s"
      using s'_simple by (auto simp: bridge_defs)

  show ?thesis
  proof (unfold sI9_Qback_Discrepancy_E3_def, intro allI impI)
    fix k q
    assume Hk: "Q_arr s' k = BOT \<and> Qback_arr s' k \<noteq> BOT"
    assume HE3: "program_counter s' q \<in> {''E3''} \<and> i_var s' q = k"

    have Hk_old: "Q_arr s k = BOT \<and> Qback_arr s k \<noteq> BOT"
      using Hk Q_unchanged T_unchanged
      by simp

    have i_same: "i_var s' q = i_var s q"
      using s'_simple unfolding bridge_defs by auto

    have v_same: "v_var s' q = v_var s q"
      using s'_simple unfolding bridge_defs by auto

    have pc_old: "program_counter s q \<in> {''E3''}"
    proof -
      have q_ne_p: "q \<noteq> p"
      proof
        assume "q = p"
        then have "program_counter s' q \<noteq> ''E3''"
          using s'_simple unfolding bridge_defs by auto
        with HE3 show False by auto
      qed
      then show ?thesis
        using HE3 s'_simple unfolding bridge_defs by auto
    qed

    have E3_old: "program_counter s q \<in> {''E3''} \<and> i_var s q = k"
      using HE3 pc_old i_same
      by auto

    have old_result: "v_var s q = Qback_arr s k"
      using sI9_Qback_Discrepancy_E3_s Hk_old E3_old
      unfolding sI9_Qback_Discrepancy_E3_def
      by auto

    show "v_var s' q = Qback_arr s' k"
      using old_result v_same T_unchanged
      by simp
  qed
  qed

  show "sI10_Qback_Unique_Vals s'"
  proof -
    have T_is_same: "Qback_arr s' = Qback_arr s"
      using s'_simple by (simp add: bridge_defs)

    show ?thesis
      using sI10_Qback_Unique_Vals_s T_is_same
      unfolding sI10_Qback_Unique_Vals_def
      by simp
  qed

  show "hI2_SSN_Bounds s'"
  proof -
    have hI2_s: "hI2_SSN_Bounds s"
      using INV unfolding system_invariant_def by blast

    have pc_p_not_L0: "program_counter s' p \<noteq> ''L0''"
      using s'_simple by (auto simp: program_counter_def)

    have pc_other_eq: "\<forall>q. q \<noteq> p \<longrightarrow> program_counter s' q = program_counter s q"
      using s'_simple by (auto simp: program_counter_def)

    have s_var_eq: "s_var s' = s_var s"
      using s'_simple by (auto simp: s_var_def)

    show ?thesis
      using hI2_s pc_p_not_L0 pc_other_eq his_seq_eq s_var_eq
      unfolding hI2_SSN_Bounds_def
      by auto
  qed

  show "sI11_x_var_Scope s'"
  proof (unfold sI11_x_var_Scope_def, intro allI impI, goal_cases)
    case (1 q)
    show ?case
    proof (cases "q = p")
      case True
      show ?thesis
        using True s'_simple unfolding bridge_defs by auto
    next
      case False
      have "program_counter s q = program_counter s' q"
        using False s'_simple unfolding bridge_defs by auto
      then have "program_counter s q \<noteq> ''D4''"
        using 1 by simp
      then have "x_var s q = BOT"
        using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def by blast
      then show ?thesis
        using False s'_simple unfolding bridge_defs by auto
    qed
  qed
qed

lemma D3_bot_preserves_pending_and_prefix:
  fixes s s' :: SysState and p jp q_val
  assumes INV: "system_invariant s"
    and s'_simple: "s' = (
      (fst s)\<lparr>
        c_program_counter := (\<lambda>x. if x = p then
             (if jp = l_var s p - 1 then ''D1'' else ''D3'')
           else CState.c_program_counter (fst s) x),
        Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr (fst s) x),
        j_var := (\<lambda>x. if x = p then
             (if jp \<noteq> l_var s p - 1 then jp + 1 else jp)
           else CState.j_var (fst s) x),
        x_var := (\<lambda>x. if x = p then BOT else CState.x_var (fst s) x)
      \<rparr>,
      snd s
    )"
    and his_seq_eq: "his_seq s' = his_seq s"
    and D3_pc: "program_counter s p = ''D3''"
    and jp_def: "jp = j_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and q_is_bot: "q_val = BOT"
    and sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s"
  shows
    "hI1_E_Phase_Pending_Enq s'"
    "Q_arr s' = Q_arr s"
    "Qback_arr s' = Qback_arr s"
    "SetA s' = SetA s"
    "SetB s' = SetB s"
    "(\<forall>x. TypeB s' x \<longleftrightarrow> TypeB s x)"
    "sI12_D3_Scanned_Prefix s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have inv_hI1_E_Phase_Pending_Enq: "hI1_E_Phase_Pending_Enq s"
    using INV unfolding system_invariant_def by blast

  have pc_p_not_E: "program_counter s' p \<notin> {''E1'', ''E2'', ''E3''}"
    using s'_simple by (auto simp: program_counter_def)

  have pc_other_eq: "\<forall>q. q \<noteq> p \<longrightarrow> program_counter s' q = program_counter s q"
    using s'_simple by (auto simp: program_counter_def)

  have v_var_eq: "v_var s' = v_var s"
    using s'_simple by (auto simp: v_var_def fun_eq_iff)

  have s_var_eq: "s_var s' = s_var s"
    using s'_simple by (auto simp: s_var_def fun_eq_iff)

  have hI1_E_s': "hI1_E_Phase_Pending_Enq s'"
    using inv_hI1_E_Phase_Pending_Enq pc_p_not_E pc_other_eq his_seq_eq v_var_eq s_var_eq
    unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def EnqCallInHis_def
    by auto

  have Q_unchanged: "Q_arr s' = Q_arr s"
    using s'_simple q_val_def q_is_bot bridge_defs
    by (auto simp: fun_eq_iff)

  have T_unchanged: "Qback_arr s' = Qback_arr s"
    using s'_simple bridge_defs
    by (auto simp: fun_eq_iff)

  have TypeB_iff: "\<And>x. TypeB s' x \<longleftrightarrow> TypeB s x"
  proof -
    fix x

    have QHas_eq: "QHas s' x \<longleftrightarrow> QHas s x"
      using Q_unchanged unfolding QHas_def by simp

    have E2_eq:
      "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow>
       (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
    proof
      assume "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x"
      then obtain q where q_stat: "program_counter s' q = ''E2''" "v_var s' q = x"
        by blast

      have "q \<noteq> p"
      proof
        assume "q = p"
        then show False
          using q_stat s'_simple D3_pc bridge_defs
          by (auto split: if_splits)
      qed

      then have "program_counter s q = ''E2''" "v_var s q = x"
        using q_stat s'_simple bridge_defs
        by auto

      then show "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x"
        by blast
    next
      assume "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x"
      then obtain q where q_stat: "program_counter s q = ''E2''" "v_var s q = x"
        by blast

      have "q \<noteq> p"
        using q_stat D3_pc by auto

      then have "program_counter s' q = ''E2''" "v_var s' q = x"
        using q_stat s'_simple bridge_defs
        by auto

      then show "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x"
        by blast
    qed

    show "TypeB s' x \<longleftrightarrow> TypeB s x"
      unfolding TypeB_def
      using QHas_eq E2_eq
      by blast
  qed

  have SetA_eq: "SetA s' = SetA s"
    unfolding SetA_def TypeA_def InQBack_def QHas_def
    using Q_unchanged T_unchanged
    by simp

  have SetB_eq: "SetB s' = SetB s"
    unfolding SetB_def
    using TypeB_iff
    by auto

  have sI12_s': "sI12_D3_Scanned_Prefix s'"
    unfolding sI12_D3_Scanned_Prefix_def
  proof (rule allI, rule impI)
    fix q
    assume pc_new_D3: "program_counter s' q = ''D3''"

    show "\<forall>k < j_var s' q. Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
    proof (cases "q = p")
      case False
      have pc_old_D3: "program_counter s q = ''D3''"
        using pc_new_D3 s'_simple False bridge_defs
        by auto

      have j_same: "j_var s' q = j_var s q"
        using s'_simple False bridge_defs
        by auto

      have old_prop: "\<forall>k < j_var s q. Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
        using sI12_D3_Scanned_Prefix_s pc_old_D3
        unfolding sI12_D3_Scanned_Prefix_def
        by blast

      show ?thesis
        using old_prop j_same Q_unchanged TypeB_iff
        by simp
    next
      case True
      have not_boundary: "jp \<noteq> l_var s p - 1"
      proof (rule ccontr)
        assume "\<not> (jp \<noteq> l_var s p - 1)"
        then have "jp = l_var s p - 1"
          by simp
        then have "program_counter s' p = ''D1''"
          using s'_simple True q_is_bot bridge_defs
          by simp
        with pc_new_D3 True show False
          by simp
      qed

      have j_new: "j_var s' p = jp + 1"
        using s'_simple True not_boundary q_is_bot unfolding jp_def bridge_defs
        by simp

      show ?thesis
        unfolding True j_new
      proof (intro allI impI)
        fix k
        assume k_bound: "k < jp + 1"

        show "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
        proof (cases "k = jp")
          case True
          have "Q_arr s' jp = BOT"
            using Q_unchanged q_is_bot q_val_def
            by simp
          then show ?thesis
            using True by simp
        next
          case False
          have "k < jp"
            using k_bound False by simp

          have old_prop_k: "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
            using sI12_D3_Scanned_Prefix_s D3_pc `k < jp`
            unfolding sI12_D3_Scanned_Prefix_def jp_def
            by (simp add: jp_def)

          then show ?thesis
            using Q_unchanged TypeB_iff
            by simp
        qed
      qed
    qed
  qed

  show "hI1_E_Phase_Pending_Enq s'"
    using hI1_E_s' .

  show "Q_arr s' = Q_arr s"
    using Q_unchanged .

  show "Qback_arr s' = Qback_arr s"
    using T_unchanged .

  show "SetA s' = SetA s"
    using SetA_eq .

  show "SetB s' = SetB s"
    using SetB_eq .

  show "(\<forall>x. TypeB s' x \<longleftrightarrow> TypeB s x)"
    using TypeB_iff by blast

  show "sI12_D3_Scanned_Prefix s'"
    using sI12_s' .
qed

lemma D3_bot_preserves_history_tail:
  fixes s s' :: SysState and p jp lp
  assumes INV: "system_invariant s"
    and D3_pc: "program_counter s p = ''D3''"
    and s'_simple: "s' = (
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
    and his_seq_eq: "his_seq s' = his_seq s"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
    and Q_unchanged: "Q_arr s' = Q_arr s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
  shows
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
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI4_s: "hI4_X_var_Lin_Sync s"
    using INV unfolding system_invariant_def by blast
  have hI7_s: "hI7_His_WF s"
    using INV unfolding system_invariant_def by blast
  have hI8_s: "hI8_Val_Unique s"
    using INV unfolding system_invariant_def by blast
  have hI6_s: "hI6_SSN_Order s"
    using INV unfolding system_invariant_def by blast
  have hI5_s: "hI5_SSN_Unique s"
    using INV unfolding system_invariant_def by blast
  have hI9_s: "hI9_Deq_Ret_Unique s"
    using INV unfolding system_invariant_def by blast
  have hI10_s: "hI10_Enq_Call_Existence s"
    using INV unfolding system_invariant_def by blast
  have hI11_s: "hI11_Enq_Ret_Existence s"
    using INV unfolding system_invariant_def by blast
  have hI12_s: "hI12_D_Phase_Pending_Deq s"
    using INV unfolding system_invariant_def by blast
  have hI13_s: "hI13_Qback_Deq_Sync s"
    using INV unfolding system_invariant_def by blast
  have hI14_s: "hI14_Pending_Enq_Qback_Exclusivity s"
    using INV unfolding system_invariant_def by blast
  have hI18_s: "hI18_Idx_Order_No_Rev_HB s"
    using INV unfolding system_invariant_def by blast
  have hI20_s: "hI20_Enq_Val_Valid s"
    using INV unfolding system_invariant_def by blast
  have hI21_s: "hI21_Ret_Implies_Call s"
    using INV unfolding system_invariant_def by blast
  have hI22_s: "hI22_Deq_Local_Pattern s"
    using INV unfolding system_invariant_def by blast
  have hI23_s: "hI23_Deq_Call_Ret_Balanced s"
    using INV unfolding system_invariant_def by blast
  have hI24_s: "hI24_HB_Implies_Idx_Order s"
    using INV unfolding system_invariant_def by blast
  have hI25_s: "hI25_Enq_Call_Ret_Balanced s"
    using INV unfolding system_invariant_def by blast
  have hI26_s: "hI26_DeqRet_D4_Mutex s"
    using INV unfolding system_invariant_def by blast
  have hI27_s: "hI27_Pending_PC_Sync s"
    using INV unfolding system_invariant_def by blast
  have hI28_s: "hI28_Fresh_Enq_Immunity s"
    using INV unfolding system_invariant_def by blast
  have sI11_s: "sI11_x_var_Scope s"
    using INV unfolding system_invariant_def by blast

  have X_var_eq: "X_var s' = X_var s"
    using s'_simple by (auto simp: X_var_def)

  have pc_update:
    "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
    using s'_simple unfolding program_counter_def
    by (auto simp: fun_eq_iff)

  have pc_p_not_E: "program_counter s' p \<notin> {''E1'', ''E2'', ''E3''}"
    using s'_simple by (auto simp: program_counter_def)

  have pc_other_eq: "\<forall>q. q \<noteq> p \<longrightarrow> program_counter s' q = program_counter s q"
    using s'_simple by (auto simp: program_counter_def)

  have v_var_eq: "v_var s' = v_var s"
    using s'_simple by (auto simp: v_var_def fun_eq_iff)

  have s_var_eq: "s_var s' = s_var s"
    using s'_simple by (auto simp: s_var_def fun_eq_iff)

  have x_p_bot_s: "x_var s p = BOT"
    using sI11_s D3_pc unfolding sI11_x_var_Scope_def by simp

  have x_eq: "x_var s' = x_var s"
    using s'_simple x_p_bot_s by (auto simp: x_var_def fun_eq_iff)

  have pc_D_eq:
    "\<forall>q. (program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}) \<longleftrightarrow>
         (program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''})"
    using s'_simple D3_pc by (auto simp: program_counter_def)

  have pc_D4_eq: "\<forall>q. program_counter s' q = ''D4'' \<longleftrightarrow> program_counter s q = ''D4''"
    using s'_simple D3_pc by (auto simp: program_counter_def)

  have pc_D4_eq':
    "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    using s'_simple D3_pc by (auto simp: program_counter_def)

  have pc_D_range_eq:
    "\<forall>q. (program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}) \<longleftrightarrow>
         (program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''})"
    using s'_simple D3_pc by (auto simp: program_counter_def)

  have pc_E_range_eq:
    "\<forall>q. (program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) \<longleftrightarrow>
         (program_counter s q \<in> {''E1'', ''E2'', ''E3''})"
    using s'_simple D3_pc by (auto simp: program_counter_def)

  have pending_deq_eq: "\<forall>q. HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
    unfolding HasPendingDeq_def DeqCallInHis_def
    using his_seq_eq s_var_eq by simp

  have EnqCallInHis_eq: "\<And>q a sn. EnqCallInHis s' q a sn = EnqCallInHis s q a sn"
    unfolding EnqCallInHis_def using his_seq_eq s_var_eq by simp

  have EnqRetInHis_eq: "\<And>q a sn. EnqRetInHis s' q a sn = EnqRetInHis s q a sn"
    unfolding EnqRetInHis_def using his_seq_eq s_var_eq by simp

  have DeqCallInHis_eq: "\<And>q sn. DeqCallInHis s' q sn = DeqCallInHis s q sn"
    unfolding DeqCallInHis_def using his_seq_eq s_var_eq by simp

  have DeqRetInHis_eq: "\<And>q a sn. DeqRetInHis s' q a sn = DeqRetInHis s q a sn"
    unfolding DeqRetInHis_def using his_seq_eq s_var_eq by simp

  show "hI4_X_var_Lin_Sync s'"
    using hI4_s X_var_eq lin_seq_eq
    unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def
    by auto

  show "hI7_His_WF s'"
    using hI7_s his_seq_eq unfolding hI7_His_WF_def by presburger

  show "hI8_Val_Unique s'"
    using hI8_s his_seq_eq unfolding hI8_Val_Unique_def by simp

  show "hI6_SSN_Order s'"
    using hI6_s his_seq_eq unfolding hI6_SSN_Order_def by presburger

  show "hI5_SSN_Unique s'"
    using hI5_s his_seq_eq unfolding hI5_SSN_Unique_def by simp

  show "hI9_Deq_Ret_Unique s'"
    using hI9_s his_seq_eq unfolding hI9_Deq_Ret_Unique_def by simp

  show "hI10_Enq_Call_Existence s'"
  proof -
    have Qback_eq: "Qback_arr s' = Qback_arr s" using T_unchanged .
    show ?thesis
      using hI10_s pc_p_not_E pc_other_eq his_seq_eq v_var_eq s_var_eq Qback_eq
      unfolding hI10_Enq_Call_Existence_def EnqCallInHis_def
      by auto
  qed

  show "hI11_Enq_Ret_Existence s'"
  proof -
    have PC_not_E_eq:
      "\<And>q. (program_counter s' q \<notin> {''E1'', ''E2'', ''E3''}) =
           (program_counter s q \<notin> {''E1'', ''E2'', ''E3''})"
      using s'_simple D3_pc by (auto simp: program_counter_def)

    have call_eq: "\<And>q a sn. EnqCallInHis s' q a sn = EnqCallInHis s q a sn"
      unfolding EnqCallInHis_def using his_seq_eq s_var_eq by simp

    have ret_eq: "\<And>q a sn. EnqRetInHis s' q a sn = EnqRetInHis s q a sn"
      unfolding EnqRetInHis_def using his_seq_eq s_var_eq by simp

    show ?thesis
      using hI11_s
      unfolding hI11_Enq_Ret_Existence_def
      using PC_not_E_eq T_unchanged call_eq ret_eq s_var_eq v_var_eq
      by presburger
  qed

  show "hI12_D_Phase_Pending_Deq s'"
  proof -
    show ?thesis
      using hI12_s pc_D_eq pending_deq_eq
      unfolding hI12_D_Phase_Pending_Deq_def
      by metis
  qed

  show "hI13_Qback_Deq_Sync s'"
  proof -
    have Q_eq: "Q_arr s' = Q_arr s" using Q_unchanged .
    have T_eq: "Qback_arr s' = Qback_arr s" using T_unchanged .
    show ?thesis
      using hI13_s Q_eq T_eq x_eq pc_D4_eq his_seq_eq
      unfolding hI13_Qback_Deq_Sync_def DeqRetInHis_def
      by auto
  qed

  show "hI14_Pending_Enq_Qback_Exclusivity s'"
  proof -
    have i_var_eq: "i_var s' = i_var s"
      using s'_simple by (auto simp: i_var_def fun_eq_iff)

    have pending_eq: "\<forall>q a. HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a"
      unfolding HasPendingEnq_def EnqCallInHis_def
      using his_seq_eq s_var_eq by auto

    show ?thesis
      using hI14_s pc_p_not_E pc_other_eq i_var_eq T_unchanged pending_eq
      unfolding hI14_Pending_Enq_Qback_Exclusivity_def
      by (metis insertCI)
  qed

  show "hI18_Idx_Order_No_Rev_HB s'"
  proof -
    have his_eq: "his_seq s' = his_seq s" using his_seq_eq .
    have T_eq: "Qback_arr s' = Qback_arr s" using T_unchanged .

    have InQBack_iff: "\<And>x. InQBack s' x \<longleftrightarrow> InQBack s x"
      using T_eq unfolding InQBack_def by simp

    have Idx_eq: "\<And>x. Idx s' x = Idx s x"
      using T_eq unfolding Idx_def AtIdx_def by simp

    have HB_iff: "\<And>a b. HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
      using his_eq unfolding HB_EnqRetCall_def
      by (simp add: HB_Act_def)

    show ?thesis
      unfolding hI18_Idx_Order_No_Rev_HB_def
      using hI18_s InQBack_iff Idx_eq HB_iff
      by (simp add: hI18_Idx_Order_No_Rev_HB_def)
  qed

  show "hI20_Enq_Val_Valid s'"
    using hI20_s his_seq_eq unfolding hI20_Enq_Val_Valid_def by simp

  show "hI21_Ret_Implies_Call s'"
    using hI21_s his_seq_eq unfolding hI21_Ret_Implies_Call_def by presburger

  show "hI22_Deq_Local_Pattern s'"
  proof -
    have Q_eq: "Q_arr s' = Q_arr s" using Q_unchanged .
    have T_eq: "Qback_arr s' = Qback_arr s" using T_unchanged .
    have his_eq: "his_seq s' = his_seq s" using his_seq_eq .

    show ?thesis
      using hI22_s
      unfolding hI22_Deq_Local_Pattern_def
      unfolding Q_eq T_eq x_eq his_eq DeqRetInHis_eq
      by blast
  qed

  show "hI23_Deq_Call_Ret_Balanced s'"
    using hI23_s his_seq_eq unfolding hI23_Deq_Call_Ret_Balanced_def by simp

  show "hI24_HB_Implies_Idx_Order s'"
    using hI24_s his_seq_eq unfolding hI24_HB_Implies_Idx_Order_def
    using HB_Act_def Model.Q_arr_def Q_unchanged by auto

  show "hI25_Enq_Call_Ret_Balanced s'"
    using hI25_s his_seq_eq unfolding hI25_Enq_Call_Ret_Balanced_def
    by (smt (verit, ccfv_SIG) D3_pc insert_iff list.inject pc_update singleton_iff)

  show "hI26_DeqRet_D4_Mutex s'"
  proof -
    have deq_ret_eq: "\<forall>q a sn. DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
      unfolding DeqRetInHis_def using his_seq_eq s_var_eq by auto

    show ?thesis
      using hI26_s x_eq pc_D4_eq deq_ret_eq
      unfolding hI26_DeqRet_D4_Mutex_def
      by simp
  qed

  show "hI27_Pending_PC_Sync s'"
  proof -
    have pend_deq_eq:
      "\<forall>q. HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
      unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def
      using his_seq_eq s'_simple by (auto simp: s_var_def)

    have pend_enq_eq:
      "\<forall>q a. HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a"
      unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def
      using his_seq_eq s'_simple by (auto simp: s_var_def)

    show ?thesis
      using hI27_s v_var_eq pc_D_range_eq pc_E_range_eq pend_deq_eq pend_enq_eq
      unfolding hI27_Pending_PC_Sync_def
      by simp
  qed

  show "hI28_Fresh_Enq_Immunity s'"
  proof -
    have pc_E12_range_eq:
      "\<forall>q. (program_counter s' q \<in> {''E1'', ''E2''}) \<longleftrightarrow>
           (program_counter s q \<in> {''E1'', ''E2''})"
      using s'_simple D3_pc by (auto simp: program_counter_def)

    have deq_ret_eq:
      "\<forall>q a sn. DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
      unfolding DeqRetInHis_def using his_seq_eq s'_simple by (auto simp: s_var_def)

    show ?thesis
      using hI28_s v_var_eq pc_E12_range_eq deq_ret_eq
      unfolding hI28_Fresh_Enq_Immunity_def
      by simp
  qed
qed

lemma D3_bot_preserves_linearization_tail:
  fixes s s' :: SysState and p jp lp
  assumes INV: "system_invariant s"
    and STEP: "Sys_D3 p s s'"
    and D3_pc: "program_counter s p = ''D3''"
    and s'_simple: "s' = (
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
    and his_seq_eq: "his_seq s' = his_seq s"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
    and Q_unchanged: "Q_arr s' = Q_arr s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and SetA_eq: "SetA s' = SetA s"
    and SetB_eq: "SetB s' = SetB s"
  shows
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
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have lI1_s: "lI1_Op_Sets_Equivalence s"
    using INV unfolding system_invariant_def by blast
  have lI2_s: "lI2_Op_Cardinality s"
    using INV unfolding system_invariant_def by blast
  have lI3_s: "lI3_HB_Ret_Lin_Sync s"
    using INV unfolding system_invariant_def by blast
  have lI4_s: "lI4_FIFO_Semantics s"
    using INV unfolding system_invariant_def by blast
  have lI5_s: "lI5_SA_Prefix s"
    using INV unfolding system_invariant_def by blast
  have lI6_s: "lI6_D4_Deq_Linearized s"
    using INV unfolding system_invariant_def by blast
  have lI7_s: "lI7_D4_Deq_Deq_HB s"
    using INV unfolding system_invariant_def by blast
  have lI8_s: "lI8_D3_Deq_Returned s"
    using INV unfolding system_invariant_def by blast
  have lI9_s: "lI9_D1_D2_Deq_Returned s"
    using INV unfolding system_invariant_def by blast
  have lI10_s: "lI10_D4_Enq_Deq_HB s"
    using INV unfolding system_invariant_def by blast
  have lI11_s: "lI11_D4_Deq_Unique s"
    using INV unfolding system_invariant_def by blast
  have sI11_s: "sI11_x_var_Scope s"
    using INV unfolding system_invariant_def by blast
  have di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by blast

  have s_var_eq: "s_var s' = s_var s"
    using s'_simple by (auto simp: s_var_def fun_eq_iff)

  have x_p_bot_s: "x_var s p = BOT"
    using sI11_s D3_pc unfolding sI11_x_var_Scope_def by simp

  have x_eq: "x_var s' = x_var s"
    using s'_simple x_p_bot_s by (auto simp: x_var_def fun_eq_iff)

  have pc_update:
    "program_counter s' = (\<lambda>x. if x = p then (if jp = lp - 1 then ''D1'' else ''D3'') else program_counter s x)"
    using s'_simple unfolding program_counter_def
    by (auto simp: fun_eq_iff)

  have pc_D4_eq:
    "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    using s'_simple D3_pc by (auto simp: program_counter_def)

  have EnqCallInHis_eq: "\<And>q a sn. EnqCallInHis s' q a sn \<longleftrightarrow> EnqCallInHis s q a sn"
    unfolding EnqCallInHis_def using his_seq_eq s_var_eq by simp

  have EnqRetInHis_eq: "\<And>q a sn. EnqRetInHis s' q a sn \<longleftrightarrow> EnqRetInHis s q a sn"
    unfolding EnqRetInHis_def using his_seq_eq s_var_eq by simp

  have DeqCallInHis_eq: "\<And>q sn. DeqCallInHis s' q sn \<longleftrightarrow> DeqCallInHis s q sn"
    unfolding DeqCallInHis_def using his_seq_eq s_var_eq by simp

  have DeqRetInHis_eq: "\<And>q a sn. DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
    unfolding DeqRetInHis_def using his_seq_eq s_var_eq by simp

  have OPLin_eq: "OPLin s' = OPLin s"
    unfolding OPLin_def using lin_seq_eq by simp

  have OP_A_enq_eq: "OP_A_enq s' = OP_A_enq s"
    unfolding OP_A_enq_def OPLin_def
    using EnqCallInHis_eq EnqRetInHis_eq SetA_eq lin_seq_eq
    by auto

  have OP_A_deq_eq: "OP_A_deq s' = OP_A_deq s"
    unfolding OP_A_deq_def OPLin_def
    using DeqCallInHis_eq DeqRetInHis_eq SetA_eq lin_seq_eq
    by auto

  have OP_B_enq_eq: "OP_B_enq s' = OP_B_enq s"
    unfolding OP_B_enq_def OPLin_def
    using SetB_eq EnqCallInHis_eq lin_seq_eq
    by auto

  show "OPLin s' = OPLin s"
    using OPLin_eq .

  show "lI1_Op_Sets_Equivalence s'"
  proof -
    have "OPLin s = OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
      using lI1_s unfolding lI1_Op_Sets_Equivalence_def by simp
    then show ?thesis
      unfolding lI1_Op_Sets_Equivalence_def
      using OPLin_eq OP_A_enq_eq OP_A_deq_eq OP_B_enq_eq
      by simp
  qed

  show "lI2_Op_Cardinality s'"
  proof -
    have EnqIdxs_eq: "\<And>a. EnqIdxs s' a = EnqIdxs s a"
      unfolding EnqIdxs_def using lin_seq_eq by simp

    have DeqIdxs_eq: "\<And>a. DeqIdxs s' a = DeqIdxs s a"
      unfolding DeqIdxs_def using lin_seq_eq by simp

    have "lI2_Op_Cardinality s' = lI2_Op_Cardinality s"
      unfolding lI2_Op_Cardinality_def
      by (simp add: SetA_eq SetB_eq EnqIdxs_eq DeqIdxs_eq lin_seq_eq his_seq_eq)

    then show ?thesis
      using lI2_s by simp
  qed

  show "lI3_HB_Ret_Lin_Sync s'"
  proof -
    have "lI3_HB_Ret_Lin_Sync s' = lI3_HB_Ret_Lin_Sync s"
      unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def EnqRetInHis_def DeqRetInHis_def
      using lin_seq_eq his_seq_eq by simp
    then show ?thesis using lI3_s by simp
  qed

  show "lI4_FIFO_Semantics s'"
    using lI4_s lin_seq_eq his_seq_eq unfolding lI4_FIFO_Semantics_def by simp

  show "lI5_SA_Prefix s'"
    using lI5_s lin_seq_eq his_seq_eq unfolding lI5_SA_Prefix_def by simp

  show "lI6_D4_Deq_Linearized s'"
  proof -
    show ?thesis
      using lI6_s x_eq s_var_eq lin_seq_eq
      unfolding lI6_D4_Deq_Linearized_def
      using pc_D4_eq by simp
  qed

  show "lI7_D4_Deq_Deq_HB s'"
  proof -
    show ?thesis
      using lI7_s
      unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
      unfolding lin_seq_eq his_seq_eq s_var_eq x_eq pc_D4_eq
      by blast
  qed

  show "lI8_D3_Deq_Returned s'"
    unfolding lI8_D3_Deq_Returned_def
    apply (intro allI impI)
    subgoal premises prems for q k
    proof (cases "q = p")
      case True
      have pc_p_old: "program_counter s p = ''D3''"
        using D3_pc .
      show ?thesis
        using lI8_s pc_p_old lin_seq_eq his_seq_eq True prems
        unfolding lI8_D3_Deq_Returned_def DeqRetInHis_def
        by (auto simp: nth_append)
    next
      case False
      have pc_q_unchanged: "program_counter s' q = program_counter s q"
        using False s'_simple unfolding bridge_defs by auto

      note prems_s = prems[unfolded pc_q_unchanged lin_seq_eq his_seq_eq]

      show ?thesis
        using lI8_s prems_s
        unfolding lI8_D3_Deq_Returned_def
        using DeqRetInHis_eq lin_seq_eq
        by auto
    qed
    done

  show "lI9_D1_D2_Deq_Returned s'"
  proof -
    have pc_transition:
      "\<forall>q. program_counter s' q \<in> {''D1'', ''D2''} \<longrightarrow>
           program_counter s q \<in> {''D1'', ''D2'', ''D3''}"
      using s'_simple D3_pc by (auto simp: program_counter_def)

    show ?thesis
      using lI8_s lI9_s pc_transition
      unfolding lI8_D3_Deq_Returned_def lI9_D1_D2_Deq_Returned_def
      unfolding lin_seq_eq his_seq_eq DeqRetInHis_eq
      by blast
  qed

  show "lI10_D4_Enq_Deq_HB s'"
  proof -
    show ?thesis
      using lI10_s
      unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
      unfolding lin_seq_eq his_seq_eq s_var_eq x_eq pc_D4_eq
      by blast
  qed

  show "lI11_D4_Deq_Unique s'"
  proof -
    show ?thesis
      using lI11_s
      unfolding lI11_D4_Deq_Unique_def
      unfolding lin_seq_eq his_seq_eq s_var_eq x_eq pc_D4_eq
      by (simp add: DeqRetInHis_eq)
  qed

  show "data_independent (lin_seq s')"
    using di_lin_s lin_seq_eq by simp

  show "Simulate_PC s'"
    using INV D3_pc s'_simple
    unfolding system_invariant_def Simulate_PC_def bridge_defs
    using Simulate_PC_def STEP Sys_D3_def
    by auto
qed

lemma D3_success_basic_facts:
  fixes s s' :: SysState and p jp q_val
  assumes INV: "system_invariant s"
    and STEP: "Sys_D3 p s s'"
    and D3_pc: "program_counter s p = ''D3''"
    and jp_def: "jp = j_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and q_not_bot: "q_val \<noteq> BOT"
    and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s"
    and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s"
    and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s"
    and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
  shows
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
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have val_eq: "q_val = Qback_arr s (j_var s p)"
    using sI8_Q_Qback_Sync_s q_not_bot
    unfolding sI8_Q_Qback_Sync_def q_val_def jp_def
    by auto

have s'_is_update: "s' = Sys_D3_success_update s p" 
  using STEP q_not_bot
  unfolding Sys_D3_def C_D3_def U_D2_def Sys_D3_success_update_def Let_def
            jp_def q_val_def s_var_def
  by (auto simp: prod_eq_iff fun_eq_iff Q_arr_def j_var_def)

  have q_neq_bot: "Q_arr s (j_var s p) \<noteq> BOT"
    using q_not_bot unfolding q_val_def jp_def by simp

  have phys_invs:
    "TypeOK s' \<and> sI2_X_var_Upper_Bound s' \<and> sI7_D4_Deq_Result s' \<and>
     sI8_Q_Qback_Sync s' \<and> sI9_Qback_Discrepancy_E3 s' \<and> sI10_Qback_Unique_Vals s'"
    using Sys_D3_success_phys_invariants[OF INV D3_pc q_neq_bot]
    unfolding s'_is_update[symmetric]
    by simp

  have TypeOK_s': "TypeOK s'" using phys_invs by simp
  have sI2_s': "sI2_X_var_Upper_Bound s'" using phys_invs by simp
  have sI7_s': "sI7_D4_Deq_Result s'" using phys_invs by simp
  have sI8_s': "sI8_Q_Qback_Sync s'" using phys_invs by simp
  have sI9_s': "sI9_Qback_Discrepancy_E3 s'" using phys_invs by simp
  have sI10_s': "sI10_Qback_Unique_Vals s'" using phys_invs by simp

  have sI1_s': "sI1_Zero_Index_BOT s'"
    using sI1_Zero_Index_BOT_s s'_is_update
    unfolding sI1_Zero_Index_BOT_def Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs)

  have sI3_s': "sI3_E2_Slot_Exclusive s'"
    using sI3_E2_Slot_Exclusive_s s'_is_update
    unfolding sI3_E2_Slot_Exclusive_def Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs)

  have sI4_s': "sI4_E3_Qback_Written s'"
    using sI4_E3_Qback_Written_s s'_is_update
    unfolding sI4_E3_Qback_Written_def Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs)

  have sI5_s': "sI5_D2_Local_Bound s'"
    using sI5_D2_Local_Bound_s s'_is_update
    unfolding sI5_D2_Local_Bound_def Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs)

  have sI6_s': "sI6_D3_Scan_Pointers s'"
    using sI6_D3_Scan_Pointers_s s'_is_update
    unfolding sI6_D3_Scan_Pointers_def Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs split: if_splits)

  have his_seq_eq: "his_seq s' = his_seq s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (simp add: his_seq_def)

  have pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_eq_iff)

  have val_consistent: "Q_arr s (j_var s p) = Qback_arr s (j_var s p)"
    using sI8_Q_Qback_Sync_s q_not_bot
    unfolding sI8_Q_Qback_Sync_def q_val_def jp_def
    by auto

  have x_var_eq:
    "x_var s' = (\<lambda>x. if x = p then Qback_arr s (j_var s p) else x_var s x)"
    using s'_is_update val_consistent
    unfolding sI5_D2_Local_Bound_def Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs)

  have i_eq: "i_var s' = i_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_eq_iff)

  have j_eq: "j_var s' = j_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_eq_iff)

  have v_eq: "v_var s' = v_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_eq_iff)

  have l_eq: "l_var s' = l_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_eq_iff)

  have T_unchanged: "Qback_arr s' = Qback_arr s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_eq_iff)

  have prem1_Q: "Q_arr s' = (Q_arr s)(jp := BOT)"
    using s'_is_update jp_def
    unfolding Sys_D3_success_update_def Let_def fun_upd_def
    by (auto simp: bridge_defs fun_eq_iff)

  have prem2_PC: "program_counter s' = (program_counter s)(p := ''D4'')"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_upd_def fun_eq_iff)

  have prem3_V: "v_var s' = v_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def
    by (auto simp: bridge_defs fun_eq_iff)

  show "q_val = Qback_arr s (j_var s p)" using val_eq .
  show "s' = Sys_D3_success_update s p" using s'_is_update .
  show "TypeOK s'" using TypeOK_s' .
  show "sI1_Zero_Index_BOT s'" using sI1_s' .
  show "sI2_X_var_Upper_Bound s'" using sI2_s' .
  show "sI3_E2_Slot_Exclusive s'" using sI3_s' .
  show "sI4_E3_Qback_Written s'" using sI4_s' .
  show "sI5_D2_Local_Bound s'" using sI5_s' .
  show "sI6_D3_Scan_Pointers s'" using sI6_s' .
  show "sI7_D4_Deq_Result s'" using sI7_s' .
  show "sI8_Q_Qback_Sync s'" using sI8_s' .
  show "sI9_Qback_Discrepancy_E3 s'" using sI9_s' .
  show "sI10_Qback_Unique_Vals s'" using sI10_s' .
  show "his_seq s' = his_seq s" using his_seq_eq .
  show "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)" using pc_eq .
  show "x_var s' = (\<lambda>x. if x = p then Qback_arr s (j_var s p) else x_var s x)" using x_var_eq .
  show "i_var s' = i_var s" using i_eq .
  show "j_var s' = j_var s" using j_eq .
  show "v_var s' = v_var s" using v_eq .
  show "l_var s' = l_var s" using l_eq .
  show "Qback_arr s' = Qback_arr s" using T_unchanged .
  show "Q_arr s' = (Q_arr s)(jp := BOT)" using prem1_Q .
  show "program_counter s' = (program_counter s)(p := ''D4'')" using prem2_PC .
  show "v_var s' = v_var s" using prem3_V .
qed

lemma D3_success_set_and_lin_facts:
  fixes s s' :: SysState and p jp q_val current_lin current_his base_lin
  assumes INV: "system_invariant s"
    and TypeOK_s: "TypeOK s"
    and D3_pc: "program_counter s p = ''D3''"
    and jp_def: "jp = j_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and current_lin_def: "current_lin = lin_seq s"
    and current_his_def: "current_his = his_seq s"
    and base_lin_def:
      "base_lin =
        (if q_val = BOT then current_lin
         else if should_modify current_lin current_his q_val
              then modify_lin current_lin current_his q_val
              else current_lin)"
    and q_not_bot: "q_val \<noteq> BOT"
    and val_eq: "q_val = Qback_arr s (j_var s p)"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
    and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s"
    and TypeOK_s': "TypeOK s'"
    and sI7_D4_Deq_Result_s': "sI7_D4_Deq_Result s'"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and other_vars_eq:
      "i_var s' = i_var s \<and> j_var s' = j_var s \<and> v_var s' = v_var s \<and> l_var s' = l_var s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and prem1_Q: "Q_arr s' = (Q_arr s)(jp := BOT)"
    and prem2_PC: "program_counter s' = (program_counter s)(p := ''D4'')"
    and prem3_V: "v_var s' = v_var s"
  shows
    "q_val \<in> SetB s"
    "SetB s' = SetB s - {q_val}"
"\<And>x. x \<in> Val \<Longrightarrow> TypeB s' x \<longleftrightarrow> TypeB s x \<and> x \<noteq> q_val"
    "u_lin_seq (snd s) = current_lin" 
    "u_his_seq (snd s) = current_his"
    "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
    "Q_arr s' = (Q_arr s)(jp := BOT)"
    "set base_lin = set (lin_seq s)"
    "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    "SetA s' = SetA s \<union> {q_val} \<and> SetB s' = SetB s - {q_val}"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have q_in_SetB: "q_val \<in> SetB s"
  proof -
    have q_has: "QHas s q_val"
      unfolding QHas_def
      using q_not_bot q_val_def by blast

    have q_in_qback: "InQBack s q_val"
      unfolding InQBack_def
      using val_eq by (auto simp: jp_def)

    have q_val_in_Val: "q_val \<in> Val"
      using InQBack_non_BOT_implies_Val[OF INV q_in_qback q_not_bot] .

    show ?thesis
      unfolding SetB_def TypeB_def
      using q_has q_val_in_Val
      by blast
  qed

  have prem4_q: "q_val = Q_arr s jp"
    using q_val_def by simp

  have prem5_j: "jp = j_var s p"
    using jp_def by simp

  have setb_update: "SetB s' = SetB s - {q_val}"
    using SetB_D3_step_lemma[where head=j_var,
      OF INV prem1_Q prem2_PC prem3_V prem4_q prem5_j q_not_bot q_in_SetB D3_pc] .

  have TypeB_update: "\<And>x. x \<in> Val \<Longrightarrow> TypeB s' x \<longleftrightarrow> TypeB s x \<and> x \<noteq> q_val"
  proof -
    fix x
    assume x_in_Val: "x \<in> Val"

    have setb_mem:
      "x \<in> SetB s' \<longleftrightarrow> x \<in> SetB s - {q_val}"
      using setb_update by blast

    have lhs: "x \<in> SetB s' \<longleftrightarrow> TypeB s' x"
      using x_in_Val unfolding SetB_def by auto

    have rhs1: "x \<in> SetB s \<longleftrightarrow> TypeB s x"
      using x_in_Val unfolding SetB_def by auto

    have rhs2: "x \<in> SetB s - {q_val} \<longleftrightarrow> (TypeB s x \<and> x \<noteq> q_val)"
      using rhs1 by blast

    show "TypeB s' x \<longleftrightarrow> TypeB s x \<and> x \<noteq> q_val"
      using lhs setb_mem rhs2 by blast
  qed

  have bridge:
    "u_lin_seq (snd s) = current_lin"
    "u_his_seq (snd s) = current_his"
    "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val"
    unfolding lin_seq_def his_seq_def current_lin_def current_his_def q_val_def jp_def
    by (simp_all add: bridge_defs)

  have Q_upd: "Q_arr s' = (Q_arr s)(jp := BOT)"
    using prem1_Q .

  have set_base_eq: "set base_lin = set (lin_seq s)"
  proof -
    have "mset base_lin = mset (lin_seq s)"
      unfolding base_lin_def current_lin_def current_his_def
      using modify_preserves_mset q_not_bot
      by presburger
    then show ?thesis by (metis set_mset_mset)
  qed

  have lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    using s'_is_update q_not_bot
    unfolding lin_seq_def Sys_D3_success_update_def base_lin_def Let_def s_var_def
    by (simp add: bridge bridge_defs)

  have seta_update: "SetA s' = SetA s \<union> {q_val} \<and> SetB s' = SetB s - {q_val}"
  proof -
    have A_eq: "SetA s' = SetA s \<union> {q_val}"
    proof (rule set_eqI)
      fix x
      consider (x_q) "x = q_val" | (x_bot) "x = BOT" | (x_other) "x \<noteq> q_val \<and> x \<noteq> BOT"
        by auto
      then show "x \<in> SetA s' \<longleftrightarrow> x \<in> SetA s \<union> {q_val}"
      proof cases
        case x_q
        have "Qback_arr s jp = q_val"
          using sI8_Q_Qback_Sync_s q_not_bot q_val_def val_eq by (simp add: jp_def)
        hence "InQBack s' q_val"
          using T_unchanged unfolding InQBack_def by auto
        moreover have "\<not> QHas s' q_val"
          unfolding QHas_def
          using Q_upd q_not_bot
          by (metis fun_upd_apply q_val_def sI10_Qback_Unique_Vals_def
              sI10_Qback_Unique_Vals_s sI8_Q_Qback_Sync_def sI8_Q_Qback_Sync_s)
        ultimately show ?thesis
          using x_q q_in_SetB unfolding SetA_def TypeA_def SetB_def by fastforce
      next
        case x_bot
        have bot_notin_old: "BOT \<notin> SetA s"
          using TypeOK_s sI8_Q_Qback_Sync_s
          unfolding TypeOK_def SetA_def TypeA_def InQBack_def QHas_def sI8_Q_Qback_Sync_def
          by force

        have bot_notin_new: "BOT \<notin> SetA s'"
          using Q_upd q_not_bot
          unfolding SetA_def TypeA_def QHas_def
          by auto

        have "BOT \<notin> SetA s \<union> {q_val}"
          using bot_notin_old q_not_bot
          by auto

        then show ?thesis
          using x_bot bot_notin_new
          by auto
      next
        case x_other
        have "QHas s' x \<longleftrightarrow> QHas s x"
        proof
          assume "QHas s' x"
          then obtain k where k1: "Q_arr s' k = x" unfolding QHas_def by blast
          have "k \<noteq> jp" using k1 Q_upd x_other by (metis fun_upd_apply)
          thus "QHas s x" unfolding QHas_def using k1 Q_upd by auto
        next
          assume "QHas s x"
          then obtain k where k1: "Q_arr s k = x" unfolding QHas_def by blast
          have "k \<noteq> jp" using k1 x_other q_val_def by auto
          thus "QHas s' x" unfolding QHas_def using k1 Q_upd by auto
        qed
        moreover have "InQBack s' x \<longleftrightarrow> InQBack s x"
          using T_unchanged unfolding InQBack_def by simp
        ultimately show ?thesis
          using x_other unfolding SetA_def TypeA_def by auto
      qed
    qed
    show ?thesis using A_eq setb_update by simp
  qed

  show "q_val \<in> SetB s" using q_in_SetB .
  show "SetB s' = SetB s - {q_val}" using setb_update .
  show "\<And>x. x \<in> Val \<Longrightarrow> TypeB s' x \<longleftrightarrow> TypeB s x \<and> x \<noteq> q_val" using TypeB_update .
  show "u_lin_seq (snd s) = current_lin" using bridge(1) .
  show "u_his_seq (snd s) = current_his" using bridge(2) .
  show "CState.Q_arr (fst s) (CState.j_var (fst s) p) = q_val" using bridge(3) .
  show "Q_arr s' = (Q_arr s)(jp := BOT)" using Q_upd .
  show "set base_lin = set (lin_seq s)" using set_base_eq .
  show "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]" using lin_s'_eq .
  show "SetA s' = SetA s \<union> {q_val} \<and> SetB s' = SetB s - {q_val}" using seta_update .
qed

lemma D3_success_preserves_hI3_L0_E_Phase_Bounds:
  fixes s s' :: SysState and p :: nat
  assumes hI3_s: "hI3_L0_E_Phase_Bounds s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and v_var_eq: "v_var s' = v_var s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
  shows "hI3_L0_E_Phase_Bounds s'"
proof -
  have V_eq: "V_var s' = V_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def V_var_def
    by simp

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def
    by (auto simp: fun_eq_iff)

  show ?thesis
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    have q_ne_p: "q \<noteq> p"
      using 1 pc_eq by auto
    have old_L0: "program_counter s q = ''L0''"
      using 1 q_ne_p pc_eq by auto

    have pend_enq_eq: "HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a" for a
      using his_seq_eq s_var_eq
      unfolding HasPendingEnq_def Let_def Model.EnqCallInHis_def
      by simp

    have pend_deq_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
      using his_seq_eq s_var_eq
      unfolding HasPendingDeq_def Let_def Model.DeqCallInHis_def
      by simp

    show ?case
      using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_s old_L0] pend_enq_eq pend_deq_eq
      by simp
  next
    case (2 q)
    have q_ne_p: "q \<noteq> p"
      using 2 pc_eq by auto
    have old_L0: "program_counter s q = ''L0''"
      using 2 q_ne_p pc_eq by auto

    show ?case
      using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_s old_L0] his_seq_eq
      by simp
  next
    case (3 q)
    have q_ne_p: "q \<noteq> p"
      using 3 pc_eq by auto
    have old_E: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using 3 q_ne_p pc_eq by auto
    have v_eq: "v_var s' q = v_var s q"
      using v_var_eq by simp

    show ?case
      using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_s old_E] v_eq V_eq
      by simp
  next
    case (4 k)
    show ?case
      using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_s] 4 his_seq_eq V_eq
      by auto
  next
    case (5 k)
    show ?case
      using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_s] T_unchanged V_eq
      by auto
  qed
qed


lemma D3_success_preserves_hI2_SSN_Bounds:
  fixes s s' :: SysState and p :: nat
  assumes hI2_s: "hI2_SSN_Bounds s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
  shows "hI2_SSN_Bounds s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  show ?thesis
    using hI2_s his_seq_eq s_var_eq pc_eq
    unfolding hI2_SSN_Bounds_def
    unfolding HasPendingDeq_def HasPendingEnq_def DeqCallInHis_def EnqCallInHis_def
    by auto
qed


lemma D3_success_preserves_sI11_x_var_Scope:
  fixes s s' :: SysState and p :: nat
  assumes sI11_s: "sI11_x_var_Scope s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and x_var_eq: "x_var s' = (\<lambda>x. if x = p then Qback_arr s (j_var s p) else x_var s x)"
  shows "sI11_x_var_Scope s'"
  using sI11_s pc_eq x_var_eq
  unfolding sI11_x_var_Scope_def
  by (auto split: if_splits)

lemma D3_success_preserves_hI1_E_Phase_Pending_Enq:
  fixes s s' :: SysState and p :: nat
  assumes hI1_s: "hI1_E_Phase_Pending_Enq s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
  shows "hI1_E_Phase_Pending_Enq s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have v_eq: "v_var s' = v_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def v_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have pc_E_eq:
    "\<forall>q. program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longrightarrow>
         program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
    using pc_eq by (auto split: if_splits)

  show ?thesis
    using hI1_s his_seq_eq v_eq s_var_eq pc_E_eq
    unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def EnqCallInHis_def
    by auto
qed


lemma D3_success_preserves_TypeB_on_untouched_slot:
  fixes s s' :: SysState and k jp :: nat and q_val
  assumes INV: "system_invariant s"
    and typeb_old: "TypeB s (Q_arr s k)"
    and k_neq_jp: "k \<noteq> jp"
    and q_not_bot: "q_val \<noteq> BOT"
    and q_val_def: "q_val = Q_arr s jp"
    and sync_s: "sI8_Q_Qback_Sync s"
    and uniq_s: "sI10_Qback_Unique_Vals s"
    and TypeB_update: "\<And>v. \<lbrakk>TypeB s v; v \<noteq> q_val\<rbrakk> \<Longrightarrow> TypeB s' v"
  shows "TypeB s' (Q_arr s k)"
proof -
  let ?v = "Q_arr s k"

  have "?v \<noteq> q_val"
  proof
    assume eq: "?v = q_val"

    have "?v \<in> Val"
      using TypeB_non_BOT_implies_Val INV typeb_old
      by (simp add: eq q_not_bot)

    have qback_k: "Qback_arr s k = ?v"
      using sync_s typeb_old `?v \<in> Val`
      unfolding sI8_Q_Qback_Sync_def
      using eq q_not_bot by force

    have qback_jp: "Qback_arr s jp = q_val"
      using sync_s q_not_bot q_val_def
      unfolding sI8_Q_Qback_Sync_def
      by force

    have "Qback_arr s k = Qback_arr s jp"
      using eq qback_k qback_jp by simp

have "k = jp"
proof (rule ccontr)
  assume k_neq_jp': "k \<noteq> jp"
  have "Qback_arr s k \<noteq> BOT"
    using `Qback_arr s k = ?v` `?v \<in> Val`
    unfolding Val_def BOT_def by auto
  moreover have "Qback_arr s jp \<noteq> BOT"
    using qback_jp q_not_bot by simp
  ultimately have "Qback_arr s k \<noteq> Qback_arr s jp"
    using uniq_s k_neq_jp'
    unfolding sI10_Qback_Unique_Vals_def by blast
  with `Qback_arr s k = Qback_arr s jp` show False by simp
qed

    with k_neq_jp show False by simp
  qed

  show ?thesis
    using TypeB_update[OF typeb_old `?v \<noteq> q_val`] .
qed

lemma D3_success_preserves_sI12_D3_Scanned_Prefix:
  fixes s s' :: SysState and p jp :: nat and q_val
  assumes INV: "system_invariant s"
    and sI12_s: "sI12_D3_Scanned_Prefix s"
    and q_not_bot: "q_val \<noteq> BOT"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and j_var_eq: "j_var s' = j_var s"
    and q_val_def: "q_val = Q_arr s jp"
    and Q_jp_bot: "Q_arr s' jp = BOT"
    and Q_other_eq: "\<And>k. k \<noteq> jp \<Longrightarrow> Q_arr s' k = Q_arr s k"
    and sync_s: "sI8_Q_Qback_Sync s"
    and uniq_s: "sI10_Qback_Unique_Vals s"
    and TypeB_update: "\<And>v. v \<in> Val \<Longrightarrow> TypeB s' v \<longleftrightarrow> (TypeB s v \<and> v \<noteq> q_val)"
  shows "sI12_D3_Scanned_Prefix s'"
proof -
  have pointwise:
    "\<And>q k. \<lbrakk>program_counter s' q = ''D3''; k < j_var s' q\<rbrakk>
           \<Longrightarrow> Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
  proof -
    fix q k
    assume pc_new_D3: "program_counter s' q = ''D3''"
    assume k_bound_new: "k < j_var s' q"

    show "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
    proof (cases "q = p")
      case True
      have "program_counter s' p = ''D4''"
        using pc_eq by simp
      with pc_new_D3 True show ?thesis by simp
    next
      case False
      have pc_old: "program_counter s q = ''D3''"
        using pc_new_D3 False pc_eq by auto

      have j_same: "j_var s' q = j_var s q"
        using j_var_eq by simp

      have k_bound_old: "k < j_var s q"
        using k_bound_new j_same by simp

      have old_k_prop: "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
        using sI12_s pc_old k_bound_old
        unfolding sI12_D3_Scanned_Prefix_def
        by blast

      show ?thesis
      proof (cases "k = jp")
        case True
        have "Q_arr s' k = BOT"
          using Q_jp_bot True by simp
        then show ?thesis by simp
      next
        case False
        have k_neq_jp: "k \<noteq> jp"
          using False .

        have Q_same: "Q_arr s' k = Q_arr s k"
          using Q_other_eq[OF k_neq_jp] .

        show ?thesis
          using old_k_prop
        proof
          assume "Q_arr s k = BOT"
          then show ?thesis
            using Q_same by simp
next
  assume typeb_old: "TypeB s (Q_arr s k)"
  let ?v = "Q_arr s k"

  show ?thesis
  proof (cases "?v = BOT")
    case True
    then have "Q_arr s' k = BOT"
      using Q_same by simp
    then show ?thesis by simp
  next
    case False
    have v_not_bot: "?v \<noteq> BOT"
      using False by simp

    have v_in_Val: "?v \<in> Val"
      using TypeB_non_BOT_implies_Val[OF INV typeb_old v_not_bot] .

    have "?v \<noteq> q_val"
    proof
      assume eq: "?v = q_val"

      have qback_k: "Qback_arr s k = ?v"
        using sync_s typeb_old v_in_Val
        unfolding sI8_Q_Qback_Sync_def
        using eq q_not_bot by force

      have qback_jp: "Qback_arr s jp = q_val"
        using sync_s q_not_bot q_val_def
        unfolding sI8_Q_Qback_Sync_def
        by force

      have "Qback_arr s k = Qback_arr s jp"
        using eq qback_k qback_jp by simp

      have "k = jp"
        using uniq_s `Qback_arr s k = Qback_arr s jp` v_in_Val
        unfolding sI10_Qback_Unique_Vals_def
        using qback_jp q_not_bot by force

      with k_neq_jp show False by simp
    qed

    have "TypeB s' ?v \<longleftrightarrow> (TypeB s ?v \<and> ?v \<noteq> q_val)"
      using TypeB_update[OF v_in_Val] .

    hence "TypeB s' ?v"
      using typeb_old `?v \<noteq> q_val` by simp

    then show ?thesis
      using Q_same by simp
        qed
        qed
      qed
    qed
  qed

  show ?thesis
    unfolding sI12_D3_Scanned_Prefix_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_hI4_X_var_Lin_Sync:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and count_eq: "LinEnqCount s' (length (lin_seq s')) = LinEnqCount s (length (lin_seq s))"
  shows "hI4_X_var_Lin_Sync s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI4_s: "hI4_X_var_Lin_Sync s"
    using INV unfolding system_invariant_def by blast

  have X_var_eq: "X_var s' = X_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def X_var_def bridge_defs
    by auto

  show ?thesis
    using hI4_s X_var_eq count_eq
    unfolding hI4_X_var_Lin_Sync_def
    by simp
qed


lemma D3_success_preserves_basic_history_facts:
  fixes s s' :: SysState
  assumes INV: "system_invariant s"
    and his_seq_eq: "his_seq s' = his_seq s"
  shows
    "hI7_His_WF s'"
    "hI8_Val_Unique s'"
    "hI5_SSN_Unique s'"
    "hI6_SSN_Order s'"
    "hI9_Deq_Ret_Unique s'"
proof -
  have hI7_s: "hI7_His_WF s"
    using INV unfolding system_invariant_def by blast
  have hI8_s: "hI8_Val_Unique s"
    using INV unfolding system_invariant_def by blast
  have hI5_s: "hI5_SSN_Unique s"
    using INV unfolding system_invariant_def by blast
  have hI6_s: "hI6_SSN_Order s"
    using INV unfolding system_invariant_def by blast
  have hI9_s: "hI9_Deq_Ret_Unique s"
    using INV unfolding system_invariant_def by blast

  show "hI7_His_WF s'"
    using hI7_s his_seq_eq
    unfolding hI7_His_WF_def
    by presburger

  show "hI8_Val_Unique s'"
    using hI8_s his_seq_eq
    unfolding hI8_Val_Unique_def
    by simp

  show "hI5_SSN_Unique s'"
    using hI5_s his_seq_eq
    unfolding hI5_SSN_Unique_def
    by simp

  show "hI6_SSN_Order s'"
    using hI6_s his_seq_eq
    unfolding hI6_SSN_Order_def
    by presburger

  show "hI9_Deq_Ret_Unique s'"
    using hI9_s his_seq_eq
    unfolding hI9_Deq_Ret_Unique_def
    by simp
qed


lemma D3_success_preserves_hI10_Enq_Call_Existence:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and pc_D3: "program_counter s p = ''D3''"
  shows "hI10_Enq_Call_Existence s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI10_s: "hI10_Enq_Call_Existence s"
    using INV unfolding system_invariant_def by blast

  have v_eq: "v_var s' = v_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def v_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by (auto simp: fun_eq_iff)

have pc_E1_eq [simp]: "(program_counter s' q = ''E1'') = (program_counter s q = ''E1'')" for q
  using pc_eq pc_D3
  by (cases "q = p"; simp)

have pc_E2_eq [simp]: "(program_counter s' q = ''E2'') = (program_counter s q = ''E2'')" for q
  using pc_eq pc_D3
  by (cases "q = p"; simp)

have pc_E3_eq [simp]: "(program_counter s' q = ''E3'') = (program_counter s q = ''E3'')" for q
  using pc_eq pc_D3
  by (cases "q = p"; simp)

  have call_eq: "\<And>q a sn. EnqCallInHis s' q a sn = EnqCallInHis s q a sn"
    unfolding EnqCallInHis_def
    using his_seq_eq s_var_eq
    by simp

show ?thesis
  using hI10_s
  unfolding hI10_Enq_Call_Existence_def
  unfolding T_unchanged v_eq s_var_eq call_eq
  by auto
qed

lemma D3_success_preserves_hI11_Enq_Ret_Existence:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and pc_D3: "program_counter s p = ''D3''"
  shows "hI11_Enq_Ret_Existence s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI11_s: "hI11_Enq_Ret_Existence s"
    using INV unfolding system_invariant_def by blast

  have v_eq: "v_var s' = v_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def v_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have pc_not_E_conj_eq [simp]:
    "(program_counter s' q \<noteq> ''E1'' \<and>
      program_counter s' q \<noteq> ''E2'' \<and>
      program_counter s' q \<noteq> ''E3'') =
     (program_counter s q \<noteq> ''E1'' \<and>
      program_counter s q \<noteq> ''E2'' \<and>
      program_counter s q \<noteq> ''E3'')" for q
    using pc_eq pc_D3
    by (cases "q = p"; simp)

  have call_eq: "EnqCallInHis s' q a sn = EnqCallInHis s q a sn" for q a sn
    unfolding EnqCallInHis_def
    using his_seq_eq s_var_eq
    by simp

  have ret_eq: "EnqRetInHis s' q a sn = EnqRetInHis s q a sn" for q a sn
    unfolding EnqRetInHis_def
    using his_seq_eq s_var_eq
    by simp

  have pointwise:
    "\<And>q a sn.
      (v_var s' q = a \<longrightarrow>
         (program_counter s' q \<noteq> ''E1'' \<and>
          program_counter s' q \<noteq> ''E2'' \<and>
          program_counter s' q \<noteq> ''E3'') \<or>
         s_var s' q \<noteq> sn) \<Longrightarrow>
      (\<exists>k. Qback_arr s' k = a) \<Longrightarrow>
      EnqCallInHis s' q a sn \<Longrightarrow>
      EnqRetInHis s' q a sn"
  proof -
    fix q a sn
    assume H1:
      "(v_var s' q = a \<longrightarrow>
         (program_counter s' q \<noteq> ''E1'' \<and>
          program_counter s' q \<noteq> ''E2'' \<and>
          program_counter s' q \<noteq> ''E3'') \<or>
         s_var s' q \<noteq> sn)"
    assume H2: "\<exists>k. Qback_arr s' k = a"
    assume H3: "EnqCallInHis s' q a sn"

    have H1_old:
      "(v_var s q = a \<longrightarrow>
         (program_counter s q \<noteq> ''E1'' \<and>
          program_counter s q \<noteq> ''E2'' \<and>
          program_counter s q \<noteq> ''E3'') \<or>
         s_var s q \<noteq> sn)"
      using H1
      by (simp add: v_eq s_var_eq)

    have H2_old: "\<exists>k. Qback_arr s k = a"
      using H2
      by (simp add: T_unchanged)

    have H3_old: "EnqCallInHis s q a sn"
      using H3
      by (simp add: call_eq)

    have ret_old: "EnqRetInHis s q a sn"
      using hI11_s H1_old H2_old H3_old
      unfolding hI11_Enq_Ret_Existence_def
      by blast

    show "EnqRetInHis s' q a sn"
      using ret_old
      by (simp add: ret_eq)
  qed

  show ?thesis
    unfolding hI11_Enq_Ret_Existence_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_hI12_D_Phase_Pending_Deq:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and pc_D3: "program_counter s p = ''D3''"
  shows "hI12_D_Phase_Pending_Deq s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI12_s: "hI12_D_Phase_Pending_Deq s"
    using INV unfolding system_invariant_def by blast

  have pc_D_eq [simp]:
    "(program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}) =
     (program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''})" for q
    using pc_eq pc_D3
    by (cases "q = p"; simp)

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have pending_eq: "HasPendingDeq s' q = HasPendingDeq s q" for q
    unfolding HasPendingDeq_def DeqCallInHis_def
    using his_seq_eq s_var_eq
    by simp

  have pointwise:
    "\<And>q. program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}
         \<Longrightarrow> HasPendingDeq s' q"
  proof -
    fix q
    assume Hnew: "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"

  have Hold: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using Hnew pc_D_eq[of q]
    by simp

    have pend_old: "HasPendingDeq s q"
      using hI12_s Hold
      unfolding hI12_D_Phase_Pending_Deq_def
      by blast

    show "HasPendingDeq s' q"
      using pend_old
      by (simp add: pending_eq)
  qed

  show ?thesis
    unfolding hI12_D_Phase_Pending_Deq_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_hI18_Idx_Order_No_Rev_HB:
  fixes s s' :: SysState
  assumes hI18_s: "hI18_Idx_Order_No_Rev_HB s"
    and his_seq_eq: "his_seq s' = his_seq s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
  shows "hI18_Idx_Order_No_Rev_HB s'"
proof -
  have eq_InQBack: "InQBack s' = InQBack s"
    using T_unchanged
    unfolding InQBack_def
    by auto

  have eq_Idx: "Idx s' = Idx s"
  proof (rule ext)
    fix x
    show "Idx s' x = Idx s x"
      using his_seq_eq
      unfolding Idx_def
      using AtIdx_def T_unchanged
      by presburger
  qed

  have eq_HB: "HB_EnqRetCall s' = HB_EnqRetCall s"
  proof (rule ext, rule ext)
    fix x y
    show "HB_EnqRetCall s' x y = HB_EnqRetCall s x y"
      using his_seq_eq
      unfolding HB_EnqRetCall_def HB_Act_def
      by simp
  qed

  show ?thesis
    using hI18_s eq_InQBack eq_Idx eq_HB
    unfolding hI18_Idx_Order_No_Rev_HB_def
    by simp
qed


lemma D3_success_preserves_hI19_Scanner_Catches_Later_Enq:
  fixes s s' :: SysState and p :: nat and q_val
  assumes INV: "system_invariant s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and TypeB_update: "\<And>x. x \<in> Val \<Longrightarrow> TypeB s' x \<longleftrightarrow> (TypeB s x \<and> x \<noteq> q_val)"
  shows "hI19_Scanner_Catches_Later_Enq s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI19_s: "hI19_Scanner_Catches_Later_Enq s"
    using INV unfolding system_invariant_def by blast

  have sI1_s: "sI1_Zero_Index_BOT s"
    using INV unfolding system_invariant_def by blast

  have his_eq: "his_seq s' = his_seq s"
    using his_seq_eq .

  have T_eq: "Qback_arr s' = Qback_arr s"
    using T_unchanged .

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have pending_eq: "HasPendingDeq s' q = HasPendingDeq s q" for q
    unfolding HasPendingDeq_def DeqCallInHis_def Let_def
    using his_eq s_var_eq
    by simp

  have Idx_eq: "Idx s' x = Idx s x" for x
    using T_eq
    unfolding Idx_def AtIdx_def
    by simp

  have jl_eq: "q \<noteq> p \<Longrightarrow> j_var s' q = j_var s q \<and> l_var s' q = l_var s q" for q
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def bridge_defs
    by (auto simp: fun_eq_iff)

  have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b" for a b
    unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def
              match_ret_def match_call_def mk_op_def op_name_def op_val_def
    using his_eq
    by auto

  have pointwise:
    "\<And>a b.
      InQBack s' a \<Longrightarrow>
      InQBack s' b \<Longrightarrow>
      TypeB s' a \<Longrightarrow>
      TypeB s' b \<Longrightarrow>
      Idx s' a < Idx s' b \<Longrightarrow>
      (\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
           Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q) \<Longrightarrow>
      \<not> HB_EnqRetCall s' a b"
  proof -
    fix a b
    assume inqa': "InQBack s' a"
    assume inqb': "InQBack s' b"
    assume tba': "TypeB s' a"
    assume tbb': "TypeB s' b"
    assume idx_lt': "Idx s' a < Idx s' b"
    assume ex_q':
      "\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
          Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q"

    have inqa: "InQBack s a"
      using inqa' T_eq unfolding InQBack_def by simp

    have inqb: "InQBack s b"
      using inqb' T_eq unfolding InQBack_def by simp

    have tba: "TypeB s a"
    proof (cases "a = BOT")
      case True
      have "Q_arr s 0 = BOT"
        using sI1_s unfolding sI1_Zero_Index_BOT_def by simp
      hence "QHas s a"
        using True unfolding QHas_def by blast
      thus ?thesis
        unfolding TypeB_def by blast
    next
      case False
      have a_in_Val: "a \<in> Val"
        using InQBack_non_BOT_implies_Val[OF INV inqa False] .
      show ?thesis
        using tba' TypeB_update[OF a_in_Val]
        by blast
    qed

    have tbb: "TypeB s b"
    proof (cases "b = BOT")
      case True
      have "Q_arr s 0 = BOT"
        using sI1_s unfolding sI1_Zero_Index_BOT_def by simp
      hence "QHas s b"
        using True unfolding QHas_def by blast
      thus ?thesis
        unfolding TypeB_def by blast
    next
      case False
      have b_in_Val: "b \<in> Val"
        using InQBack_non_BOT_implies_Val[OF INV inqb False] .
      show ?thesis
        using tbb' TypeB_update[OF b_in_Val]
        by blast
    qed

    have idx_lt: "Idx s a < Idx s b"
      using idx_lt' Idx_eq by simp

    have deq_old:
      "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and>
          Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
    proof -
      from ex_q' obtain q where q_props:
        "HasPendingDeq s' q"
        "program_counter s' q = ''D3''"
        "Idx s' a < j_var s' q"
        "j_var s' q \<le> Idx s' b"
        "Idx s' b < l_var s' q"
        by blast

      have q_neq_p: "q \<noteq> p"
      proof
        assume "q = p"
        then have "program_counter s' p = ''D3''"
          using q_props(2) by simp
        moreover have "program_counter s' p = ''D4''"
          using s'_is_update
          unfolding Sys_D3_success_update_def Let_def bridge_defs
          by auto
        ultimately show False
          by simp
      qed

      have q_pend: "HasPendingDeq s q"
        using q_props(1) pending_eq by simp

      have q_D3: "program_counter s q = ''D3''"
        using q_props(2) q_neq_p s'_is_update
        unfolding Sys_D3_success_update_def Let_def bridge_defs
        by auto

      have q_idx1: "Idx s a < j_var s q"
        using q_props(3) Idx_eq jl_eq[OF q_neq_p] by auto

      have q_idx2: "j_var s q \<le> Idx s b"
        using q_props(4) Idx_eq jl_eq[OF q_neq_p] by auto

      have q_idx3: "Idx s b < l_var s q"
        using q_props(5) Idx_eq jl_eq[OF q_neq_p] by auto

      show ?thesis
        using q_pend q_D3 q_idx1 q_idx2 q_idx3 by blast
    qed

    have "\<not> HB_EnqRetCall s a b"
      using hI19_s inqa inqb tba tbb idx_lt deq_old
      unfolding hI19_Scanner_Catches_Later_Enq_def
      by blast

    then show "\<not> HB_EnqRetCall s' a b"
      using hb_eq by simp
  qed

  show ?thesis
    unfolding hI19_Scanner_Catches_Later_Enq_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_hI20_Enq_Val_Valid:
  fixes s s' :: SysState
  assumes hI20_s: "hI20_Enq_Val_Valid s"
    and his_seq_eq: "his_seq s' = his_seq s"
  shows "hI20_Enq_Val_Valid s'"
  using hI20_s his_seq_eq
  unfolding hI20_Enq_Val_Valid_def
  by simp


lemma D3_success_preserves_hI21_Ret_Implies_Call:
  fixes s s' :: SysState
  assumes hI21_s: "hI21_Ret_Implies_Call s"
    and his_seq_eq: "his_seq s' = his_seq s"
  shows "hI21_Ret_Implies_Call s'"
  using hI21_s his_seq_eq
  unfolding hI21_Ret_Implies_Call_def
  by presburger

lemma D3_success_preserves_hI22_Deq_Local_Pattern:
  fixes s s' :: SysState and p jp :: nat and q_val
  assumes INV: "system_invariant s"
    and pc_D3: "program_counter s p = ''D3''"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and jp_def: "jp = j_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and q_not_bot: "q_val \<noteq> BOT"
  shows "hI22_Deq_Local_Pattern s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have inv_hI22_Deq_Local_Pattern: "hI22_Deq_Local_Pattern s"
    using INV unfolding system_invariant_def by blast
  have inv_sI11_x_var_Scope: "sI11_x_var_Scope s"
    using INV unfolding system_invariant_def by blast
  have inv_sI8_Q_Qback_Sync: "sI8_Q_Qback_Sync s"
    using INV unfolding system_invariant_def by blast

  have his_eq: "his_seq s' = his_seq s"
    using his_seq_eq .
  have T_eq: "Qback_arr s' = Qback_arr s"
    using T_unchanged .

  have x_p_update: "x_var s' p = q_val"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def jp_def q_val_def bridge_defs
    by simp

  have Q_jp_bot: "Q_arr s' jp = BOT"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def jp_def bridge_defs
    by simp

  have Q_other: "\<forall>k. k \<noteq> jp \<longrightarrow> Q_arr s' k = Q_arr s k"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def jp_def bridge_defs
    by simp

  have x_other: "\<forall>q. q \<noteq> p \<longrightarrow> x_var s' q = x_var s q"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def bridge_defs
    by simp

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by auto

  show ?thesis
    unfolding hI22_Deq_Local_Pattern_def
  proof (intro allI impI)
    fix p_check a sn
    assume Prem: "(\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a \<and> (\<forall>q. x_var s' q \<noteq> a)) \<and>
                  DeqRetInHis s' p_check a sn"

    from Prem obtain k where k_props:
      "Q_arr s' k = BOT" "Qback_arr s' k = a" "\<forall>q. x_var s' q \<noteq> a"
      by blast
    have RetHis: "DeqRetInHis s' p_check a sn"
      using Prem by blast

    show "let p_his = filter (\<lambda>e. act_pid e = p_check) (his_seq s') in
          \<exists>i<length p_his. p_his ! i = mk_act deq a p_check sn ret \<and>
          (0 < i \<and> p_his ! (i - 1) = mk_act deq BOT p_check sn call)"
    proof (cases "a = q_val")
      case True
      have "x_var s' p = a"
        using x_p_update True by simp
      with k_props(3) have False
        by blast
      thus ?thesis ..
    next
      case False
      have "Qback_arr s jp = q_val"
        using q_not_bot q_val_def inv_sI8_Q_Qback_Sync
        unfolding sI8_Q_Qback_Sync_def
        by metis
      hence "Qback_arr s' jp = q_val"
        using T_eq by simp
      with k_props(2) False have k_not_jp: "k \<noteq> jp"
        by auto

      have Q_s: "Q_arr s k = BOT"
        using Q_other k_not_jp k_props(1) by simp
      have T_s: "Qback_arr s k = a"
        using T_eq k_props(2) by simp

      have x_s: "\<forall>q. x_var s q \<noteq> a"
      proof (intro allI)
        fix q
        show "x_var s q \<noteq> a"
        proof (cases "q = p")
          case True
          have "x_var s p = BOT"
            using inv_sI11_x_var_Scope pc_D3
            unfolding sI11_x_var_Scope_def by simp
          moreover have "a \<noteq> BOT"
            using inv_hI22_Deq_Local_Pattern
                  RetHis his_eq
            unfolding hI22_Deq_Local_Pattern_def DeqRetInHis_def
            by (metis BOT_def DeqRetInHis_def INV Qback_Value_Is_Valid Val_def
                      less_irrefl_nat mem_Collect_eq)
          ultimately show ?thesis
            using True by simp
        next
          case False
          thus ?thesis
            using x_other k_props(3) by auto
        qed
      qed

      have RetHis_s: "DeqRetInHis s p_check a sn"
        using RetHis his_eq s_var_eq
        unfolding DeqRetInHis_def by simp

      with inv_hI22_Deq_Local_Pattern Q_s T_s x_s show ?thesis
        unfolding hI22_Deq_Local_Pattern_def
        using his_eq by auto
    qed
  qed
qed

lemma D3_success_preserves_hI25_Enq_Call_Ret_Balanced:
  fixes s s' :: SysState and p :: nat
  assumes hI25_s: "hI25_Enq_Call_Ret_Balanced s"
    and his_seq_eq: "his_seq s' = his_seq s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and pc_D3: "program_counter s p = ''D3''"
  shows "hI25_Enq_Call_Ret_Balanced s'"
proof -
  have pc_E_eq [simp]:
    "(program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) =
     (program_counter s q \<in> {''E1'', ''E2'', ''E3''})" for q
    using pc_eq pc_D3
    by (cases "q = p"; simp)

  have pc_E_disj_eq [simp]:
    "(program_counter s' q = ''E1'' \<or>
      program_counter s' q = ''E2'' \<or>
      program_counter s' q = ''E3'') =
     (program_counter s q = ''E1'' \<or>
      program_counter s q = ''E2'' \<or>
      program_counter s q = ''E3'')" for q
    using pc_eq pc_D3
    by (cases "q = p"; simp)

  have len_eq: "length (his_seq s') = length (his_seq s)"
    using his_seq_eq by simp

  have pointwise:
    "\<And>q k.
      k \<le> length (his_seq s') \<Longrightarrow>
      length (filter (\<lambda>e. act_cr e = ret)
        (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s'))))
      \<le>
      length (filter (\<lambda>e. act_cr e = call)
        (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')))) \<and>
      length (filter (\<lambda>e. act_cr e = call)
        (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s'))))
      -
      length (filter (\<lambda>e. act_cr e = ret)
        (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s'))))
      \<le> 1 \<and>
      (k = length (his_seq s') \<longrightarrow>
       (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} =
        (length (filter (\<lambda>e. act_cr e = call)
           (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s'))))
         -
         length (filter (\<lambda>e. act_cr e = ret)
           (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s'))))
         = 1)))"
  proof -
    fix q k
    assume k_bound: "k \<le> length (his_seq s')"

    let ?new_filter = "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s'))"
    let ?old_filter = "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s))"

    have filter_eq: "?new_filter = ?old_filter"
      using his_seq_eq by simp

    have k_bound_old: "k \<le> length (his_seq s)"
      using k_bound len_eq by simp

    let ?call_cnt = "length (filter (\<lambda>e. act_cr e = call) ?old_filter)"
    let ?ret_cnt  = "length (filter (\<lambda>e. act_cr e = ret) ?old_filter)"

    have old_point:
      "?ret_cnt \<le> ?call_cnt \<and>
       ?call_cnt - ?ret_cnt \<le> 1 \<and>
       (k = length (his_seq s) \<longrightarrow>
        (program_counter s q \<in> {''E1'', ''E2'', ''E3''} =
         (?call_cnt - ?ret_cnt = 1)))"
      using hI25_s[unfolded hI25_Enq_Call_Ret_Balanced_def Let_def, rule_format, OF k_bound_old] .

    have bound_part1: "?ret_cnt \<le> ?call_cnt"
      using old_point by simp

    have bound_part2: "?call_cnt - ?ret_cnt \<le> 1"
      using old_point by simp

    have pc_part: "k = length (his_seq s') \<longrightarrow>
      (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} =
       (length (filter (\<lambda>e. act_cr e = call) ?new_filter) -
        length (filter (\<lambda>e. act_cr e = ret) ?new_filter) = 1))"
    proof
      assume k_full: "k = length (his_seq s')"
      hence k_full_old: "k = length (his_seq s)"
        using len_eq by simp

      have old_full:
        "(program_counter s q \<in> {''E1'', ''E2'', ''E3''}) =
         (?call_cnt - ?ret_cnt = 1)"
        using old_point k_full_old by simp

      have eq2: "(program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) =
                 (program_counter s q \<in> {''E1'', ''E2'', ''E3''})"
        using pc_E_eq[of q] by simp

      show "(program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) =
            (length (filter (\<lambda>e. act_cr e = call) ?new_filter) -
             length (filter (\<lambda>e. act_cr e = ret) ?new_filter) = 1)"
        using old_full filter_eq eq2
        by simp
    qed

    show "length (filter (\<lambda>e. act_cr e = ret) ?new_filter)
          \<le> length (filter (\<lambda>e. act_cr e = call) ?new_filter) \<and>
          length (filter (\<lambda>e. act_cr e = call) ?new_filter)
          - length (filter (\<lambda>e. act_cr e = ret) ?new_filter) \<le> 1 \<and>
          (k = length (his_seq s') \<longrightarrow>
           (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} =
            (length (filter (\<lambda>e. act_cr e = call) ?new_filter)
             - length (filter (\<lambda>e. act_cr e = ret) ?new_filter) = 1)))"
      using filter_eq bound_part1 bound_part2 pc_part by simp
  qed

  show ?thesis
    unfolding hI25_Enq_Call_Ret_Balanced_def Let_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_hI26_DeqRet_D4_Mutex:
  fixes s s' :: SysState and p :: nat and q_val
  assumes hI26_s: "hI26_DeqRet_D4_Mutex s"
    and hI15_s: "hI15_Deq_Result_Exclusivity s"
    and his_seq_eq: "his_seq s' = his_seq s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and x_var_eq: "x_var s' = (\<lambda>x. if x = p then q_val else x_var s x)"
    and q_val_phys: "q_val = Q_arr s (j_var s p)"
  shows "hI26_DeqRet_D4_Mutex s'"
proof -
  have ret_eq: "DeqRetInHis s' p' a sn = DeqRetInHis s p' a sn" for p' a sn
    using his_seq_eq
    unfolding DeqRetInHis_def
    by simp

  have pointwise:
    "\<And>p' a. a \<in> Val \<Longrightarrow> \<not> ((\<exists>sn. DeqRetInHis s' p' a sn) \<and> program_counter s' p' = ''D4'' \<and> x_var s' p' = a)"
  proof -
    fix p' a
    assume a_val: "a \<in> Val"

    show "\<not> ((\<exists>sn. DeqRetInHis s' p' a sn) \<and> program_counter s' p' = ''D4'' \<and> x_var s' p' = a)"
    proof
      assume bad: "((\<exists>sn. DeqRetInHis s' p' a sn) \<and> program_counter s' p' = ''D4'' \<and> x_var s' p' = a)"
      then obtain sn where his_a_prime: "DeqRetInHis s' p' a sn"
        and pc_d4: "program_counter s' p' = ''D4''"
        and x_var_a: "x_var s' p' = a"
        by blast

      show False
      proof (cases "p' = p")
        case True
        have a_is_qval: "a = q_val"
          using True x_var_a x_var_eq by simp
        hence a_is_qphys: "a = Q_arr s (j_var s p)"
          using q_val_phys by simp

        have "\<not> (\<exists>sn'. DeqRetInHis s p a sn')"
          using hI15_s a_val a_is_qphys
          unfolding hI15_Deq_Result_Exclusivity_def
          by blast

        moreover have "DeqRetInHis s p a sn"
          using his_a_prime True ret_eq by simp

        ultimately show False
          by blast
      next
        case False
        have old_pc: "program_counter s p' = ''D4''"
          using pc_d4 False pc_eq by simp

        have old_x: "x_var s p' = a"
          using x_var_a False x_var_eq by simp

        have old_his: "\<exists>sn. DeqRetInHis s p' a sn"
          using his_a_prime ret_eq by blast

        from hI26_s[unfolded hI26_DeqRet_D4_Mutex_def] a_val old_pc old_x old_his
        show False
          by blast
      qed
    qed
  qed

  show ?thesis
    unfolding hI26_DeqRet_D4_Mutex_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_hI29_E2_Scanner_Immunity:
  fixes s s' :: SysState and p :: nat and q_val
  assumes INV: "system_invariant s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and TypeB_update: "\<And>x. x \<in> Val \<Longrightarrow> TypeB s' x \<longleftrightarrow> (TypeB s x \<and> x \<noteq> q_val)"
  shows "hI29_E2_Scanner_Immunity s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI29_s: "hI29_E2_Scanner_Immunity s"
    using INV unfolding system_invariant_def by blast

  have his_eq: "his_seq s' = his_seq s"
    using his_seq_eq .

  have T_eq: "Qback_arr s' = Qback_arr s"
    using T_unchanged .

  have s_var_eq: "s_var s' = s_var s"
    using s'_is_update
    unfolding Sys_D3_success_update_def Let_def s_var_def bridge_defs
    by (auto simp: fun_eq_iff)

  have pointwise:
    "\<And>p_enq a q.
      program_counter s' p_enq = ''E2'' \<Longrightarrow>
      InQBack s' a \<Longrightarrow>
      TypeB s' a \<Longrightarrow>
      HasPendingDeq s' q \<Longrightarrow>
      program_counter s' q = ''D3'' \<Longrightarrow>
      Idx s' a < j_var s' q \<Longrightarrow>
      j_var s' q \<le> i_var s' p_enq \<Longrightarrow>
      i_var s' p_enq < l_var s' q \<Longrightarrow>
      \<not> HB_EnqRetCall s' a (v_var s' p_enq)"
  proof -
    fix p_enq a q
    assume pc_e': "program_counter s' p_enq = ''E2''"
    assume inqa': "InQBack s' a"
    assume tba': "TypeB s' a"
    assume pend_q': "HasPendingDeq s' q"
    assume pc_q_D3': "program_counter s' q = ''D3''"
    assume idx1': "Idx s' a < j_var s' q"
    assume idx2': "j_var s' q \<le> i_var s' p_enq"
    assume idx3': "i_var s' p_enq < l_var s' q"

    show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
    proof (cases "q = p")
      case True
      have "program_counter s' p = ''D4''"
        using pc_eq by simp
      thus ?thesis
        using pc_q_D3' True by simp
    next
      case False
      have q_neq_p: "q \<noteq> p"
        using False by simp

      have p_enq_neq_p: "p_enq \<noteq> p"
      proof
        assume "p_enq = p"
        then have "program_counter s' p = ''E2''"
          using pc_e' by simp
        moreover have "program_counter s' p = ''D4''"
          using pc_eq by simp
        ultimately show False
          by simp
      qed

      have pc_q_s: "program_counter s q = ''D3''"
        using pc_q_D3' q_neq_p pc_eq by simp

      have pc_e_s: "program_counter s p_enq = ''E2''"
        using pc_e' p_enq_neq_p pc_eq by simp

      have inqa_s: "InQBack s a"
        using inqa' T_eq unfolding InQBack_def by simp

  have sI1_s: "sI1_Zero_Index_BOT s"
    using INV unfolding system_invariant_def by blast

            have tba_s: "TypeB s a"
      proof (cases "a = BOT")
        case True
        have "Q_arr s 0 = BOT"
          using sI1_s unfolding sI1_Zero_Index_BOT_def by simp
        hence "QHas s a"
          using True unfolding QHas_def by blast
        thus ?thesis
          unfolding TypeB_def by blast
      next
        case False
        have a_in_Val: "a \<in> Val"
          using InQBack_non_BOT_implies_Val[OF INV inqa_s False] .
        show ?thesis
          using tba' TypeB_update[OF a_in_Val]
          by blast
      qed

      have pend_q_s: "HasPendingDeq s q"
        using pend_q' his_eq s_var_eq
        unfolding HasPendingDeq_def DeqCallInHis_def Let_def by simp

      have idx_eq: "Idx s' x = Idx s x" for x
        using T_eq unfolding Idx_def AtIdx_def by simp

      have j_var_eq: "j_var s' q = j_var s q"
        using q_neq_p s'_is_update
        unfolding Sys_D3_success_update_def Let_def bridge_defs
        by (auto simp: fun_eq_iff)

      have l_var_eq: "l_var s' q = l_var s q"
        using q_neq_p s'_is_update
        unfolding Sys_D3_success_update_def Let_def bridge_defs
        by (auto simp: fun_eq_iff)

      have i_var_eq: "i_var s' p_enq = i_var s p_enq"
        using p_enq_neq_p s'_is_update
        unfolding Sys_D3_success_update_def Let_def bridge_defs
        by (auto simp: fun_eq_iff)

      have v_var_eq: "v_var s' p_enq = v_var s p_enq"
        using p_enq_neq_p s'_is_update
        unfolding Sys_D3_success_update_def Let_def bridge_defs
        by (auto simp: fun_eq_iff)

      have bound1: "Idx s a < j_var s q"
        using idx1' idx_eq j_var_eq by simp

      have bound2: "j_var s q \<le> i_var s p_enq"
        using idx2' j_var_eq i_var_eq by simp

      have bound3: "i_var s p_enq < l_var s q"
        using idx3' i_var_eq l_var_eq by simp

      have hb_eq: "HB_EnqRetCall s' a (v_var s' p_enq) = HB_EnqRetCall s a (v_var s p_enq)"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def
                  match_ret_def match_call_def mk_op_def op_name_def op_val_def
        using his_eq v_var_eq by auto

      have "\<not> HB_EnqRetCall s a (v_var s p_enq)"
        using hI29_s pc_e_s inqa_s tba_s pend_q_s pc_q_s bound1 bound2 bound3
        unfolding hI29_E2_Scanner_Immunity_def by blast

      then show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
        using hb_eq by simp
    qed
  qed

  show ?thesis
    unfolding hI29_E2_Scanner_Immunity_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_hI30_Ticket_HB_Immunity:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
    and s'_is_update: "s' = Sys_D3_success_update s p"
    and his_seq_eq: "his_seq s' = his_seq s"
    and T_unchanged: "Qback_arr s' = Qback_arr s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
  shows "hI30_Ticket_HB_Immunity s'"
proof -
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def

  have hI30_s: "hI30_Ticket_HB_Immunity s"
    using INV unfolding system_invariant_def by blast

  have his_eq: "his_seq s' = his_seq s"
    using his_seq_eq .

  have T_eq: "Qback_arr s' = Qback_arr s"
    using T_unchanged .

  have pointwise:
    "\<And>b q.
      program_counter s' q \<in> {''E2'', ''E3''} \<Longrightarrow>
      InQBack s' b \<Longrightarrow>
      b \<noteq> BOT \<Longrightarrow>
      b \<noteq> v_var s' q \<Longrightarrow>
      HB_EnqRetCall s' b (v_var s' q) \<Longrightarrow>
      Idx s' b < i_var s' q"
  proof -
    fix b q
    assume pc_q': "program_counter s' q \<in> {''E2'', ''E3''}"
    assume inqb': "InQBack s' b"
    assume b_not_bot': "b \<noteq> BOT"
    assume b_neq_v': "b \<noteq> v_var s' q"
    assume hb': "HB_EnqRetCall s' b (v_var s' q)"

    have q_neq_p: "q \<noteq> p"
    proof
      assume "q = p"
      then have "program_counter s' p \<in> {''E2'', ''E3''}"
        using pc_q' by simp
      moreover have "program_counter s' p = ''D4''"
        using pc_eq by simp
      ultimately show False
        by simp
    qed

    have v_var_eq_q: "v_var s' q = v_var s q"
      using q_neq_p s'_is_update
      unfolding Sys_D3_success_update_def Let_def bridge_defs
      by (auto simp: fun_eq_iff)

    have i_var_eq_q: "i_var s' q = i_var s q"
      using q_neq_p s'_is_update
      unfolding Sys_D3_success_update_def Let_def bridge_defs
      by (auto simp: fun_eq_iff)

    have pc_eq_q: "program_counter s' q = program_counter s q"
      using q_neq_p pc_eq by simp

    have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}"
      using pc_q' pc_eq_q by simp

    have inqb_s: "InQBack s b"
      using inqb' T_eq unfolding InQBack_def by simp

    have b_neq_v_s: "b \<noteq> v_var s q"
      using b_neq_v' v_var_eq_q by simp

    have hb_eq: "HB_EnqRetCall s' b (v_var s' q) = HB_EnqRetCall s b (v_var s q)"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def
                match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq v_var_eq_q by auto

    have hb_s: "HB_EnqRetCall s b (v_var s q)"
      using hb' hb_eq by simp

    have idx_eq: "Idx s' b = Idx s b"
      unfolding Idx_def AtIdx_def using T_eq by simp

    have "Idx s b < i_var s q"
      using hI30_s pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
      unfolding hI30_Ticket_HB_Immunity_def
      by blast

    thus "Idx s' b < i_var s' q"
      using idx_eq i_var_eq_q by simp
  qed

  show ?thesis
    unfolding hI30_Ticket_HB_Immunity_def
    using pointwise
    by blast
qed

lemma D3_success_preserves_data_independent_lin_seq:
  fixes s s' :: SysState and p sn q_val :: nat and base_lin
  assumes INV: "system_invariant s"
    and q_in_SetB: "q_val \<in> SetB s"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                               then modify_lin (lin_seq s) (his_seq s) q_val
                               else lin_seq s)"
    and s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p sn]"
  shows "data_independent (lin_seq s')"
proof -
  have di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by simp

  have no_deq_q_lin:
    "\<forall>i < length (lin_seq s).
      op_name (lin_seq s ! i) = deq \<longrightarrow> op_val (lin_seq s ! i) \<noteq> q_val"
    using SetB_implies_no_deq_in_lin[OF INV q_in_SetB]
    unfolding DeqIdxs_def by auto

  have mset_base_eq: "mset base_lin = mset (lin_seq s)"
    unfolding base_def
    using modify_preserves_mset
    by presburger

  have no_deq_q_base:
    "\<forall>i < length base_lin.
      op_name (base_lin ! i) = deq \<longrightarrow> op_val (base_lin ! i) \<noteq> q_val"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length base_lin"
    assume name_deq: "op_name (base_lin ! i) = deq"

    have "base_lin ! i \<in> set base_lin"
      using i_lt by simp
    hence "base_lin ! i \<in> set (lin_seq s)"
      using mset_base_eq by (metis mset_eq_setD)
    then obtain j where j_lt: "j < length (lin_seq s)"
      and j_eq: "lin_seq s ! j = base_lin ! i"
      by (auto simp: in_set_conv_nth)

    show "op_val (base_lin ! i) \<noteq> q_val"
      using no_deq_q_lin j_lt j_eq name_deq by auto
  qed

  have di_base: "data_independent base_lin"
    using di_lin_s mset_base_eq data_independent_cong
    by blast

  show ?thesis
    using data_independent_append_deq_fresh[OF di_base no_deq_q_base]
    by (simp add: s'_lin_def)
qed

lemma D3_success_preserves_lI1_Op_Sets_Equivalence:
  fixes s s' :: SysState and p q_val :: nat and base_lin
  assumes INV: "system_invariant s"
    and pc_D3: "program_counter s p = ''D3''"
    and his_seq_eq: "his_seq s' = his_seq s"
    and q_in_SetB: "q_val \<in> SetB s"
    and set_base_eq: "set base_lin = set (lin_seq s)"
    and lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and seta_update: "SetA s' = SetA s \<union> {q_val} \<and> SetB s' = SetB s - {q_val}"
  shows "lI1_Op_Sets_Equivalence s'"
proof -
  have hI12_s: "hI12_D_Phase_Pending_Deq s"
    using INV unfolding system_invariant_def by blast

  have lI1_s: "lI1_Op_Sets_Equivalence s"
    using INV unfolding system_invariant_def by blast

  let ?sn_deq = "s_var s p"
  let ?deq_act = "mk_op deq q_val p ?sn_deq"
  let ?q_enqs = "{mk_op enq q_val pid sn | pid sn. EnqCallInHis s pid q_val sn}"

  have OPLin_new: "OPLin s' = OPLin s \<union> {?deq_act}"
  proof -
    have "set (lin_seq s') = set base_lin \<union> {?deq_act}"
      using lin_s'_eq by simp
    then show ?thesis
      unfolding OPLin_def
      using set_base_eq by simp
  qed

  have EnqCall_eq: "\<And>pid a sn. EnqCallInHis s' pid a sn \<longleftrightarrow> EnqCallInHis s pid a sn"
    unfolding EnqCallInHis_def
    using his_seq_eq by simp

  have DeqCall_eq: "\<And>pid sn. DeqCallInHis s' pid sn \<longleftrightarrow> DeqCallInHis s pid sn"
    unfolding DeqCallInHis_def
    using his_seq_eq by simp

  have OP_B_enq_new: "OP_B_enq s' = OP_B_enq s - ?q_enqs"
  proof (rule set_eqI, rule iffI)
    fix x
    assume "x \<in> OP_B_enq s'"
    then obtain pid b sn where
      x_def: "x = mk_op enq b pid sn"
      and b_in: "b \<in> SetB s'"
      and call_in: "EnqCallInHis s' pid b sn"
      unfolding OP_B_enq_def by blast
    show "x \<in> OP_B_enq s - ?q_enqs"
      using seta_update x_def b_in call_in EnqCall_eq
      unfolding OP_B_enq_def mk_op_def by auto
  next
    fix x
    assume "x \<in> OP_B_enq s - ?q_enqs"
    then show "x \<in> OP_B_enq s'"
      using seta_update EnqCall_eq
      unfolding OP_B_enq_def mk_op_def by auto
  qed

  have OP_A_enq_new: "OP_A_enq s' = OP_A_enq s \<union> ?q_enqs"
  proof (rule set_eqI, rule iffI)
    fix x
    assume "x \<in> OP_A_enq s'"
    then obtain pid a sn where
      x_def: "x = mk_op enq a pid sn"
      and a_in: "a \<in> SetA s'"
      and call_in: "EnqCallInHis s' pid a sn"
      unfolding OP_A_enq_def by blast
    show "x \<in> OP_A_enq s \<union> ?q_enqs"
      using seta_update x_def a_in call_in EnqCall_eq
      unfolding OP_A_enq_def mk_op_def by auto
  next
    fix x
    assume "x \<in> OP_A_enq s \<union> ?q_enqs"
    then show "x \<in> OP_A_enq s'"
      using seta_update EnqCall_eq
      unfolding OP_A_enq_def mk_op_def by auto
  qed

  have q_val_enqs_exist: "?q_enqs \<subseteq> OP_B_enq s"
    unfolding OP_B_enq_def
    using q_in_SetB by auto

  have Enq_Union_Invariant: "OP_A_enq s' \<union> OP_B_enq s' = OP_A_enq s \<union> OP_B_enq s"
    using OP_A_enq_new OP_B_enq_new q_val_enqs_exist
    by blast

  have OP_A_deq_new: "OP_A_deq s' = OP_A_deq s \<union> {?deq_act}"
  proof (rule set_eqI, rule iffI)
    fix x
    assume "x \<in> OP_A_deq s'"
    then have x_in_OPLin': "x \<in> OPLin s'"
      and op_deq: "op_name x = deq"
      and val_A: "op_val x \<in> SetA s'"
      and call': "DeqCallInHis s' (op_pid x) (op_ssn x)"
      unfolding OP_A_deq_def by auto

    have call_s: "DeqCallInHis s (op_pid x) (op_ssn x)"
      using call' DeqCall_eq by simp

    have x_in_OPLin_s: "x \<in> OPLin s \<or> x = ?deq_act"
      using x_in_OPLin' OPLin_new by auto

    show "x \<in> OP_A_deq s \<union> {?deq_act}"
    proof (cases "x = ?deq_act")
      case True
      then show ?thesis by simp
    next
      case False
      with x_in_OPLin_s have x_in_lin: "x \<in> OPLin s"
        by simp

      have "op_val x \<in> SetA s"
      proof (rule ccontr)
        assume val_not_A: "op_val x \<notin> SetA s"
        with val_A seta_update have val_is_q: "op_val x = q_val"
          by auto
        have q_deq_empty: "DeqIdxs s q_val = {}"
  using SetB_implies_no_deq_in_lin[OF INV q_in_SetB] .

    have "\<forall>act \<in> set (lin_seq s). op_val act = q_val \<longrightarrow> op_name act \<noteq> deq"
    proof (intro ballI impI)
      fix act
      assume act_in: "act \<in> set (lin_seq s)"
      assume val_act_q: "op_val act = q_val"
    
      then obtain j where j_lt: "j < length (lin_seq s)" and j_eq: "lin_seq s ! j = act"
        using act_in by (auto simp: in_set_conv_nth)
    
      show "op_name act \<noteq> deq"
      proof
        assume name_deq: "op_name act = deq"
    
        have "j \<in> DeqIdxs s q_val"
          unfolding DeqIdxs_def
          using j_lt j_eq val_act_q name_deq
          by auto
    
        with q_deq_empty show False
          by simp
      qed
    qed
        moreover have "x \<in> set (lin_seq s)"
          using x_in_lin unfolding OPLin_def by simp
        ultimately show False
          using op_deq val_is_q by blast
      qed
      thus ?thesis
        using x_in_lin op_deq call_s unfolding OP_A_deq_def by blast
    qed
  next
    fix x
    assume x_in_union: "x \<in> OP_A_deq s \<union> {?deq_act}"
    show "x \<in> OP_A_deq s'"
    proof (cases "x = ?deq_act")
      case True
      have "?deq_act \<in> OPLin s'"
        using OPLin_new by simp
      moreover have "op_name ?deq_act = deq"
        unfolding mk_op_def op_name_def by simp
      moreover have "op_val ?deq_act \<in> SetA s'"
        using seta_update unfolding mk_op_def op_val_def by simp
      moreover have "DeqCallInHis s' (op_pid ?deq_act) (op_ssn ?deq_act)"
      proof -
        have pc_in: "program_counter s p \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
          using pc_D3 by simp

        have pending: "HasPendingDeq s p"
          using hI12_s pc_in
          unfolding hI12_D_Phase_Pending_Deq_def by blast

        show ?thesis
          using pending DeqCall_eq[symmetric]
          unfolding HasPendingDeq_def Let_def mk_op_def op_pid_def op_ssn_def
          by auto
      qed
      ultimately show ?thesis
        unfolding OP_A_deq_def using True by simp
    next
      case False
      hence "x \<in> OP_A_deq s"
        using x_in_union by auto
      then have "x \<in> OPLin s" and "op_name x = deq" and "op_val x \<in> SetA s"
        and "DeqCallInHis s (op_pid x) (op_ssn x)"
        unfolding OP_A_deq_def by auto

      moreover have "x \<in> OPLin s'"
        using \<open>x \<in> OPLin s\<close> OPLin_new by auto
      moreover have "op_val x \<in> SetA s'"
        using \<open>op_val x \<in> SetA s\<close> seta_update by auto
      moreover have "DeqCallInHis s' (op_pid x) (op_ssn x)"
        using \<open>DeqCallInHis s (op_pid x) (op_ssn x)\<close> DeqCall_eq by simp
      ultimately show ?thesis
        unfolding OP_A_deq_def by simp
    qed
  qed

  have OPLin_s: "OPLin s = OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_s unfolding lI1_Op_Sets_Equivalence_def by simp

  show ?thesis
    unfolding lI1_Op_Sets_Equivalence_def
    using OPLin_new OP_A_deq_new Enq_Union_Invariant OPLin_s
    by blast
qed

lemma D3_success_preserves_lI3_HB_Ret_Lin_Sync:
  fixes s s' :: SysState and p jp q_val :: nat and base_lin
  assumes INV: "system_invariant s"
    and pc_D3: "program_counter s p = ''D3''"
    and jp_def: "jp = j_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and val_eq: "q_val = Qback_arr s jp"
    and q_not_bot: "q_val \<noteq> BOT"
    and q_in_SetB: "q_val \<in> SetB s"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                               then modify_lin (lin_seq s) (his_seq s) q_val
                               else lin_seq s)"
    and lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and his_seq_eq: "his_seq s' = his_seq s"
  shows "lI3_HB_Ret_Lin_Sync s'"
proof -
  let ?sn_deq = "s_var s p"
  let ?deq_act = "mk_op deq q_val p ?sn_deq"

  have lI3_s: "lI3_HB_Ret_Lin_Sync s"
    using INV unfolding system_invariant_def by blast

  have di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by simp

  have hI15_s: "hI15_Deq_Result_Exclusivity s"
    using INV unfolding system_invariant_def by blast

  have sI6_s: "sI6_D3_Scan_Pointers s"
    using INV unfolding system_invariant_def by blast

  have sI8_s: "sI8_Q_Qback_Sync s"
    using INV unfolding system_invariant_def by blast

  have sI10_s: "sI10_Qback_Unique_Vals s"
    using INV unfolding system_invariant_def by blast

  have H_eq: "his_seq s' = his_seq s"
    using his_seq_eq .

  have hb_cons_base: "HB_consistent base_lin (his_seq s)"
  proof (cases "should_modify (lin_seq s) (his_seq s) q_val")
    case True
    have base_lin_form: "base_lin = modify_lin (lin_seq s) (his_seq s) q_val"
      unfolding base_def using True by simp

    show ?thesis
      unfolding base_lin_form
    proof (rule modify_preserves_HB_consistent[OF INV])
      show "lin_seq s = lin_seq s" by simp
      show "his_seq s = his_seq s" by simp
      show "HB_consistent (lin_seq s) (his_seq s)"
        using lI3_s
        unfolding lI3_HB_Ret_Lin_Sync_def
        by (simp add: HB_Act_def HB_consistent_def)
      show "data_independent (lin_seq s)"
        using di_lin_s .
      show "TypeBT s q_val"
      proof -
        have typeB_q: "TypeB s q_val"
          using q_in_SetB unfolding SetB_def by simp

        have in_qback_q: "InQBack s q_val"
          using q_in_SetB
          unfolding SetB_def InQBack_def
          using val_eq
          by auto

        have idx_eq_j: "Idx s q_val = j_var s p"
          using val_eq sI10_s sI8_s q_not_bot
          unfolding sI10_Qback_Unique_Vals_def sI8_Q_Qback_Sync_def Idx_def AtIdx_def
          using q_val_def jp_def
          by (smt (verit, ccfv_threshold) some_eq_imp)

        have cond1: "j_var s p \<le> Idx s q_val"
          using idx_eq_j by simp

        have cond2: "Idx s q_val < l_var s p"
        proof -
          have "j_var s p < l_var s p"
            using sI6_s pc_D3
            unfolding sI6_D3_Scan_Pointers_def by force
          then show ?thesis
            using idx_eq_j by simp
        qed

        have cond3: "\<forall>k. j_var s p \<le> k \<and> k < Idx s q_val \<longrightarrow> Q_arr s k = BOT"
          using idx_eq_j by simp

        have struct_part:
          "\<exists>p'. program_counter s p' = ''D3'' \<and>
                j_var s p' \<le> Idx s q_val \<and>
                Idx s q_val < l_var s p' \<and>
                (\<forall>k. j_var s p' \<le> k \<and> k < Idx s q_val \<longrightarrow> Q_arr s k = BOT)"
          by (rule exI[where x=p], use pc_D3 cond1 cond2 cond3 in simp)

        show ?thesis
          unfolding TypeBT_def
          using typeB_q in_qback_q struct_part by blast
      qed
    qed
  next
    case False
    have base_lin_form: "base_lin = lin_seq s"
      unfolding base_def using False by simp

    show ?thesis
      unfolding base_lin_form
      using lI3_s
      unfolding lI3_HB_Ret_Lin_Sync_def
      by (simp add: HB_Act_def HB_consistent_def)
  qed

  have hb_cons_final: "HB_consistent (base_lin @ [?deq_act]) (his_seq s)"
  proof (rule HB_consistent_append)
    show "HB_consistent base_lin (his_seq s)"
      by (rule hb_cons_base)

    have deq_act_cannot_HB: "\<forall>x. \<not> HB (his_seq s) ?deq_act x"
    proof
      fix x
      show "\<not> HB (his_seq s) ?deq_act x"
      proof
        assume "HB (his_seq s) ?deq_act x"
        then obtain k where
          k_bounds: "k < length (his_seq s)" and
          match_pid: "act_pid ((his_seq s)!k) = op_pid ?deq_act" and
          match_val: "act_val ((his_seq s)!k) = op_val ?deq_act" and
          match_oper: "act_name ((his_seq s)!k) = deq" and
          match_cr: "act_cr ((his_seq s)!k) = ret"
          unfolding HB_def match_ret_def Let_def mk_op_def op_name_def
          by auto

        have p_eq: "op_pid ?deq_act = p"
          unfolding mk_op_def op_pid_def by simp

        have val_eq_act: "op_val ?deq_act = q_val"
          unfolding mk_op_def op_val_def by simp

        have q_in_val: "q_val \<in> Val"
          using q_in_SetB q_not_bot
          unfolding SetB_def TypeB_def QHas_def
          by auto

let ?k_sn = "act_ssn ((his_seq s) ! k)"

have hist_evt_in_set: "(his_seq s ! k) \<in> set (his_seq s)"
  using k_bounds by simp 

have deq_ret_his: "DeqRetInHis s p q_val ?k_sn"
  unfolding DeqRetInHis_def
  using hist_evt_in_set match_pid match_val match_oper match_cr p_eq val_eq_act
  by auto

        have no_q_in_arr: "\<forall>k. Q_arr s k \<noteq> q_val"
          using hI15_s q_in_val deq_ret_his
          unfolding hI15_Deq_Result_Exclusivity_def
          by blast

        have q_in_arr: "Q_arr s jp = q_val"
          using q_val_def by simp

        then show False
          using no_q_in_arr by blast
      qed
    qed

    show "\<forall>a \<in> set base_lin. \<not> HB (his_seq s) ?deq_act a"
      using deq_act_cannot_HB by blast

    show "\<not> HB (his_seq s) ?deq_act ?deq_act"
      using deq_act_cannot_HB by blast
  qed

  have set_base_eq: "set base_lin = set (lin_seq s)"
  proof (cases "should_modify (lin_seq s) (his_seq s) q_val")
    case True
    then have "base_lin = modify_lin (lin_seq s) (his_seq s) q_val"
      unfolding base_def by simp
    then have "mset base_lin = mset (lin_seq s)"
      using modify_preserves_mset by simp
    then show ?thesis
      by (metis set_mset_mset)
  next
    case False
    then show ?thesis
      unfolding base_def by simp
  qed

  show ?thesis
    unfolding lI3_HB_Ret_Lin_Sync_def lin_s'_eq H_eq
  proof (intro conjI)
    show "\<forall>k1 k2.
      k1 < length (base_lin @ [?deq_act]) \<and>
      k2 < length (base_lin @ [?deq_act]) \<and>
      HB_Act s' ((base_lin @ [?deq_act]) ! k1) ((base_lin @ [?deq_act]) ! k2) \<longrightarrow>
      k1 < k2"
    proof (intro allI impI)
      fix k1 k2
      assume asm:
        "k1 < length (base_lin @ [?deq_act]) \<and>
         k2 < length (base_lin @ [?deq_act]) \<and>
         HB_Act s' ((base_lin @ [?deq_act]) ! k1) ((base_lin @ [?deq_act]) ! k2)"
      have "HB (his_seq s) ((base_lin @ [?deq_act]) ! k1) ((base_lin @ [?deq_act]) ! k2)"
        using asm unfolding HB_Act_def H_eq by simp
      then show "k1 < k2"
        using hb_cons_final asm
        unfolding HB_consistent_def by blast
    qed

    show "\<forall>p a sn.
      EnqRetInHis s' p a sn \<longrightarrow>
      (\<exists>k < length (base_lin @ [?deq_act]). (base_lin @ [?deq_act]) ! k = mk_op enq a p sn)"
    proof (intro allI impI)
      fix p' a sn
      assume "EnqRetInHis s' p' a sn"
      then have "EnqRetInHis s p' a sn"
        using his_seq_eq unfolding EnqRetInHis_def by simp

      then obtain k where old_k: "k < length (lin_seq s)"
        and old_act: "lin_seq s ! k = mk_op enq a p' sn"
        using lI3_s unfolding lI3_HB_Ret_Lin_Sync_def by blast

      have "lin_seq s ! k \<in> set (lin_seq s)"
        using nth_mem old_k by simp
      then have "lin_seq s ! k \<in> set base_lin"
        using set_base_eq by simp
      then have "lin_seq s ! k \<in> set (base_lin @ [?deq_act])"
        by simp
      then obtain k' where k'_props: "k' < length (base_lin @ [?deq_act])"
        and k'_val: "(base_lin @ [?deq_act]) ! k' = lin_seq s ! k"
        using in_set_conv_nth by metis

      show "\<exists>k < length (base_lin @ [?deq_act]). (base_lin @ [?deq_act]) ! k = mk_op enq a p' sn"
        by (rule exI[where x=k'], use k'_props k'_val old_act in simp)
    qed

    show "\<forall>p a sn.
      DeqRetInHis s' p a sn \<longrightarrow>
      (\<exists>k < length (base_lin @ [?deq_act]). (base_lin @ [?deq_act]) ! k = mk_op deq a p sn)"
    proof (intro allI impI)
      fix p' a sn
      assume "DeqRetInHis s' p' a sn"
      then have "DeqRetInHis s p' a sn"
        using his_seq_eq unfolding DeqRetInHis_def by simp

      then obtain k where old_k: "k < length (lin_seq s)"
        and old_act: "lin_seq s ! k = mk_op deq a p' sn"
        using lI3_s unfolding lI3_HB_Ret_Lin_Sync_def by blast

      have "lin_seq s ! k \<in> set (lin_seq s)"
        using nth_mem old_k by simp
      then have "lin_seq s ! k \<in> set base_lin"
        using set_base_eq by simp
      then have "lin_seq s ! k \<in> set (base_lin @ [?deq_act])"
        by simp
      then obtain k' where k'_props: "k' < length (base_lin @ [?deq_act])"
        and k'_val: "(base_lin @ [?deq_act]) ! k' = lin_seq s ! k"
        using in_set_conv_nth by metis

      show "\<exists>k < length (base_lin @ [?deq_act]). (base_lin @ [?deq_act]) ! k = mk_op deq a p' sn"
        by (rule exI[where x=k'], use k'_props k'_val old_act in simp)
    qed
  qed
qed

lemma D3_success_preserves_lI6_D4_Deq_Linearized:
  fixes s s' :: SysState and p q_val :: nat and base_lin
  assumes lI6_s: "lI6_D4_Deq_Linearized s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and x_var_eq: "x_var s' = (\<lambda>x. if x = p then q_val else x_var s x)"
    and s_var_eq: "s_var s' = s_var s"
    and lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and set_base_eq: "set base_lin = set (lin_seq s)"
  shows "lI6_D4_Deq_Linearized s'"
proof -
  have pointwise:
    "\<And>q. program_counter s' q = ''D4'' \<Longrightarrow>
         mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s')"
  proof -
    fix q
    assume q_D4: "program_counter s' q = ''D4''"
    show "mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s')"
    proof (cases "q = p")
      case True
      have x_p: "x_var s' p = q_val"
        using x_var_eq by simp
      have sn_p: "s_var s' p = s_var s p"
        using s_var_eq by simp
      have act_eq: "mk_op deq (x_var s' p) p (s_var s' p) = mk_op deq q_val p (s_var s p)"
        using x_p sn_p by simp
      have in_list: "mk_op deq q_val p (s_var s p) \<in> set (lin_seq s')"
        using lin_s'_eq by simp
      thus ?thesis
        using act_eq True by simp
    next
      case False
      have pc_old: "program_counter s q = ''D4''"
        using q_D4 False pc_eq by simp

      have x_old: "x_var s' q = x_var s q"
        using False x_var_eq by simp

      have sn_old: "s_var s' q = s_var s q"
        using s_var_eq by simp

      have old_in: "mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s)"
        using lI6_s pc_old x_old sn_old
        unfolding lI6_D4_Deq_Linearized_def by auto

      have "set (lin_seq s) \<subseteq> set (lin_seq s')"
        using lin_s'_eq set_base_eq by auto

      thus ?thesis
        using old_in by blast
    qed
  qed

  show ?thesis
    unfolding lI6_D4_Deq_Linearized_def
    using pointwise
    by simp
qed

lemma D3_success_preserves_lI7_D4_Deq_Deq_HB:
  fixes s s' :: SysState and p q_val :: nat and base_lin
  assumes INV: "system_invariant s"
    and q_in_SetB: "q_val \<in> SetB s"
    and q_not_bot: "q_val \<noteq> BOT"
    and q_val_eq: "q_val = Q_arr s (j_var s p)"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                               then modify_lin (lin_seq s) (his_seq s) q_val
                               else lin_seq s)"
    and s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and his_eq: "his_seq s' = his_seq s"
    and pc_s': "program_counter s' = (program_counter s)(p := ''D4'')"
    and pc_s: "program_counter s p = ''D3''"
    and lI8_s:
      "\<forall>q. program_counter s q = ''D3'' \<longrightarrow>
         (\<forall>k < length (lin_seq s).
           (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q) \<longrightarrow>
           DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))"
    and x_eq: "\<forall>q. q \<noteq> p \<longrightarrow> x_var s' q = x_var s q"
    and sn_eq: "\<forall>q. q \<noteq> p \<longrightarrow> s_var s' q = s_var s q"
  shows "lI7_D4_Deq_Deq_HB s'"
  using modify_preserves_lI7_D4_Deq_Deq_HB[
    OF INV q_in_SetB q_not_bot q_val_eq base_def s'_lin_def his_eq pc_s' pc_s lI8_s x_eq sn_eq
  ]
  by blast

lemma D3_success_preserves_lI8_D3_Deq_Returned:
  fixes s s' :: SysState and p q_val :: nat and base_lin
  assumes lI8_s: "lI8_D3_Deq_Returned s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and his_seq_eq: "his_seq s' = his_seq s"
    and set_base_eq: "set base_lin = set (lin_seq s)"
  shows "lI8_D3_Deq_Returned s'"
proof -
  have old_point:
    "\<And>q k. program_counter s q = ''D3'' \<Longrightarrow>
           k < length (lin_seq s) \<Longrightarrow>
           (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q) \<Longrightarrow>
           DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
    using lI8_s unfolding lI8_D3_Deq_Returned_def by blast

  show ?thesis
    unfolding lI8_D3_Deq_Returned_def
  proof (intro allI impI)
    fix q k
    assume q_D3: "program_counter s' q = ''D3''"
       and k_bound: "k < length (lin_seq s')"
       and act_match: "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"

    show "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
    proof (cases "q = p")
      case True
      have "program_counter s' p = ''D4''"
        using pc_eq by simp
      with q_D3 True show ?thesis
        by simp
    next
      case False
      have pc_q_old: "program_counter s q = ''D3''"
        using q_D3 False pc_eq by simp

      have k_old: "k < length base_lin"
      proof (rule ccontr)
        assume "\<not> k < length base_lin"
        hence "k = length base_lin"
          using k_bound lin_s'_eq by auto
        hence "op_pid (lin_seq s' ! k) = p"
          using lin_s'_eq by (simp add: nth_append mk_op_def op_pid_def)
        with act_match False show False
          by simp
      qed

      have act_k: "lin_seq s' ! k \<in> set base_lin"
        using k_old lin_s'_eq by (simp add: nth_append)

      have "lin_seq s' ! k \<in> set (lin_seq s)"
        using act_k set_base_eq by blast

      then obtain k_orig where
        k_orig_bound: "k_orig < length (lin_seq s)"
        and k_orig_match: "lin_seq s ! k_orig = lin_seq s' ! k"
        by (metis in_set_conv_nth)

      have old_inv: "DeqRetInHis s q (op_val (lin_seq s ! k_orig)) (op_ssn (lin_seq s ! k_orig))"
        using old_point[OF pc_q_old k_orig_bound]
              k_orig_match act_match
        by metis

      thus ?thesis
        using k_orig_match his_seq_eq
        unfolding DeqRetInHis_def by simp
    qed
  qed
qed

lemma D3_success_preserves_lI9_D1_D2_Deq_Returned:
  fixes s s' :: SysState and p q_val :: nat and base_lin
  assumes lI9_s: "lI9_D1_D2_Deq_Returned s"
    and pc_eq: "program_counter s' = (\<lambda>x. if x = p then ''D4'' else program_counter s x)"
    and lin_s'_eq: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and his_seq_eq: "his_seq s' = his_seq s"
    and set_base_eq: "set base_lin = set (lin_seq s)"
  shows "lI9_D1_D2_Deq_Returned s'"
proof -
  have old_point:
    "\<And>q k. (program_counter s q = ''D1'' \<or> program_counter s q = ''D2'') \<Longrightarrow>
           k < length (lin_seq s) \<Longrightarrow>
           (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q) \<Longrightarrow>
           DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
    using lI9_s unfolding lI9_D1_D2_Deq_Returned_def by blast

  show ?thesis
    unfolding lI9_D1_D2_Deq_Returned_def
  proof (intro allI impI)
    fix q k
    assume q_D12: "program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2''"
       and k_bound: "k < length (lin_seq s')"
       and act_match: "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"

    show "DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
    proof (cases "q = p")
      case True
      have "program_counter s' p = ''D4''"
        using pc_eq by simp
      with q_D12 True show ?thesis
        by simp
    next
      case False
      have pc_q_old: "program_counter s q = ''D1'' \<or> program_counter s q = ''D2''"
        using q_D12 False pc_eq by simp

      have k_old: "k < length base_lin"
      proof (rule ccontr)
        assume "\<not> k < length base_lin"
        hence "k = length base_lin"
          using k_bound lin_s'_eq by auto
        hence "op_pid (lin_seq s' ! k) = p"
          using lin_s'_eq by (simp add: nth_append mk_op_def op_pid_def)
        with act_match False show False
          by simp
      qed

      have act_k: "lin_seq s' ! k \<in> set base_lin"
        using k_old lin_s'_eq by (simp add: nth_append)

      have "lin_seq s' ! k \<in> set (lin_seq s)"
        using act_k set_base_eq by blast

      then obtain k_orig where
        k_orig_bound: "k_orig < length (lin_seq s)"
        and k_orig_match: "lin_seq s ! k_orig = lin_seq s' ! k"
        by (metis in_set_conv_nth)

      have old_inv: "DeqRetInHis s q (op_val (lin_seq s ! k_orig)) (op_ssn (lin_seq s ! k_orig))"
        using old_point[OF pc_q_old k_orig_bound] k_orig_match act_match
        by metis

      thus ?thesis
        using k_orig_match his_seq_eq
        unfolding DeqRetInHis_def by simp
    qed
  qed
qed

lemma D3_success_preserves_lI10_D4_Enq_Deq_HB:
  fixes s s' :: SysState and p q_val :: nat and base_lin
  assumes INV: "system_invariant s"
    and q_in_SetB: "q_val \<in> SetB s"
    and q_not_bot: "q_val \<noteq> BOT"
    and q_val_eq: "q_val = Q_arr s (j_var s p)"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                               then modify_lin (lin_seq s) (his_seq s) q_val
                               else lin_seq s)"
    and s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and xv_s': "x_var s' = (x_var s)(p := q_val)"
    and sv_s': "s_var s' = s_var s"
    and his_eq: "his_seq s' = his_seq s"
    and pc_s': "program_counter s' = (program_counter s)(p := ''D4'')"
    and pc_s: "program_counter s p = ''D3''"
    and lI8_s:
      "\<forall>p. program_counter s p = ''D3'' \<longrightarrow>
            (\<forall>k < length (lin_seq s).
              (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = p) \<longrightarrow>
              DeqRetInHis s p (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))"
  shows "lI10_D4_Enq_Deq_HB s'"
  using modify_preserves_lI10_D4_Enq_Deq_HB[
    OF INV q_in_SetB q_not_bot q_val_eq base_def s'_lin_def
       xv_s' sv_s' his_eq pc_s' pc_s lI8_s
  ]
  by blast

lemma D3_success_preserves_lI11_D4_Deq_Unique:
  fixes s s' :: SysState and p jp q_val :: nat and base_lin
  assumes INV: "system_invariant s"
    and q_in_SetB: "q_val \<in> SetB s"
    and q_not_bot: "q_val \<noteq> BOT"
    and jp_def: "jp = j_var s p"
    and q_val_def: "q_val = Q_arr s jp"
    and val_eq: "q_val = Qback_arr s jp"
    and base_def: "base_lin = (if should_modify (lin_seq s) (his_seq s) q_val
                               then modify_lin (lin_seq s) (his_seq s) q_val
                               else lin_seq s)"
    and s'_lin_def: "lin_seq s' = base_lin @ [mk_op deq q_val p (s_var s p)]"
    and xv_s': "x_var s' = (x_var s)(p := q_val)"
    and sv_s': "s_var s' = s_var s"
    and his_eq: "his_seq s' = his_seq s"
    and pc_s': "program_counter s' = (program_counter s)(p := ''D4'')"
    and pc_s: "program_counter s p = ''D3''"
    and lI8_s:
      "\<forall>p. program_counter s p = ''D3'' \<longrightarrow>
            (\<forall>k < length (lin_seq s).
              (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = p) \<longrightarrow>
              DeqRetInHis s p (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))"
  shows "lI11_D4_Deq_Unique s'"
proof -
  have sI6_s: "sI6_D3_Scan_Pointers s"
    using INV unfolding system_invariant_def by blast

  have sI10_s: "sI10_Qback_Unique_Vals s"
    using INV unfolding system_invariant_def by blast

  have type_bt: "TypeBT s q_val"
  proof -
    have typeB_q: "TypeB s q_val"
      using q_in_SetB unfolding SetB_def by simp

    have at_idx: "AtIdx s q_val jp"
      unfolding AtIdx_def
      using val_eq by simp

    have uniq: "\<And>k. AtIdx s q_val k \<Longrightarrow> k = jp"
  using INV q_not_bot at_idx
  unfolding system_invariant_def sI10_Qback_Unique_Vals_def
  by (metis AtIdx_def)

    have idx_is_jp: "Idx s q_val = jp"
      unfolding Idx_def
      using at_idx uniq by blast

    have jp_less: "jp < l_var s p"
      using sI6_s pc_s
      unfolding sI6_D3_Scan_Pointers_def jp_def
      by blast

    have in_qb: "InQBack s q_val"
      unfolding InQBack_def
      using val_eq by blast

    have path_bot: "\<forall>k. j_var s p \<le> k \<and> k < Idx s q_val \<longrightarrow> Q_arr s k = BOT"
      using idx_is_jp jp_def by simp

have j_le_idx: "j_var s p \<le> Idx s q_val"
  using idx_is_jp jp_def by simp

have idx_less_l: "Idx s q_val < l_var s p"
  using idx_is_jp jp_less by simp

have struct_part:
  "\<exists>p'. program_counter s p' = ''D3'' \<and>
        j_var s p' \<le> Idx s q_val \<and>
        Idx s q_val < l_var s p' \<and>
        (\<forall>k. j_var s p' \<le> k \<and> k < Idx s q_val \<longrightarrow> Q_arr s k = BOT)"
proof
  show "program_counter s p = ''D3'' \<and>
        j_var s p \<le> Idx s q_val \<and>
        Idx s q_val < l_var s p \<and>
        (\<forall>k. j_var s p \<le> k \<and> k < Idx s q_val \<longrightarrow> Q_arr s k = BOT)"
    using pc_s j_le_idx idx_less_l path_bot
    by simp
qed

    show ?thesis
      unfolding TypeBT_def
      using typeB_q in_qb struct_part
      by blast
  qed

  show ?thesis
    using modify_preserves_lI11_D4_Deq_Unique[
      OF INV type_bt q_not_bot base_def s'_lin_def his_eq pc_s' pc_s xv_s' sv_s' lI8_s
    ]
    by blast
qed

end