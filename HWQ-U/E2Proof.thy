(* E2 transition rule of system-invariant preservation proof *)
theory E2Proof
  imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    E1Lemmas
    E2Lemmas
begin

(* ========================================================================= *)
(* E2 main theorem: original Proof in of prove to *)
(* ========================================================================= *)
lemma E2_preserves_invariant_core:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E2 p s s'"
  shows "system_invariant s'"
proof -
  (* ========================================================================= *)
  (* 0. definition and *)
  (* ========================================================================= *)
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def
                     x_var_def v_var_def s_var_def lin_seq_def his_seq_def

  define ip where "ip = i_var s p"
  define val where "val = v_var s p"
  define new_act where "new_act = mk_op enq val p (s_var s p)"

  (* 1. extractallold state of preconditioninvariant *)
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
   and uI1_USpec_EffOps_Lin_s: "uI1_USpec_EffOps_Lin s"
   and uI2_USpec_E1UE2_s: "uI2_USpec_E1UE2 s"
   and uI3_USpec_D3UD2_s: "uI3_USpec_D3UD2 s"
   and di_lin_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  (* 2. analyze Sys_E2, extractphysical of updatefact *)
  have step_facts [simp]:
    "program_counter s p = ''E2''"
    "program_counter s' = (program_counter s)(p := ''E3'')"
    "Q_arr s' = (Q_arr s)(i_var s p := v_var s p)"
    "Qback_arr s' = (Qback_arr s)(i_var s p := v_var s p)"
    "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
    "X_var s' = X_var s" "V_var s' = V_var s"
    "i_var s' = i_var s" "v_var s' = v_var s" "s_var s' = s_var s"
    "lin_seq s' = lin_seq s @ [new_act]"
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

    show "lin_seq s' = lin_seq s @ [new_act]"
      using STEP
      unfolding Sys_E2_def U_E2_def lin_seq_def new_act_def val_def
                v_var_def s_var_def Let_def by auto

    show "his_seq s' = his_seq s"
      using STEP unfolding Sys_E2_def his_seq_def by auto
  qed

  have u_pc_eq [simp]:
    "\<And>q. u_program_counter (snd s') q =
       (if q = p then ''UE3'' else u_program_counter (snd s) q)"
    using STEP unfolding Sys_E2_def U_E2_def by auto

  have u_his_eq [simp]: "u_his_seq (snd s') = u_his_seq (snd s)"
    using STEP unfolding Sys_E2_def U_E2_def by auto

  have u_lin_eq [simp]:
    "u_lin_seq (snd s') = u_lin_seq (snd s) @ [new_act]"
    using STEP
    unfolding Sys_E2_def U_E2_def new_act_def val_def v_var_def s_var_def
    by auto

  have u_eff_eq [simp]:
    "u_eff_ops (snd s') = insert new_act (u_eff_ops (snd s))"
    using STEP
    unfolding Sys_E2_def U_E2_def new_act_def val_def v_var_def s_var_def
    by auto

  have u_S_eq [simp]: "S_var (snd s') = S_var (snd s)"
    using STEP unfolding Sys_E2_def U_E2_def by auto

  have uspec_effOps_eq [simp]:
    "uspec_effOps s' = insert new_act (uspec_effOps s)"
    unfolding uspec_effOps_def using u_eff_eq by simp

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
  (* 3. coreset derivation (of) *)
  (* ========================================================================= *)
  (* 1. prove val is validvalue *)
  have pending_s: "HasPendingEnq s p val"
    using hI1_E_Phase_Pending_Enq_s step_facts(1) unfolding hI1_E_Phase_Pending_Enq_def val_def by blast
  have val_in_Val: "val \<in> Val"
    using pending_s hI20_Enq_Val_Valid_s unfolding HasPendingEnq_def EnqCallInHis_def hI20_Enq_Val_Valid_def val_def Let_def
    by (metis in_set_conv_nth)
  have val_not_bot: "val \<noteq> BOT"
    using val_in_Val unfolding Val_def BOT_def by simp

  (* 2. use hI14_Pending_Enq_Qback_Exclusivity and sI3_E2_Slot_Exclusive prove val definitely in old of array in *)
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
        (* : if be of is ip, be of value one is BOT *)
        hence "x = BOT"
          using sI3_E2_Slot_Exclusive_s step_facts(1) k_def ip_def unfolding sI3_E2_Slot_Exclusive_def by auto
        have "ip \<noteq> 0"
          using sI3_E2_Slot_Exclusive_s step_facts(1) ip_def unfolding sI3_E2_Slot_Exclusive_def Val_def by auto
        (* And 0 BOT, does not be *)
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
        (* Similarly of apply in Qback_arr *)
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

  have typeb_new: "\<And>x. TypeB s' x \<longleftrightarrow> TypeB s x \<or> x = val"
    unfolding TypeB_def using qhas_s' by simp

  have typea_eq: "\<And>x. TypeA s' x \<longleftrightarrow> TypeA s x"
  proof -
    fix x
    show "TypeA s' x \<longleftrightarrow> TypeA s x"
      unfolding TypeA_def
      using inqback_s'[of x] qhas_s'[of x] not_in_qback_s val_def by auto
  qed

  (* 5. out SetA and SetB of definitely *)
  have set_facts [simp]:
    "SetA s' = SetA s"
    "SetB s' = insert val (SetB s)"
  proof -
    show "SetA s' = SetA s" unfolding SetA_def using typea_eq by simp
    show "SetB s' = insert val (SetB s)"
      unfolding SetB_def using typeb_new val_in_Val by auto
  qed

  (* ========================================================================= *)
  (* 4. physical invariant preservation *)
  (* ========================================================================= *)

  have "TypeOK s'"
    using TypeOK_s pc_eqs step_facts unfolding TypeOK_def by auto

  have "sI1_Zero_Index_BOT s'"
  proof -
    (* From sI3_E2_Slot_Exclusive_s in extract out when before process p of i_var as 0 of fact *)
    have "i_var s p \<noteq> 0"
      using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def Val_def by auto

    (* Make auto unfoldpremise and conclusion in of sI1_Zero_Index_BOT_def *)
    thus ?thesis
      using sI1_Zero_Index_BOT_s step_facts(3) step_facts(4)
      by (auto simp: fun_upd_def sI1_Zero_Index_BOT_def)
  qed

  have "sI2_X_var_Upper_Bound s'"
  proof -
    (* From sI3_E2_Slot_Exclusive_s extractwhen before process p of i_var strictly less than X_var of fact *)
    have "i_var s p < X_var s"
      using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def by auto

    (* When for auto of *)
    thus ?thesis
      using sI2_X_var_Upper_Bound_s step_facts
      unfolding sI2_X_var_Upper_Bound_def
      by (auto simp: fun_upd_def)
  qed


  have "sI3_E2_Slot_Exclusive s'"
    unfolding sI3_E2_Slot_Exclusive_def
  proof (intro allI impI)
    fix p0 assume pc_p0: "program_counter s' p0 = ''E2''"

    (* 1. if p0 in s' in is E2, then it in old state s in also is E2, and is when before E2 of process p *)
    hence "program_counter s p0 = ''E2''" and "p0 \<noteq> p"
      using pc_eqs by auto

    (* 2. p0 in old of sI3_E2_Slot_Exclusive_s, extract in p0 of five can of *)
    have p0_props:
      "i_var s p0 \<in> Val \<and>
       i_var s p0 < X_var s \<and>
       Q_arr s (i_var s p0) = BOT \<and>
       Qback_arr s (i_var s p0) = BOT \<and>
       (\<forall>q. q \<noteq> p0 \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p0 \<noteq> i_var s q)"
      using sI3_E2_Slot_Exclusive_s `program_counter s p0 = ''E2''` unfolding sI3_E2_Slot_Exclusive_def by auto

    (* 3. core: usemutual exclusionprovewhen before in of slot(i_var s p)definitely is p0 of slot *)
    have "i_var s p0 \<noteq> i_var s p"
      using p0_props `p0 \<noteq> p` step_facts(1) by auto

    (* 4. "slot " of, make auto unfoldarrayupdate and direct closureall goal *)
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

    (* In E3 of process as two: enter of when before process p, with originally then in of its it process *)
    consider (is_p) "p0 = p" | (not_p) "p0 \<noteq> p" by blast
    then show "i_var s' p0 \<in> Val \<and>
               i_var s' p0 < X_var s' \<and>
               (Q_arr s' (i_var s' p0) = v_var s' p0 \<or> Q_arr s' (i_var s' p0) = BOT) \<and>
               Qback_arr s' (i_var s' p0) = v_var s' p0 \<and>
               (\<forall>q. q \<noteq> p0 \<and> program_counter s' q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' p0 \<noteq> i_var s' q)"
    proof cases
      case is_p
      (* Case 1: p0 then is p. it in old state s in E2 *)
      have p_props:
        "i_var s p \<in> Val"
        "i_var s p < X_var s"
        "(\<forall>q. q \<noteq> p \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p \<noteq> i_var s q)"
        using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def by auto

      (* P of i_var in of v_var, E3 of array *)
      show ?thesis
        using is_p p_props step_facts pc_eqs
        by (auto simp: fun_upd_def)

    next
      case not_p
      (* Case 2: p0 is its process. it in old state s in then already in E3 *)
      hence "program_counter s p0 = ''E3''" using pc_p0 pc_eqs by auto

      have p0_props:
        "i_var s p0 \<in> Val"
        "i_var s p0 < X_var s"
        "Q_arr s (i_var s p0) = v_var s p0 \<or> Q_arr s (i_var s p0) = BOT"
        "Qback_arr s (i_var s p0) = v_var s p0"
        "(\<forall>q. q \<noteq> p0 \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p0 \<noteq> i_var s q)"
        using sI4_E3_Qback_Written_s `program_counter s p0 = ''E3''` unfolding sI4_E3_Qback_Written_def by auto

      (* Core of: extract out p0 of slot and p in of slotdefinitely equal of! *)
      have "i_var s p0 \<noteq> i_var s p"
        using p0_props(5) step_facts(1) not_p by auto

      (* Has slot, arrayupdate (fun_upd) for p0 then in update, old *)
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
    (* Core: prove in D4 of process, its j_var definitelyimpossibleequal to in be in of i_var *)
    have no_conflict: "\<And>pa. program_counter s pa = ''D4'' \<Longrightarrow> j_var s pa \<noteq> i_var s p"
    proof -
      fix pa assume "program_counter s pa = ''D4''"
      (* D4 of processcorresponds to of slot, in Qback already has value (BOT) *)
      hence "Qback_arr s (j_var s pa) \<noteq> BOT"
        using sI7_D4_Deq_Result_s unfolding sI7_D4_Deq_Result_def by auto
      (* And E2 process in of slot, in Qback is empty of (BOT) *)
      moreover have "Qback_arr s (i_var s p) = BOT"
        using sI3_E2_Slot_Exclusive_s step_facts(1) unfolding sI3_E2_Slot_Exclusive_def by auto
      ultimately show "j_var s pa \<noteq> i_var s p" by metis
    qed

    (* Slotdefinitely equal of, make auto close the goal directlyarray *)
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

    (* 1. in value as BOT of fact(it valid of Val set) *)
    have pending: "HasPendingEnq s p (v_var s p)"
      using hI1_E_Phase_Pending_Enq_s step_facts(1) unfolding hI1_E_Phase_Pending_Enq_def by auto
    have "v_var s p \<in> Val"
      using pending hI20_Enq_Val_Valid_s unfolding HasPendingEnq_def EnqCallInHis_def hI20_Enq_Val_Valid_def Let_def
      by (metis in_set_conv_nth)
    hence val_not_bot: "v_var s p \<noteq> BOT" unfolding Val_def BOT_def by auto

    (* 2. slot: because ip be in BOT value, and k as BOT, therefore k definitely is ip *)
    have k_neq_ip: "k \<noteq> i_var s p"
    proof
      assume "k = i_var s p"
      hence "Q_arr s' k = v_var s p" using step_facts(3) by (simp add: fun_upd_def)
      with cond1 val_not_bot show False by simp
    qed

    (* 3. process: q of i_var is k, and p of i_var is ip, therefore q definitely is p *)
    have q_neq_p: "q \<noteq> p"
    proof
      assume "q = p"
      hence "i_var s' q = i_var s p" using step_facts by simp
      with cond2 k_neq_ip show False by simp
    qed

    (* 4. since q \<noteq> p and k \<noteq> ip, array and process precise old state *)
    have "program_counter s q \<in> {''E3''}" "i_var s q = k"
      using cond2 q_neq_p pc_eqs step_facts by auto
    moreover have "Q_arr s k = BOT" "Qback_arr s k \<noteq> BOT"
      using cond1 k_neq_ip step_facts(3) step_facts(4) by (auto simp: fun_upd_def)

    (* 5. old state of sI9_Qback_Discrepancy_E3_s close the goal directly *)
    ultimately have "v_var s q = Qback_arr s k"
      using sI9_Qback_Discrepancy_E3_s unfolding sI9_Qback_Discrepancy_E3_def by blast

    thus "v_var s' q = Qback_arr s' k"
      using q_neq_p k_neq_ip step_facts by (simp add: fun_upd_def)
  qed

  have "sI10_Qback_Unique_Vals s'"
  proof -
    (* From we in Step 3 already of in extract: val definitely in old of Qback_arr in *)
    have val_is_new: "\<forall>k. Qback_arr s k \<noteq> v_var s p"
      using not_in_qback_s unfolding InQBack_def val_def by auto

    (* "newvaluedefinitely and old value " of, make auto unfoldarrayupdate *)
    thus ?thesis
      using sI10_Qback_Unique_Vals_s step_facts(4)
      unfolding sI10_Qback_Unique_Vals_def
      by (auto simp: fun_upd_def)
  qed

  have "hI2_SSN_Bounds s'"
  proof -
    (* 1. from pc_eqs in extract L0 of fact *)
    have pc_L0: "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
      using pc_eqs by simp

    (* 2. old invariant, physical fact and PC prove *)
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

    (* 1. q in old state s in of:
          If q = p, then it in old state is E2; if q \<noteq> p, then it.
          No case, it in old state also in {E1, E2, E3} set *)
    have old_pc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using pc_q pc_eqs step_facts(1) by auto

    (* 2. useold state of hI1_E_Phase_Pending_Enq extract q of Pending *)
    have "HasPendingEnq s q (v_var s q)"
      using hI1_E_Phase_Pending_Enq_s old_pc unfolding hI1_E_Phase_Pending_Enq_def by blast

    (* 3. because s_var, his_seq and v_var all has change, therefore Pending in s' in precisepreserve *)
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

    (* 1. extract *)
    have pc_s: "program_counter s pa = ''D3'' " using pa_pc pc_eqs by auto
    have j_s: "j_var s' pa = j_var s pa" using step_facts by auto

    show "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
    proof (cases "k = i_var s p")
      case True
      (* --- branch A: in --- *)
      (* Physicalfact: Q_arr s' k in newvalue v_var s p *)
      have val_new: "Q_arr s' k = v_var s p"
        using True step_facts by simp

      (* Derivation: provenew in of value still is TypeB *)
      have "TypeB s' (v_var s p)"
      proof -
        (* 1. prove this value already in array Q_arr in (because Q_arr s' k = v_var s p) *)
        have "QHas s' (v_var s p)"
          unfolding QHas_def
          using True val_new by blast

        (* 2. TypeB of definition, only QHas, this value then is TypeB *)
        thus ?thesis
          unfolding TypeB_def by blast
      qed
      thus ?thesis using val_new by simp

    next
      case False
      (* --- branch B: in --- *)
      (* Physicalvalue *)
      have q_stable: "Q_arr s' k = Q_arr s k"
        using False step_facts by auto

      (* From old state sI12_D3_Scanned_Prefix *)
      have "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
        using sI12_D3_Scanned_Prefix_s pc_s k_lt j_s unfolding sI12_D3_Scanned_Prefix_def
        by simp

      (* Use the of typeb_eq (because k \<noteq> i_var, and p E2, its TypeB into preserve) *)
      thus ?thesis using q_stable typeb_new by auto
    qed
  qed

(* ========================================================================= *)
  (* Prove hI4_X_var_Lin_Sync: physical and mappingconsistency (E2 state transition) *)
  (* ========================================================================= *)
  have "hI4_X_var_Lin_Sync s'"
  proof -
    let ?new_slots = "{i. i < X_var s' \<and>
        (\<exists>q. program_counter s' q = ''E2'' \<and> i_var s' q = i)}"
    let ?old_slots = "{i. i < X_var s \<and>
        (\<exists>q. program_counter s q = ''E2'' \<and> i_var s q = i)}"

    have slot_set: "?old_slots = insert ip ?new_slots"
    proof (rule set_eqI)
      fix i
      show "i \<in> ?old_slots \<longleftrightarrow> i \<in> insert ip ?new_slots"
      proof
        assume old: "i \<in> ?old_slots"
        then obtain q where q_pc: "program_counter s q = ''E2''"
          and q_i: "i_var s q = i" and i_bound: "i < X_var s"
          by auto
        show "i \<in> insert ip ?new_slots"
        proof (cases "q = p")
          case True
          then show ?thesis using q_i unfolding ip_def by simp
        next
          case False
          then have "program_counter s' q = ''E2''"
            using q_pc pc_eqs by simp
          then show ?thesis
            using q_i i_bound False step_facts by auto
        qed
      next
        assume new: "i \<in> insert ip ?new_slots"
        show "i \<in> ?old_slots"
        proof (cases "i = ip")
          case True
          have ip_bound: "ip < X_var s"
            using sI3_E2_Slot_Exclusive_s step_facts(1)
            unfolding sI3_E2_Slot_Exclusive_def ip_def by blast
          have witness: "\<exists>q. program_counter s q = ''E2'' \<and> i_var s q = ip"
            using step_facts(1) unfolding ip_def by blast
          show ?thesis using True ip_bound witness by simp
        next
          case False
          from new False obtain q where q_pc: "program_counter s' q = ''E2''"
            and q_i: "i_var s' q = i" and i_bound: "i < X_var s'"
            by auto
          have q_ne_p: "q \<noteq> p" using q_pc step_facts by auto
          then have "program_counter s q = ''E2''" using q_pc pc_eqs by simp
          then show ?thesis using q_i i_bound step_facts by auto
        qed
      qed
    qed

    have finite_new: "finite ?new_slots"
      by (rule finite_subset[of _ "{..<X_var s'}"]) auto

    have fresh: "ip \<notin> ?new_slots"
    proof
      assume "ip \<in> ?new_slots"
      then obtain q where q_pc: "program_counter s' q = ''E2''"
        and q_i: "i_var s' q = ip" by auto
      have q_ne_p: "q \<noteq> p" using q_pc step_facts by auto
      have q_old: "program_counter s q = ''E2''" using q_pc q_ne_p pc_eqs by simp
      have distinct: "i_var s p \<noteq> i_var s q"
        using sI3_E2_Slot_Exclusive_s step_facts(1) q_old q_ne_p
        unfolding sI3_E2_Slot_Exclusive_def by blast
      show False using distinct q_i step_facts unfolding ip_def by simp
    qed

    have slot_count: "E2SlotCount s = Suc (E2SlotCount s')"
      unfolding E2SlotCount_def using slot_set finite_new fresh by simp

    show ?thesis
      using hI4_X_var_Lin_Sync_s slot_count step_facts
      unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def new_act_def
      by (simp add: mk_op_def op_name_def)
  qed

  (* ========================================================================= *)
  (* 5. history and invariantpreserve (hI, linI) *)
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

  (* --- prove hI10_Enq_Call_Existence in E2 preserve --- *)
  have "hI10_Enq_Call_Existence s'"
    unfolding hI10_Enq_Call_Existence_def
  proof (intro conjI)
    (* Part 1: prove PC in E1-E3 of historyconsistency *)
    (* One in hI1_E_Phase_Pending_Enq s', use already conclusion *)
    show "\<forall>p a. program_counter s' p \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' p = a \<longrightarrow>
                EnqCallInHis s' p a (s_var s' p)"
      using `hI1_E_Phase_Pending_Enq s'` unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def
      by metis

  next
    (* Part 2: prove Qback array in of value in history in (use helper lemma) *)
    show "\<forall>a. a \<in> Val \<and> (\<exists>k. Qback_arr s' k = a) \<longrightarrow>
              (\<exists>q. Ex (EnqCallInHis s' q a))"
    proof (intro allI impI)
      fix a
      assume PRE: "a \<in> Val \<and> (\<exists>k. Qback_arr s' k = a)"
      then have A_VAL: "a \<in> Val" and EX: "\<exists>k. Qback_arr s' k = a"
        by blast+

      (* Use helper lemma hI10_Enq_Call_Existence_E2_step *)
      (* Note: Isabelle \<exists>sn. P sn and Ex P of *)
      show "\<exists>q. Ex (EnqCallInHis s' q a)"
        using hI10_Enq_Call_Existence_E2_step[OF INV STEP A_VAL EX]
        by auto
    qed
  qed

  (* --- prove hI11_Enq_Ret_Existence in E2 preserve --- *)
  have "hI11_Enq_Ret_Existence s'"
    by (rule hI11_Enq_Ret_Existence_E2_step [OF INV STEP])

(* 1. prove HasPendingDeq in one physical in is of *)
  have hpd_eq: "\<And>pa. HasPendingDeq s' pa = HasPendingDeq s pa"
  proof -
    fix pa
    (* From STEP extract his_seq equal of fact, outside *)
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
    (* Process pa in new state in D1-D4 *)
    assume "program_counter s' pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"

    (* Use the definition of pc_eqs, derivation out pa in old state also in D1-D4 *)
    hence pc_old: "program_counter s pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using pc_eqs by auto

    (* Old invariant hI12_D_Phase_Pending_Deq_s and hpd_eq *)
    from hI12_D_Phase_Pending_Deq_s pc_old hpd_eq show "HasPendingDeq s' pa"
      unfolding hI12_D_Phase_Pending_Deq_def by auto
  qed

  have "hI13_Qback_Deq_Sync s'"
  proof (unfold hI13_Qback_Deq_Sync_def, intro allI impI)
    fix a
    assume a_nz: "a \<noteq> BOT"
    assume gap_new: "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a"

    (* 1. extract the old state of invariant and physical fact *)
    from INV have hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s" unfolding system_invariant_def by auto
    from gap_new obtain k where k_gap: "Q_arr s' k = BOT" "Qback_arr s' k = a" by blast

    (* 2. core: k impossible is when before of in i_var s p *)
    have k_not_p: "k \<noteq> i_var s p"
    proof
      assume "k = i_var s p"
      (* In E2, in be v_var s p, sI3_E2_Slot_Exclusive2 property, v_var necessarily BOT *)
      (* If the of in v_var s p necessarily in Val and Val BOT *)
      hence "Q_arr s' k = v_var s p" using step_facts by simp
      with k_gap(1) have "v_var s p = BOT" by simp
      (* Use process nonempty of property, is sI11_x_var_Scope or *)
      moreover from INV have "v_var s p \<noteq> BOT"
        unfolding system_invariant_def hI20_Enq_Val_Valid_def (* HI20_Enq_Val_Valid enqueuevalue BOT *)
        using step_facts
        using val_def val_not_bot by blast
      ultimately show False by contradiction
    qed

    (* 3. since k, note empty in old state s in then already in *)
    hence gap_old: "Q_arr s k = BOT \<and> Qback_arr s k = a"
      using k_gap step_facts by auto

    (* 4. useold state of hI13_Qback_Deq_Sync_s obtainconclusion *)
    with hI13_Qback_Deq_Sync_s a_nz have "\<exists>p. (program_counter s p = ''D4'' \<and> x_var s p = a) \<or> (\<exists>sn. DeqRetInHis s p a sn)"
      unfolding hI13_Qback_Deq_Sync_def by blast

    (* 5. prove this conclusion in s' into (prove) *)
    thus "\<exists>p. (program_counter s' p = ''D4'' \<and> x_var s' p = a) \<or> (\<exists>sn. DeqRetInHis s' p a sn)"
    proof (elim exE disjE, goal_cases)
      case (1 pa) (* In D4 of processcase *)
      (* Pa is when before of process p, because p in E2 *)
      hence "pa \<noteq> p" using step_facts(1) by auto
      hence "program_counter s' pa = ''D4'' " "x_var s' pa = a"
        using 1 step_facts by auto
      thus ?case by blast
    next
      case (2 pa sn) (* Already return of historyrecordcase *)
      hence "DeqRetInHis s' pa a sn"
        using step_facts(12) unfolding DeqRetInHis_def by simp
      thus ?case by blast
    qed
  qed

(* --- prove hI14_Pending_Enq_Qback_Exclusivity in E2 preserve --- *)
  have "hI14_Pending_Enq_Qback_Exclusivity s'"
    by (rule hI14_Pending_Enq_Qback_Exclusivity_E2_step [OF INV STEP])

(* --- prove hI15_Deq_Result_Exclusivity in E2 preserve --- *)
  have "hI15_Deq_Result_Exclusivity s'"
    by (rule hI15_Deq_Result_Exclusivity_E2_step [OF INV STEP])

(* HI16_BO_BT_No_HB, hI17_BT_BT_No_HB, hI18_Idx_Order_No_Rev_HB, hI19_Scanner_Catches_Later_Enq: E2 of, SetBT of (simplification step) *)
  have "hI16_BO_BT_No_HB s'" using hI16_BO_BT_No_HB_E2_step[OF INV STEP] .

  have "hI17_BT_BT_No_HB s'" using hI17_BT_BT_No_HB_E2_step[OF INV STEP] .

  have "hI18_Idx_Order_No_Rev_HB s'" using hI18_Idx_Order_No_Rev_HB_E2_step[OF INV STEP] .

  have "hI19_Scanner_Catches_Later_Enq s'" using hI19_Scanner_Catches_Later_Enq_E2_step[OF INV STEP] .

  have "hI20_Enq_Val_Valid s'"
    using hI20_Enq_Val_Valid_s step_facts unfolding hI20_Enq_Val_Valid_def by simp

  have "hI21_Ret_Implies_Call s'"
  proof -
    (* : history no *)
    have seq_eq: "his_seq s' = his_seq s" using step_facts(1) by simp

    (* Auto and its if, match of *)
    show ?thesis
      using hI21_Ret_Implies_Call_s seq_eq
      unfolding hI21_Ret_Implies_Call_def
      by (auto split: if_splits)
  qed

(* ========================================================================= *)
  (* Prove hI22_Deq_Local_Pattern: dequeuelocalhistory (E2 only in newvalue, BOT empty, precise) *)
  (* ========================================================================= *)
  have "hI22_Deq_Local_Pattern s'"
    unfolding hI22_Deq_Local_Pattern_def
  proof (intro allI impI, goal_cases)
    case (1 p_deq a sn)
    (* 1. extractallprecondition *)
    then obtain k where k_props:
      "Q_arr s' k = BOT"
      "Qback_arr s' k = a"
      "\<forall>q. x_var s' q \<noteq> a"
      "DeqRetInHis s' p_deq a sn"
      by blast

    (* 2. guards: extract the old state of hI22_Deq_Local_Pattern *)
    have hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s" using INV unfolding system_invariant_def by blast

    (* 3. logical contradiction step: prove premise of slot k definitelyimpossible is p in of slot *)
    have "k \<noteq> i_var s p"
    proof
      assume "k = i_var s p"
      (* E2 in i_var s p in of is v_var s p *)
      hence "Q_arr s' k = v_var s p" using step_facts(8) by simp
      with k_props(1) have "v_var s p = BOT" by simp
      (* But we before already prove, enqueue of newvaluedefinitely is BOT (val_not_bot)!contradiction! *)
      with val_not_bot show False
        by (simp add: val_def)
    qed

    (* 4. precisemapping old state *)
    hence old_Q: "Q_arr s k = BOT" and old_Qback: "Qback_arr s k = a"
      using k_props(1,2) step_facts(8,9) by auto

    have old_x: "\<forall>q. x_var s q \<noteq> a"
      using k_props(3) step_facts(2) by auto

    have old_his: "DeqRetInHis s p_deq a sn"
      using k_props(4) step_facts(1) unfolding DeqRetInHis_def Let_def by auto

    (* 5. old premise, old guards *)
    have old_antecedent: "((\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a \<and> (\<forall>q. x_var s q \<noteq> a)) \<and> DeqRetInHis s p_deq a sn)"
      using old_Q old_Qback old_x old_his by blast

    from hI22_Deq_Local_Pattern_s[unfolded hI22_Deq_Local_Pattern_def, rule_format, OF old_antecedent]
    have old_consequent: "let p_his = filter (\<lambda>e. act_pid e = p_deq) (his_seq s) in
      \<exists>i < length p_his.
          p_his ! i = mk_act deq a p_deq sn ret \<and>
         (i > 0 \<and> p_his ! (i - 1) = mk_act deq BOT p_deq sn call)" .

    (* 6. becausehistory, conclusion translate new state *)
    thus ?case using step_facts(1) by simp
  qed

  have "hI23_Deq_Call_Ret_Balanced s'"
    using hI23_Deq_Call_Ret_Balanced_s step_facts unfolding hI23_Deq_Call_Ret_Balanced_def by simp

  have "hI24_HB_Implies_Idx_Order s'"
    by (rule hI24_HB_Implies_Idx_Order_E2_step [OF INV STEP])

  have "hI25_Enq_Call_Ret_Balanced s'"
  proof -
    (* Proof step: prove for in {E1, E2, E3} set, all processes of PC into is complete of *)
    have pc_stable: "\<And>q. (program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) = (program_counter s q \<in> {''E1'', ''E2'', ''E3''})"
    proof -
      fix q
      show "(program_counter s' q \<in> {''E1'', ''E2'', ''E3''}) = (program_counter s q \<in> {''E1'', ''E2'', ''E3''})"
      proof (cases "q = p")
        case True
        (* For in when before process p, from E2 to E3, but it still in large set inside *)
        hence "program_counter s' q = ''E3''" using pc_eqs by simp
        moreover have "program_counter s q = ''E2''"
          by (simp add: True)
        ultimately show ?thesis by simp
      next
        case False
        (* For in its process, PC, *)
        thus ?thesis using pc_eqs by simp
      qed
    qed

    (* Sincehistory (step_facts(1)), PC in set in of also (pc_stable), hI25_Enq_Call_Ret_Balanced translate into *)
    show ?thesis
      using hI25_Enq_Call_Ret_Balanced_s step_facts(1) pc_stable
      unfolding hI25_Enq_Call_Ret_Balanced_def
      by simp
  qed

  (* ========================================================================= *)
  (* Prove hI26_DeqRet_D4_Mutex: dequeuereturn of mutual exclusion (E2 changehistory and dequeue, precise) *)
  (* ========================================================================= *)
  have "hI26_DeqRet_D4_Mutex s'"
    unfolding hI26_DeqRet_D4_Mutex_def
  proof (intro allI impI, goal_cases)
    case (1 q a)
    (* At this point 1(1): a \<in> Val *)
    show ?case
    proof (rule notI)
      (* Contradiction: has ret, in D4 value *)
      assume bad: "(\<exists>sn. DeqRetInHis s' q a sn) \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a"
      then obtain sn where ret_s': "DeqRetInHis s' q a sn"
                       and pc_q_s': "program_counter s' q = ''D4''"
                       and x_q_s': "x_var s' q = a" by blast

      have hI26_DeqRet_D4_Mutex_s: "hI26_DeqRet_D4_Mutex s" using INV unfolding system_invariant_def by blast

      show False
      proof (cases "q = p", goal_cases)
        case 1
        (* Logical contradiction step 1: q then is when before process p. but p to E3, this impossibleequal to D4! *)
        have "program_counter s' p = ''E3''" using pc_eqs by simp
        with pc_q_s' 1 show False by simp
      next
        case 2
        (* Logical contradiction step 2: q is its process. E2 for q of has and history into *)
        have "program_counter s q = ''D4''" using pc_q_s' 2 pc_eqs by simp

        (* X_var in E2 global (step_facts x_var s' = x_var s) *)
        have "x_var s q = a" using x_q_s' step_facts by simp

        (* His_seq in E2 global, mapping old state of DeqRet fact *)
        have "DeqRetInHis s q a sn"
          using ret_s' step_facts unfolding DeqRetInHis_def Let_def by simp

        (* Old stateguards, contradiction *)
        from hI26_DeqRet_D4_Mutex_s 1(1) `program_counter s q = ''D4''` `x_var s q = a` `DeqRetInHis s q a sn`
        show False unfolding hI26_DeqRet_D4_Mutex_def by blast
      qed
    qed
  qed

(* ========================================================================= *)
  (* Extractglobal physical fact: E2 state transition of this mapping *)
  (* ========================================================================= *)

  (* A. PC fact *)
  have pc_p_E2: "program_counter s p = ''E2'' "
    using STEP unfolding Sys_E2_def C_E2_def by (simp add: program_counter_def)

  (* B. TypeB of new old (provenew state of has value is enqueue of, is old state then has of) *)
  have typeb_cases: "\<And>x. TypeB s' x \<Longrightarrow> x = v_var s p \<or> TypeB s x"
  proof -
    fix x assume typeb_s': "TypeB s' x"
    then obtain k where q_at_k: "Q_arr s' k = x"
      unfolding TypeB_def QHas_def by blast
    show "x = v_var s p \<or> TypeB s x"
      using q_at_k step_facts pc_p_E2
      unfolding TypeB_def QHas_def by (cases "k = i_var s p") auto
  qed
  (* C. physical (proveoldelement in queue in of physical idx in E2 in definitely) *)
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
  (* Prove hI19: start and PC of (E2 state transition) *)
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
  (* Prove hI20: enqueuevalue of definitelynew (E2 state transition) *)
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
  (* Prove hI21: E2 phase of scan guards (useno ret simplification step) *)
  (* ========================================================================= *)
  have "hI29_E2_Scanner_Immunity s'"
    unfolding hI29_E2_Scanner_Immunity_def
  proof (intro allI impI, goal_cases)
    case (1 p_enq a q)
    show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
    proof
      assume hb: "HB_EnqRetCall s' a (v_var s' p_enq)"
      (* Extract a \<in> Val *)
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
        (* Logical contradiction step: a is newelement, necessarily has ret record, and HB contradiction! *)
        have "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = v_var s p \<and> act_cr (his_seq s ! k_ret) = ret"
          using hb_s True unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def mk_op_def op_name_def op_val_def by force

        (* Key correction: explicitly constructset into prove, OF of match *)
        have pc_p_active: "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" using pc_p_E2 by simp
        moreover have "\<not> (\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_enq_val_has_no_ret[OF INV pc_p_active] by simp

        ultimately show False
          by (simp add:
              \<open>\<exists>k_ret<length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and> act_val (his_seq s ! k_ret) = Model.v_var s p \<and> act_cr (his_seq s ! k_ret) = ret\<close>)
      next
        case False
        (* A is oldelement, precise old state hI21 guards *)
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
    (* HI22: physical of definitelyorder preservation (E2 state transition - newversionsimplified definition) *)
    (* : newoldelement, use"enqueue in no Ret" final step *)
    (* ========================================================================= *)
    have "hI30_Ticket_HB_Immunity s'"
    proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI, goal_cases)
      case (1 b q)

      (* 1. extractgoal in of 5 coreprecondition (precise versiondefinition) *)
      from 1 have pc_q': "program_counter s' q \<in> {''E2'', ''E3''}" by blast
      from 1 have inqb': "InQBack s' b" by blast
      from 1 have b_not_bot': "b \<noteq> BOT" by blast
      from 1 have b_neq_v': "b \<noteq> v_var s' q" by blast
      from 1 have hb': "HB_EnqRetCall s' b (v_var s' q)" by blast

      (* 2. basic translate (E2 history definitely, onlyupdatephysicalarrayslot) *)
      have inv_hI22: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast

      have his_eq: "his_seq s' = his_seq s" using step_facts by simp
      have v_var_eq_all: "v_var s' = v_var s" using step_facts by auto
      have i_var_eq_all: "i_var s' = i_var s" using step_facts by auto

      (* Process p of when before *)
      have pc_p_s: "program_counter s p = ''E2''" using step_facts pc_eqs by auto

      (* Q is as p *)
      have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}"
      proof (cases "q = p")
        case True thus ?thesis using pc_p_s by simp
      next
        case False thus ?thesis using pc_q' step_facts pc_eqs by auto
      qed

      (* History, HB precisetranslate *)
      have hb_s: "HB_EnqRetCall s b (v_var s q)"
        using hb' his_eq v_var_eq_all
        unfolding HB_EnqRetCall_def HB_Act_def HB_def match_ret_def match_call_def Let_def mk_op_def op_name_def op_val_def
        by simp

      (* 3. core: b to is old element, is p insert of newelement? *)
      show "Idx s' b < i_var s' q"
      proof (cases "b = v_var s p")
        case True
        (* ==================================================================== *)
        (* Contradiction: if b is p in enqueue of newelement, it definitelyimpossible has returnrecord! *)
        (* ==================================================================== *)

        (* A.: in E2 of p, its v_var has Ret record *)
        have pc_p_E123: "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" using pc_p_s by simp
        have no_ret: "\<not> (\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v_var s p \<and> act_cr (his_seq s ! k) = ret)"
          using pending_enq_val_has_no_ret[OF INV pc_p_E123] by simp

        (* B. from HB in out b of returnrecord *)
        (* HB_EnqRetCall b has Ret, use match_ret_def unfold *)
        have "\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = b \<and> act_cr (his_seq s ! k) = ret"
          using hb_s unfolding HB_EnqRetCall_def HB_Act_def HB_def match_ret_def match_call_def Let_def mk_op_def op_name_def op_val_def
          by auto

        (* C. for: b then is v_var s p, A and B physicalcontradiction *)
        with no_ret True show ?thesis
          by auto

      next
        case False
        (* ==================================================================== *)
        (* Translate: b is already in queue in of oldelement, old stateguards *)
        (* ==================================================================== *)

        (* Since b \<noteq> v_var s p, and v_var has Freshness(newelement old slot),
           B of physical Idx in E2 of value after preserve. *)
        have idx_eq: "Idx s' b = Idx s b"
          using False step_facts
          unfolding Idx_def AtIdx_def
          by (metis sI3_E2_Slot_Exclusive_def sI3_E2_Slot_Exclusive_s b_not_bot' fun_upd_def)

        have inqb_s: "InQBack s b"
          using inqb' False step_facts unfolding InQBack_def by auto

        have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_var_eq_all by simp

        (* Version old guards, in 5! *)
        have "Idx s b < i_var s q"
          using inv_hI22 pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
          unfolding hI30_Ticket_HB_Immunity_def by blast

        (* Conclusiontranslate new state, close immediately *)
        thus ?thesis using idx_eq i_var_eq_all by simp
      qed
    qed

  (* ========================================================================= *)
  (* 6. invariantpreserve () *)
  (* Because lin_seq/his_seq/SetA/SetB complete equal, complete! *)
  (* ========================================================================= *)

  have lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    using step_facts by simp
  have his_eq [simp]: "his_seq s' = his_seq s"
    using step_facts by simp
  have call_p: "EnqCallInHis s p val (s_var s p)"
    using pending_s unfolding HasPendingEnq_def by metis
  have typeB_val: "TypeB s' val"
    using typeb_new by simp

  have OPLin_new: "OPLin s' = insert new_act (OPLin s)"
    unfolding OPLin_def lin_eq by simp
  have OP_A_enq_eq: "OP_A_enq s' = OP_A_enq s"
    using set_facts his_eq unfolding OP_A_enq_def EnqCallInHis_def by auto
  have OP_A_deq_eq: "OP_A_deq s' = OP_A_deq s"
    using set_facts his_eq lin_eq
    unfolding OP_A_deq_def OPLin_def DeqCallInHis_def
              new_act_def mk_op_def op_name_def by auto
  have OP_B_enq_new: "OP_B_enq s' = insert new_act (OP_B_enq s)"
    using E1_op_b_enq_new[OF his_eq set_facts(2) hI8_Val_Unique_s
          call_p val_in_Val typeB_val new_act_def] .

  have "lI1_Op_Sets_Equivalence s'"
    using lI1_Op_Sets_Equivalence_s OPLin_new OP_A_enq_eq
          OP_A_deq_eq OP_B_enq_new
    unfolding lI1_Op_Sets_Equivalence_def by blast

  have lI2_Op_Cardinality_s': "lI2_Op_Cardinality s'"
    using E1_op_cardinality[OF INV set_facts(1) set_facts(2) typeB_val
          val_in_Val not_in_qback_s sI8_Q_Qback_Sync_s
          sI1_Zero_Index_BOT_s lI1_Op_Sets_Equivalence_s
          lI4_FIFO_Semantics_s di_lin_s lin_eq new_act_def] .

  have "lI3_HB_Ret_Lin_Sync s'"
    using E1_hb_ret_lin_sync[OF INV his_eq his_eq lin_eq pending_s new_act_def] .

  have "lI4_FIFO_Semantics s'"
    using E1_fifo_semantics[OF INV lin_eq new_act_def] .

  have "lI5_SA_Prefix s'"
    using E1_sa_prefix[OF INV lin_eq new_act_def typeB_val val_in_Val
          lI2_Op_Cardinality_s' \<open>lI1_Op_Sets_Equivalence s'\<close>
          lI1_Op_Sets_Equivalence_s lI2_Op_Cardinality_s
          set_facts(1) not_in_qback_s] .

  have "lI6_D4_Deq_Linearized s'"
    using lI6_D4_Deq_Linearized_s pc_eqs step_facts
    unfolding lI6_D4_Deq_Linearized_def new_act_def mk_op_def op_name_def
    by auto

  have "lI7_D4_Deq_Deq_HB s'"
    using E1_d4_deq_deq_hb[OF INV step_facts(1) step_facts(2)
          step_facts(5) step_facts(12) step_facts(14)
          his_eq lin_eq new_act_def] .

  have "lI8_D3_Deq_Returned s'"
    using lI8_D3_Deq_Returned_s pc_eqs step_facts
    unfolding lI8_D3_Deq_Returned_def DeqRetInHis_def
              new_act_def mk_op_def op_name_def op_pid_def
    by (auto simp: nth_append)

  have "lI9_D1_D2_Deq_Returned s'"
    using lI9_D1_D2_Deq_Returned_s pc_eqs step_facts
    unfolding lI9_D1_D2_Deq_Returned_def DeqRetInHis_def
              new_act_def mk_op_def op_name_def op_pid_def
    by (auto simp: nth_append)

  have "lI10_D4_Enq_Deq_HB s'"
    using E1_d4_enq_deq_hb[OF INV step_facts(1) step_facts(2)
          step_facts(5) step_facts(12) step_facts(14)
          his_eq lin_eq pending_s new_act_def] .

  have "lI11_D4_Deq_Unique s'"
    using E1_d4_deq_unique[OF INV step_facts(1) step_facts(2)
          step_facts(5) step_facts(12) step_facts(14)
          his_eq lin_eq new_act_def] .

  have "data_independent (lin_seq s')"
    using E1_data_independent[OF not_in_qback_s sI8_Q_Qback_Sync_s
          sI1_Zero_Index_BOT_s lI1_Op_Sets_Equivalence_s
          di_lin_s]
    unfolding lin_eq new_act_def by simp

  (* ========================================================================= *)
  (* 6b. USpec invariants uI1-uI3                                                *)
  (* ========================================================================= *)

  have uI1_USpec_EffOps_Lin_s': "uI1_USpec_EffOps_Lin s'"
    using uI1_USpec_EffOps_Lin_s uspec_effOps_eq lin_eq
    unfolding uI1_USpec_EffOps_Lin_def by simp

  have uI2_USpec_E1UE2_s': "uI2_USpec_E1UE2 s'"
  proof (unfold uI2_USpec_E1UE2_def, intro allI impI)
    fix q
    assume pc_q': "program_counter s' q \<in> {''E1'', ''E2''}"
    assume upc_q': "u_program_counter (snd s') q = ''UE2''"

    let ?op = "mk_op enq (v_var s' q) q (s_var s' q)"
    let ?L = "lin_seq s'"
    let ?H = "his_seq s'"

    have pending_q: "HasPendingEnq s' q (v_var s' q)"
      using \<open>hI1_E_Phase_Pending_Enq s'\<close> pc_q'
      unfolding hI1_E_Phase_Pending_Enq_def by blast
    have val_q: "v_var s' q \<in> Val"
      using pending_q \<open>hI20_Enq_Val_Valid s'\<close>
      unfolding HasPendingEnq_def EnqCallInHis_def
                hI20_Enq_Val_Valid_def Let_def
      by (metis in_set_conv_nth)
    have val_q_not_bot: "v_var s' q \<noteq> BOT"
      using val_q unfolding Val_def BOT_def by simp

    have not_in_qback_q: "\<not> InQBack s' (v_var s' q)"
    proof (cases "program_counter s' q = ''E1''")
      case True
      then show ?thesis
        using \<open>hI14_Pending_Enq_Qback_Exclusivity s'\<close> pending_q
        unfolding hI14_Pending_Enq_Qback_Exclusivity_def InQBack_def
        by blast
    next
      case False
      then have q_E2: "program_counter s' q = ''E2''" using pc_q' by auto
      have no_other:
        "\<not> (\<exists>k. Qback_arr s' k = v_var s' q \<and> k \<noteq> i_var s' q)"
        using \<open>hI14_Pending_Enq_Qback_Exclusivity s'\<close> pending_q q_E2
        unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
      have own_bot: "Qback_arr s' (i_var s' q) = BOT"
        using \<open>sI3_E2_Slot_Exclusive s'\<close> q_E2
        unfolding sI3_E2_Slot_Exclusive_def by blast
      show ?thesis
        using no_other own_bot val_q_not_bot unfolding InQBack_def by metis
    qed

    have di_candidate: "data_independent (?L @ [?op])"
      using E1_data_independent[OF not_in_qback_q
            \<open>sI8_Q_Qback_Sync s'\<close> \<open>sI1_Zero_Index_BOT s'\<close>
            \<open>lI1_Op_Sets_Equivalence s'\<close>
            \<open>data_independent (lin_seq s')\<close>, of q]
      by simp

    have called_op: "OpCalledInHis ?H ?op"
    proof -
      have call: "EnqCallInHis s' q (v_var s' q) (s_var s' q)"
        using pending_q unfolding HasPendingEnq_def by metis
      show ?thesis using EnqCallInHis_imp_OpCalledInHis[OF call] by simp
    qed
    have called_lin: "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
      using all_lin_called_from_lI1[OF \<open>lI1_Op_Sets_Equivalence s'\<close>] .

    have no_ret: "\<forall>k<length ?H. \<not> match_ret ?H k ?op"
      using pending_q
      unfolding HasPendingEnq_def EnqRetInHis_def match_ret_def Let_def
                mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
      by auto
    have no_HB_from: "\<And>x. \<not> HB ?H ?op x"
      using no_ret unfolding HB_def by (metis match_ret_def)

    have hb_lin: "HB_consistent ?L ?H"
      using \<open>lI3_HB_Ret_Lin_Sync s'\<close>
      unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def HB_consistent_def
      by blast
    have hb_candidate: "HB_consistent (?L @ [?op]) ?H"
      by (rule HB_consistent_append[OF hb_lin])
         (use no_HB_from in blast)+

    have queue_before: "QueueSpecLin ?L"
      using \<open>lI4_FIFO_Semantics s'\<close>
      unfolding QueueSpecLin_def lI4_FIFO_Semantics_def by simp
    have queue_candidate: "QueueSpecLin (?L @ [?op])"
      using E1_QueueSpecLin_append_enq[OF queue_before,
            of "v_var s' q" q "s_var s' q"]
      by simp

    have eff_eq: "uspec_effOps s' = set ?L"
      using uI1_USpec_EffOps_Lin_s'
      unfolding uI1_USpec_EffOps_Lin_def by simp

    have gen_concrete:
      "USpec_GenLin ?H (uspec_effOps s') ?op (?L @ [?op])"
      unfolding USpec_GenLin_def
      using eff_eq called_lin called_op hb_candidate queue_candidate di_candidate
      by auto

    show "USpec_GenLin (u_his_seq (snd s'))
             (u_eff_ops (snd s')) ?op
             (u_lin_seq (snd s') @ [?op])"
      using gen_concrete
      unfolding lin_seq_def his_seq_def uspec_effOps_def
      by simp
  qed

  have uI3_USpec_D3UD2_s': "uI3_USpec_D3UD2 s'"
  proof (unfold uI3_USpec_D3UD2_def, intro allI impI)
    fix q
    assume pc_q': "program_counter s' q = ''D3''"
    assume qj_q': "Q_arr s' (j_var s' q) \<noteq> BOT"
    assume upc_q': "u_program_counter (snd s') q = ''UD2''"

    let ?x = "Q_arr s' (j_var s' q)"
    let ?op = "mk_op deq ?x q (s_var s' q)"
    let ?base =
      "(if should_modify (lin_seq s') (his_seq s') ?x
        then modify_lin (lin_seq s') (his_seq s') ?x
        else lin_seq s')"
    let ?L = "?base @ [?op]"
    let ?H = "his_seq s'"

    have pending_q:
      "HasPendingDeq s' q"
      using `hI12_D_Phase_Pending_Deq s'` pc_q'
      unfolding hI12_D_Phase_Pending_Deq_def
      by auto

    have deq_call_q:
      "DeqCallInHis s' q (s_var s' q)"
      using pending_q
      unfolding HasPendingDeq_def Let_def
      by blast

    have op_called:
      "OpCalledInHis ?H ?op"
      using DeqCallInHis_imp_OpCalledInHis[OF deq_call_q, of ?x]
      by simp

    have no_HB_from_op:
      "\<forall>x. \<not> HB ?H ?op x"
    proof
      fix x
      show "\<not> HB ?H ?op x"
      proof
        assume hb: "HB ?H ?op x"

        then obtain k1 where
          mr: "match_ret ?H k1 ?op"
          unfolding HB_def
          by blast

        have k1_lt:
          "k1 < length ?H"
          using mr
          unfolding match_ret_def Let_def
          by simp

        have pid_eq:
          "act_pid (?H ! k1) = q"
          using mr
          unfolding match_ret_def Let_def
          by (simp add: mk_op_def op_pid_def)

        have ssn_eq:
          "act_ssn (?H ! k1) = s_var s' q"
          using mr
          unfolding match_ret_def Let_def
          by (simp add: mk_op_def op_ssn_def)

        have cr_eq:
          "act_cr (?H ! k1) = ret"
          using mr
          unfolding match_ret_def Let_def
          by simp

        have in_his:
          "?H ! k1 \<in> set ?H"
          using k1_lt
          by simp

        have no_ret:
          "\<forall>e\<in>set ?H.
             \<not> (act_pid e = q \<and>
                  act_ssn e = s_var s' q \<and>
                  act_cr e = ret)"
          using pending_q
          unfolding HasPendingDeq_def Let_def
          by blast

        show False
          using no_ret in_his pid_eq ssn_eq cr_eq
          by blast
      qed
    qed

    have hb_lin:
      "HB_consistent (lin_seq s') ?H"
      using `lI3_HB_Ret_Lin_Sync s'`
      unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def HB_consistent_def
      by simp

    have lI4_list_s':
      "lI4_FIFO_Semantics_list (lin_seq s')"
      using `lI4_FIFO_Semantics s'`
      unfolding lI4_FIFO_Semantics_def
      by simp

    have lI5_list_s':
      "lI5_SA_Prefix_list (lin_seq s')"
      using `lI5_SA_Prefix s'`
      unfolding lI5_SA_Prefix_def
      by simp

    have x_val:
      "?x \<in> Val"
      using `TypeOK s'` qj_q'
      unfolding TypeOK_def
      by auto

    have typeBT_x:
      "TypeBT s' ?x"
      using D3_j_nonBOT_TypeBT_from_local[
        OF `sI6_D3_Scan_Pointers s'`
           `sI8_Q_Qback_Sync s'`
           `sI10_Qback_Unique_Vals s'`
           pc_q' qj_q'
    ] .

    have x_SetB:
      "?x \<in> SetB s'"
      using x_val typeBT_x
      unfolding SetB_def TypeBT_def
      by blast

    have pending_x_lin:
      "\<forall>i < length (lin_seq s').
         op_val (lin_seq s' ! i) = ?x \<longrightarrow>
         op_name (lin_seq s' ! i) \<noteq> deq"
      by (rule SetB_implies_no_deq_in_lin_from_LI2[
            OF `lI2_Op_Cardinality s'` x_SetB
        ])

    have enq_exists_x_lin:
      "\<exists>k < length (lin_seq s').
         op_name (lin_seq s' ! k) = enq \<and>
         op_val (lin_seq s' ! k) = ?x"
      by (rule SetB_implies_enq_in_lin_from_LI2[
            OF `lI2_Op_Cardinality s'` x_SetB
        ])

    have base_def':
      "?base =
        (if should_modify (lin_seq s') (his_seq s') ?x
         then modify_lin (lin_seq s') (his_seq s') ?x
         else lin_seq s')"
      by simp

    have mset_base_eq:
      "mset ?base = mset (lin_seq s')"
      using D3_base_mset_eq_from_local_invs[OF base_def'] .

    have set_base_eq:
      "set ?base = set (lin_seq s')"
      using mset_base_eq
      by (metis set_mset_mset)

    have all_called_lin:
      "\<forall>a\<in>set (lin_seq s'). OpCalledInHis ?H a"
    proof
      fix a
      assume a_in: "a \<in> set (lin_seq s')"

      have a_oplin:
        "a \<in> OPLin s'"
        using a_in
        unfolding OPLin_def
        by simp

      have cases:
        "a \<in> OP_A_enq s' \<or> a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
        using `lI1_Op_Sets_Equivalence s'` a_oplin
        unfolding lI1_Op_Sets_Equivalence_def
        by blast

      thus "OpCalledInHis ?H a"
      proof
        assume "a \<in> OP_A_enq s'"
        then obtain qq vv sn where
          a_eq: "a = mk_op enq vv qq sn"
          and call: "EnqCallInHis s' qq vv sn"
          unfolding OP_A_enq_def
          by blast

        show ?thesis
          using EnqCallInHis_imp_OpCalledInHis[OF call]
          unfolding a_eq
          by simp
      next
        assume rest: "a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
        thus ?thesis
        proof
          assume "a \<in> OP_A_deq s'"

          hence name_deq: "op_name a = deq"
            and call: "DeqCallInHis s' (op_pid a) (op_ssn a)"
            unfolding OP_A_deq_def
            by auto

          have a_mk:
            "mk_op deq (op_val a) (op_pid a) (op_ssn a) = a"
            using name_deq
            by (cases a)
               (simp add: mk_op_def op_name_def op_val_def op_pid_def op_ssn_def)

          have called_mk:
            "OpCalledInHis ?H
               (mk_op deq (op_val a) (op_pid a) (op_ssn a))"
            using DeqCallInHis_imp_OpCalledInHis[OF call, of "op_val a"] .

          show ?thesis
            using called_mk a_mk
            by simp
        next
          assume "a \<in> OP_B_enq s'"
          then obtain qq vv sn where
            a_eq: "a = mk_op enq vv qq sn"
            and call: "EnqCallInHis s' qq vv sn"
            unfolding OP_B_enq_def
            by blast

          show ?thesis
            using EnqCallInHis_imp_OpCalledInHis[OF call]
            unfolding a_eq
            by simp
        qed
      qed
    qed

    have hb_base:
      "HB_consistent ?base ?H"
    proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
      case False

      have base_eq:
        "?base = lin_seq s'"
        using False
        by (simp only: if_False)

      show ?thesis
        unfolding base_eq
        using hb_lin .
    next
      case True

      have base_eq:
        "?base = modify_lin (lin_seq s') (his_seq s') ?x"
        using True
        by (simp only: if_True)

      have hb_modify:
        "HB_consistent
           (modify_lin (lin_seq s') (his_seq s') ?x)
           (his_seq s')"
      proof (rule modify_preserves_HB_consistent_from_local_invs[
               where s = s'
                 and L = "lin_seq s'"
                 and H = "his_seq s'"
                 and bt_val = ?x
           ])
        show "his_seq s' = his_seq s'"
          by simp
      next
        show "HB_consistent (lin_seq s') (his_seq s')"
          using hb_lin .
      next
        show "data_independent (lin_seq s')"
          using `data_independent (lin_seq s')` .
      next
        show "TypeBT s' ?x"
          using typeBT_x .
      next
        show "mset (lin_seq s') = mset (lin_seq s')"
          by simp
      next
        show "\<forall>v. in_SA v (lin_seq s') = in_SA v (lin_seq s')"
          by simp
      next
        show "lI1_Op_Sets_Equivalence s'"
          using `lI1_Op_Sets_Equivalence s'` .
      next
        show "lI2_Op_Cardinality s'"
          using `lI2_Op_Cardinality s'` .
      next
        show "lI4_FIFO_Semantics s'"
          using `lI4_FIFO_Semantics s'` .
      next
        show "hI5_SSN_Unique s'"
          using `hI5_SSN_Unique s'` .
      next
        show "hI7_His_WF s'"
          using `hI7_His_WF s'` .
      next
        show "hI16_BO_BT_No_HB s'"
          using `hI16_BO_BT_No_HB s'` .
      next
        show "hI17_BT_BT_No_HB s'"
          using `hI17_BT_BT_No_HB s'` .
      next
        show "hI20_Enq_Val_Valid s'"
          using `hI20_Enq_Val_Valid s'` .
      qed

      show ?thesis
        unfolding base_eq
        using hb_modify .
    qed

    have hb_final:
      "HB_consistent ?L ?H"
    proof (rule HB_consistent_append)
      show "HB_consistent ?base ?H"
        using hb_base .
    next
      show "\<forall>a\<in>set ?base. \<not> HB ?H ?op a"
        using no_HB_from_op
        by blast
    next
      show "\<not> HB ?H ?op ?op"
        using no_HB_from_op
        by blast
    qed

    have qs_base:
      "QueueSpecLin ?base"
    proof (rule D3_qs_base_from_local_invs[
             where L = "lin_seq s'"
               and H = "his_seq s'"
               and v = ?x
               and base_lin = ?base
         ])
      show "lI4_FIFO_Semantics_list (lin_seq s')"
        using lI4_list_s' .
    next
      show "data_independent (lin_seq s')"
        using `data_independent (lin_seq s')` .
    next
      show "lI5_SA_Prefix_list (lin_seq s')"
        using lI5_list_s' .
    next
      show "\<forall>k<length (lin_seq s').
              op_val (lin_seq s' ! k) = ?x \<longrightarrow>
              op_name (lin_seq s' ! k) \<noteq> deq"
        using pending_x_lin .
    next
      show "?base =
            (if should_modify (lin_seq s') (his_seq s') ?x
             then modify_lin (lin_seq s') (his_seq s') ?x
             else lin_seq s')"
        using base_def' .
    qed

    have qs_final:
      "QueueSpecLin ?L"
    proof (rule D3_qs_final_from_local_invs[
             where L = "lin_seq s'"
               and H = "his_seq s'"
               and v = ?x
               and base_lin = ?base
               and deq_act = ?op
         ])
      show "lI4_FIFO_Semantics_list (lin_seq s')"
        using lI4_list_s' .
    next
      show "data_independent (lin_seq s')"
        using `data_independent (lin_seq s')` .
    next
      show "lI5_SA_Prefix_list (lin_seq s')"
        using lI5_list_s' .
    next
      show "\<forall>k<length (lin_seq s').
              op_val (lin_seq s' ! k) = ?x \<longrightarrow>
              op_name (lin_seq s' ! k) \<noteq> deq"
        using pending_x_lin .
    next
      show "\<exists>k<length (lin_seq s').
              op_name (lin_seq s' ! k) = enq \<and>
              op_val (lin_seq s' ! k) = ?x"
        using enq_exists_x_lin .
    next
      show "?base =
            (if should_modify (lin_seq s') (his_seq s') ?x
             then modify_lin (lin_seq s') (his_seq s') ?x
             else lin_seq s')"
        using base_def' .
    next
      show "op_name ?op = deq"
        by (simp add: mk_op_def op_name_def)
    next
      show "op_val ?op = ?x"
        by (simp add: mk_op_def op_val_def)
    qed

    have di_final:
      "data_independent ?L"
    proof (rule D3_di_final_from_local_invs[
             where L = "lin_seq s'"
               and H = "his_seq s'"
               and v = ?x
               and base_lin = ?base
               and p = q
               and sn = "s_var s' q"
         ])
      show "data_independent (lin_seq s')"
        using `data_independent (lin_seq s')` .
    next
      show "\<forall>k<length (lin_seq s').
              op_val (lin_seq s' ! k) = ?x \<longrightarrow>
              op_name (lin_seq s' ! k) \<noteq> deq"
        using pending_x_lin .
    next
      show "?base =
            (if should_modify (lin_seq s') (his_seq s') ?x
             then modify_lin (lin_seq s') (his_seq s') ?x
             else lin_seq s')"
        using base_def' .
    qed

    have eff_eq:
      "uspec_effOps s' = set (lin_seq s')"
      using uI1_USpec_EffOps_Lin_s'
      unfolding uI1_USpec_EffOps_Lin_def
      by simp

    have eff_subset:
      "uspec_effOps s' \<subseteq> set ?L"
      using eff_eq set_base_eq
      by auto

    have op_in:
      "?op \<in> set ?L"
      by simp

    have all_called:
      "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
      using all_called_lin set_base_eq op_called
      by auto

    have finite_eff_s':
      "finite (uspec_effOps s')"
      using eff_eq
      by simp

    have gen:
      "USpec_GenLin ?H (uspec_effOps s') ?op ?L"
      unfolding USpec_GenLin_def
    proof (intro conjI)
      show "finite (uspec_effOps s')"
        using finite_eff_s' .
    next
      show "uspec_effOps s' \<subseteq> set ?L"
        using eff_subset .
    next
      show "?op \<in> set ?L"
        using op_in .
    next
      show "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
        using all_called .
    next
      show "HB_consistent ?L ?H"
        using hb_final .
    next
      show "QueueSpecLin ?L"
        using qs_final .
    next
      show "data_independent ?L"
        using di_final .
    qed

    show "let cur_lin = lin_seq s';
              cur_his = his_seq s';
              x_val = Q_arr s' (j_var s' q);
              op = mk_op deq x_val q (s_var s' q);
              new_lin =
                (if should_modify cur_lin cur_his x_val
                 then modify_lin cur_lin cur_his x_val
                 else cur_lin) @ [op]
          in USpec_GenLin cur_his (uspec_effOps s') op new_lin"
      using gen
      by (simp only: Let_def)
  qed

  have "Simulate_PC s'"
    using STEP unfolding Sys_E2_def by simp

  (* ========================================================================= *)
  (* 7. assemble the final conclusion *)
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
    using uI1_USpec_EffOps_Lin_s' uI2_USpec_E1UE2_s' uI3_USpec_D3UD2_s'
    using `data_independent (lin_seq s')`
    by blast
qed


(* ========================================================================= *)
(* For outside: " / history / " three, E2Proof only *)
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


lemma E2_preserves_uspec_invs_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
      and STEP: "Sys_E2 p s s'"
  shows
    "uI1_USpec_EffOps_Lin s' \<and>
     uI2_USpec_E1UE2 s' \<and>
     uI3_USpec_D3UD2 s'"
  using E2_preserves_invariant_core[OF INV STEP]
  unfolding system_invariant_def by auto

lemma E2_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E2 p s s'"
  shows "system_invariant s'"
  using E2_preserves_invariant_core[OF INV STEP] .

end
