(* E1 transition rule of system-invariant preservation proof *)
theory E1Proof
  imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    DeqLib
    D3Lemmas
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
  (* 0. definition and *)
  (* ========================================================================= *)
  note bridge_defs = program_counter_def X_var_def V_var_def Q_arr_def
                     Qback_arr_def i_var_def j_var_def l_var_def
                     x_var_def v_var_def s_var_def lin_seq_def his_seq_def

  (* 1. extractallold state of preconditioninvariant (align new) *)
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

  (* 2. analyze Sys_E1, extractphysical of updatefact *)
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
      unfolding Sys_E1_def C_E1_def Q_arr_def Qback_arr_def x_var_def j_var_def
                l_var_def V_var_def v_var_def s_var_def Let_def by auto

    show "his_seq s' = his_seq s"
      using STEP unfolding Sys_E1_def his_seq_def
      using STEP Sys_E1_history_unchanged his_seq_def by auto
  qed

  (* E1 reserves a slot; the abstract linearization sequence is unchanged. *)
  define v where "v = v_var s p"
  define new_act where "new_act = mk_op enq v p (s_var s p)"
  have lin_eq [simp]: "lin_seq s' = lin_seq s"
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
  (* 3. coresetderivation (SetA / SetB of) *)
  (* ========================================================================= *)

  (* 0. extractwhen before process of PC *)
  have pc_p_E1: "program_counter s p = ''E1''"
    using Sys_E1_pc_before[OF STEP] .

  (* 1. hI1_E_Phase_Pending_Enq, in E1 of process p has one Pending of enqueueoperation *)
  have pend_p: "HasPendingEnq s p v"
    using hI1_E_Phase_Pending_Enq_s pc_p_E1 unfolding hI1_E_Phase_Pending_Enq_def v_def by simp

  (* 2. Pending as history in of Call record *)
  have call_p: "EnqCallInHis s p v (s_var s p)"
    using HasPendingEnq_implies_EnqCallInHis[OF pend_p] .

  (* 3. prove v is valid of value(in Val set inside) *)
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

  (* 4. use hI14_Pending_Enq_Qback_Exclusivity prove: since p in E1 and has Pending, its valuedefinitelyimpossible already enter Qback slot *)
  have not_InQBack_v: "\<not> InQBack s v"
    using hI14_Pending_Enq_Qback_Exclusivity_s pend_p pc_p_E1 unfolding hI14_Pending_Enq_Qback_Exclusivity_def InQBack_def v_def by blast

  (* 5. close the goal directly only in Qback, impossible is TypeBT (TypeBT must in Qback in) *)
  have not_TypeBT_v: "\<not> TypeBT s v"
    using not_InQBack_v unfolding TypeBT_def by simp

  (* 6. from TypeOK in extractglobal of validity *)
  have X_in_Val: "X_var s \<in> Val"
    using TypeOK_s unfolding TypeOK_def by simp

  have V_in_Val: "V_var s \<in> Val"
    using TypeOK_s unfolding TypeOK_def by simp

(* Extracthistory in E1 definitely of use fact, after large use *)
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

  have TypeB_eq: "TypeB s' a \<longleftrightarrow> TypeB s a" for a
    using Sys_E1_TypeB_eq[OF STEP, of a] .

  have TypeBO_eq: "TypeBO s' a \<longleftrightarrow> TypeBO s a" for a
    using TypeB_eq[of a] TypeBT_eq[of a] unfolding TypeBO_def by blast

  have SetBO_eq: "SetBO s' = SetBO s"
    unfolding SetBO_def using TypeBO_eq by blast

  have setB_eq: "SetB s' = SetB s"
    unfolding SetB_def using TypeB_eq by blast

  (* ========================================================================= *)
  (* 4. physical invariant preservation *)
  (* ========================================================================= *)

  have "TypeOK s'"
    using TypeOK_s step_facts pc_eqs
    unfolding TypeOK_def Val_def BOT_def
    by auto

  have "sI1_Zero_Index_BOT s'" using sI1_Zero_Index_BOT_s step_facts unfolding sI1_Zero_Index_BOT_def by auto
  have "sI2_X_var_Upper_Bound s'" using sI2_X_var_Upper_Bound_s step_facts unfolding sI2_X_var_Upper_Bound_def
    using TypeOK_def \<open>TypeOK s'\<close> add_leD1 by presburger

  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_e2_slot_exclusive, not rewriteoriginalprove. *)
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

    (* 1. derivation q in old state in of PC also necessarily in {E1, E2, E3} *)
    have qpc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using qpc' pc_eqs by auto

    (* 2. from old state of hI1_E_Phase_Pending_Enq in extract q of Pending *)
    have pend_old: "HasPendingEnq s q (v_var s q)"
      using hI1_E_Phase_Pending_Enq_s qpc unfolding hI1_E_Phase_Pending_Enq_def by blast

    (* 3. Pending of definition, use v_var, s_var, his_seq change of fact, translate *)
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

    (* 1. derivation pa in old state of PC also is D3, and j_var *)
    have pc_pa: "program_counter s pa = ''D3''"
      using pc_pa' pc_eqs by auto
    have k_lt: "k < j_var s pa"
      using k_lt' step_facts by simp

    (* 2. useold state of sI12_D3_Scanned_Prefix extract *)
    have old_sI12_D3_Scanned_Prefix: "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
      using sI12_D3_Scanned_Prefix_s pc_pa k_lt unfolding sI12_D3_Scanned_Prefix_def by blast

    (* 3. inside prove TypeB of: old of TypeB necessarily also is new of TypeB *)
    have typeb_mono: "\<And>x. TypeB s x \<Longrightarrow> TypeB s' x"
      unfolding TypeB_def QHas_def
      using step_facts pc_eqs by auto

    (* 4. physicalarray of fact, close immediately *)
    show "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
      using old_sI12_D3_Scanned_Prefix typeb_mono step_facts by auto
  qed

  have "hI4_X_var_Lin_Sync s'"
  proof -
    (* 1. physical fact: in E1, global X_var 1 *)
    have step_X: "X_var s' = X_var s + 1"
      using step_facts by simp

    let ?old_slots = "{i. i < X_var s \<and>
        (\<exists>q. program_counter s q = ''E2'' \<and> i_var s q = i)}"

    have slot_set:
      "{i. i < X_var s' \<and>
          (\<exists>q. program_counter s' q = ''E2'' \<and> i_var s' q = i)} =
       insert (X_var s) ?old_slots"
    proof (rule set_eqI)
      fix i
      show "i \<in> {i. i < X_var s' \<and>
              (\<exists>q. program_counter s' q = ''E2'' \<and> i_var s' q = i)} \<longleftrightarrow>
            i \<in> insert (X_var s) ?old_slots"
      proof
        assume new: "i \<in> {i. i < X_var s' \<and>
            (\<exists>q. program_counter s' q = ''E2'' \<and> i_var s' q = i)}"
        then obtain q where q_pc: "program_counter s' q = ''E2''"
          and q_i: "i_var s' q = i"
          by auto
        show "i \<in> insert (X_var s) ?old_slots"
        proof (cases "q = p")
          case True
          then have "i = X_var s"
            using q_i step_facts by simp
          then show ?thesis by simp
        next
          case False
          have old_pc: "program_counter s q = ''E2''"
            using q_pc False step_facts by simp
          have old_i: "i_var s q = i"
            using q_i False step_facts by simp
          have old_bound: "i_var s q < X_var s"
            using sI3_E2_Slot_Exclusive_s old_pc
            unfolding sI3_E2_Slot_Exclusive_def by blast
          show ?thesis
            using old_pc old_i old_bound by auto
        qed
      next
        assume old: "i \<in> insert (X_var s) ?old_slots"
        show "i \<in> {i. i < X_var s' \<and>
            (\<exists>q. program_counter s' q = ''E2'' \<and> i_var s' q = i)}"
        proof (cases "i = X_var s")
          case True
          then show ?thesis
            using step_facts by auto
        next
          case False_i: False
          from old False_i obtain q where old_pc: "program_counter s q = ''E2''"
            and old_i: "i_var s q = i" and old_bound: "i < X_var s"
            by auto
          have q_ne_p: "q \<noteq> p"
            using old_pc step_facts by auto
          show ?thesis
            using old_pc old_i old_bound q_ne_p step_facts by auto
        qed
      qed
    qed

    have finite_old_slots: "finite ?old_slots"
      by (rule finite_subset[of _ "{..<X_var s}"]) auto

    have fresh_slot: "X_var s \<notin> ?old_slots"
      by simp

    have slot_count_step: "E2SlotCount s' = Suc (E2SlotCount s)"
      unfolding E2SlotCount_def
      using slot_set finite_old_slots fresh_slot by simp

    (* 3. guards: unfold of definition, make to two +1 of precise *)
    show ?thesis
      using hI4_X_var_Lin_Sync_s step_X lin_eq slot_count_step
      unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def
      by simp
  qed

  (* ========================================================================= *)
  (* 5. history and physicalconsistencyinvariantpreserve (hI) *)
  (* ========================================================================= *)

  have "hI7_His_WF s'" using hI7_His_WF_s step_facts unfolding hI7_His_WF_def by simp
  have "hI8_Val_Unique s'" using hI8_Val_Unique_s step_facts unfolding hI8_Val_Unique_def by simp
  have "hI5_SSN_Unique s'" using hI5_SSN_Unique_s step_facts unfolding hI5_SSN_Unique_def by simp
  have "hI6_SSN_Order s'" using hI6_SSN_Order_s step_facts unfolding hI6_SSN_Order_def by simp
  have "hI9_Deq_Ret_Unique s'" using hI9_Deq_Ret_Unique_s step_facts unfolding hI9_Deq_Ret_Unique_def by simp

  have "hI10_Enq_Call_Existence s'"
  proof (unfold hI10_Enq_Call_Existence_def, intro conjI allI impI, goal_cases)
    case (1 q a)
    (* 1. use of pc_eqs and step_facts PC and v_var precisemapping old state *)
    have qpc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using 1 pc_eqs pc_p_E1 by auto
    have qv: "v_var s q = a"
      using 1 step_facts by simp

    (* 2. from old state of guards in extract Call record *)
    have call_old: "EnqCallInHis s q a (s_var s q)"
      using hI10_Enq_Call_Existence_s qpc qv unfolding hI10_Enq_Call_Existence_def by blast

    (* 3., usehistory and of fact, close immediately! *)
    show ?case
      using call_old step_facts
      unfolding EnqCallInHis_def Let_def
      by auto
  next
    case (2 a)
    have a_val: "a \<in> Val" using 2 by blast
    (* 1. Physical fact: E1 leaves Qback_arr unchanged. *)
    have inq: "\<exists>k. Qback_arr s k = a"
      using 2 step_facts by simp

    (* 2. from old stateextractconclusion: definition, extract of process q and sn *)
    then obtain q sn where call_old: "EnqCallInHis s q a sn"
      using hI10_Enq_Call_Existence_s a_val
      unfolding hI10_Enq_Call_Existence_def by blast

    (* 3. similarly of, sn translate new state *)
    show ?case
      using call_old step_facts
      unfolding EnqCallInHis_def Let_def
      by metis
  qed

  have "hI11_Enq_Ret_Existence s'"
  proof (unfold hI11_Enq_Ret_Existence_def, intro allI impI, goal_cases)
    case (1 q a sn)

    (* 1. precondition: extract sn of complete three, *)
    from 1 have pre1: "program_counter s' q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn" by blast
    from 1 have pre2: "\<exists>k. Qback_arr s' k = a" by blast
    from 1 have pre3: "EnqCallInHis s' q a sn" by blast

    (* 2. derivation cond_old, inside similarly goal_cases *)
    have cond_old: "program_counter s q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s q \<noteq> a \<or> s_var s q \<noteq> sn"
    proof (cases "q = p", goal_cases)
      case 1 (* q = p *)
      (* If q = p, then it in new state of PC is E2, in {E1, E2, E3} *)
      have "program_counter s' q = ''E2''" using 1 step_facts by simp
      then have "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}" by simp
      (* Pre1 in of No. one as, must is after in valueor of as real *)
      with pre1 have "v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn" by blast
      then show ?case using step_facts 1 by simp
    next
      case 2 (* q \<noteq> p *)
      (* If q \<noteq> p, it of PC, v_var and s_var all has, translate *)
      have "program_counter s' q = program_counter s q" using 2 step_facts by simp
      moreover have "v_var s' q = v_var s q" using 2 step_facts by simp
      moreover have "s_var s' q = s_var s q" using 2 step_facts by simp
      ultimately show ?case using pre1 by simp
    qed

    (* 3. and translate outside two physical fact *)
    have inq_old: "\<exists>k. Qback_arr s k = a"
      using pre2 step_facts by simp

    have call_old: "EnqCallInHis s q a sn"
      using pre3 step_facts unfolding EnqCallInHis_def Let_def by auto

    (* 4. old stateguards, Ret record *)
    have ret_old: "EnqRetInHis s q a sn"
      using hI11_Enq_Ret_Existence_s cond_old inq_old call_old unfolding hI11_Enq_Ret_Existence_def by blast

    (* 5. close immediatelywhen before case of goal *)
    show ?case
      using ret_old step_facts unfolding EnqRetInHis_def Let_def by auto
  qed

  have "hI12_D_Phase_Pending_Deq s'"
  proof (unfold hI12_D_Phase_Pending_Deq_def, intro allI impI)
    fix pa
    assume pc_pa': "program_counter s' pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"

    (* 1. derivation pa in old state of PC necessarily also in {D1, D2, D3, D4} *)
    have pc_pa: "program_counter s pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using pc_pa' pc_eqs by auto

    (* 2. from old state of hI12_D_Phase_Pending_Deq in extract its has PendingDeq of *)
    have pend_old: "HasPendingDeq s pa"
      using hI12_D_Phase_Pending_Deq_s pc_pa unfolding hI12_D_Phase_Pending_Deq_def by auto

    (* 3. HasPendingDeq of definition, usehistory and of fact, translate! *)
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
    (* 1. provedequeue of in E1 is definitely of *)
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

    (* 1. extractgoal in of set *)
    have a_in': "a \<in> SetBO s'" using 1 by blast
    have b_in': "b \<in> SetBT s'" using 1 by blast

    (* 2. physicalmapping: history, HB_EnqRetCall complete *)
    have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq by auto

    (* 3. SetBT definitely, mappingoldvalue *)
    have b_old: "b \<in> SetBT s"
      using b_in' SetBT_eq by simp

    (* 4. Separate the pending enqueue value v from all other values. *)
    show ?case
    proof (cases "a = v", goal_cases)
      case 1 (* a = v *)
      (* v is the pending enqueue value before E1, so it has no enqueue-return record yet.
         We in common proof section already proved previously no_enq_ret_v: "\<forall>q sn. \<not> EnqRetInHis s q v sn" *)
      have no_ret_v: "\<not> (\<exists>k<length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = v \<and> act_cr (his_seq s ! k) = ret)"
        using EnqRetInHis_def hI7_His_WF_s hI8_Val_Unique_s
          no_enq_ret_for_pending_value nth_mem pend_p by blast

      (* Since ret record all has, HB *)
      have "\<not> HB_EnqRetCall s v b"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def mk_op_def op_name_def op_val_def
        using no_ret_v by auto

      then show ?case using 1 hb_eq by simp
    next
      case 2 (* a \<noteq> v *)
      (* For a \<noteq> v, SetBO is unchanged across E1. *)
      have a_old: "a \<in> SetBO s"
        using a_in' SetBO_eq by auto

      (* Precise old state of, old state of hI16_BO_BT_No_HB_s guards *)
      have "\<not> HB_EnqRetCall s a b"
        using hI16_BO_BT_No_HB_s a_old b_old unfolding hI16_BO_BT_No_HB_def by blast

      then show ?case using hb_eq by simp
    qed
  qed

  have "hI17_BT_BT_No_HB s'"
  proof (unfold hI17_BT_BT_No_HB_def, intro allI impI, goal_cases)
    case (1 a b)

    (* 1. extractgoal in of set, and use mapping old state *)
    have a_old: "a \<in> SetBT s" using 1 SetBT_eq by simp
    have b_old: "b \<in> SetBT s" using 1 SetBT_eq by simp

    (* 2. physicalmapping: history, HB_EnqRetCall complete *)
    have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq by auto

    (* 3. sinceelement all is oldelement, old state of hI17_BT_BT_No_HB_s guardsdirect closure *)
    have "\<not> HB_EnqRetCall s a b"
      using hI17_BT_BT_No_HB_s a_old b_old unfolding hI17_BT_BT_No_HB_def by blast

    (* 4. close immediately *)
    then show ?case using hb_eq by simp
  qed

  have "hI18_Idx_Order_No_Rev_HB s'"
  proof (unfold hI18_Idx_Order_No_Rev_HB_def, intro allI impI, goal_cases)
    case (1 a b)

    (* 1. from goal in extract out new state of precondition *)
    have inqa': "InQBack s' a" using 1 by blast
    have inqb': "InQBack s' b" using 1 by blast
    have idx_lt': "Idx s' a < Idx s' b" using 1 by blast

    (* 2. E1 leaves Qback_arr unchanged, so membership and physical indices translate back to s. *)
    have inqa: "InQBack s a"
      using inqa' step_facts unfolding InQBack_def by simp

    have inqb: "InQBack s b"
      using inqb' step_facts unfolding InQBack_def by simp

    have idx_lt: "Idx s a < Idx s b"
      using idx_lt' step_facts unfolding Idx_def AtIdx_def by simp

    (* 3. historymapping: his_seq, HB complete *)
    have hb_eq: "HB_EnqRetCall s' b a = HB_EnqRetCall s b a"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq by auto

    (* 4. precise old state, old state hI18_Idx_Order_No_Rev_HB_s guards *)
    have "\<not> HB_EnqRetCall s b a"
      using hI18_Idx_Order_No_Rev_HB_s inqa inqb idx_lt unfolding hI18_Idx_Order_No_Rev_HB_def by blast

    (* 5. close immediately *)
    then show ?case using hb_eq by simp
  qed

  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_scanner_catches_later_enq, not rewriteoriginalprove. *)
  have "hI19_Scanner_Catches_Later_Enq s'"
    using E1_scanner_catches_later_enq[
      OF hI19_Scanner_Catches_Later_Enq_s not_InQBack_v v_def step_facts pc_eqs his_eq
  ] .

  have "hI20_Enq_Val_Valid s'" using hI20_Enq_Val_Valid_s step_facts unfolding hI20_Enq_Val_Valid_def by simp

  have "hI21_Ret_Implies_Call s'"
  proof (unfold hI21_Ret_Implies_Call_def, intro allI impI, goal_cases)
    case (1 k)

    (* 1. physicalmapping: historyrecorddefinitely *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by simp
    have k_len: "k < length (his_seq s)" using 1 his_eq by simp
    have k_ret: "act_cr (his_seq s ! k) = ret" using 1 his_eq by simp

    (* 2. old state hI21_Ret_Implies_Call_s guards, extractcorresponds to of call record tm *)
    from hI21_Ret_Implies_Call_s k_len k_ret obtain tm where tm_props:
      "tm < k"
      "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k)"
      "act_name (his_seq s ! tm) = act_name (his_seq s ! k)"
      "act_cr (his_seq s ! tm) = call"
      "(if act_name (his_seq s ! k) = enq then act_val (his_seq s ! tm) = act_val (his_seq s ! k) else act_val (his_seq s ! tm) = BOT)"
      unfolding hI21_Ret_Implies_Call_def by blast

    (* 3. for when before returnrecord of operation, if-then-else *)
    show ?case
    proof (cases "act_name (his_seq s ! k) = enq")
      case True
      (* If is enqueueoperation, analyze out corresponds to of *)
      have oper_enq: "act_name (his_seq s ! tm) = enq" using tm_props(3) True by simp
      have val_eq: "act_val (his_seq s ! tm) = act_val (his_seq s ! k)" using tm_props(5) True by simp

      show ?thesis
        using tm_props True oper_enq val_eq his_eq 1 by auto
    next
      case False
      (* If is dequeueoperation, analyze out corresponds to *)
      have val_bot: "act_val (his_seq s ! tm) = BOT" using tm_props(5) False by simp

      show ?thesis
        using tm_props False val_bot his_eq 1 by auto
    qed
  qed

  have "hI22_Deq_Local_Pattern s'"
  proof (unfold hI22_Deq_Local_Pattern_def, intro allI impI, goal_cases)
    case (1 p a sn)

    (* 1. E1 leaves the dequeue-relevant array and history components unchanged. *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by auto
    have q_eq: "Q_arr s' = Q_arr s" using step_facts by auto
    have qback_eq: "Qback_arr s' = Qback_arr s" using step_facts by auto
    have x_var_eq: "\<And>q. x_var s' q = x_var s q" using step_facts by auto

    (* 2. fill in of coremapping: dequeuereturnhistory in E1 definitely *)
    have deq_ret_eq: "DeqRetInHis s' p a sn \<longleftrightarrow> DeqRetInHis s p a sn"
      unfolding DeqRetInHis_def Let_def using his_eq by auto

    (* 3. extractgoal in of coreprecondition, and use translate old state s *)
    from 1 have cond_q': "\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a \<and> (\<forall>q. x_var s' q \<noteq> a)" by blast
    from 1 have cond_ret': "DeqRetInHis s' p a sn" by blast

    have cond_q: "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a \<and> (\<forall>q. x_var s q \<noteq> a)"
      using cond_q' q_eq qback_eq x_var_eq by simp
    have cond_ret: "DeqRetInHis s p a sn"
      using cond_ret' deq_ret_eq by simp

    (* 4. old state hI22_Deq_Local_Pattern_s guards, of coreconclusion *)
    have "let p_his = filter (\<lambda>e. act_pid e = p) (his_seq s)
          in \<exists>i<length p_his. p_his ! i = mk_act deq a p sn ret \<and> 0 < i \<and> p_his ! (i - Suc 0) = mk_act deq BOT p sn call"
      using hI22_Deq_Local_Pattern_s cond_q cond_ret unfolding hI22_Deq_Local_Pattern_def
      by simp

    (* 5. to of history conclusiontranslate new state s', close immediately! *)
    then show ?case using his_eq by simp
  qed

  have "hI23_Deq_Call_Ret_Balanced s'" using hI23_Deq_Call_Ret_Balanced_s step_facts unfolding hI23_Deq_Call_Ret_Balanced_def by simp

  have "hI24_HB_Implies_Idx_Order s'"
  proof (unfold hI24_HB_Implies_Idx_Order_def, intro allI impI, goal_cases)
    case (1 u1 u2 v1 v2 idx1 idx2 sn1 sn2)

    (* 1. from goal in extract out new state s' of 3 coreprecondition *)
    from 1 have hb': "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)" by blast
    from 1 have q1': "CState.Q_arr (fst s') idx1 = v1" by blast
    from 1 have q2': "CState.Q_arr (fst s') idx2 = v2" by blast

    (* 2. E1 changes only the reserving process's enqueue-local state; queue contents and history stay unchanged. *)
    (* Near step_facts, fst s' = fst s with his_seq s' = his_seq s *)
    have hb: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
      using hb' step_facts unfolding HB_Act_def Let_def by auto

    have q1: "CState.Q_arr (fst s) idx1 = v1"
      using q1' step_facts
      using Model.Q_arr_def by auto

    have q2: "CState.Q_arr (fst s) idx2 = v2"
      using q2' step_facts
      using Model.Q_arr_def by fastforce

    (* 3. old statepremiseall, hI24_HB_Implies_Idx_Order_s guards one final step! *)
    show ?case
      using hI24_HB_Implies_Idx_Order_s hb q1 q2 unfolding hI24_HB_Implies_Idx_Order_def by blast
  qed

  have "hI25_Enq_Call_Ret_Balanced s'"
  proof (unfold hI25_Enq_Call_Ret_Balanced_def, intro allI impI, goal_cases)
    case (1 q k)

    (* 1. physicalmapping: historyrecordcomplete *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by simp

    (* Proof step: fill in impI after, 1 precise into k \<le> length (his_seq s'), derivation succeeds! *)
    have k_le: "k \<le> length (his_seq s)" using 1 his_eq by simp

    (* 2. becausehistoryrecord, extract out old state s of completeguards (three let) *)
    have hI25_Enq_Call_Ret_Balanced_old: "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s)) in
           let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
           let n_ret  = length (filter (\<lambda>e. act_cr e = ret) p_his) in
           n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
           (k = length (his_seq s) \<longrightarrow> (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1))"
      using hI25_Enq_Call_Ret_Balanced_s k_le unfolding hI25_Enq_Call_Ret_Balanced_def by blast

    (* 3. E1 moves only process p from E1 to E2; both phases remain inside
          the enqueue-phase set {E1, E2, E3}. *)
    have pc_eq: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
    proof (cases "q = p")
      case True
      (* Process p in set inside translate, *)
      have pc_s: "program_counter s p = ''E1''" using step_facts by simp
      have pc_s': "program_counter s' p = ''E2''" using step_facts by simp
      show ?thesis using True pc_s pc_s' by auto
    next
      case False
      (* Its process PC *)
      have "program_counter s' q = program_counter s q" using step_facts False pc_eqs by auto
      then show ?thesis by simp
    qed

    (* 4. all of 's' to s', use let unfoldcomplete into final step *)
    show ?case
      using hI25_Enq_Call_Ret_Balanced_old pc_eq his_eq unfolding Let_def by auto
  qed

  have "hI26_DeqRet_D4_Mutex s'"
  proof (unfold hI26_DeqRet_D4_Mutex_def, intro allI impI, goal_cases)
    case (1 q a)

    (* Goal is derivation \<not> (...), use directlyno proof notI *)
    show ?case
    proof
      (* 1. in of process q *)
      assume bad_cond: "(\<exists>sn. DeqRetInHis s' q a sn) \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a"

      (* 2. when before process p: because p in E1 after in E2, therefore q impossible is p *)
      have q_neq_p: "q \<noteq> p"
      proof
        assume "q = p"
        with bad_cond have "program_counter s' p = ''D4''" by simp
        moreover have "program_counter s' p = ''E2''" using step_facts by simp
        ultimately show False by simp
      qed

      (* 3. physicalmapping: history global, and for in q \<noteq> p, PC and x_var definitely *)
      obtain sn where sn_his: "DeqRetInHis s' q a sn" using bad_cond by blast

      have his_eq: "his_seq s' = his_seq s" using step_facts by auto
      have sn_his_s: "DeqRetInHis s q a sn"
        using sn_his his_eq unfolding DeqRetInHis_def Let_def by simp

      have pc_q_s: "program_counter s q = ''D4''"
        using bad_cond q_neq_p step_facts pc_eqs by auto

      (* E1 this change x_var, globaltranslate *)
      have x_var_eq: "\<And>x. x_var s' x = x_var s x" using step_facts by auto
      have x_q_s: "x_var s q = a"
        using bad_cond x_var_eq by auto

      (* 4. precise original out old state of, old guards hI26_DeqRet_D4_Mutex_s direct closure! *)
      have "\<not> ((\<exists>sn. DeqRetInHis s q a sn) \<and> program_counter s q = ''D4'' \<and> x_var s q = a)"
        using hI26_DeqRet_D4_Mutex_s 1 unfolding hI26_DeqRet_D4_Mutex_def by blast

      (* 5. contradiction, close immediately *)
      then show False using sn_his_s pc_q_s x_q_s by blast
    qed
  qed

  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_pending_pc_sync, not rewriteoriginalprove. *)
  have "hI27_Pending_PC_Sync s'"
    using E1_pending_pc_sync[OF hI27_Pending_PC_Sync_s step_facts pc_eqs] .

have "hI28_Fresh_Enq_Immunity s'"
  proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI, goal_cases)
    case (1 p' q a sn)

    (* 1. extractgoal in of coreprecondition *)
    from 1 have pc_p': "program_counter s' p' \<in> {''E1'', ''E2''}" by blast
    from 1 have v_p': "v_var s' p' = a" by blast
    from 1 have a_not_bot: "a \<noteq> BOT" by blast

    (* 2. physicalmapping: E1 definitely globalhistory *)
    have his_eq: "his_seq s' = his_seq s" using step_facts by simp
    have deq_eq: "DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
      unfolding DeqRetInHis_def Let_def using his_eq by simp

    (* 3.: to is in? *)
    show ?case
      proof (cases "p' = p")
      case True
      (* 3.1 final stepwhen before process p: it in of then is old state in already of v_var s p *)
      have a_is_v: "a = v_var s p" using True v_p' step_facts by auto

      (* Core extraction from step_facts: recover facts about the old state s. *)
      have pc_s: "program_counter s p = ''E1''" using step_facts by auto
      have v_var_s: "v_var s p = a" using True v_p' step_facts by auto

      (* Since p in old state already is E1, and in a (BOT),
         Old of hI28_Fresh_Enq_Immunity_s guards early then it has dequeuehistory! direct closure! *)
      have "\<not> DeqRetInHis s q a sn"
        using hI28_Fresh_Enq_Immunity_s pc_s v_var_s a_not_bot
        unfolding hI28_Fresh_Enq_Immunity_def by blast

      then show ?thesis using deq_eq by simp
    next
      case False
      (* 3.2 its process p': if is when before process, it of all definitely *)
      have pc_p'_s: "program_counter s p' = program_counter s' p'"
        using step_facts False pc_eqs by auto
      have v_p'_s: "v_var s p' = v_var s' p'"
        using step_facts False by auto

      (* Translate old state s *)
      have pc_in_set: "program_counter s p' \<in> {''E1'', ''E2''}"
        using pc_p' pc_p'_s by simp
      have v_val_eq: "v_var s p' = a"
        using v_p' v_p'_s
        by blast

      (* Old guards hI28_Fresh_Enq_Immunity_s one direct closure! *)
      have "\<not> DeqRetInHis s q a sn"
        using hI28_Fresh_Enq_Immunity_s pc_in_set v_val_eq a_not_bot
        unfolding hI28_Fresh_Enq_Immunity_def by blast

      (* Translate new state s' *)
      then show ?thesis using deq_eq by simp
    qed
  qed

  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_e2_scanner_immune, not rewriteoriginalprove. *)
  have "hI29_E2_Scanner_Immunity s'"
    using E1_e2_scanner_immune[OF INV not_InQBack_v v_def step_facts pc_eqs] .

(* ========================================================================= *)
    (* HI22: physical of definitelyorder preservation (E1 state transition - newversionsimplified definition) *)
    (* : use sI2_X_var_Upper_Bound spaceguardsprove"oldelementticketnecessarilyless thannew of X_var" *)
    (* ========================================================================= *)
    (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
    (* Belowonly new in helper lemma E1_ticket_hb_immune, not rewriteoriginalprove. *)
    have "hI30_Ticket_HB_Immunity s'"
      using E1_ticket_hb_immune[OF INV step_facts pc_eqs] .

  (* ========================================================================= *)
  (* 6. invariantpreserve (linI) *)
  (* Core: E1 does not append to lin_seq; reuse the old OPLin, OP_A_enq, and OP_B_enq sets. *)
  (* ========================================================================= *)

  have OPLin_eq: "OPLin s' = OPLin s"
    unfolding OPLin_def lin_eq by simp

  have OP_A_enq_eq: "OP_A_enq s' = OP_A_enq s"
    using his_eq setA_eq unfolding OP_A_enq_def by (auto simp: EnqCallInHis_his_eq[OF his_eq])

  have OP_A_deq_eq: "OP_A_deq s' = OP_A_deq s"
  proof
    show "OP_A_deq s' \<subseteq> OP_A_deq s"
    proof (intro subsetI)
      fix act assume act_in: "act \<in> OP_A_deq s'"

      (* Key correction: use obtain split! from setderivation in extract four *)
      have act_lin: "act \<in> OPLin s'"
       and act_deq: "op_name act = deq"
       and act_setA: "op_val act \<in> SetA s'"
       and act_call: "DeqCallInHis s' (op_pid act) (op_ssn act)"
        using act_in unfolding OP_A_deq_def by simp_all

      (* new_act is a synthetic enqueue operation used only for this local case split. *)
      have "op_name new_act = enq"
        unfolding new_act_def mk_op_def op_name_def by simp

      hence "act \<noteq> new_act" using act_deq
        by auto

      (* Since OPLin is unchanged across E1, act already belongs to the old OPLin. *)
      hence old_lin: "act \<in> OPLin s" using act_lin OPLin_eq by blast

      (* Physical definitely translate *)
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

      (* And, translate new state *)
      have new_lin: "act \<in> OPLin s'" using act_lin OPLin_eq by blast
      have new_setA: "op_val act \<in> SetA s'" using act_setA setA_eq by simp
      have new_call: "DeqCallInHis s' (op_pid act) (op_ssn act)"
        using act_call his_eq unfolding DeqCallInHis_def Let_def by auto

      show "act \<in> OP_A_deq s'"
        unfolding OP_A_deq_def using new_lin act_deq new_setA new_call by simp
    qed
  qed

  have OP_B_enq_eq: "OP_B_enq s' = OP_B_enq s"
    using his_eq setB_eq unfolding OP_B_enq_def EnqCallInHis_def by auto

  have "lI1_Op_Sets_Equivalence s'"
    using lI1_Op_Sets_Equivalence_s OPLin_eq OP_A_enq_eq OP_A_deq_eq OP_B_enq_eq
    unfolding lI1_Op_Sets_Equivalence_def by blast

  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_op_cardinality, not rewriteoriginalprove. *)
  have lI2_Op_Cardinality_s': "lI2_Op_Cardinality s'"
    using lI2_Op_Cardinality_s setA_eq setB_eq lin_eq
    unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def by simp


  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_hb_ret_lin_sync, not rewriteoriginalprove. *)
  have "lI3_HB_Ret_Lin_Sync s'"
    using lI3_HB_Ret_Lin_Sync_s his_eq lin_eq
    unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def
              EnqRetInHis_def DeqRetInHis_def by simp

  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_fifo_semantics, not rewriteoriginalprove. *)
  have "lI4_FIFO_Semantics s'"
    using lI4_FIFO_Semantics_s lin_eq unfolding lI4_FIFO_Semantics_def by simp

  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_sa_prefix, not rewriteoriginalprove. *)
  have "lI5_SA_Prefix s'"
    using lI5_SA_Prefix_s lin_eq unfolding lI5_SA_Prefix_def by simp

(* ========================================================================= *)
  (* LI6_D4_Deq_Linearized: Pending Dequeue action in of in *)
  (* : goal_cases start, useprocess (q \<noteq> p) translateold state of into *)
  (* ========================================================================= *)
  have "lI6_D4_Deq_Linearized s'"
  proof (unfold lI6_D4_Deq_Linearized_def, intro allI impI, goal_cases)
    (* 1. here of q arbitrary one in D4 of process *)
    case (1 q)
    then have pc_q: "program_counter s' q = ''D4''" by simp

    (* 2. core: prove q is when before of process p *)
    have "q \<noteq> p"
    proof
      assume "q = p"
      hence "program_counter s' p = ''D4''" using pc_q by simp
      moreover have "program_counter s' p = ''E2''" using step_facts by simp
      ultimately show False by simp
    qed

    (* 3. translate: since q \<noteq> p, q of all in s and s' in complete one *)
    have pc_q_s: "program_counter s q = ''D4''"
      using pc_q \<open>q \<noteq> p\<close> step_facts by (auto simp: fun_upd_def)
    have x_q_s: "x_var s' q = x_var s q" using step_facts \<open>q \<noteq> p\<close> by simp
    have s_q_s: "s_var s' q = s_var s q" using step_facts \<open>q \<noteq> p\<close> by simp

    (* 4. use old state: q of action already in old in *)
    have lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" using INV unfolding system_invariant_def by blast
    hence "mk_op deq (x_var s q) q (s_var s q) \<in> set (lin_seq s)"
      using pc_q_s unfolding lI6_D4_Deq_Linearized_def by blast

    (* 5.: old is new of *)
    thus ?case
      using x_q_s s_q_s lin_eq by (auto simp: nth_append)
  qed

(* ========================================================================= *)
  (* LI7_D4_Deq_Deq_HB: Pending Dequeue of order preservation (HB) *)
  (* : use goal_cases, No. one split large of, and use q *)
  (* ========================================================================= *)
  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_d4_deq_deq_hb, not rewriteoriginalprove. *)
  have pc_D4_eq: "\<And>q. program_counter s' q = ''D4'' \<longleftrightarrow>
                              program_counter s q = ''D4''"
    using pc_eqs by simp

  have lI7_pc_cong:
    "lI7_D4_Deq_Deq_HB_list L H pc' xv sv =
     lI7_D4_Deq_Deq_HB_list L H pc xv sv"
    if PC: "\<And>q. pc' q = ''D4'' \<longleftrightarrow> pc q = ''D4''"
    for L H pc' pc xv sv
    using PC unfolding lI7_D4_Deq_Deq_HB_list_def by blast

  have lI7_list_eq:
    "lI7_D4_Deq_Deq_HB_list (lin_seq s') (his_seq s')
       (program_counter s') (x_var s') (s_var s') =
     lI7_D4_Deq_Deq_HB_list (lin_seq s) (his_seq s)
       (program_counter s) (x_var s) (s_var s)"
  proof -
    have pc_only:
      "lI7_D4_Deq_Deq_HB_list (lin_seq s') (his_seq s')
         (program_counter s') (x_var s') (s_var s') =
       lI7_D4_Deq_Deq_HB_list (lin_seq s') (his_seq s')
         (program_counter s) (x_var s') (s_var s')"
      by (rule lI7_pc_cong[OF pc_D4_eq])
    show ?thesis using pc_only lin_eq his_eq step_facts by simp
  qed

  have "lI7_D4_Deq_Deq_HB s'"
    using lI7_D4_Deq_Deq_HB_s lI7_list_eq
    unfolding lI7_D4_Deq_Deq_HB_def by simp

  have "lI8_D3_Deq_Returned s'"
    using lI8_D3_Deq_Returned_s lin_eq his_eq step_facts pc_eqs
    unfolding lI8_D3_Deq_Returned_def DeqRetInHis_def by simp

  have "lI9_D1_D2_Deq_Returned s'"
    using lI9_D1_D2_Deq_Returned_s lin_eq his_eq step_facts pc_eqs
    unfolding lI9_D1_D2_Deq_Returned_def DeqRetInHis_def by simp

  have lI10_pc_cong:
    "lI10_D4_Enq_Deq_HB_list L H pc' xv sv =
     lI10_D4_Enq_Deq_HB_list L H pc xv sv"
    if PC: "\<And>q. pc' q = ''D4'' \<longleftrightarrow> pc q = ''D4''"
    for L H pc' pc xv sv
    using PC unfolding lI10_D4_Enq_Deq_HB_list_def by blast

  have lI10_list_eq:
    "lI10_D4_Enq_Deq_HB_list (lin_seq s') (his_seq s')
       (program_counter s') (x_var s') (s_var s') =
     lI10_D4_Enq_Deq_HB_list (lin_seq s) (his_seq s)
       (program_counter s) (x_var s) (s_var s)"
  proof -
    have pc_only:
      "lI10_D4_Enq_Deq_HB_list (lin_seq s') (his_seq s')
         (program_counter s') (x_var s') (s_var s') =
       lI10_D4_Enq_Deq_HB_list (lin_seq s') (his_seq s')
         (program_counter s) (x_var s') (s_var s')"
      by (rule lI10_pc_cong[OF pc_D4_eq])
    show ?thesis using pc_only lin_eq his_eq step_facts by simp
  qed

  have "lI10_D4_Enq_Deq_HB s'"
    using lI10_D4_Enq_Deq_HB_s lI10_list_eq
    unfolding lI10_D4_Enq_Deq_HB_def by simp

  have "lI11_D4_Deq_Unique s'"
    using lI11_D4_Deq_Unique_s lin_eq his_eq step_facts pc_eqs
    unfolding lI11_D4_Deq_Unique_def DeqRetInHis_def by simp

(* ========================================================================= *)
  (* Data_independent is preserved because E1 leaves lin_seq unchanged. *)
  (* ========================================================================= *)
  (* This proof block has been factored out from E1Proof.thy into E1Lemmas.thy. *)
  (* Belowonly new in helper lemma E1_data_independent, not rewriteoriginalprove. *)
  have "data_independent (lin_seq s')"
    using di_lin_s lin_eq by simp



  (* ========================================================================= *)
  (* 6'. USpec invariantpreserve: uI1/uI2/uI3 *)
  (* ========================================================================= *)

  have snd_eq [simp]: "snd s' = snd s"
    using STEP unfolding Sys_E1_def by simp

  have uspec_effOps_eq [simp]: "uspec_effOps s' = uspec_effOps s"
    using snd_eq unfolding uspec_effOps_def by simp

  have uI1_USpec_EffOps_Lin_s': "uI1_USpec_EffOps_Lin s'"
    using uI1_USpec_EffOps_Lin_s snd_eq lin_eq
    unfolding uI1_USpec_EffOps_Lin_def uspec_effOps_def by simp

  have uI2_USpec_E1UE2_s': "uI2_USpec_E1UE2 s'"
    using uI2_USpec_E1UE2_s step_facts snd_eq
    unfolding uI2_USpec_E1UE2_def by auto

  have uI3_USpec_D3UD2_s': "uI3_USpec_D3UD2 s'"
    using uI3_USpec_D3UD2_s step_facts snd_eq lin_eq
    unfolding uI3_USpec_D3UD2_def uspec_effOps_def by auto

  have "Simulate_PC s'"
    using STEP unfolding Sys_E1_def by simp

  (* ========================================================================= *)
  (* 7. assemble the final conclusion *)
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
    using uI1_USpec_EffOps_Lin_s' uI2_USpec_E1UE2_s' uI3_USpec_D3UD2_s'
    using `data_independent (lin_seq s')`
    by blast
qed

end
