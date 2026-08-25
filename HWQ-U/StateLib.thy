theory StateLib
  imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
begin

lemma HWQ_Init_nonempty:
  "\<exists>cs us. Init (cs, us)"
proof -
  let ?cs0 = "\<lparr>
    c_program_counter = (\<lambda>p. ''L0''),
    CState.X_var = 1,
    CState.Q_arr = (\<lambda>idx. BOT),
    CState.i_var = (\<lambda>p. 1),
    CState.j_var = (\<lambda>p. 1),
    CState.l_var = (\<lambda>p. 1),
    CState.x_var = (\<lambda>p. BOT),
    CState.v_var = (\<lambda>p. 1),
    CState.Qback_arr = (\<lambda>idx. BOT),
    CState.V_var = 1\<rparr>"
  let ?us0 = "\<lparr>
    u_program_counter = (\<lambda>p. ''UL0''),
    u_lin_seq = [],
    u_his_seq = [],
    u_eff_ops = {},
    UState.S_var = (\<lambda>p. 1)\<rparr>"
  have INV: "system_invariant (?cs0, ?us0)"
    unfolding system_invariant_def
      Simulate_PC_def TypeOK_def
      sI1_Zero_Index_BOT_def sI2_X_var_Upper_Bound_def
      sI3_E2_Slot_Exclusive_def sI4_E3_Qback_Written_def
      sI5_D2_Local_Bound_def sI6_D3_Scan_Pointers_def
      sI7_D4_Deq_Result_def sI8_Q_Qback_Sync_def
      sI9_Qback_Discrepancy_E3_def sI10_Qback_Unique_Vals_def
      sI11_x_var_Scope_def sI12_D3_Scanned_Prefix_def
      hI1_E_Phase_Pending_Enq_def hI2_SSN_Bounds_def
      hI3_L0_E_Phase_Bounds_def hI4_X_var_Lin_Sync_def
      hI5_SSN_Unique_def hI6_SSN_Order_def hI7_His_WF_def
      hI8_Val_Unique_def hI9_Deq_Ret_Unique_def
      hI10_Enq_Call_Existence_def hI11_Enq_Ret_Existence_def
      hI12_D_Phase_Pending_Deq_def hI13_Qback_Deq_Sync_def
      hI14_Pending_Enq_Qback_Exclusivity_def
      hI15_Deq_Result_Exclusivity_def hI16_BO_BT_No_HB_def
      hI17_BT_BT_No_HB_def hI18_Idx_Order_No_Rev_HB_def
      hI19_Scanner_Catches_Later_Enq_def hI20_Enq_Val_Valid_def
      hI21_Ret_Implies_Call_def hI22_Deq_Local_Pattern_def
      hI23_Deq_Call_Ret_Balanced_def hI24_HB_Implies_Idx_Order_def
      hI25_Enq_Call_Ret_Balanced_def hI26_DeqRet_D4_Mutex_def
      hI27_Pending_PC_Sync_def hI28_Fresh_Enq_Immunity_def
      hI29_E2_Scanner_Immunity_def hI30_Ticket_HB_Immunity_def
      lI1_Op_Sets_Equivalence_def lI2_Op_Cardinality_def
      lI3_HB_Ret_Lin_Sync_def lI4_FIFO_Semantics_def
      lI4_FIFO_Semantics_list_def lI5_SA_Prefix_def
      lI5_SA_Prefix_list_def lI6_D4_Deq_Linearized_def
      lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
      lI8_D3_Deq_Returned_def lI9_D1_D2_Deq_Returned_def
      lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
      lI11_D4_Deq_Unique_def uI1_USpec_EffOps_Lin_def
      uI2_USpec_E1UE2_def uI3_USpec_D3UD2_def data_independent_def
      program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def
      i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def
      lin_seq_def his_seq_def uspec_effOps_def
      Val_def BOT_def E2SlotCount_def LinEnqCount_def
      HasPendingEnq_def HasPendingDeq_def
      EnqCallInHis_def EnqRetInHis_def DeqCallInHis_def DeqRetInHis_def
      HB_Act_def HB_EnqRetCall_def HB_def match_call_def match_ret_def
      QHas_def InQBack_def TypeA_def TypeB_def TypeBT_def TypeBO_def
      SetA_def SetB_def SetBT_def SetBO_def EnqIdxs_def DeqIdxs_def
      OPLin_def OP_A_enq_def OP_A_deq_def OP_B_enq_def
    by auto
  have "Init (?cs0, ?us0)"
    using INV
    unfolding Init_def Simulate_PC_def X_var_def V_var_def Q_arr_def Qback_arr_def
      i_var_def j_var_def l_var_def x_var_def v_var_def
    by simp
  then show ?thesis by blast
qed

lemma Simulate_PC_one_process_cong:
  assumes OLD: "Simulate_PC (cs, us)"
      and C_OTHER:
        "\<And>q. q \<noteq> p \<Longrightarrow>
          CState.c_program_counter cs' q = CState.c_program_counter cs q"
      and U_OTHER:
        "\<And>q. q \<noteq> p \<Longrightarrow>
          u_program_counter us' q = u_program_counter us q"
      and CURRENT:
        "(CState.c_program_counter cs' p = ''L0'' \<longleftrightarrow>
            u_program_counter us' p = ''UL0'') \<and>
         (CState.c_program_counter cs' p \<in> {''E1'', ''E2''} \<longleftrightarrow>
            u_program_counter us' p = ''UE2'') \<and>
         (CState.c_program_counter cs' p = ''E3'' \<longleftrightarrow>
            u_program_counter us' p = ''UE3'') \<and>
         (CState.c_program_counter cs' p \<in> {''D1'', ''D2'', ''D3''} \<longleftrightarrow>
            u_program_counter us' p = ''UD2'') \<and>
         (CState.c_program_counter cs' p = ''D4'' \<longleftrightarrow>
            u_program_counter us' p = ''UD3'')"
  shows "Simulate_PC (cs', us')"
  unfolding Simulate_PC_def
  apply (intro allI)
  subgoal for q
    apply (cases "q = p")
     apply (erule ssubst)
     apply (simp only: fst_conv snd_conv)
     apply (rule CURRENT)
    apply (subgoal_tac
      "CState.c_program_counter cs' q = CState.c_program_counter cs q")
     prefer 2
     apply (rule C_OTHER)
     apply assumption
    apply (subgoal_tac
      "u_program_counter us' q = u_program_counter us q")
     prefer 2
     apply (rule U_OTHER)
     apply assumption
    apply (insert OLD)
    apply (unfold Simulate_PC_def)
    apply (drule_tac x=q in spec)
    apply simp
    done
  done


lemma Same_Process_Total_Order:
  assumes sys: "system_invariant s"
    and H_def: "H = his_seq s"
    and a_ret: "\<exists>k. match_ret H k a"
    and b_ret: "\<exists>k. match_ret H k b"
    and same_pid: "op_pid a = op_pid b"
    and distinct: "op_ssn a \<noteq> op_ssn b"  (* Key proof fix. Related symbols: SSN. *)
  shows "HB_Act s a b \<or> HB_Act s b a"
proof -
  (* Step 1: extract the required facts. *)
  obtain kr_a where kr_a: "kr_a < length H" "match_ret H kr_a a"
  proof -
    from a_ret obtain k where k: "match_ret H k a" by blast
    have "k < length H" using k unfolding match_ret_def by simp
    with k show ?thesis using that by blast
  qed

  obtain kr_b where kr_b: "kr_b < length H" "match_ret H kr_b b"
  proof -
    from b_ret obtain k where k: "match_ret H k b" by blast
    have "k < length H" using k unfolding match_ret_def by simp
    with k show ?thesis using that by blast
  qed

  (* Step 2: extract the required facts. *)
  have wf: "hI7_His_WF s" using sys unfolding system_invariant_def by blast

  obtain kc_a where kc_a: "kc_a < kr_a" "match_call H kc_a a"
  proof -
    have r_props: "act_pid (H ! kr_a) = op_pid a" "act_ssn (H ! kr_a) = op_ssn a"
                  "act_name (H ! kr_a) = op_name a" "act_val (H ! kr_a) = op_val a"
                  "act_cr (H ! kr_a) = ret"
      using kr_a(2) unfolding match_ret_def Let_def by auto

    with wf kr_a(1) obtain j where j_props: "j < kr_a"
      "act_pid (H ! j) = act_pid (H ! kr_a)"
      "act_ssn (H ! j) = act_ssn (H ! kr_a)"
      "act_name (H ! j) = act_name (H ! kr_a)"
      "act_cr (H ! j) = call"
      "if act_name (H ! kr_a) = enq then act_val (H ! j) = act_val (H ! kr_a) else act_val (H ! j) = BOT"
      unfolding hI7_His_WF_def H_def Let_def by (smt (verit))

    have "match_call H j a"
      unfolding match_call_def
    proof (intro conjI)
      show "j < length H" using j_props(1) kr_a(1) by simp
      (* Key proof fix. Related symbols: ?thesis. *)
      show "let e = H ! j in act_name e = op_name a \<and> act_pid e = op_pid a \<and>
            act_ssn e = op_ssn a \<and> act_val e = (if op_name a = deq then BOT else op_val a) \<and>
            act_cr e = call"
        using j_props r_props
        by (metis mname.distinct(1) mname.exhaust)
    qed
    thus ?thesis using `j < kr_a` that by blast
  qed

  obtain kc_b where kc_b: "kc_b < kr_b" "match_call H kc_b b"
  proof -
    have r_props: "act_pid (H ! kr_b) = op_pid b" "act_ssn (H ! kr_b) = op_ssn b"
                  "act_name (H ! kr_b) = op_name b" "act_val (H ! kr_b) = op_val b"
                  "act_cr (H ! kr_b) = ret"
      using kr_b(2) unfolding match_ret_def Let_def by auto

    with wf kr_b(1) obtain j where j_props: "j < kr_b"
      "act_pid (H ! j) = act_pid (H ! kr_b)"
      "act_ssn (H ! j) = act_ssn (H ! kr_b)"
      "act_name (H ! j) = act_name (H ! kr_b)"
      "act_cr (H ! j) = call"
      "if act_name (H ! kr_b) = enq then act_val (H ! j) = act_val (H ! kr_b) else act_val (H ! j) = BOT"
      unfolding hI7_His_WF_def H_def Let_def by (smt (verit))

    have "match_call H j b"
      unfolding match_call_def
    proof (intro conjI)
      show "j < length H" using j_props(1) kr_b(1) by simp
      show "let e = H ! j in act_name e = op_name b \<and> act_pid e = op_pid b \<and>
            act_ssn e = op_ssn b \<and> act_val e = (if op_name b = deq then BOT else op_val b) \<and>
            act_cr e = call"
        using j_props r_props
        by (metis mname.distinct(1) mname.exhaust)
    qed
    thus ?thesis using `j < kr_b` that by blast
  qed

  (* Step 3: use the available invariant or hypothesis. Related symbols: SSN. *)
  have ssn_order: "hI6_SSN_Order s" using sys unfolding system_invariant_def by blast

  show ?thesis
  proof (cases "op_ssn a < op_ssn b")
    case True (* Proof note. Related symbols: SSN. *)
    have "kr_a < kc_b"
    proof (rule ccontr)
      assume "\<not> kr_a < kc_b"
      then have "kc_b \<le> kr_a" by simp

      have "kc_b \<noteq> kr_a"
      proof
        assume "kc_b = kr_a"
        have "act_cr (H ! kc_b) = call" using kc_b(2) unfolding match_call_def Let_def by simp
        moreover have "act_cr (H ! kr_a) = ret" using kr_a(2) unfolding match_ret_def Let_def by simp
        ultimately show False using `kc_b = kr_a` by simp
      qed
      with `kc_b \<le> kr_a` have "kc_b < kr_a" by simp

      have pid_eq: "act_pid (H ! kc_b) = act_pid (H ! kr_a)"
        using kc_b(2) kr_a(2) same_pid unfolding match_call_def match_ret_def Let_def by simp

      (* Prove the required intermediate property. Related symbols: kc_b. *)
      have "kc_b < length H" using `kc_b < kr_a` kr_a(1) by simp

      (* Proof-automation note. *)
      have "act_ssn (H ! kc_b) < act_ssn (H ! kr_a) \<or>
            (act_ssn (H ! kc_b) = act_ssn (H ! kr_a) \<and> act_cr (H ! kc_b) = call \<and> act_cr (H ! kr_a) = ret)"
        using ssn_order `kc_b < kr_a` kr_a(1) `kc_b < length H` pid_eq
        unfolding hI6_SSN_Order_def H_def by auto
      then have "act_ssn (H ! kc_b) \<le> act_ssn (H ! kr_a)" by auto

      moreover have "act_ssn (H ! kc_b) = op_ssn b" using kc_b(2) unfolding match_call_def Let_def by simp
      moreover have "act_ssn (H ! kr_a) = op_ssn a" using kr_a(2) unfolding match_ret_def Let_def by simp
      ultimately have "op_ssn b \<le> op_ssn a" by simp
      with True show False by simp
    qed

    then have "HB_Act s a b"
      unfolding HB_Act_def HB_def using kr_a(2) kc_b(2)
      using H_def by auto
    thus ?thesis by simp

  next
    case False (* Proof note. Related symbols: SSN. *)
    with distinct have "op_ssn b < op_ssn a" by simp

    have "kr_b < kc_a"
    proof (rule ccontr)
      assume "\<not> kr_b < kc_a"
      then have "kc_a \<le> kr_b" by simp

      have "kc_a \<noteq> kr_b"
      proof
        assume "kc_a = kr_b"
        have "act_cr (H ! kc_a) = call" using kc_a(2) unfolding match_call_def Let_def by simp
        moreover have "act_cr (H ! kr_b) = ret" using kr_b(2) unfolding match_ret_def Let_def by simp
        ultimately show False using `kc_a = kr_b` by simp
      qed
      with `kc_a \<le> kr_b` have "kc_a < kr_b" by simp

      have pid_eq: "act_pid (H ! kc_a) = act_pid (H ! kr_b)"
        using kc_a(2) kr_b(2) same_pid unfolding match_call_def match_ret_def Let_def by simp

      (* Prove the required intermediate property. Related symbols: kc_a. *)
      have "kc_a < length H" using `kc_a < kr_b` kr_b(1) by simp

      (* Proof-automation note. *)
      have "act_ssn (H ! kc_a) < act_ssn (H ! kr_b) \<or>
            (act_ssn (H ! kc_a) = act_ssn (H ! kr_b) \<and> act_cr (H ! kc_a) = call \<and> act_cr (H ! kr_b) = ret)"
        using ssn_order `kc_a < kr_b` kr_b(1) `kc_a < length H` pid_eq
        unfolding hI6_SSN_Order_def H_def by auto
      then have "act_ssn (H ! kc_a) \<le> act_ssn (H ! kr_b)" by auto

      moreover have "act_ssn (H ! kc_a) = op_ssn a" using kc_a(2) unfolding match_call_def Let_def by simp
      moreover have "act_ssn (H ! kr_b) = op_ssn b" using kr_b(2) unfolding match_ret_def Let_def by simp
      ultimately have "op_ssn a \<le> op_ssn b" by simp
      with `op_ssn b < op_ssn a` show False by simp
    qed

    then have "HB_Act s b a"
      unfolding HB_Act_def HB_def using kr_b(2) kc_a(2)
      using H_def by auto
    thus ?thesis by simp
  qed
qed



lemma HB_implies_idx_order:
  assumes inv_sys: "system_invariant (cs, us)"
      and hb: "HB_Act (cs, us) (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"  (* Key proof fix. Related symbols: sn2, sn1. *)
      and arr1: "CState.Q_arr cs idx1 = v1"
      and arr2: "CState.Q_arr cs idx2 = v2"
  shows "idx2 < idx1"
  using inv_sys hb arr1 arr2
  unfolding system_invariant_def hI24_HB_Implies_Idx_Order_def
  by fastforce


(* ========================================================== *)
(* Auxiliary proof material. Related symbols: SA. *)
(* Definitions and lemmas for distance and modify_lin. Related symbols: modify_lin, lin_seq. *)
(* ========================================================== *)
lemma Enq_After_Last_SA_Is_Active_Gen:
  assumes sys_inv: "system_invariant s"
  assumes mset_eq: "mset L = mset (lin_seq s)"
  assumes sa_iso: "\<forall>x. in_SA x L \<longleftrightarrow> in_SA x (lin_seq s)"
  assumes idx_valid: "i < length L"
  assumes idx_after_sa: "int i > find_last_SA L"
  assumes is_enq: "op_name (L ! i) = enq"
  assumes last_sa_prop: "\<forall>k. k < length L \<and> int k > find_last_SA L \<longrightarrow> \<not> in_SA (op_val (L ! k)) L"

  shows "L ! i \<in> active_enqs s"
proof -
  have lI1_Op_Sets_Equivalence: "lI1_Op_Sets_Equivalence s" using sys_inv unfolding system_invariant_def by simp
  have lI2_Op_Cardinality: "lI2_Op_Cardinality s" using sys_inv unfolding system_invariant_def by simp

  let ?x = "L ! i"

  (* Step 1: prove the required intermediate property. Related symbols: lin_seq. *)
  have x_in_L: "?x \<in> set L" using idx_valid nth_mem by blast
  have x_in_s: "?x \<in> set (lin_seq s)"
    using x_in_L mset_eq by (metis mset_eq_setD)

  (* Step 2: prove the required intermediate property. Related symbols: SA. *)
  have not_sa_L: "\<not> in_SA (op_val ?x) L"
    using last_sa_prop idx_valid idx_after_sa by blast

  (* Step 3: use the available invariant or hypothesis. Related symbols: lin_seq, sa_iso. *)
  have not_sa_s: "\<not> in_SA (op_val ?x) (lin_seq s)"
    using not_sa_L sa_iso by simp

  (* Step 4 of the proof. *)
  show ?thesis
    using non_SA_enqs_are_active[OF lI1_Op_Sets_Equivalence lI2_Op_Cardinality] x_in_s is_enq not_sa_s
    by blast
qed


lemma Qback_Value_Is_Valid:
  assumes INV: "system_invariant s"
  assumes RET: "DeqRetInHis s p a sn"  (* Key proof fix. *)
  shows "a \<in> Val"
proof -
  (* Step 1: extract the required facts. *)
  have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s"
    using INV unfolding system_invariant_def by blast+

  (* Happens-before reasoning. Related symbols: lI3_HB_Ret_Lin_Sync. *)
  obtain idx where idx_props: "idx < length (lin_seq s)" "op_name (lin_seq s ! idx) = deq" "op_val (lin_seq s ! idx) = a"
  proof -
    (* Happens-before reasoning. Related symbols: lI3_HB_Ret_Lin_Sync, mk_op. *)
    from lI3_HB_Ret_Lin_Sync_s RET have "\<exists>k < length (lin_seq s). lin_seq s ! k = mk_op deq a p sn"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
    then obtain k where "k < length (lin_seq s)" "lin_seq s ! k = mk_op deq a p sn" by blast
    (* Extract the required witnesses and facts. Related symbols: mk_op. *)
    thus ?thesis using that unfolding mk_op_def op_name_def op_val_def by simp
  qed

  (* Step 3: use the available invariant or hypothesis. Related symbols: lI4_FIFO_Semantics_list. *)
  obtain enq_idx where enq_idx_props: "enq_idx < length (lin_seq s)" "op_name (lin_seq s ! enq_idx) = enq" "op_val (lin_seq s ! enq_idx) = a"
  proof -
    from lI4_FIFO_Semantics_s idx_props(1) idx_props(2) idx_props(3)
    have "\<exists>k2 < idx. op_name (lin_seq s ! k2) = enq \<and> op_val (lin_seq s ! k2) = a"
      unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def Let_def by blast
    then obtain k2 where k2_props: "k2 < idx" "op_name (lin_seq s ! k2) = enq" "op_val (lin_seq s ! k2) = a"
      by blast

    have "k2 < length (lin_seq s)"
      using k2_props(1) `idx < length (lin_seq s)` by linarith

    thus ?thesis using k2_props that by blast
  qed

  let ?enq_act = "lin_seq s ! enq_idx"
  have "?enq_act \<in> OPLin s"
    unfolding OPLin_def using enq_idx_props(1) by (metis nth_mem)

  (* Step 4: perform the set/cardinality reasoning. Related symbols: lI1_Op_Sets_Equivalence. *)
  have "?enq_act \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_Op_Sets_Equivalence_s `?enq_act \<in> OPLin s` unfolding lI1_Op_Sets_Equivalence_def by blast

  moreover have "?enq_act \<notin> OP_A_deq s"
    unfolding OP_A_deq_def using enq_idx_props(2) by simp

  ultimately have "?enq_act \<in> OP_A_enq s \<union> OP_B_enq s" by blast

  (* Step 5: extract the required facts. *)
  then obtain e where e_in_his: "e \<in> set (his_seq s)" "act_name e = enq" "act_val e = a"
  proof
    assume "?enq_act \<in> OP_A_enq s"
    (* Key proof fix. *)
    then obtain p' a' sn' where "?enq_act = mk_op enq a' p' sn'" "EnqCallInHis s p' a' sn'"
      unfolding OP_A_enq_def by blast
    moreover have "a' = a" using `?enq_act = mk_op enq a' p' sn'` enq_idx_props(3)
      unfolding mk_op_def op_val_def by simp
    ultimately have "EnqCallInHis s p' a sn'" by simp

    (* History-existence checks based on SSN and set mappings. *)
    then obtain e_call where "e_call \<in> set (his_seq s)" "act_name e_call = enq" "act_val e_call = a"
      unfolding EnqCallInHis_def by blast
    thus ?thesis using that by blast
  next
    assume "?enq_act \<in> OP_B_enq s"
    (* Enqueue-side reasoning. Related symbols: OP_B_enq. *)
    then obtain p' b' sn' where "?enq_act = mk_op enq b' p' sn'" "EnqCallInHis s p' b' sn'"
      unfolding OP_B_enq_def by blast
    moreover have "b' = a" using `?enq_act = mk_op enq b' p' sn'` enq_idx_props(3)
      unfolding mk_op_def op_val_def by simp
    ultimately have "EnqCallInHis s p' a sn'" by simp

    then obtain e_call where "e_call \<in> set (his_seq s)" "act_name e_call = enq" "act_val e_call = a"
      unfolding EnqCallInHis_def by blast
    thus ?thesis using that by blast
  qed

  (* Step 6: prove the required intermediate property. Related symbols: hI20_Enq_Val_Valid. *)
  have "\<forall>ev \<in> set (his_seq s). act_name ev = enq \<longrightarrow> act_val ev \<in> Val"
    using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def
    by (metis in_set_conv_nth)

  with e_in_his show "a \<in> Val" by blast
qed


(* Proof note. Related symbols: TypeB, \<noteq>, BOT, \<in>, Val. *)
lemma TypeB_non_BOT_implies_Val:
  assumes "system_invariant s"
  assumes "TypeB s a"
  assumes "a \<noteq> BOT"
  shows "a \<in> Val"
proof -
  from assms(1) have TypeOK_s: "TypeOK s" unfolding system_invariant_def by simp

  (* Unfold the relevant definition and expose the required facts. Related symbols: TypeB. *)
  from assms(2) obtain k where "Q_arr s k = a"
    unfolding TypeB_def QHas_def by blast
  with TypeOK_s have "a \<in> Val \<union> {BOT}" unfolding TypeOK_def by force
  with assms(3) show ?thesis by simp
qed

lemma Act_Val_Is_Valid:
  assumes sys_inv: "system_invariant s"
  assumes H_def: "H = his_seq s"
  assumes b_cond: "op_name b = enq \<or> op_val b \<in> Val"
  assumes enq_in_history: "op_name b = enq \<longrightarrow> (\<exists>k < length H. act_name (H!k) = enq \<and> act_val (H!k) = op_val b)"
  shows "op_val b \<in> Val"
proof (cases "op_name b = enq")
  case True
  (* Use the relevant invariant, lemma, or hypothesis. Related symbols: hI20_Enq_Val_Valid. *)
  from True enq_in_history obtain k where
    "k < length H" "act_name (H!k) = enq" "act_val (H!k) = op_val b" by auto
  then show ?thesis
    using sys_inv unfolding system_invariant_def hI20_Enq_Val_Valid_def H_def
    by (metis (mono_tags, lifting)) (* Use the relevant invariant, lemma, or hypothesis. Related symbols: hI20_Enq_Val_Valid. *)
next
  case False
  (* Use the relevant invariant, lemma, or hypothesis. Related symbols: b_cond. *)
  (* Proof note. Related symbols: op_val, \<in>, Val. *)
  then show ?thesis using b_cond by auto
qed


lemma Act_Val_Is_Valid_Simple:
  assumes sys_inv: "system_invariant s"
  assumes H_def: "H = his_seq s"
  assumes b_unique: "op_name b = enq \<or> op_val b \<in> Val"
  (* Original source location. *)
  assumes k_valid: "k < length H"
  assumes k_match: "act_name (H!k) = op_name b"
                   "op_name b = enq \<longrightarrow> act_val (H!k) = op_val b"
  shows "op_val b \<in> Val"
using assms proof (cases "op_name b = enq")
  case True
  (* Case Enq *)
  have "act_name (H!k) = enq" using True k_match(1) by simp
  have "act_val (H!k) = op_val b" using True k_match(2) by simp
  (* Use the relevant invariant, lemma, or hypothesis. Related symbols: hI20_Enq_Val_Valid. *)
  show ?thesis
    using sys_inv `act_name (H!k) = enq` `act_val (H!k) = op_val b` k_valid
    unfolding system_invariant_def hI20_Enq_Val_Valid_def H_def
    by metis
next
  case False
  (* Case Deq *)
  then show ?thesis using b_unique by auto
qed



(* ---------------------------------------------------------------- *)
(* Prove the required intermediate property. Related symbols: SSN. *)
(* ---------------------------------------------------------------- *)
lemma lemma_Call_Before_Ret:
  assumes sys_inv: "system_invariant s"
  assumes H_def: "H = his_seq s"
  (* Proof note. Related symbols: mk_act. *)
  assumes k_call: "k_call < length H" "match_call H k_call b"
  assumes k_ret:  "k_ret < length H"  "match_ret H k_ret b"
  shows "k_call < k_ret"
proof -
  (* Step 1 of the proof. *)
  have is_ret: "act_cr (H ! k_ret) = ret" "act_pid (H ! k_ret) = op_pid b" "act_ssn (H ! k_ret) = op_ssn b"
    using k_ret(2) unfolding match_ret_def Let_def by auto

  have is_call: "act_cr (H ! k_call) = call" "act_pid (H ! k_call) = op_pid b" "act_ssn (H ! k_call) = op_ssn b"
    using k_call(2) unfolding match_call_def Let_def by auto

  (* Step 2: use the available invariant or hypothesis. Related symbols: WF, k_ret. *)
  have wf: "hI7_His_WF s" using sys_inv unfolding system_invariant_def by blast

  obtain j where j_props: "j < k_ret" "act_cr (H ! j) = call"
    "act_pid (H ! j) = op_pid b" "act_ssn (H ! j) = op_ssn b"
  proof -
    from wf k_ret(1) is_ret(1) have "\<exists>j < k_ret. act_pid (H ! j) = act_pid (H ! k_ret) \<and>
                                                 act_ssn (H ! j) = act_ssn (H ! k_ret) \<and>
                                                 act_cr (H ! j) = call"
      unfolding hI7_His_WF_def H_def Let_def by meson
    then obtain j where "j < k_ret" "act_cr (H ! j) = call"
      "act_pid (H ! j) = act_pid (H ! k_ret)" "act_ssn (H ! j) = act_ssn (H ! k_ret)"
      by blast
    thus ?thesis using is_ret(2) is_ret(3) that by simp
  qed

  (* Step 3: use the available invariant or hypothesis. Related symbols: SSN, k_call. *)
  have unique: "hI5_SSN_Unique s" using sys_inv unfolding system_invariant_def by blast
  have "j < length H" using j_props(1) k_ret(1) by simp

  have "j = k_call"
  proof (rule ccontr)
    assume "j \<noteq> k_call"
    have "act_pid (H ! j) = act_pid (H ! k_call) \<and>
          act_ssn (H ! j) = act_ssn (H ! k_call) \<and>
          act_cr (H ! j) = act_cr (H ! k_call)"
      using j_props is_call by simp

    (* History well-formedness and call/return reasoning. Related symbols: SSN_Unique. *)
    with unique `j < length H` k_call(1) `j \<noteq> k_call` show False
      unfolding hI5_SSN_Unique_def H_def by blast
  qed

  (* Step 4 of the proof. Related symbols: k_call, k_ret. *)
  thus ?thesis using `j < k_ret` by simp
qed


(* ---------------------------------------------------------------- *)
(* Happens-before reasoning. Related symbols: HB, HB_transitive_lemma. *)
(* History well-formedness and call/return reasoning. Related symbols: lemma_Call_Before_Ret. *)
(* ---------------------------------------------------------------- *)
lemma HB_transitive_lemma:
  assumes sys_inv: "system_invariant s"
  assumes H_def: "H = his_seq s"
  assumes hb_ab: "HB_Act s a b"
  assumes hb_bc: "HB_Act s b c"
  assumes b_unique: "op_name b = enq \<or> op_val b \<in> Val" (* History well-formedness and call/return reasoning. *)
  shows "HB_Act s a c"
proof -
  (* Happens-before reasoning. Related symbols: HB. *)
  obtain kr_a kc_b where ab: "kr_a < kc_b" "match_ret H kr_a a" "match_call H kc_b b"
  proof -
    from hb_ab have "\<exists>k1 k2. k1 < k2 \<and> match_ret H k1 a \<and> match_call H k2 b"
      unfolding HB_Act_def HB_def H_def[symmetric] by blast
    thus ?thesis using that by blast
  qed

  (* Happens-before reasoning. Related symbols: HB. *)
  obtain kr_b kc_c where bc: "kr_b < kc_c" "match_ret H kr_b b" "match_call H kc_c c"
  proof -
    from hb_bc have "\<exists>k1 k2. k1 < k2 \<and> match_ret H k1 b \<and> match_call H k2 c"
      unfolding HB_Act_def HB_def H_def[symmetric] by blast
    thus ?thesis using that by blast
  qed

  (* Step 3: extract the required facts. *)
  have kc_b_len: "kc_b < length H" using ab(3) unfolding match_call_def Let_def by simp
  have kr_b_len: "kr_b < length H" using bc(2) unfolding match_ret_def Let_def by simp

  (* Step 4: prove the required intermediate property. Related symbols: Call_b, Ret_b. *)
  have "kc_b < kr_b"
    using lemma_Call_Before_Ret[OF sys_inv H_def kc_b_len ab(3) kr_b_len bc(2)] .

  (* Step 5 of the proof. Related symbols: kr_a, kc_b, kr_b, kc_c, \<Longrightarrow>. *)
  have "kr_a < kc_c"
    using ab(1) `kc_b < kr_b` bc(1) by linarith

  (* Happens-before reasoning. Related symbols: HB. *)
  show ?thesis
    unfolding HB_Act_def HB_def H_def[symmetric]
    using `kr_a < kc_c` ab(2) bc(3) by blast
qed


(* ---------------------------------------------------------------- *)
(* Dequeue-side reasoning. Related symbols: \<in>, Val. *)
(* ---------------------------------------------------------------- *)
lemma LinSeq_Deq_Val_Valid:
  assumes sys_inv: "system_invariant s"
  assumes x_in: "x \<in> set (lin_seq s)"
  assumes is_deq: "op_name x = deq"
  shows "op_val x \<in> Val"
proof -
  (* Step 1: extract the required facts. *)
  have lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" and hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s"
    using sys_inv unfolding system_invariant_def by auto

  (* Step 2 of the proof. *)
  obtain k where k_bound: "k < length (lin_seq s)" and x_at_k: "lin_seq s ! k = x"
    using x_in by (meson in_set_conv_nth)

  (* Step 3: use the available invariant or hypothesis. Related symbols: lI4_FIFO_Semantics_list, k2. *)
  obtain k2 where k2_props: "k2 < k" "op_name (lin_seq s ! k2) = enq" "op_val (lin_seq s ! k2) = op_val x"
  proof -
    (* Extract the required witnesses and facts. Related symbols: lI4_FIFO_Semantics_list. *)
    from lI4_FIFO_Semantics_s k_bound have "op_name (lin_seq s ! k) = deq \<longrightarrow>
      (\<exists>k2 < k. op_name (lin_seq s ! k2) = enq \<and> op_val (lin_seq s ! k2) = op_val (lin_seq s ! k))"
      unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def Let_def by blast
    moreover have "op_name (lin_seq s ! k) = deq" using x_at_k is_deq by simp
    ultimately obtain k2 where "k2 < k" "op_name (lin_seq s ! k2) = enq" "op_val (lin_seq s ! k2) = op_val x"
      using x_at_k by blast
    thus ?thesis using that by blast
  qed

  (* Enqueue-side reasoning. *)
  let ?y = "lin_seq s ! k2"
  have "?y \<in> OPLin s" unfolding OPLin_def using k2_props(1) k_bound by auto

  (* Step 4: use the available invariant or hypothesis. Related symbols: lI1_Op_Sets_Equivalence, OP_A_deq. *)
  have "?y \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_Op_Sets_Equivalence_s `?y \<in> OPLin s` unfolding lI1_Op_Sets_Equivalence_def by blast

  moreover have "?y \<notin> OP_A_deq s"
    unfolding OP_A_deq_def using k2_props(2) by simp

  ultimately have "?y \<in> OP_A_enq s \<union> OP_B_enq s" by blast

  (* Step 5: perform the set/cardinality reasoning. *)
  then obtain e where e_in_his: "e \<in> set (his_seq s)" "act_name e = enq" "act_val e = op_val x"
  proof
    assume "?y \<in> OP_A_enq s"
    (* Key proof fix. Related symbols: SSN. *)
    then obtain p a sn where y_def: "?y = mk_op enq a p sn" and "EnqCallInHis s p a sn"
      unfolding OP_A_enq_def by blast
    moreover have "a = op_val x" using y_def k2_props(3)
      unfolding mk_op_def op_val_def by simp
    ultimately have "EnqCallInHis s p (op_val x) sn" by simp

    (* History-existence checks based on SSN and set mappings. *)
    then obtain e_call where "e_call \<in> set (his_seq s)" "act_name e_call = enq" "act_val e_call = op_val x"
      unfolding EnqCallInHis_def by blast
    thus ?thesis using that by blast
  next
    assume "?y \<in> OP_B_enq s"
    (* Enqueue-side reasoning. Related symbols: OP_B_enq. *)
    then obtain p b sn where y_def: "?y = mk_op enq b p sn" and "EnqCallInHis s p b sn"
      unfolding OP_B_enq_def by blast
    moreover have "b = op_val x" using y_def k2_props(3)
      unfolding mk_op_def op_val_def by simp
    ultimately have "EnqCallInHis s p (op_val x) sn" by simp

    (* History-existence checks based on SSN and set mappings. *)
    then obtain e_call where "e_call \<in> set (his_seq s)" "act_name e_call = enq" "act_val e_call = op_val x"
      unfolding EnqCallInHis_def by blast
    thus ?thesis using that by blast
  qed

  (* Step 6: prove the required intermediate property. Related symbols: hI20_Enq_Val_Valid. *)
  have "\<forall>ev \<in> set (his_seq s). act_name ev = enq \<longrightarrow> act_val ev \<in> Val"
    using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def
    by (metis in_set_conv_nth)

  with e_in_his show "op_val x \<in> Val"
    by auto
qed

(* ---------------------------------------------------------------- *)
(* Enqueue-side reasoning. Related symbols: \<in>, Val. *)
(* ---------------------------------------------------------------- *)
lemma LinSeq_Enq_Val_Valid:
  assumes sys_inv: "system_invariant s"
  assumes x_in: "x \<in> set (lin_seq s)"
  assumes is_enq: "op_name x = enq"
  shows "op_val x \<in> Val"
proof -
  (* Step 1: extract the required facts. *)
  have lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s"
    using sys_inv unfolding system_invariant_def by auto

  (* Step 2 of the proof. *)
  have "x \<in> OPLin s"
    unfolding OPLin_def using x_in by simp

  then have x_union: "x \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_Op_Sets_Equivalence_s unfolding lI1_Op_Sets_Equivalence_def by simp

  (* Step 3 of the proof. Related symbols: OP_A_deq. *)
  have "x \<notin> OP_A_deq s"
    unfolding OP_A_deq_def using is_enq
    by simp

  then have x_source: "x \<in> OP_A_enq s \<union> OP_B_enq s"
    using x_union by blast

  (* Step 4: perform the set/cardinality reasoning. *)
  then obtain e where e_in_his: "e \<in> set (his_seq s)" "act_name e = enq" "act_val e = op_val x"
  proof
    assume "x \<in> OP_A_enq s"
    (* Key proof fix. Related symbols: SSN. *)
    then obtain p a sn where x_def: "x = mk_op enq a p sn" and "EnqCallInHis s p a sn"
      unfolding OP_A_enq_def by blast
    moreover have "a = op_val x" using x_def
      unfolding mk_op_def op_val_def by simp
    ultimately have "EnqCallInHis s p (op_val x) sn" by simp

    (* History-existence checks based on SSN and set mappings. *)
    then obtain e_call where "e_call \<in> set (his_seq s)" "act_name e_call = enq" "act_val e_call = op_val x"
      unfolding EnqCallInHis_def by blast
    thus ?thesis using that by blast
  next
    assume "x \<in> OP_B_enq s"
    (* Enqueue-side reasoning. Related symbols: OP_B_enq. *)
    then obtain p b sn where x_def: "x = mk_op enq b p sn" and "EnqCallInHis s p b sn"
      unfolding OP_B_enq_def by blast
    moreover have "b = op_val x" using x_def
      unfolding mk_op_def op_val_def by simp
    ultimately have "EnqCallInHis s p (op_val x) sn" by simp

    (* History-existence checks based on SSN and set mappings. *)
    then obtain e_call where "e_call \<in> set (his_seq s)" "act_name e_call = enq" "act_val e_call = op_val x"
      unfolding EnqCallInHis_def by blast
    thus ?thesis using that by blast
  qed

  (* Step 5: prove the required intermediate property. Related symbols: hI20_Enq_Val_Valid. *)
  have "\<forall>ev \<in> set (his_seq s). act_name ev = enq \<longrightarrow> act_val ev \<in> Val"
    using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def
    by (metis in_set_conv_nth)

  with e_in_his show "op_val x \<in> Val" by auto
qed


lemma SetB_implies_no_deq_in_lin:
  assumes INV: "system_invariant s"
  assumes x_in_SetB: "x \<in> SetB s"
  shows "\<forall>act \<in> set (lin_seq s). op_val act = x \<longrightarrow> op_name act \<noteq> deq"
proof (intro ballI impI)
  fix act assume in_lin: "act \<in> set (lin_seq s)"
  assume val_eq: "op_val act = x"

  (* Step 1 of the proof. *)
  have I2: "lI2_Op_Cardinality s" using INV unfolding system_invariant_def by simp
  have card_is_0: "card (DeqIdxs s x) = 0"
    using I2 x_in_SetB unfolding lI2_Op_Cardinality_def by simp

  (* Step 2 of the proof. Related symbols: op_name. *)
  show "op_name act \<noteq> deq"
  proof (cases "op_name act = deq")
    case True
    (* Case A. *)

    (* List-index and filtering reasoning. Related symbols: A.1. *)
    obtain k where k_def: "k < length (lin_seq s)" "lin_seq s ! k = act"
      using in_lin by (metis in_set_conv_nth)

    (* Prove the required intermediate property. Related symbols: A.2. *)
    have k_in_set: "k \<in> DeqIdxs s x"
      unfolding DeqIdxs_def
      using k_def val_eq True by simp

    (* Prove the required intermediate property. Related symbols: A.3. *)
    have set_finite: "finite (DeqIdxs s x)"
    proof -
      have "DeqIdxs s x \<subseteq> {0..<length (lin_seq s)}"
        unfolding DeqIdxs_def by auto
      then show ?thesis
        using finite_atLeastLessThan[of 0 "length (lin_seq s)"]
        by (rule finite_subset)
    qed

    (* Set, cardinality, and uniqueness reasoning. Related symbols: A.4. *)
    have card_gt_0: "card (DeqIdxs s x) > 0"
      using set_finite k_in_set card_gt_0_iff by blast

    (* Contradiction argument. Related symbols: A.5. *)
    have False
      using card_gt_0 card_is_0 by simp

    (* Proof note. *)
    then show ?thesis by simp

  next
    case False
    (* Case B. *)
    then show ?thesis by simp
  qed
qed

lemma SetB_implies_enq_in_lin:
  assumes INV: "system_invariant s"
  assumes x_in_SetB: "x \<in> SetB s"
  shows "\<exists>k < length (lin_seq s). op_name (lin_seq s ! k) = enq \<and> op_val (lin_seq s ! k) = x"
proof -
  (* Extract the required witnesses and facts. Related symbols: lI2_Op_Cardinality. *)
  from INV have "lI2_Op_Cardinality s" unfolding system_invariant_def by simp
  (* Set, cardinality, and uniqueness reasoning. Related symbols: lI2_Op_Cardinality, SetB. *)
  with x_in_SetB have "card (EnqIdxs s x) = 1" unfolding lI2_Op_Cardinality_def by blast
  (* Set, cardinality, and uniqueness reasoning. *)
  then obtain k where "k \<in> EnqIdxs s x" by (metis card_1_singletonE insert_iff)
  thus ?thesis unfolding EnqIdxs_def by auto
qed


(* ---------------------------------------------------------------- *)
(* Enqueue-side reasoning. Related symbols: Val. *)
(* ---------------------------------------------------------------- *)
lemma HasPendingEnq_imp_Val:
  assumes "system_invariant s"
  assumes "HasPendingEnq s p a"
  shows "a \<in> Val"
proof -
  (* Step 1: extract the required facts. Related symbols: hI20_Enq_Val_Valid. *)
  have hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s"
    using assms(1) unfolding system_invariant_def by blast

  (* Step 2: extract the required facts. *)
  obtain k where k_props: "k < length (his_seq s)" "act_name (his_seq s ! k) = enq" "act_val (his_seq s ! k) = a"
  proof -
    (* Unfold the relevant definition and expose the required facts. *)
    from assms(2) have "\<exists>k < length (his_seq s). act_name (his_seq s ! k) = enq \<and> act_val (his_seq s ! k) = a"
      unfolding HasPendingEnq_def EnqCallInHis_def Let_def
      by (metis in_set_conv_nth)
    thus ?thesis using that by blast
  qed

  (* Step 3: perform the set/cardinality reasoning. *)
  let ?e = "his_seq s ! k"
  have "?e \<in> set (his_seq s)"
    using k_props(1) by simp

  (* Step 4: use the available invariant or hypothesis. Related symbols: hI20_Enq_Val_Valid. *)
  have "\<forall>e \<in> set (his_seq s). act_name e = enq \<longrightarrow> act_val e \<in> Val"
    using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def
    by (metis in_set_conv_nth)

  with `?e \<in> set (his_seq s)` have "act_val ?e \<in> Val"
    using k_props(2) by blast

  thus "a \<in> Val"
    using k_props(3) by simp
qed


(* ========================================================================= *)
(* History well-formedness and call/return reasoning. *)
(* ========================================================================= *)

(* Proof note. *)
(* Reasoning about appending one history or sequence element. *)

lemma EnqCall_mono:
  assumes "EnqCallInHis s q a sn" and "his_seq s' = his_seq s @ [e]"
  shows "EnqCallInHis s' q a sn"
  using assms unfolding EnqCallInHis_def Let_def by (auto simp: nth_append)

lemma EnqRet_mono:
  assumes "EnqRetInHis s q a sn" and "his_seq s' = his_seq s @ [e]"
  shows "EnqRetInHis s' q a sn"
  using assms unfolding EnqRetInHis_def Let_def by (auto simp: nth_append)

lemma DeqCall_mono:
  (* History well-formedness and call/return reasoning. *)
  assumes "DeqCallInHis s q sn" and "his_seq s' = his_seq s @ [e]"
  shows "DeqCallInHis s' q sn"
  using assms unfolding DeqCallInHis_def Let_def by (auto simp: nth_append)

lemma DeqRet_mono:
  assumes "DeqRetInHis s q a sn" and "his_seq s' = his_seq s @ [e]"
  shows "DeqRetInHis s' q a sn"
  using assms unfolding DeqRetInHis_def Let_def by (auto simp: nth_append)


(* Proof note. *)
(* Reasoning about appending one history or sequence element.
*)

lemma EnqCall_rev:
  assumes "EnqCallInHis s' q a sn"
    and "his_seq s' = his_seq s @ [e]"
    and "act_name e \<noteq> enq \<or> act_cr e \<noteq> call"
  shows "EnqCallInHis s q a sn"
proof -
  (* Step 1: extract the required facts. *)
  from assms(1) obtain t where t_props:
    "t < length (his_seq s')"
    "act_pid (his_seq s' ! t) = q"
    "act_name (his_seq s' ! t) = enq"
    "act_cr (his_seq s' ! t) = call"
    "act_val (his_seq s' ! t) = a"
    "act_ssn (his_seq s' ! t) = sn"
    unfolding EnqCallInHis_def Let_def
    by (metis in_set_conv_nth)

  (* Step 2: prove the required intermediate property. *)
  have "t < length (his_seq s)"
  proof (rule ccontr)
    assume "\<not> t < length (his_seq s)"
    with t_props(1) assms(2) have "t = length (his_seq s)" by simp
    hence "his_seq s' ! t = e" using assms(2) by (simp add: nth_append)
    with t_props(3,4) have "act_name e = enq" "act_cr e = call" by auto
    thus False using assms(3) by blast
  qed

  (* Step 3 of the proof. *)
  thus ?thesis
    unfolding EnqCallInHis_def Let_def
    using t_props assms(2) by (auto simp: nth_append)
qed

lemma EnqRet_rev:
  assumes "EnqRetInHis s' q a sn"
    and "his_seq s' = his_seq s @ [e]"
    and "act_name e \<noteq> enq \<or> act_cr e \<noteq> ret"
  shows "EnqRetInHis s q a sn"
proof -
  (* Step 1: extract the required facts. *)
  from assms(1) obtain t_elt where t_props_raw:
    "t_elt \<in> set (his_seq s')" "act_pid t_elt = q"
    "act_name t_elt = enq" "act_cr t_elt = ret"
    "act_val t_elt = a" "act_ssn t_elt = sn"
    unfolding EnqRetInHis_def by blast

  (* Step 2: use the available invariant or hypothesis. *)
  from t_props_raw(1) obtain t where t_def:
    "t < length (his_seq s')" "his_seq s' ! t = t_elt"
    by (auto simp: set_conv_nth)

  (* Step 3: prove the required intermediate property. *)
  have t_old: "t < length (his_seq s)"
  proof (rule ccontr)
    assume "\<not> t < length (his_seq s)"
    with t_def(1) assms(2) have "t = length (his_seq s)" by simp
    hence "his_seq s' ! t = e" using assms(2) by (simp add: nth_append)
    with t_def(2) t_props_raw(3,4) have "act_name e = enq" "act_cr e = ret" by auto
    thus False using assms(3) by blast
  qed

  (* Step 4: perform the set/cardinality reasoning. Related symbols: his_seq. *)
  show ?thesis unfolding EnqRetInHis_def
  proof (rule bexI)
    (* Prove the required intermediate property. *)
    show "his_seq s ! t \<in> set (his_seq s)"
      using t_old
      by simp

    (* Prove the required intermediate property. *)
    (* List-index and filtering reasoning. Related symbols: his_seq. *)
    show "act_pid (his_seq s ! t) = q \<and> act_ssn (his_seq s ! t) = sn \<and>
          act_name (his_seq s ! t) = enq \<and> act_cr (his_seq s ! t) = ret \<and>
          act_val (his_seq s ! t) = a"
      using t_props_raw t_def t_old assms(2)
      by (auto simp: nth_append)
  qed
qed

lemma DeqCall_rev:
  assumes "DeqCallInHis s' q sn"
    and "his_seq s' = his_seq s @ [e]"
    and "act_name e \<noteq> deq \<or> act_cr e \<noteq> call"
  shows "DeqCallInHis s q sn"
proof -
  (* Step 1: extract the required facts. Related symbols: t_elt. *)
  from assms(1) obtain t_elt where t_props_raw:
    "t_elt \<in> set (his_seq s')" "act_pid t_elt = q"
    "act_name t_elt = deq" "act_cr t_elt = call"
    "act_val t_elt = BOT" "act_ssn t_elt = sn"
    unfolding DeqCallInHis_def by blast

  (* Step 2: use the available invariant or hypothesis. Related symbols: his_seq. *)
  from t_props_raw(1) obtain t where t_def:
    "t < length (his_seq s')" "his_seq s' ! t = t_elt"
    by (auto simp: set_conv_nth)

  (* Step 3: prove the required intermediate property. *)
  have t_old: "t < length (his_seq s)"
  proof (rule ccontr)
    assume "\<not> t < length (his_seq s)"
    with t_def(1) assms(2) have "t = length (his_seq s)" by simp
    hence "his_seq s' ! t = e" using assms(2) by (simp add: nth_append)
    with t_def(2) t_props_raw(3,4) have "act_name e = deq" "act_cr e = call" by auto
    thus False using assms(3) by blast
  qed

  (* Step 4: perform the set/cardinality reasoning. *)
  show ?thesis unfolding DeqCallInHis_def
  proof (rule bexI)
    (* Prove the required intermediate property. *)
    show "his_seq s ! t \<in> set (his_seq s)"
      using t_old
      by simp

    (* Prove the required intermediate property. *)
    (* List-index and filtering reasoning. Related symbols: his_seq. *)
    show "act_pid (his_seq s ! t) = q \<and> act_ssn (his_seq s ! t) = sn \<and>
          act_name (his_seq s ! t) = deq \<and> act_cr (his_seq s ! t) = call \<and>
          act_val (his_seq s ! t) = BOT"
      using t_props_raw t_def t_old assms(2)
      by (auto simp: nth_append)
  qed
qed

lemma DeqRet_rev:
  assumes "DeqRetInHis s' q a sn"
    and "his_seq s' = his_seq s @ [e]"
    and "act_name e \<noteq> deq \<or> act_cr e \<noteq> ret"
  shows "DeqRetInHis s q a sn"
proof -
  (* Step 1: extract the required facts. Related symbols: t_elt. *)
  from assms(1) obtain t_elt where t_props_raw:
    "t_elt \<in> set (his_seq s')" "act_pid t_elt = q"
    "act_name t_elt = deq" "act_cr t_elt = ret"
    "act_val t_elt = a" "act_ssn t_elt = sn"
    unfolding DeqRetInHis_def by blast

  (* Step 2: use the available invariant or hypothesis. *)
  from t_props_raw(1) obtain t where t_def:
    "t < length (his_seq s')" "his_seq s' ! t = t_elt"
    by (auto simp: set_conv_nth)

  (* Step 3: prove the required intermediate property. *)
  have t_old: "t < length (his_seq s)"
  proof (rule ccontr)
    assume "\<not> t < length (his_seq s)"
    with t_def(1) assms(2) have "t = length (his_seq s)" by simp
    hence "his_seq s' ! t = e" using assms(2) by (simp add: nth_append)
    with t_def(2) t_props_raw(3,4) have "act_name e = deq" "act_cr e = ret" by auto
    thus False using assms(3) by blast
  qed

  (* Step 4: perform the set/cardinality reasoning. *)
  show ?thesis unfolding DeqRetInHis_def
  proof (rule bexI)
    (* Prove the required intermediate property. *)
    show "his_seq s ! t \<in> set (his_seq s)"
      using t_old by simp

    (* Use the relevant invariant, lemma, or hypothesis. *)
    show "act_pid (his_seq s ! t) = q \<and> act_ssn (his_seq s ! t) = sn \<and>
          act_name (his_seq s ! t) = deq \<and> act_cr (his_seq s ! t) = ret \<and>
          act_val (his_seq s ! t) = a"
      using t_props_raw t_def t_old assms(2)
      by (auto simp: nth_append)
  qed
qed

(* ========================================================================= *)
(* Ticket-counter freshness and ordering reasoning. Related symbols: hI22. *)
(* ========================================================================= *)
lemma hb_implies_idx_lt_i_var:
  assumes INV: "system_invariant s"
      and pc_E2: "program_counter s p = ''E2''"
      and b_in_qback: "InQBack s b"
      and b_not_new: "b \<noteq> v_var s p"
      and hb: "HB_EnqRetCall s b (v_var s p)"
  shows "Idx s b < i_var s p"
proof -
  have hI22: "hI30_Ticket_HB_Immunity s"
    using INV unfolding system_invariant_def by blast
  have pc_cond: "program_counter s p \<in> {''E2'', ''E3''}"
    using pc_E2 by simp

  (* Extract the required witnesses and facts. Related symbols: BOT. *)
  have "b \<in> Val"
  proof -
    from hb obtain p1 p2 sn1 sn2 where
      "HB_Act s (mk_op enq b p1 sn1) (mk_op enq (v_var s p) p2 sn2)"
      unfolding HB_EnqRetCall_def by blast
    then obtain k_ret where match_ret: "match_ret (his_seq s) k_ret (mk_op enq b p1 sn1)"
      unfolding HB_Act_def HB_def by blast

    have k_ret_lt: "k_ret < length (his_seq s)"
      using match_ret unfolding match_ret_def by (auto simp: Let_def)

    have val_b: "act_val (his_seq s ! k_ret) = b"
     and oper_enq: "act_name (his_seq s ! k_ret) = enq"
      using match_ret unfolding match_ret_def
      by (auto simp: Let_def mk_op_def op_val_def op_name_def op_pid_def op_ssn_def)

    show "b \<in> Val"
      using INV k_ret_lt val_b oper_enq
      unfolding system_invariant_def hI20_Enq_Val_Valid_def
      by force
  qed
  hence b_not_bot: "b \<noteq> BOT" unfolding Val_def BOT_def by auto

  (* Prove the required intermediate property. Related symbols: TypeB. *)
  show ?thesis
    using hI22 pc_cond b_in_qback b_not_bot b_not_new hb
    unfolding hI30_Ticket_HB_Immunity_def by blast
qed

lemma hI3_L0_E_Phase_BoundsI:
  assumes "\<forall>q. program_counter s q = ''L0'' \<longrightarrow> (\<forall>a. \<not> HasPendingEnq s q a) \<and> \<not> HasPendingDeq s q"
  assumes "\<forall>q. program_counter s q = ''L0'' \<longrightarrow>
             length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
             length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
  assumes "\<forall>q. program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longrightarrow> v_var s q < V_var s"
  assumes "\<forall>k<length (his_seq s).
             act_name (his_seq s ! k) = enq \<and> act_cr (his_seq s ! k) = call \<longrightarrow>
             act_val (his_seq s ! k) < V_var s"
  assumes "\<forall>k. Qback_arr s k = BOT \<or> Qback_arr s k < V_var s"
  shows "hI3_L0_E_Phase_Bounds s"
  using assms
  unfolding hI3_L0_E_Phase_Bounds_def
  by blast

lemma hI3_L0_E_Phase_Bounds_L0_pending:
  assumes "hI3_L0_E_Phase_Bounds s"
  assumes "program_counter s q = ''L0''"
  shows "(\<forall>a. \<not> HasPendingEnq s q a) \<and> \<not> HasPendingDeq s q"
  using assms
  unfolding hI3_L0_E_Phase_Bounds_def
  by blast

lemma hI3_L0_E_Phase_Bounds_L0_deq_balanced:
  assumes "hI3_L0_E_Phase_Bounds s"
  assumes "program_counter s q = ''L0''"
  shows "length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
         length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
  using assms
  unfolding hI3_L0_E_Phase_Bounds_def
  by blast

(* Extract the required witnesses and facts. *)
lemma hI3_L0_E_Phase_Bounds_E_v_var_lt:
  assumes "hI3_L0_E_Phase_Bounds s"
  assumes "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
  shows "v_var s q < V_var s"
  using assms
  unfolding hI3_L0_E_Phase_Bounds_def
  by blast

lemma hI3_L0_E_Phase_Bounds_hist_call_lt:
  assumes "hI3_L0_E_Phase_Bounds s"
  assumes "k < length (his_seq s)"
  shows "act_name (his_seq s ! k) = enq \<and> act_cr (his_seq s ! k) = call \<longrightarrow>
         act_val (his_seq s ! k) < V_var s"
  using assms
  unfolding hI3_L0_E_Phase_Bounds_def
  by blast

lemma hI3_L0_E_Phase_Bounds_qback_cases:
  assumes "hI3_L0_E_Phase_Bounds s"
  shows "Qback_arr s k = BOT \<or> Qback_arr s k < V_var s"
  using assms
  unfolding hI3_L0_E_Phase_Bounds_def
  by blast

(* Extract the required witnesses and facts. *)
lemma system_invariantE:
  assumes "system_invariant s"
  obtains
    "TypeOK s" "sI1_Zero_Index_BOT s"
    "sI2_X_var_Upper_Bound s" "sI3_E2_Slot_Exclusive s" "sI4_E3_Qback_Written s" "sI5_D2_Local_Bound s" "sI6_D3_Scan_Pointers s" "sI7_D4_Deq_Result s" "hI3_L0_E_Phase_Bounds s" "sI8_Q_Qback_Sync s" "sI9_Qback_Discrepancy_E3 s" "sI10_Qback_Unique_Vals s"  "hI2_SSN_Bounds s"  "sI11_x_var_Scope s"
    "hI1_E_Phase_Pending_Enq s"   "sI12_D3_Scanned_Prefix s" "hI4_X_var_Lin_Sync s"
    "hI7_His_WF s" "hI8_Val_Unique s"  "hI5_SSN_Unique s" "hI6_SSN_Order s"
    "hI9_Deq_Ret_Unique s" "hI10_Enq_Call_Existence s" "hI11_Enq_Ret_Existence s" "hI12_D_Phase_Pending_Deq s"  "hI13_Qback_Deq_Sync s" "hI14_Pending_Enq_Qback_Exclusivity s" "hI15_Deq_Result_Exclusivity s" "hI16_BO_BT_No_HB s" "hI17_BT_BT_No_HB s" "hI18_Idx_Order_No_Rev_HB s" "hI19_Scanner_Catches_Later_Enq s" "hI20_Enq_Val_Valid s"
    "hI21_Ret_Implies_Call s" "hI22_Deq_Local_Pattern s" "hI23_Deq_Call_Ret_Balanced s" "hI24_HB_Implies_Idx_Order s" "hI25_Enq_Call_Ret_Balanced s" "hI26_DeqRet_D4_Mutex s"
    "hI27_Pending_PC_Sync s" "hI28_Fresh_Enq_Immunity s"  "hI29_E2_Scanner_Immunity s" "hI30_Ticket_HB_Immunity s"
    "lI1_Op_Sets_Equivalence s" "lI2_Op_Cardinality s" "lI3_HB_Ret_Lin_Sync s" "lI4_FIFO_Semantics s" "lI5_SA_Prefix s"  "lI6_D4_Deq_Linearized s" "lI7_D4_Deq_Deq_HB s"  "lI8_D3_Deq_Returned s" "lI9_D1_D2_Deq_Returned s"
    "data_independent (lin_seq s)"
proof -
  (* Proof note. *)
  from assms have INV:
    "TypeOK s \<and> sI1_Zero_Index_BOT s \<and>
     sI2_X_var_Upper_Bound s \<and> sI3_E2_Slot_Exclusive s \<and> sI4_E3_Qback_Written s \<and> sI5_D2_Local_Bound s \<and> sI6_D3_Scan_Pointers s \<and> sI7_D4_Deq_Result s \<and> hI3_L0_E_Phase_Bounds s \<and> sI8_Q_Qback_Sync s \<and> sI9_Qback_Discrepancy_E3 s \<and> sI10_Qback_Unique_Vals s \<and> hI2_SSN_Bounds s \<and> sI11_x_var_Scope s \<and>
     hI1_E_Phase_Pending_Enq s \<and> sI12_D3_Scanned_Prefix s \<and> hI4_X_var_Lin_Sync s \<and>
     hI7_His_WF s \<and> hI8_Val_Unique s \<and> hI5_SSN_Unique s \<and> hI6_SSN_Order s \<and>
     hI9_Deq_Ret_Unique s \<and> hI10_Enq_Call_Existence s \<and> hI11_Enq_Ret_Existence s \<and> hI12_D_Phase_Pending_Deq s \<and> hI13_Qback_Deq_Sync s \<and> hI14_Pending_Enq_Qback_Exclusivity s \<and> hI15_Deq_Result_Exclusivity s \<and> hI16_BO_BT_No_HB s \<and> hI17_BT_BT_No_HB s \<and> hI18_Idx_Order_No_Rev_HB s \<and> hI19_Scanner_Catches_Later_Enq s \<and>
     hI20_Enq_Val_Valid s \<and> hI21_Ret_Implies_Call s \<and> hI22_Deq_Local_Pattern s  \<and> hI23_Deq_Call_Ret_Balanced s  \<and> hI24_HB_Implies_Idx_Order s  \<and> hI25_Enq_Call_Ret_Balanced s \<and> hI26_DeqRet_D4_Mutex s  \<and>
     hI27_Pending_PC_Sync s \<and> hI28_Fresh_Enq_Immunity s  \<and> hI29_E2_Scanner_Immunity s  \<and> hI30_Ticket_HB_Immunity s  \<and>
     lI1_Op_Sets_Equivalence s \<and> lI2_Op_Cardinality s \<and> lI3_HB_Ret_Lin_Sync s \<and> lI4_FIFO_Semantics s \<and> lI5_SA_Prefix s \<and>  lI6_D4_Deq_Linearized s \<and>  lI7_D4_Deq_Deq_HB s \<and> lI8_D3_Deq_Returned s \<and> lI9_D1_D2_Deq_Returned s \<and>
     data_independent (lin_seq s)"
    unfolding system_invariant_def by simp

  (* Proof-automation note. *)
  from INV show ?thesis
    using that by blast
qed

end
