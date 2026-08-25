(* D2 transition rule of system-invariant preservation proof *)
theory D2Proof
  imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    Termination
    DeqLib
    EnqLib
    D3Lemmas
begin

lemma D2_preserves_invariant:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_D2 p s s'"
  shows "system_invariant s'"
proof -
  (* 0. definitiononly as use *)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def
                lin_seq_def his_seq_def
  have INV_s: "system_invariant s" using INV by simp

  (* 1. extract the old stateinvariantguards *)
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
   and uI1_USpec_EffOps_Lin_s: "uI1_USpec_EffOps_Lin s"
   and uI2_USpec_E1UE2_s: "uI2_USpec_E1UE2 s"
   and uI3_USpec_D3UD2_s: "uI3_USpec_D3UD2 s"
    using INV unfolding system_invariant_def by auto

(* 2. extractglobal fact (Note: in D2 in l_var, i_var as global) *)
  have step_facts [simp]:
    "his_seq s' = his_seq s"
    "lin_seq s' = lin_seq s"
    "Q_arr s' = Q_arr s"
    "Qback_arr s' = Qback_arr s"
    "v_var s' = v_var s"
    "x_var s' = x_var s"
    "i_var s' = i_var s"
    "l_var s' = l_var s"
    "X_var s' = X_var s"
    "V_var s' = V_var s"
    "snd s' = snd s"
    "program_counter s p = ''D2'' "
    using STEP unfolding Sys_D2_def C_D2_def bridge by (auto simp: prod_eq_iff split: if_splits)

  (* Extract D2 of branch *)
  have branch_facts [simp]:
    "l_var s p = 1 \<Longrightarrow> program_counter s' p = ''D1'' "
    "l_var s p = 1 \<Longrightarrow> j_var s' p = j_var s p"
    "l_var s p \<noteq> 1 \<Longrightarrow> program_counter s' p = ''D3'' "
    "l_var s p \<noteq> 1 \<Longrightarrow> j_var s' p = 1"
    using STEP unfolding Sys_D2_def C_D2_def bridge by (auto split: if_splits)

  (* Extract its process of *)
  have other_facts [simp]:
    "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    "\<And>q. q \<noteq> p \<Longrightarrow> j_var s' q = j_var s q"
    using STEP unfolding Sys_D2_def C_D2_def bridge by (auto split: if_splits)

  (* 2. PC prove (branch) *)
  have pc_s': "program_counter s' = (program_counter s)(p := if l_var s p = 1 then ''D1'' else ''D3'')"
    using STEP unfolding Sys_D2_def C_D2_def bridge by (auto simp: ext split: if_splits)

  have pc_p_not_D4: "program_counter s' p \<noteq> ''D4'' "
    using pc_s' by auto

(* PC equivalenceprove (D2: note p in D1, D2, D3) *)
  have pc_eqs [simp]:
    "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
    "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'')"
    "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'')"
    "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
    "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    "\<And>q. (program_counter s' q \<in> {''E2'', ''E3''}) = (program_counter s q \<in> {''E2'', ''E3''})"
  proof -
    fix q
    (* D2 in, p of PC does not into *)
    have "program_counter s' p \<notin> {''L0'', ''E1'', ''E2'', ''E3'', ''D4''}"
      using STEP unfolding Sys_D2_def C_D2_def bridge by (auto split: if_splits)
    thus "(program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
         "(program_counter s' q = ''E1'') = (program_counter s q = ''E1'')"
         "(program_counter s' q = ''E2'') = (program_counter s q = ''E2'')"
         "(program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
         "(program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
         "(program_counter s' q \<in> {''E2'', ''E3''}) = (program_counter s q \<in> {''E2'', ''E3''})"
      using step_facts(12) other_facts(1)[of q] by (cases "q = p", auto)+
  qed

  (* 3. prove set of *)
  have typeb_eq: "\<And>x. TypeB s' x = TypeB s x"
  proof -
    fix x
    have "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x) \<longleftrightarrow> (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x)"
    proof
      assume "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x"
      then obtain q where "program_counter s' q = ''E2'' " "v_var s' q = x" by blast
      moreover have "q \<noteq> p" using `program_counter s' q = ''E2'' ` step_facts branch_facts by force
      ultimately show "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x" using step_facts other_facts by auto
    next
      assume "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = x"
      then obtain q where "program_counter s q = ''E2'' " "v_var s q = x" by blast
      moreover have "q \<noteq> p" using `program_counter s q = ''E2'' ` step_facts by auto
      ultimately show "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = x" using step_facts other_facts by metis
    qed
    thus "TypeB s' x = TypeB s x" unfolding TypeB_def QHas_def step_facts by simp
  qed

  have typebt_eq: "\<And>x. TypeBT s' x = TypeBT s x"
  proof -
    fix x
    have idx_eq: "Idx s' x = Idx s x" unfolding Idx_def AtIdx_def step_facts by simp

    show "TypeBT s' x = TypeBT s x"
    proof (cases "\<forall>k < Idx s x. Q_arr s k = BOT")
      case True
      (* Case 1: ifprefix as BOT, TypeBT_def in of \<or> left into, *)
      thus ?thesis unfolding TypeBT_def InQBack_def typeb_eq idx_eq step_facts by auto
    next
      case False
      (* Case 2: if \<or> left into, we prove right of \<exists>q *)
      have "(\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)) \<longleftrightarrow>
            (\<exists>q. program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT))"
      proof
         (* Derivation: if s' in of q *)
         assume "\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)"
         then obtain q where q_props:
           "program_counter s' q = ''D3'' "
           "j_var s' q \<le> Idx s' x"
           "Idx s' x < l_var s' q"
           "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT" by blast

         (* Core: prove q definitelyimpossible is D2 enter D3 of process p *)
         have "q \<noteq> p"
         proof
           assume "q = p"
           (* Since q = p, D2 of branch, its j_var be as 1 *)
           hence j_is_1: "j_var s' q = 1"
             using q_props(1) branch_facts by fastforce

           (* Since j_var=1, q_props(4), then [1, Idx) in s' (s) in as BOT *)
           (* Because Q_arr 0 as BOT (sI1_Zero_Index_BOT), can with derivation out [0, Idx) as BOT *)
           have "\<forall>k < Idx s x. Q_arr s k = BOT"
           proof (intro allI impI)
              fix k assume "k < Idx s x"
              show "Q_arr s k = BOT"
              proof (cases "k = 0")
                 case True thus ?thesis using sI1_Zero_Index_BOT_s unfolding sI1_Zero_Index_BOT_def by simp
              next
                 case False
                 hence "1 \<le> k" by simp
                 thus ?thesis using `k < Idx s x` q_props(4) j_is_1 idx_eq step_facts by auto
              qed
           qed
           (* And when before in False branch(prefix as BOT)contradiction! *)
           thus False using False by simp
         qed

         (* Since already prove q \<noteq> p, then q in s in one also in D3, andall *)
         thus "\<exists>q. program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT)"
           using q_props idx_eq step_facts other_facts by auto
      next
         (* Derivation: if s in of q *)
         assume "\<exists>q. program_counter s q = ''D3'' \<and> j_var s q \<le> Idx s x \<and> Idx s x < l_var s q \<and> (\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT)"
         then obtain q where q_props:
           "program_counter s q = ''D3'' "
           "j_var s q \<le> Idx s x"
           "Idx s x < l_var s q"
           "\<forall>k. j_var s q \<le> k \<and> k < Idx s x \<longrightarrow> Q_arr s k = BOT" by blast

         (* Because p in old state s in D2, therefore q in D3 necessarily q \<noteq> p *)
         have "q \<noteq> p" using q_props(1) step_facts(12) by auto

         (* , q in s' in is *)
         thus "\<exists>q. program_counter s' q = ''D3'' \<and> j_var s' q \<le> Idx s' x \<and> Idx s' x < l_var s' q \<and> (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' x \<longrightarrow> Q_arr s' k = BOT)"
           using q_props idx_eq step_facts other_facts by metis
      qed
      thus ?thesis unfolding TypeBT_def InQBack_def typeb_eq idx_eq step_facts by simp
    qed
  qed

  have set_facts [simp]:
    "SetA s' = SetA s" "SetB s' = SetB s" "SetBT s' = SetBT s" "SetBO s' = SetBO s"
    "\<And>x. TypeB s' x = TypeB s x" "\<And>x. TypeBT s' x = TypeBT s x"
    unfolding SetA_def SetB_def SetBT_def SetBO_def TypeA_def TypeBO_def InQBack_def QHas_def
    using typeb_eq typebt_eq step_facts by auto

  have s_var_eq [simp]: "s_var s' = s_var s"
    using STEP
    unfolding Sys_D2_def C_D2_def bridge s_var_def
    by (auto simp: ext split: if_splits)

(* --- basic and --- *)
  have "TypeOK s'"
  proof -
    (* 1. Val set of fact *)
    have val_1: "1 \<in> Val" unfolding Val_def by auto

    (* 2. prove PC validity (use the previously of pc_ok) *)
    have pc_ok: "\<forall>q. program_counter s' q \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
    proof (intro allI)
      fix q show "program_counter s' q \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
      proof (cases "q = p")
        case True thus ?thesis using branch_facts by (cases "l_var s p = 1", auto)
      next
        case False thus ?thesis using TypeOK_s other_facts unfolding TypeOK_def by auto
      qed
    qed

    (* 3. prove j_var validity (splitbranch with) *)
    have j_ok: "\<forall>q. j_var s' q = BOT \<or> j_var s' q \<in> Val"
    proof (intro allI)
      fix q
      show "j_var s' q = BOT \<or> j_var s' q \<in> Val"
      proof (cases "q = p")
        case True
        (* Q = p, l_var of value one *)
        show ?thesis
        proof (cases "l_var s p = 1")
          case True_l: True
          (* Branch 1: l_var = 1, j_var preserve *)
          hence "j_var s' q = j_var s p" using branch_facts True by simp
          thus ?thesis using TypeOK_s unfolding TypeOK_def by auto
        next
          case False_l: False
          (* Branch 2: l_var \<noteq> 1, j_var be as 1 *)
          hence "j_var s' q = 1" using branch_facts True by simp
          thus ?thesis using val_1 by simp
        qed
      next
        case False
        (* Q \<noteq> p, old statefact *)
        thus ?thesis using TypeOK_s other_facts unfolding TypeOK_def by auto
      qed
    qed

    have sn_ok: "\<forall>q. s_var s' q \<in> Val"
    proof
      fix q
      have "s_var s' q = s_var s q"
        by simp
      then show "s_var s' q \<in> Val"
        using TypeOK_s
        unfolding TypeOK_def
        by auto
    qed

    (* 5. prove TypeOK *)
    show ?thesis
      using TypeOK_s step_facts pc_ok j_ok sn_ok unfolding TypeOK_def by auto
  qed

  have "sI1_Zero_Index_BOT s'" using sI1_Zero_Index_BOT_s unfolding sI1_Zero_Index_BOT_def by simp
  have "sI2_X_var_Upper_Bound s'" using sI2_X_var_Upper_Bound_s unfolding sI2_X_var_Upper_Bound_def by simp

  (* SI3_E2_Slot_Exclusive/sI4_E3_Qback_Written/sI5_D2_Local_Bound/sI7_D4_Deq_Result: p in corresponds to of, and, *)
  have "sI3_E2_Slot_Exclusive s'" using INV_s pc_s' step_facts unfolding system_invariant_def sI3_E2_Slot_Exclusive_def by (auto simp: pc_p_not_D4)
  have "sI4_E3_Qback_Written s'" using INV_s pc_s' step_facts unfolding system_invariant_def sI4_E3_Qback_Written_def by (auto simp: pc_p_not_D4)
  have "sI5_D2_Local_Bound s'" using INV_s pc_s' step_facts unfolding system_invariant_def sI5_D2_Local_Bound_def by (auto simp: pc_p_not_D4)

  have "sI6_D3_Scan_Pointers s'"
  proof -
    have "\<forall>q. program_counter s' q = ''D3'' \<longrightarrow> j_var s' q \<in> Val \<and> l_var s' q \<in> Val \<and> 1 \<le> j_var s' q \<and> j_var s' q < l_var s' q \<and> l_var s' q \<le> X_var s'"
    proof (intro allI impI)
       fix q assume q_D3: "program_counter s' q = ''D3'' "
       show "j_var s' q \<in> Val \<and> l_var s' q \<in> Val \<and> 1 \<le> j_var s' q \<and> j_var s' q < l_var s' q \<and> l_var s' q \<le> X_var s'"
       proof (cases "q = p")
         case True
         have lp_neq_1: "l_var s p \<noteq> 1" using True q_D3 branch_facts by (auto split: if_splits)
         have j_is_1: "j_var s' p = 1" using True lp_neq_1 branch_facts by simp
         have "l_var s p \<in> Val \<and> 1 \<le> l_var s p \<and> l_var s p \<le> X_var s" using sI5_D2_Local_Bound_s step_facts unfolding sI5_D2_Local_Bound_def by auto
         thus ?thesis using True j_is_1 lp_neq_1 step_facts unfolding Val_def by auto
       next
         case False
         thus ?thesis using sI6_D3_Scan_Pointers_s unfolding sI6_D3_Scan_Pointers_def step_facts other_facts q_D3
           using q_D3 by auto
       qed
    qed
    thus ?thesis unfolding sI6_D3_Scan_Pointers_def by simp
  qed

  have "sI7_D4_Deq_Result s'" using INV_s pc_s' step_facts unfolding system_invariant_def sI7_D4_Deq_Result_def by (auto simp: pc_p_not_D4)

  (* ========================================================================= *)
  (* HI3_L0_E_Phase_Bounds: new and L0 empty guards (D2 state transition) *)
  (* ========================================================================= *)

  have "hI3_L0_E_Phase_Bounds s'"
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    have q_ne_p: "q \<noteq> p"
      using 1 step_facts
      by auto
    have pc_s: "program_counter s q = ''L0''"
      using 1 q_ne_p other_facts
      by auto
    have old_pending: "(\<forall>a. \<not> HasPendingEnq s q a) \<and> \<not> HasPendingDeq s q"
      using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s pc_s] .

    show ?case
    proof (intro conjI allI)
      fix a
      from old_pending show "\<not> HasPendingEnq s' q a"
        using HasPendingEnq_his_eq s_var_eq step_facts(1)
        by presburger
    next
      from old_pending show "\<not> HasPendingDeq s' q"
        using HasPendingDeq_his_eq s_var_eq step_facts(1)
        by presburger
    qed
  next
    case (2 q)
    have q_ne_p: "q \<noteq> p"
      using 2 step_facts
      by auto
    have "program_counter s q = ''L0''"
      using 2 q_ne_p other_facts
      by auto
    then show ?case
      using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s]
      by simp
  next
    case (3 q)
    have q_ne_p: "q \<noteq> p"
      using 3 step_facts
      by auto
    have "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using 3 q_ne_p other_facts
      by auto
    then show ?case
      using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s]
      by auto
  next
    case (4 k)
    then show ?case
      using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s]
      by auto
  next
    case (5 k)
    then show ?case
      using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s]
      by auto
  qed

  have "sI8_Q_Qback_Sync s'" using sI8_Q_Qback_Sync_s unfolding sI8_Q_Qback_Sync_def by simp
  have "sI9_Qback_Discrepancy_E3 s'" using sI9_Qback_Discrepancy_E3_s unfolding sI9_Qback_Discrepancy_E3_def by auto
  have "sI10_Qback_Unique_Vals s'" using sI10_Qback_Unique_Vals_s unfolding sI10_Qback_Unique_Vals_def by simp

  have "hI2_SSN_Bounds s'" using hI2_SSN_Bounds_s unfolding hI2_SSN_Bounds_def s_var_def step_facts
    using s_var_def s_var_eq by auto

  have "sI11_x_var_Scope s'" using INV_s pc_s' step_facts unfolding system_invariant_def sI11_x_var_Scope_def by auto

  have "hI1_E_Phase_Pending_Enq s'"
    using hI1_E_Phase_Pending_Enq_s step_facts pc_eqs
    unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def EnqCallInHis_def s_var_def Let_def
    using s_var_def s_var_eq by auto

  have "sI12_D3_Scanned_Prefix s'"
  proof -
    have core: "\<And>q. program_counter s' q = ''D3'' \<Longrightarrow> \<forall>k < j_var s' q. Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
    proof -
      fix q assume q_D3: "program_counter s' q = ''D3'' "
      show "\<forall>k < j_var s' q. Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
      proof (cases "q = p")
        case True
        hence j1: "j_var s' q = 1" using q_D3 branch_facts by fastforce
        show ?thesis proof (intro allI impI) fix k assume "k < j_var s' q" hence "k = 0" using j1 by simp
          thus "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)" using sI1_Zero_Index_BOT_s step_facts unfolding sI1_Zero_Index_BOT_def by simp qed
      next
        case False thus ?thesis using sI12_D3_Scanned_Prefix_s other_facts unfolding sI12_D3_Scanned_Prefix_def step_facts set_facts q_D3
          using QHas_def TypeB_def by blast
      qed
    qed
    thus ?thesis unfolding sI12_D3_Scanned_Prefix_def by (auto simp: core)
  qed

  (* ========================================================================= *)
  (* HI4_X_var_Lin_Sync: physical- mappingconsistency (D1 state transition) *)
  (* ========================================================================= *)
  have "hI4_X_var_Lin_Sync s'"
  proof -
    have X_var_eq: "X_var s' = X_var s" using step_facts by simp
    have lin_seq_eq: "lin_seq s' = lin_seq s" using step_facts by simp
    have slots_eq: "E2SlotCount s' = E2SlotCount s"
      apply (rule E2SlotCount_cong)
      using X_var_eq apply simp
      using pc_eqs apply simp
      using step_facts apply simp
      done
    show ?thesis
      using hI4_X_var_Lin_Sync_s X_var_eq lin_seq_eq slots_eq
      unfolding hI4_X_var_Lin_Sync_def LinEnqCount_def
      by auto
  qed

  have "hI7_His_WF s'" using hI7_His_WF_s unfolding hI7_His_WF_def step_facts by simp
  have "hI8_Val_Unique s'" using hI8_Val_Unique_s unfolding hI8_Val_Unique_def by simp
  have "hI5_SSN_Unique s'" using hI5_SSN_Unique_s unfolding hI5_SSN_Unique_def step_facts by simp
  have "hI6_SSN_Order s'" using hI6_SSN_Order_s unfolding hI6_SSN_Order_def step_facts by simp

  have "hI9_Deq_Ret_Unique s'" using hI9_Deq_Ret_Unique_s unfolding hI9_Deq_Ret_Unique_def by simp



  have "hI10_Enq_Call_Existence s'"
    using hI10_Enq_Call_Existence_s
    unfolding hI10_Enq_Call_Existence_def EnqCallInHis_def Let_def
    by simp

  have "hI11_Enq_Ret_Existence s'"
    using hI11_Enq_Ret_Existence_s step_facts
    unfolding hI11_Enq_Ret_Existence_def EnqCallInHis_def EnqRetInHis_def s_var_def Let_def
    using s_var_def s_var_eq by auto


(* HI12_D_Phase_Pending_Deq: and start dequeueoperation of consistency prove *)
  have "hI12_D_Phase_Pending_Deq s'"
  proof -
    (* 1: in heredefinitely unfold HasPendingDeq_def, it of " outside " *)
    show ?thesis
      unfolding hI12_D_Phase_Pending_Deq_def
    proof (intro allI impI)
      fix q
      assume pc_q_s': "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"

      (* 2: because outside, show precise goal, match *)
      show "HasPendingDeq s' q"
      proof (cases "q = p")
        case True
        (* 1. of process p *)
        have "program_counter s p = ''D2'' " using step_facts by simp
        (* Extract p in old state of HasPendingDeq *)
        hence p_pend: "HasPendingDeq s p" using hI12_D_Phase_Pending_Deq_s unfolding hI12_D_Phase_Pending_Deq_def by blast

        (* 3: in prove of last one, then inside outside definitionall, for auto close the goal directly *)
        thus ?thesis
          using True step_facts p_pend
          unfolding HasPendingDeq_def DeqCallInHis_def Let_def
          using s_var_eq by presburger
      next
        case False
        (* 2. of its process q *)
        hence "program_counter s q = program_counter s' q" by simp
        with pc_q_s' have "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
          by metis
        hence q_pend: "HasPendingDeq s q" using hI12_D_Phase_Pending_Deq_s unfolding hI12_D_Phase_Pending_Deq_def by blast

        thus ?thesis
          using False step_facts other_facts q_pend
          unfolding HasPendingDeq_def DeqCallInHis_def Let_def
          using s_var_eq by presburger
      qed
    qed
  qed

  have "hI13_Qback_Deq_Sync s'" using hI13_Qback_Deq_Sync_s unfolding hI13_Qback_Deq_Sync_def DeqRetInHis_def by auto

(* HI14_Pending_Enq_Qback_Exclusivity: and start enqueueoperation of consistency replace *)
  have "hI14_Pending_Enq_Qback_Exclusivity s'"
  proof -
    (* 1. prove of " this " in s and s' complete *)
    have eq_pend_enq: "\<And>q a. HasPendingEnq s' q a = HasPendingEnq s q a"
      unfolding HasPendingEnq_def EnqCallInHis_def s_var_def Let_def using step_facts
      using s_var_def s_var_eq by presburger

    (* 2. extract the old state of hI14_Pending_Enq_Qback_Exclusivity fact *)
    note old_hI14_Pending_Enq_Qback_Exclusivity = hI14_Pending_Enq_Qback_Exclusivity_s[unfolded hI14_Pending_Enq_Qback_Exclusivity_def]

    (* 3. one: unfold hI14_Pending_Enq_Qback_Exclusivity s', use and pc_eqs replace as old state *)
    show ?thesis
      using old_hI14_Pending_Enq_Qback_Exclusivity
      unfolding hI14_Pending_Enq_Qback_Exclusivity_def
      using eq_pend_enq by force
  qed


(* HI15_Deq_Result_Exclusivity: Deq of global replace (already remove definition) *)
  have "hI15_Deq_Result_Exclusivity s'"
  proof -
    (* 1. prove of " this " in old state and new state complete *)
    have eq_deq_ret: "\<And>q a x. DeqRetInHis s' q a x = DeqRetInHis s q a x"
      unfolding DeqRetInHis_def s_var_def Let_def using step_facts by simp

    (* Unfold HasPendingDeq_def, use step_facts (his_seq and snd of) close immediately *)
    have eq_pend_deq: "\<And>q. HasPendingDeq s' q = HasPendingDeq s q"
      unfolding HasPendingDeq_def s_var_def Let_def using step_facts
      using DeqCallInHis_def
      using s_var_def s_var_eq by auto

    (* 2. extract the old state of hI15_Deq_Result_Exclusivity fact *)
    note old_hI15_Deq_Result_Exclusivity = hI15_Deq_Result_Exclusivity_s[unfolded hI15_Deq_Result_Exclusivity_def]

    (* 3. one: unfold hI15_Deq_Result_Exclusivity s', use and global replace as old state *)
    show ?thesis
      using old_hI15_Deq_Result_Exclusivity
      unfolding hI15_Deq_Result_Exclusivity_def
      using eq_deq_ret eq_pend_deq pc_eqs(5) step_facts(3,6)
      by presburger
  qed

  have "hI16_BO_BT_No_HB s'" using hI16_BO_BT_No_HB_s unfolding hI16_BO_BT_No_HB_def HB_EnqRetCall_def HB_Act_def by simp
  have "hI17_BT_BT_No_HB s'" using hI17_BT_BT_No_HB_s unfolding hI17_BT_BT_No_HB_def HB_EnqRetCall_def HB_Act_def by simp
  have "hI18_Idx_Order_No_Rev_HB s'" using hI18_Idx_Order_No_Rev_HB_s unfolding hI18_Idx_Order_No_Rev_HB_def HB_EnqRetCall_def HB_Act_def InQBack_def Idx_def AtIdx_def by simp

(* ========================================================================= *)
  (* HI19_Scanner_Catches_Later_Enq: newversionsimplified definition (D2 state transition - p enter D3 of boundary) *)
  (* ========================================================================= *)
  have "hI19_Scanner_Catches_Later_Enq s'"
  proof (unfold hI19_Scanner_Catches_Later_Enq_def, intro allI impI, goal_cases)
    case (1 a b)
    (* 1. extractgoal in of 6 coreprecondition (precise newdefinition) *)
    from 1 have inqa': "InQBack s' a" by blast
    from 1 have inqb': "InQBack s' b" by blast
    from 1 have tba': "TypeB s' a" by blast
    from 1 have tbb': "TypeB s' b" by blast
    from 1 have idx_lt': "Idx s' a < Idx s' b" by blast
    from 1 have ex_q': "\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
                            Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q" by blast

    (* 2. enter large branch: process q is as when before process p *)
    show "\<not> HB_EnqRetCall s' a b"
    proof -
      from ex_q' obtain q where q_props:
        "HasPendingDeq s' q" "program_counter s' q = ''D3'' "
        "Idx s' a < j_var s' q" "j_var s' q \<le> Idx s' b" "Idx s' b < l_var s' q" by blast

      show ?thesis
      proof (cases "q = p")
        case True
        (* --- branch 1: q = p, usephysical (Idx a = 0) --- *)
        show ?thesis
        proof (rule notI)
          assume hb: "HB_EnqRetCall s' a b"

          (* Because q = p enter D3, therefore it of j_var be as 1 *)
          have j_is_1: "j_var s' p = 1"
            using True q_props(2) STEP unfolding Sys_D2_def C_D2_def Let_def
            using branch_facts(4) by fastforce
          have idx_a_0: "Idx s' a = 0"
            using q_props(3) True j_is_1 by simp

          have "Qback_arr s' (Idx s' a) = a"
            using inqa' unfolding InQBack_def Idx_def AtIdx_def by (rule someI_ex)
          hence a_bot: "a = BOT"
            using idx_a_0 sI1_Zero_Index_BOT_s step_facts unfolding sI1_Zero_Index_BOT_def by auto

          (* Actual of contradiction: a = BOT, but a and HB_EnqRetCall, note it in history in has enqueuerecord.
             We need extract out record, and prove a in Val in *)
          have "a \<in> Val"
          proof -
            (* 1. from HB in extract out a of ret event *)
            from hb obtain k1 p1 sn1 where k1_props:
              "k1 < length (his_seq s')" "act_cr (his_seq s' ! k1) = ret"
              "act_name (his_seq s' ! k1) = enq" "act_val (his_seq s' ! k1) = a"
              "act_pid (his_seq s' ! k1) = p1" "act_ssn (his_seq s' ! k1) = sn1"
              unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
              by (auto simp: op_name_def op_pid_def op_val_def op_ssn_def)

            have k1_s: "k1 < length (his_seq s)" "act_cr (his_seq s ! k1) = ret"
                       "act_name (his_seq s ! k1) = enq" "act_val (his_seq s ! k1) = a"
                       "act_pid (his_seq s ! k1) = p1" "act_ssn (his_seq s ! k1) = sn1"
              using k1_props step_facts by auto

            (* 2. usehistory invariant to its corresponds to of call event *)
            have "\<exists>j<k1. act_pid (his_seq s ! j) = p1 \<and> act_ssn (his_seq s ! j) = sn1 \<and>
                         act_name (his_seq s ! j) = enq \<and> act_cr (his_seq s ! j) = call \<and> act_val (his_seq s ! j) = a"
              using hI7_His_WF_s k1_s unfolding hI7_His_WF_def Let_def match_ret_def match_call_def
              by (auto split: if_splits)
            then obtain j where j_props: "j < length (his_seq s)" "act_pid (his_seq s ! j) = p1"
              "act_ssn (his_seq s ! j) = sn1" "act_name (his_seq s ! j) = enq"
              "act_cr (his_seq s ! j) = call" "act_val (his_seq s ! j) = a"
              using k1_s(1)
              using order.strict_trans by auto

            (* 3. EnqCallInHis fact, and use hI10_Enq_Call_Existence out a \<in> Val *)
            have "EnqCallInHis s p1 a sn1"
              unfolding EnqCallInHis_def Let_def using j_props by force
            thus "a \<in> Val" using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def
              using hI20_Enq_Val_Valid_def hI20_Enq_Val_Valid_s k1_s(1,3,4) by auto
          qed

          (* For out one! *)
          thus False using a_bot unfolding Val_def BOT_def by simp
        qed

      next
        case False
        (* --- branch 2: q \<noteq> p, is its process, precisetranslate --- *)
        have q_D3_old: "program_counter s q = ''D3'' "
          using q_props(2) False other_facts by auto

        have q_pending_old: "HasPendingDeq s q"
          using q_props(1) step_facts unfolding HasPendingDeq_def s_var_def Let_def
          by (metis DeqCallInHis_his_eq s_var_def s_var_eq)

        have win_old: "Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
          using q_props(3,4,5) False other_facts step_facts unfolding Idx_def AtIdx_def by auto

        (* Prove and queue *)
        have a_type_old: "TypeB s a" using tba' typeb_eq by simp
        have b_type_old: "TypeB s b" using tbb' typeb_eq by simp
        have a_in_old: "InQBack s a" using inqa' step_facts unfolding InQBack_def by simp
        have b_in_old: "InQBack s b" using inqb' step_facts unfolding InQBack_def by simp
        have idx_order_old: "Idx s a < Idx s b" using idx_lt' step_facts unfolding Idx_def AtIdx_def by auto

        (* HB: history, HB complete one *)
        have hb_stable: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def op_name_def op_pid_def op_val_def op_ssn_def match_ret_def match_call_def
          using step_facts by simp

        (* Old state of invariant hI19_Scanner_Catches_Later_Enq_s close immediately *)
        show ?thesis
        proof (rule notI)
          assume hb_new: "HB_EnqRetCall s' a b"
          hence hb_old: "HB_EnqRetCall s a b" using hb_stable by simp

          have "\<not> HB_EnqRetCall s a b"
            using hI19_Scanner_Catches_Later_Enq_s a_in_old b_in_old a_type_old b_type_old idx_order_old q_pending_old q_D3_old win_old
            unfolding hI19_Scanner_Catches_Later_Enq_def by blast

          thus False using hb_old by contradiction
        qed
      qed
    qed
  qed

  have "hI20_Enq_Val_Valid s'" using hI20_Enq_Val_Valid_s unfolding hI20_Enq_Val_Valid_def by simp

  (* HI21_Ret_Implies_Call: one Ret event all has one match of Call event (new if-else definitionversion) *)
    have "hI21_Ret_Implies_Call s'"
    proof -
      (* 1. D2 step change historyrecord (if in this fact step_facts, replace) *)
      have seq_eq: "his_seq s' = his_seq s"
        using step_facts by simp

      (* 2. usehistoryrecord one, old state close directly *)
      show "hI21_Ret_Implies_Call s'"
        using hI21_Ret_Implies_Call_s seq_eq
        unfolding hI21_Ret_Implies_Call_def
        by presburger
    qed

  have "hI22_Deq_Local_Pattern s'" using hI22_Deq_Local_Pattern_s unfolding hI22_Deq_Local_Pattern_def DeqRetInHis_def by simp
  have "hI23_Deq_Call_Ret_Balanced s'" using hI23_Deq_Call_Ret_Balanced_s unfolding hI23_Deq_Call_Ret_Balanced_def by simp

  (* HI24_HB_Implies_Idx_Order: and of consistency replace *)
  have "hI24_HB_Implies_Idx_Order s'"
  proof -
    (* 1. prove of HB_Act in s and s' complete (because history) *)
    have eq_hb: "\<And>a b. HB_Act s' a b = HB_Act s a b"
      unfolding HB_Act_def HB_def mk_op_def using step_facts by simp

    (* 2. extract the old state of hI24_HB_Implies_Idx_Order fact *)
    note old_hI24_HB_Implies_Idx_Order = hI24_HB_Implies_Idx_Order_s[unfolded hI24_HB_Implies_Idx_Order_def]

    (* 3. one: unfold hI24_HB_Implies_Idx_Order s', use replace as old state *)
    show ?thesis
      using old_hI24_HB_Implies_Idx_Order
      unfolding hI24_HB_Implies_Idx_Order_def
      using Model.Q_arr_def eq_hb step_facts(3) by presburger
  qed

  have "hI25_Enq_Call_Ret_Balanced s'" using hI25_Enq_Call_Ret_Balanced_s unfolding hI25_Enq_Call_Ret_Balanced_def by auto

  (* HI26_DeqRet_D4_Mutex: D4 and DeqRet history of *)
  have "hI26_DeqRet_D4_Mutex s'"
  proof -
    (* Fill in of sn *)
    have "\<forall>q a sn. a \<in> Val \<longrightarrow> \<not> (DeqRetInHis s' q a sn \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a)"
    proof (intro allI impI)
      fix q a sn assume v: "a \<in> Val"
      show "\<not> (DeqRetInHis s' q a sn \<and> program_counter s' q = ''D4'' \<and> x_var s' q = a)"
      proof (cases "q = p")
        case True
        (* Branch 1: q = p. because p complete D2, its PC impossible is D4, into *)
        thus ?thesis using branch_facts step_facts by auto
      next
        case False
        (* Branch 2: q \<noteq> p. physical, old state of hI26_DeqRet_D4_Mutex_s *)
        thus ?thesis using hI26_DeqRet_D4_Mutex_s other_facts step_facts v
        unfolding hI26_DeqRet_D4_Mutex_def DeqRetInHis_def by auto
      qed
    qed
    thus ?thesis unfolding hI26_DeqRet_D4_Mutex_def
      by auto
  qed

  (* ========================================================================= *)
  (* HI19: and physical PC of (D2 state transition) *)
  (* ========================================================================= *)
  have "hI27_Pending_PC_Sync s'"
  proof (unfold hI27_Pending_PC_Sync_def, intro conjI allI impI)
    have s_var_eq: "s_var s' = s_var s" unfolding s_var_def using step_facts(11)
      using s_var_def s_var_eq by auto

    (* Deq prove *)
    show "\<And>p'. HasPendingDeq s' p' \<Longrightarrow> program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    proof -
      fix p' assume pending_prime: "HasPendingDeq s' p'"
      have pend_deq_eq: "HasPendingDeq s' p' = HasPendingDeq s p'"
        unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def
        using step_facts(1) s_var_eq by simp
      have pending_s: "HasPendingDeq s p'" using pending_prime pend_deq_eq by simp

      show "program_counter s' p' \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof (cases "p' = p")
        case True
        have "program_counter s' p \<in> {''D1'', ''D3''}" using branch_facts by (cases "l_var s p = 1") auto
        thus ?thesis using True
          by auto
      next
        case False thus ?thesis using hI19_s pending_s False other_facts(1) unfolding hI27_Pending_PC_Sync_def
          by auto
      qed
    qed

    (* Enq prove *)
    show "\<And>p'. HasPendingEnq s' p' (v_var s' p') \<Longrightarrow> program_counter s' p' \<in> {''E1'', ''E2'', ''E3''}"
    proof -
      fix p' assume pending_enq_prime: "HasPendingEnq s' p' (v_var s' p')"
      have pend_enq_eq: "HasPendingEnq s' p' (v_var s' p') = HasPendingEnq s p' (v_var s p')"
        unfolding HasPendingEnq_def EnqCallInHis_def EnqRetInHis_def Let_def
        using step_facts(1) step_facts(5) s_var_eq by simp
      have pending_enq_s: "HasPendingEnq s p' (v_var s p')" using pending_enq_prime pend_enq_eq by simp

      show "program_counter s' p' \<in> {''E1'', ''E2'', ''E3''}"
      proof (cases "p' = p")
        case True
        have "program_counter s p = ''D2''" using step_facts(12) by simp
        moreover have "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" using hI19_s pending_enq_s True unfolding hI27_Pending_PC_Sync_def by blast
        ultimately show ?thesis by simp
      next
        case False thus ?thesis using hI19_s pending_enq_s False other_facts(1) unfolding hI27_Pending_PC_Sync_def
          by simp
      qed
    qed
  qed

(* ========================================================================= *)
  (* HI20: enqueuevalue of definitelynew (D2 state transition - fixguard + goal_cases) *)
  (* ========================================================================= *)
  have "hI28_Fresh_Enq_Immunity s'"
  proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI)
    fix p_enq q_deq a sn

    (* Key correction: alignnewversion hI20 definition, E3, onlyguard E1 and E2 *)
    assume prems: "program_counter s' p_enq \<in> {''E1'', ''E2''} \<and>
                   v_var s' p_enq = a \<and>
                   a \<noteq> BOT"
    hence pc_e_prime: "program_counter s' p_enq \<in> {''E1'', ''E2''}"
      and v_eq_prime: "v_var s' p_enq = a"
      and a_not_bot: "a \<noteq> BOT" by auto

    have s_var_eq: "s_var s' = s_var s" unfolding s_var_def using step_facts(11)
      using s_var_def s_var_eq by auto

    show "\<not> DeqRetInHis s' q_deq a sn"
    proof (rule notI)
      assume his_prime: "DeqRetInHis s' q_deq a sn"
      have his_eq: "DeqRetInHis s' q_deq a sn = DeqRetInHis s q_deq a sn"
        unfolding DeqRetInHis_def using step_facts(1) s_var_eq by simp
      have his_s: "DeqRetInHis s q_deq a sn" using his_prime his_eq by simp

      show False
      proof (cases "p_enq = p", goal_cases)
        case 1
        (* At this point 1 premise p_enq = p *)
        have "program_counter s' p \<in> {''D1'', ''D3''}" using branch_facts by (cases "l_var s p = 1") auto
        with pc_e_prime 1 show False by auto
      next
        case 2
        (* At this point 2 premise p_enq \<noteq> p *)
        have old_pc: "program_counter s p_enq \<in> {''E1'', ''E2''}" using pc_e_prime 2 other_facts(1) by simp
        have old_v: "v_var s p_enq = a" using v_eq_prime 2 step_facts(5) by simp

        from hI20_s[unfolded hI28_Fresh_Enq_Immunity_def] old_pc old_v a_not_bot his_s
        show False by blast
      qed
    qed
  qed

(* ========================================================================= *)
  (* HI21: E2 phase process of (D2 state transition - complete version) *)
  (* ========================================================================= *)
  have "hI29_E2_Scanner_Immunity s'"
  proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI, goal_cases)
    case (1 p_enq a q_deq)

    (* 1. extractgoal in of coreprecondition *)
    from 1 have pc_e': "program_counter s' p_enq = ''E2''" by blast
    from 1 have inqa': "InQBack s' a" by blast
    from 1 have tba': "TypeB s' a" by blast
    from 1 have pend_q': "HasPendingDeq s' q_deq" by blast
    from 1 have pc_q_D3': "program_counter s' q_deq = ''D3''" by blast
    from 1 have idx1': "Idx s' a < j_var s' q_deq" by blast
    from 1 have idx2': "j_var s' q_deq \<le> i_var s' p_enq" by blast
    from 1 have idx3': "i_var s' p_enq < l_var s' q_deq" by blast

    (* 2. extractglobalphysicalguards *)
    have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast

    (* 3. enqueueprocess p_enq: D2 p of new state is D1 or D3, impossible is E2 *)
    have p_enq_neq_p: "p_enq \<noteq> p"
    proof
      assume "p_enq = p"
      with pc_e' have "program_counter s' p = ''E2''" by simp
      moreover have "program_counter s' p \<in> {''D1'', ''D3''}" using step_facts pc_eqs
        using branch_facts(1,3) by blast
      ultimately show False by simp
    qed

    (* 4. scan q_deq is is state transition of when before process p *)
    show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
    proof (cases "q_deq = p")
      case True
      (* ==================================================================== *)
      (* 4.1 final stepwhen before process p: use BOT HB *)
      (* ==================================================================== *)

      (* D2 of state transition then, if p to D3, it of j_var be as 1 *)
      have j_var_is_1: "j_var s' p = 1"
        using STEP unfolding Sys_D2_def C_D2_def Let_def
        using True pc_q_D3' step_facts
        using branch_facts(4) by fastforce

      (* J_var s' p = 1 in premise, obtain Idx s' a < 1, Idx = 0 *)
      have "Idx s' a = 0" using idx1' True j_var_is_1 by simp

      (* Use SOME extract out 0 element a *)
      moreover have "Qback_arr s' (Idx s' a) = a"
        using inqa' unfolding InQBack_def Idx_def AtIdx_def by (rule someI_ex)
      ultimately have "a = Qback_arr s' 0" by simp

      (* SI1_Zero_Index_BOT, physicalqueue 0 definitely is BOT! *)
      hence a_bot: "a = BOT" using sI1_Zero_Index_BOT_s step_facts unfolding sI1_Zero_Index_BOT_def by auto

      (* A = BOT, but and HB_EnqRetCall of definition *)
      show ?thesis
      proof (rule notI)
        assume hb: "HB_EnqRetCall s' a (v_var s' p_enq)"

        (* 1. from HB in extract out a corresponds to of enqueue ret record *)
        from hb obtain k1 p1 sn1 where k1_props:
          "k1 < length (his_seq s')" "act_cr (his_seq s' ! k1) = ret"
          "act_name (his_seq s' ! k1) = enq" "act_val (his_seq s' ! k1) = a"
          "act_pid (his_seq s' ! k1) = p1" "act_ssn (his_seq s' ! k1) = sn1"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def mk_op_def Let_def match_ret_def match_call_def
          by (auto simp: op_name_def op_pid_def op_val_def op_ssn_def)

        have k1_s: "k1 < length (his_seq s)" "act_cr (his_seq s ! k1) = ret"
                   "act_name (his_seq s ! k1) = enq" "act_val (his_seq s ! k1) = a"
                   "act_pid (his_seq s ! k1) = p1" "act_ssn (his_seq s ! k1) = sn1"
          using k1_props step_facts by auto

        (* 2. use invariant to its corresponds to of call record *)
        have "\<exists>j<k1. act_pid (his_seq s ! j) = p1 \<and> act_ssn (his_seq s ! j) = sn1 \<and>
                     act_name (his_seq s ! j) = enq \<and> act_cr (his_seq s ! j) = call \<and> act_val (his_seq s ! j) = a"
          using hI7_His_WF_s k1_s unfolding hI7_His_WF_def Let_def match_ret_def match_call_def
          by (auto split: if_splits)
        then obtain j where j_props: "j < length (his_seq s)" "act_pid (his_seq s ! j) = p1"
          "act_ssn (his_seq s ! j) = sn1" "act_name (his_seq s ! j) = enq"
          "act_cr (his_seq s ! j) = call" "act_val (his_seq s ! j) = a"
          using k1_s(1)
          using order_less_trans by blast

        (* 3. EnqCallInHis, and use hI10_Enq_Call_Existence out allenqueue of valuenecessarily in Val set in *)
        have "EnqCallInHis s p1 a sn1"
          unfolding EnqCallInHis_def Let_def using j_props by force
        hence "a \<in> Val" using hI10_Enq_Call_Existence_s unfolding hI10_Enq_Call_Existence_def
          using hI20_Enq_Val_Valid_def hI20_Enq_Val_Valid_s k1_s(1,3,4) by blast

        (* 4.: a \<in> Val, but a = BOT (BOT \<notin> Val) *)
        thus False using a_bot unfolding Val_def BOT_def by simp
      qed

    next
      case False
      (* ==================================================================== *)
      (* 4.2 its process: physical, translate old guardsdirect closure *)
      (* ==================================================================== *)

      (* Translate all physical attributes back to the old state s *)
      have pc_e_s: "program_counter s p_enq = ''E2''" using pc_e' p_enq_neq_p step_facts pc_eqs by auto
      have pc_q_s: "program_counter s q_deq = ''D3''" using pc_q_D3' False step_facts pc_eqs by auto

      have inqa_s: "InQBack s a" using inqa' step_facts unfolding InQBack_def by auto
      have tba_s: "TypeB s a" using tba' typeb_eq by simp

      have pend_q_s: "HasPendingDeq s q_deq"
      proof -
        have "HasPendingDeq s' q_deq = HasPendingDeq s q_deq"
          unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def s_var_def
          using step_facts False
          using s_var_def s_var_eq by auto
        thus ?thesis using pend_q' by simp
      qed

      (* Translateall of coordinate *)
      have idx_eq: "Idx s' a = Idx s a" unfolding Idx_def AtIdx_def step_facts by simp
      have j_var_eq: "j_var s' q_deq = j_var s q_deq" using False step_facts by auto
      have l_var_eq: "l_var s' q_deq = l_var s q_deq" using False step_facts by auto
      have i_var_eq: "i_var s' p_enq = i_var s p_enq" using p_enq_neq_p step_facts by auto
      have v_var_eq: "v_var s' p_enq = v_var s p_enq" using p_enq_neq_p step_facts by auto

      have bound1: "Idx s a < j_var s q_deq" using idx1' idx_eq j_var_eq by simp
      have bound2: "j_var s q_deq \<le> i_var s p_enq" using idx2' j_var_eq i_var_eq by simp
      have bound3: "i_var s p_enq < l_var s q_deq" using idx3' i_var_eq l_var_eq by simp

      (* Old stateguardsdirect closure! all *)
      have no_hb_old: "\<not> HB_EnqRetCall s a (v_var s p_enq)"
        using hI21_s pc_e_s inqa_s tba_s pend_q_s pc_q_s bound1 bound2 bound3
        unfolding hI29_E2_Scanner_Immunity_def by blast

      (* Prove HB in D2 preserve, close immediately *)
      show "\<not> HB_EnqRetCall s' a (v_var s' p_enq)"
      proof -
        have hb_stable: "HB_EnqRetCall s' a (v_var s' p_enq) = HB_EnqRetCall s a (v_var s p_enq)"
          unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def op_ssn_def op_pid_def
          using step_facts v_var_eq by auto
        thus ?thesis using no_hb_old by simp
      qed
    qed
  qed


    (* ========================================================================= *)
    (* HI22: physical of definitelyorder preservation (D2 state transition - newversionsimplified definition) *)
    (* : globalhistory and physicalqueue, precise q \<noteq> p old guards *)
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

      (* 2. extractglobal old guards *)
      have hI22_old: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast

      (* 3. isolate the process currently taking the transition p: p in D2 after impossible in E2/E3 *)
      have q_neq_p: "q \<noteq> p"
      proof
        assume "q = p"
        with pc_q' have "program_counter s' p \<in> {''E2'', ''E3''}" by simp
        moreover have "program_counter s' p \<notin> {''E2'', ''E3''}" using step_facts pc_eqs by auto
        ultimately show False by simp
      qed

      (* 4. translate all physical attributes back to the old state s *)
      (* Use q \<noteq> p q of PC *)
      have pc_eq_q: "program_counter s' q = program_counter s q"
        using q_neq_p step_facts pc_eqs by auto
      have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}"
        using pc_q' pc_eq_q by simp

      (* Global: history and after queue *)
      have seq_eq: "his_seq s' = his_seq s" using step_facts by simp
      have qback_eq: "Qback_arr s' = Qback_arr s" using step_facts by simp

      (* Local *)
      have v_var_eq: "v_var s' q = v_var s q" using q_neq_p step_facts by auto
      have i_var_eq: "i_var s' q = i_var s q" using q_neq_p step_facts by auto

      (* Physical *)
      have inqb_s: "InQBack s b" using inqb' qback_eq unfolding InQBack_def by simp
      have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_var_eq by simp

      (* Sincehistory, HB precise () *)
      have hb_eq: "HB_EnqRetCall s' b (v_var s' q) = HB_EnqRetCall s b (v_var s q)"
        unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
        using seq_eq v_var_eq by simp
      have hb_s: "HB_EnqRetCall s b (v_var s q)" using hb' hb_eq by simp

      have idx_eq: "Idx s' b = Idx s b" unfolding Idx_def AtIdx_def using qback_eq by simp

      (* 5. precisemapping old state, version old guards, in 5! *)
      have "Idx s b < i_var s q"
        using hI22_old pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
        unfolding hI30_Ticket_HB_Immunity_def by blast

      (* 6. conclusiontranslate new state, close immediately *)
      thus "Idx s' b < i_var s' q" using idx_eq i_var_eq by simp
    qed

  have "lI1_Op_Sets_Equivalence s'" using lI1_Op_Sets_Equivalence_s unfolding lI1_Op_Sets_Equivalence_def OPLin_def OP_A_enq_def OP_A_deq_def OP_B_enq_def EnqCallInHis_def DeqCallInHis_def by simp
  have "lI2_Op_Cardinality s'" using lI2_Op_Cardinality_s unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def by simp
  have "lI3_HB_Ret_Lin_Sync s'" using lI3_HB_Ret_Lin_Sync_s unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def EnqRetInHis_def DeqRetInHis_def by simp
  have "lI4_FIFO_Semantics s'" using lI4_FIFO_Semantics_s unfolding lI4_FIFO_Semantics_def by simp
  have "lI5_SA_Prefix s'" using lI5_SA_Prefix_s unfolding lI5_SA_Prefix_def by simp
  (* LI6_D4_Deq_Linearized: invariant of *)
  have "lI6_D4_Deq_Linearized s'"
  proof -
    (* 1. extract and unfoldold state of lI6_D4_Deq_Linearized fact *)
    note old_lI6_D4_Deq_Linearized = lI6_D4_Deq_Linearized_s[unfolded lI6_D4_Deq_Linearized_def]

    (* 2. use auto of derivation, all fact simplification step *)
    show ?thesis
      using old_lI6_D4_Deq_Linearized step_facts pc_eqs branch_facts other_facts
      unfolding lI6_D4_Deq_Linearized_def Let_def s_var_def
      using s_var_def s_var_eq by auto
  qed

  (* LI7_D4_Deq_Deq_HB: list and of Isar derivation *)
  have "lI7_D4_Deq_Deq_HB s'"
  proof -
    (* Old state of fact unfold use *)
    note old_lI7_D4_Deq_Deq_HB = lI7_D4_Deq_Deq_HB_s[unfolded lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def HB_def]

    (* In allphysical (step_facts), its process PC (pc_eqs)
       With when before process fact (branch_facts).
       LI7_D4_Deq_Deq_HB_list in of one corresponds to, precise fun_upd_other *)
    show ?thesis
      using old_lI7_D4_Deq_Deq_HB step_facts pc_eqs branch_facts other_facts
      unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def HB_def s_var_def Let_def
      by (smt (verit, best) s_var_def s_var_eq)
  qed

  (* LI8_D3_Deq_Returned: smt, fill in fact of Isar prove *)
  have "lI8_D3_Deq_Returned s'"
  proof -
    (* Extract the old state of fact use *)
    note old_lI8_D3_Deq_Returned = lI8_D3_Deq_Returned_s[unfolded lI8_D3_Deq_Returned_def]

    (* In all of physical, when before branch with its process of fact *)
    show ?thesis
      using old_lI8_D3_Deq_Returned step_facts pc_eqs branch_facts other_facts
      unfolding lI8_D3_Deq_Returned_def DeqRetInHis_def s_var_def Let_def
      by (metis (no_types, lifting) DeqRetInHis_def lI9_D1_D2_Deq_Returned_def
          lI9_D1_D2_Deq_Returned_s)
  qed

  have "lI9_D1_D2_Deq_Returned s'" using lI9_D1_D2_Deq_Returned_s step_facts other_facts unfolding lI9_D1_D2_Deq_Returned_def DeqRetInHis_def by (smt (verit) fun_upd_other)

  (* LI10_D4_Enq_Deq_HB: use goal_cases match and *)
  have "lI10_D4_Enq_Deq_HB s'"
    unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
  proof (intro allI impI, goal_cases)
    case (1 k1 k2 q)
    (* At this point '1' then one premise, the need it *)

    show "k1 < k2"
    proof (cases "q = p")
      case True
      (* Branch 1: q = p. use D2 factprovecontradiction *)
      (* From premise '1' in extract out PC *)
      from 1 True have pc_p_s': "program_counter s' p = ''D4'' " by blast

      (* Fact: p after only is D1 or D3, impossible is D4 *)
      have pc_p_dest: "program_counter s' p \<in> {''D1'', ''D3''}"
        using branch_facts by (cases "l_var s p = 1") auto

      from pc_p_s' pc_p_dest show ?thesis by auto
    next
      case False
      (* Branch 2: q \<noteq> p. at this point q of PC and physical *)
      from 1 False have pc_q_old: "program_counter s q = ''D4'' "
        using other_facts by auto

      (* Useold state of lI10_D4_Enq_Deq_HB_s prove *)
      (* Note: here we premise '1' for auto, it s' to s of *)
      show ?thesis
        using lI10_D4_Enq_Deq_HB_s[unfolded lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def] 1 False pc_q_old step_facts other_facts
        unfolding EnqRetInHis_def s_var_def Let_def
        by (metis HB_Act_def lI3_HB_Ret_Lin_Sync_def
            lI3_HB_Ret_Lin_Sync_s)
    qed
  qed

(* LI11_D4_Deq_Unique: for in of prove *)
  have "lI11_D4_Deq_Unique s'"
    unfolding lI11_D4_Deq_Unique_def
  proof (intro allI impI, goal_cases)
    case (1 q)
    (* At this point 1 premise: program_counter s' q = ''D4'' *)

    show "\<exists>k2 < length (lin_seq s').
            lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
            (\<forall>k3 < length (lin_seq s').
               op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
               k3 < k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3)))"
    proof (cases "q = p")
      case True
      (* Branch 1: q = p. contradiction: D2 after PC is D4 *)
      from 1 True have "program_counter s' p = ''D4'' " by blast
      moreover have "program_counter s' p \<in> {''D1'', ''D3''}"
        using branch_facts by (cases "l_var s p = 1") auto
      ultimately show ?thesis by auto (* Premisecontradiction, close directly *)
    next
      case False
      (* Branch 2: q \<noteq> p. at this point q of all in s and s' *)
      hence pc_q_old: "program_counter s q = ''D4'' "
        using 1 other_facts by auto

      (* Core: useold state of lI11_D4_Deq_Unique_s.
         Since D2 change lin_seq, x_var, s_var, his_seq,
         Therefore s of k2 is s' we of k2 *)
      show ?thesis
        using lI11_D4_Deq_Unique_s[unfolded lI11_D4_Deq_Unique_def] pc_q_old step_facts other_facts
        unfolding DeqRetInHis_def s_var_def Let_def
        using s_var_def s_var_eq by presburger
    qed
  qed

  have di_s': "data_independent (lin_seq s')"
    using di_lin_s step_facts(2)
    by simp

  (* USpec invariants uI1-uI3.  D2 keeps the abstract USpec state,
     lin_seq, his_seq, and queue contents unchanged.  Since D2 may move
     the active process into D3, uI3 is reconstructed from the already
     established local invariants of s'. *)
  have uspec_effOps_eq [simp]:
    "uspec_effOps s' = uspec_effOps s"
    using step_facts(11)
    unfolding uspec_effOps_def
    by simp

  have "uI1_USpec_EffOps_Lin s'"
  proof -
    have old:
      "uspec_effOps s = set (lin_seq s)"
      using uI1_USpec_EffOps_Lin_s
      unfolding uI1_USpec_EffOps_Lin_def
      by simp

    show ?thesis
      unfolding uI1_USpec_EffOps_Lin_def
      using old step_facts(2) uspec_effOps_eq
      by simp
  qed

  have "uI2_USpec_E1UE2 s'"
  proof (unfold uI2_USpec_E1UE2_def, intro allI impI)
    fix q
    assume pc_q': "program_counter s' q \<in> {''E1'', ''E2''}"
    assume upc_q': "u_program_counter (snd s') q = ''UE2''"

    have pc_q_old:
      "program_counter s q \<in> {''E1'', ''E2''}"
      using pc_q'
      by simp

    have upc_q_old:
      "u_program_counter (snd s) q = ''UE2''"
      using upc_q' step_facts(11)
      by simp

    let ?op_old = "mk_op enq (v_var s q) q (s_var s q)"
    let ?op_new = "mk_op enq (v_var s' q) q (s_var s' q)"

    have old_gen:
      "USpec_GenLin
         (his_seq s)
         (uspec_effOps s)
         ?op_old
         (lin_seq s @ [?op_old])"
      using uI2_USpec_E1UE2_s pc_q_old upc_q_old
      unfolding uI2_USpec_E1UE2_def his_seq_def lin_seq_def uspec_effOps_def
      by blast

    have op_eq:
      "?op_new = ?op_old"
      using step_facts(5) s_var_eq
      by simp

    show "USpec_GenLin
            (u_his_seq (snd s'))
            (u_eff_ops (snd s'))
            ?op_new
            (u_lin_seq (snd s') @ [?op_new])"
      using old_gen op_eq step_facts(1,2,11) uspec_effOps_eq
      unfolding his_seq_def lin_seq_def uspec_effOps_def
      by simp
  qed

  have "uI3_USpec_D3UD2 s'"
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
        using a_in unfolding OPLin_def by simp

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
          unfolding OP_A_enq_def by blast

        show ?thesis
          using EnqCallInHis_imp_OpCalledInHis[OF call]
          unfolding a_eq by simp
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
            unfolding OP_B_enq_def by blast

          show ?thesis
            using EnqCallInHis_imp_OpCalledInHis[OF call]
            unfolding a_eq by simp
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
          using di_s' .
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
      show "\<forall>x\<in>set ?base. \<not> HB ?H ?op x"
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
        using di_s' .
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
        using di_s' .
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
        using di_s' .
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

    have eff_subset:
      "uspec_effOps s' \<subseteq> set ?L"
    proof -
      have old_eff:
        "uspec_effOps s' = set (lin_seq s')"
        using `uI1_USpec_EffOps_Lin s'`
        unfolding uI1_USpec_EffOps_Lin_def
        by simp

      have "set (lin_seq s') \<subseteq> set ?base"
        using set_base_eq
        by simp

      thus ?thesis
        using old_eff
        by auto
    qed

    have op_in:
      "?op \<in> set ?L"
      by simp

    have all_called:
      "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
      using all_called_lin set_base_eq op_called
      by auto

    have finite_eff:
      "finite (uspec_effOps s')"
      using `uI1_USpec_EffOps_Lin s'`
      unfolding uI1_USpec_EffOps_Lin_def
      by simp

    have gen:
      "USpec_GenLin ?H (uspec_effOps s') ?op ?L"
      unfolding USpec_GenLin_def
    proof (intro conjI)
      show "finite (uspec_effOps s')"
        using finite_eff .
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

  have "Simulate_PC s'" using STEP unfolding Sys_D2_def by simp

  (* 5. assemble the final conclusion *)
  show ?thesis
    unfolding system_invariant_def
    using `Simulate_PC s'` `TypeOK s'` `sI1_Zero_Index_BOT s'`
    `sI2_X_var_Upper_Bound s'` `sI3_E2_Slot_Exclusive s'` `sI4_E3_Qback_Written s'` `sI5_D2_Local_Bound s'` `sI6_D3_Scan_Pointers s'` `sI7_D4_Deq_Result s'`  `hI3_L0_E_Phase_Bounds s'`
    `sI8_Q_Qback_Sync s'` `sI9_Qback_Discrepancy_E3 s'` `sI10_Qback_Unique_Vals s'` `hI2_SSN_Bounds s'` `sI11_x_var_Scope s'` `hI1_E_Phase_Pending_Enq s'``sI12_D3_Scanned_Prefix s'` `uI1_USpec_EffOps_Lin s'` `uI2_USpec_E1UE2 s'` `uI3_USpec_D3UD2 s'` `hI4_X_var_Lin_Sync s'`
    `hI7_His_WF s'` `hI8_Val_Unique s'` `hI5_SSN_Unique s'` `hI6_SSN_Order s'`
    `hI9_Deq_Ret_Unique s'` `hI10_Enq_Call_Existence s'` `hI11_Enq_Ret_Existence s'` `hI12_D_Phase_Pending_Deq s'` `hI13_Qback_Deq_Sync s'` `hI14_Pending_Enq_Qback_Exclusivity s'` `hI15_Deq_Result_Exclusivity s'` `hI16_BO_BT_No_HB s'` `hI17_BT_BT_No_HB s'` `hI18_Idx_Order_No_Rev_HB s'` `hI19_Scanner_Catches_Later_Enq s'` `hI20_Enq_Val_Valid s'` `hI21_Ret_Implies_Call s'` `hI22_Deq_Local_Pattern s'` `hI23_Deq_Call_Ret_Balanced s'` `hI24_HB_Implies_Idx_Order s'` `hI25_Enq_Call_Ret_Balanced s'`  `hI26_DeqRet_D4_Mutex s'`
    `hI27_Pending_PC_Sync s'` `hI28_Fresh_Enq_Immunity s'` `hI29_E2_Scanner_Immunity s'` `hI30_Ticket_HB_Immunity s'` (* Fill in *)
    `lI1_Op_Sets_Equivalence s'` `lI2_Op_Cardinality s'` `lI3_HB_Ret_Lin_Sync s'` `lI4_FIFO_Semantics s'` `lI5_SA_Prefix s'` `lI6_D4_Deq_Linearized s'` `lI7_D4_Deq_Deq_HB s'` `lI8_D3_Deq_Returned s'` `lI9_D1_D2_Deq_Returned s'` `lI10_D4_Enq_Deq_HB s'` `lI11_D4_Deq_Unique s'`
    `data_independent (lin_seq s')`
    by blast
qed

end
