theory E1Lemmas
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
(* Preservation lemmas for the E1 transition                   *)
(* ========================================================== *)

(* ========================================================================= *)
(* Step 1: Basic state-transition facts (Physical State Transition Facts for Sys_E1) *)
(* We work directly with the primitive model definitions, without relying on update_state *)
(* ========================================================================= *)

(* Bridge definitions used to unfold all system variables in one place *)
lemmas E1_bridge =
  program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def
  i_var_def j_var_def l_var_def x_var_def v_var_def s_var_def
  lin_seq_def his_seq_def

lemma Sys_E1_pc_before:
  assumes "Sys_E1 p s s'"
  shows "program_counter s p = ''E1''"
  using assms unfolding Sys_E1_def C_E1_def E1_bridge by auto

lemma Sys_E1_history_unchanged:
  assumes "Sys_E1 p s s'"
  shows "his_seq s' = his_seq s"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge
  by (simp add: U_E2_def)

lemma Sys_E1_lin_append:
  assumes "Sys_E1 p s s'"
  shows "lin_seq s' = lin_seq s @ [mk_op enq (v_var s p) p (s_var s p)]"
  using assms unfolding Sys_E1_def C_E1_def U_E2_def Let_def E1_bridge
  by auto

lemma Sys_E1_lin_last:
  assumes STEP: "Sys_E1 p s s'"
  shows "lin_seq s' ! length (lin_seq s) = mk_op enq (v_var s p) p (s_var s p)"
  using Sys_E1_lin_append[OF STEP]
  by simp

lemma Sys_E1_pc_eq:
  assumes "Sys_E1 p s s'"
  shows "program_counter s' q = (if q = p then ''E2'' else program_counter s q)"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_i_eq:
  assumes "Sys_E1 p s s'"
  shows "i_var s' q = (if q = p then X_var s else i_var s q)"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_X_eq:
  assumes "Sys_E1 p s s'"
  shows "X_var s' = X_var s + 1"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by auto

lemma Sys_E1_V_eq:
  assumes "Sys_E1 p s s'"
  shows "V_var s' = V_var s"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by auto

lemma Sys_E1_v_eq:
  assumes "Sys_E1 p s s'"
  shows "v_var s' q = v_var s q"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_j_eq:
  assumes "Sys_E1 p s s'"
  shows "j_var s' q = j_var s q"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_l_eq:
  assumes "Sys_E1 p s s'"
  shows "l_var s' q = l_var s q"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_x_eq:
  assumes "Sys_E1 p s s'"
  shows "x_var s' q = x_var s q"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_qarr_eq:
  assumes "Sys_E1 p s s'"
  shows "Q_arr s' k = Q_arr s k"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_qback_eq:
  assumes "Sys_E1 p s s'"
  shows "Qback_arr s' k = Qback_arr s k"
  using assms unfolding Sys_E1_def C_E1_def Let_def E1_bridge by (auto simp: fun_eq_iff)

lemma Sys_E1_uhis_eq:
  assumes "Sys_E1 p s s'"
  shows "his_seq s' = his_seq s"
  using Sys_E1_history_unchanged[OF assms] .


(* ========================================================================= *)
(* Step 2: Preservation of logical-state and set-based invariants (Logical State & Set Invariants) *)
(* ========================================================================= *)

lemma Sys_E1_lin_nth_old:
  assumes STEP: "Sys_E1 p s s'"
  assumes K: "k < length (lin_seq s)"
  shows "lin_seq s' ! k = lin_seq s ! k"
  using Sys_E1_lin_append[OF STEP] K
  by (simp add: nth_append)


lemma Sys_E1_QHas_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "QHas s' a \<longleftrightarrow> QHas s a"
proof -
  have "Q_arr s' = Q_arr s"
    using fun_eq_iff Sys_E1_qarr_eq[OF STEP] by blast
  then show ?thesis
    unfolding QHas_def by simp
qed

lemma Sys_E1_InQBack_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "InQBack s' a \<longleftrightarrow> InQBack s a"
proof -
  have "Qback_arr s' = Qback_arr s"
    using fun_eq_iff Sys_E1_qback_eq[OF STEP] by blast
  then show ?thesis
    unfolding InQBack_def by simp
qed

lemma Sys_E1_AtIdx_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "AtIdx s' a k \<longleftrightarrow> AtIdx s a k"
  using Sys_E1_qback_eq[OF STEP, of k] unfolding AtIdx_def by simp

lemma Sys_E1_TypeA_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "TypeA s' a \<longleftrightarrow> TypeA s a"
  using Sys_E1_QHas_eq[OF STEP, of a] Sys_E1_InQBack_eq[OF STEP, of a]
  unfolding TypeA_def by simp

lemma Sys_E1_SetA_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "SetA s' = SetA s"
proof -
  have "\<forall>a. a \<in> SetA s' \<longleftrightarrow> a \<in> SetA s"
    using Sys_E1_TypeA_eq[OF STEP] unfolding SetA_def by simp
  then show ?thesis by blast
qed

lemma Sys_E1_Idx_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "Idx s' a = Idx s a"
proof -
  have atidx_eq: "AtIdx s' a = AtIdx s a"
  proof (rule ext)
    fix k
    show "AtIdx s' a k = AtIdx s a k"
      using Sys_E1_AtIdx_eq[OF STEP, of a k] by simp
  qed
  show ?thesis
    using atidx_eq unfolding Idx_def by simp
qed

lemma Sys_E1_HB_Act_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "HB_Act s' x y \<longleftrightarrow> HB_Act s x y"
  using Sys_E1_history_unchanged[OF STEP] unfolding HB_Act_def by simp

lemma Sys_E1_HB_EnqRetCall_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
  using Sys_E1_HB_Act_eq[OF STEP] unfolding HB_EnqRetCall_def by simp

lemma Sys_E1_TypeB_eq:
  assumes STEP: "Sys_E1 p s s'"
  shows "TypeB s' a \<longleftrightarrow> TypeB s a \<or> a = v_var s p"
proof
  assume type_new: "TypeB s' a"
  then have type_new_cases:
    "QHas s' a \<or> (\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = a)"
    unfolding TypeB_def by simp
  then show "TypeB s a \<or> a = v_var s p"
  proof
    assume qhas_new: "QHas s' a"
    have "QHas s a"
      using qhas_new Sys_E1_QHas_eq[OF STEP, of a] by simp
    then show "TypeB s a \<or> a = v_var s p"
      unfolding TypeB_def by blast
  next
    assume ex_new: "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = a"
    then obtain q where
      q_pc_new: "program_counter s' q = ''E2''" and
      q_v_new: "v_var s' q = a"
      by blast
    show "TypeB s a \<or> a = v_var s p"
    proof (cases "q = p")
      case True
      then show ?thesis
        using q_v_new Sys_E1_v_eq[OF STEP, of p] by simp
    next
      case False
      have "program_counter s q = ''E2''"
        using q_pc_new False Sys_E1_pc_eq[OF STEP, of q] by simp
      moreover have "v_var s q = a"
        using q_v_new False Sys_E1_v_eq[OF STEP, of q] by simp
      ultimately have "TypeB s a"
        unfolding TypeB_def by blast
      then show ?thesis by blast
    qed
  qed
next
  assume type_old_or_new: "TypeB s a \<or> a = v_var s p"
  from type_old_or_new show "TypeB s' a"
  proof
    assume type_old: "TypeB s a"
    have type_old_cases:
      "QHas s a \<or> (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = a)"
      using type_old unfolding TypeB_def by simp
    then show ?thesis
    proof
      assume qhas_old: "QHas s a"
      have "QHas s' a"
        using qhas_old Sys_E1_QHas_eq[OF STEP, of a] by simp
      then show "TypeB s' a"
        unfolding TypeB_def by blast
    next
      assume ex_old: "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = a"
      then obtain q where
        q_pc_old: "program_counter s q = ''E2''" and
        q_v_old: "v_var s q = a"
        by blast
      have q_ne_p: "q \<noteq> p"
      proof
        assume "q = p"
        then show False
          using q_pc_old Sys_E1_pc_before[OF STEP] by simp
      qed
      have "program_counter s' q = ''E2''"
        using q_pc_old q_ne_p Sys_E1_pc_eq[OF STEP, of q] by simp
      moreover have "v_var s' q = a"
        using q_v_old Sys_E1_v_eq[OF STEP, of q] by simp
      ultimately show "TypeB s' a"
        unfolding TypeB_def by blast
    qed
  next
    assume a_eq: "a = v_var s p"
    have "program_counter s' p = ''E2''"
      using Sys_E1_pc_eq[OF STEP, of p] by simp
    moreover have "v_var s' p = a"
      using a_eq Sys_E1_v_eq[OF STEP, of p] by simp
    ultimately show ?thesis
      unfolding TypeB_def by blast
  qed
qed

lemma Sys_E1_TypeB_eq_other:
  assumes STEP: "Sys_E1 p s s'"
  assumes A_NE: "a \<noteq> v_var s p"
  shows "TypeB s' a \<longleftrightarrow> TypeB s a"
  using Sys_E1_TypeB_eq[OF STEP, of a] A_NE by blast

lemma Sys_E1_TypeBT_eq_other:
  assumes STEP: "Sys_E1 p s s'"
  assumes A_NE: "a \<noteq> v_var s p"
  shows "TypeBT s' a \<longleftrightarrow> TypeBT s a"
proof
  assume bt_new: "TypeBT s' a"
  then have
    type_new: "TypeB s' a"
    and inq_new: "InQBack s' a"
    and rest_new:
      "(\<forall>k. k < Idx s' a \<longrightarrow> Q_arr s' k = BOT) \<or>
       (\<exists>q. program_counter s' q = ''D3'' \<and>
            j_var s' q \<le> Idx s' a \<and> Idx s' a < l_var s' q \<and>
            (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT))"
    unfolding TypeBT_def by simp_all

  have type_old: "TypeB s a"
    using Sys_E1_TypeB_eq_other[OF STEP A_NE] type_new by simp
  have inq_old: "InQBack s a"
    using Sys_E1_InQBack_eq[OF STEP, of a] inq_new by simp

  have rest_old:
    "(\<forall>k. k < Idx s a \<longrightarrow> Q_arr s k = BOT) \<or>
     (\<exists>q. program_counter s q = ''D3'' \<and>
          j_var s q \<le> Idx s a \<and> Idx s a < l_var s q \<and>
          (\<forall>k. j_var s q \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT))"
  proof -
    from rest_new show ?thesis
    proof
      assume pref_new: "\<forall>k. k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
      have "\<forall>k. k < Idx s a \<longrightarrow> Q_arr s k = BOT"
      proof (intro allI impI)
        fix k
        assume "k < Idx s a"
        then have "k < Idx s' a"
          using Sys_E1_Idx_eq[OF STEP, of a] by simp
        then have "Q_arr s' k = BOT"
          using pref_new by simp
        then show "Q_arr s k = BOT"
          using Sys_E1_qarr_eq[OF STEP, of k] by simp
      qed
      then show ?thesis by blast
    next
      assume ex_new:
        "\<exists>q. program_counter s' q = ''D3'' \<and>
             j_var s' q \<le> Idx s' a \<and> Idx s' a < l_var s' q \<and>
             (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)"
      then obtain q where
        q_pc_new: "program_counter s' q = ''D3''"
        and q_bounds_new: "j_var s' q \<le> Idx s' a"
        and q_upper_new: "Idx s' a < l_var s' q"
        and q_pref_new: "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
        by blast
      have q_ne_p: "q \<noteq> p"
      proof
        assume "q = p"
        then show False
          using q_pc_new Sys_E1_pc_eq[OF STEP, of p] by simp
      qed
      have q_pc_old: "program_counter s q = ''D3''"
        using q_pc_new q_ne_p Sys_E1_pc_eq[OF STEP, of q] by simp
      have q_bounds_old: "j_var s q \<le> Idx s a"
        using q_bounds_new Sys_E1_j_eq[OF STEP, of q] Sys_E1_Idx_eq[OF STEP, of a] by simp
      have q_upper_old: "Idx s a < l_var s q"
        using q_upper_new Sys_E1_l_eq[OF STEP, of q] Sys_E1_Idx_eq[OF STEP, of a] by simp
      have q_pref_old: "\<forall>k. j_var s q \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT"
      proof (intro allI impI)
        fix k
        assume "j_var s q \<le> k \<and> k < Idx s a"
        then have "j_var s' q \<le> k \<and> k < Idx s' a"
          using Sys_E1_j_eq[OF STEP, of q] Sys_E1_Idx_eq[OF STEP, of a] by simp
        then have "Q_arr s' k = BOT"
          using q_pref_new by simp
        then show "Q_arr s k = BOT"
          using Sys_E1_qarr_eq[OF STEP, of k] by simp
      qed
      show ?thesis
        using q_pc_old q_bounds_old q_upper_old q_pref_old by blast
    qed
  qed
  show "TypeBT s a"
    using type_old inq_old rest_old unfolding TypeBT_def by blast
next
  assume bt_old: "TypeBT s a"
  then have
    type_old: "TypeB s a"
    and inq_old: "InQBack s a"
    and rest_old:
      "(\<forall>k. k < Idx s a \<longrightarrow> Q_arr s k = BOT) \<or>
       (\<exists>q. program_counter s q = ''D3'' \<and>
            j_var s q \<le> Idx s a \<and> Idx s a < l_var s q \<and>
            (\<forall>k. j_var s q \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT))"
    unfolding TypeBT_def by simp_all

  have type_new: "TypeB s' a"
    using Sys_E1_TypeB_eq_other[OF STEP A_NE] type_old by simp
  have inq_new: "InQBack s' a"
    using Sys_E1_InQBack_eq[OF STEP, of a] inq_old by simp

  have rest_new:
    "(\<forall>k. k < Idx s' a \<longrightarrow> Q_arr s' k = BOT) \<or>
     (\<exists>q. program_counter s' q = ''D3'' \<and>
          j_var s' q \<le> Idx s' a \<and> Idx s' a < l_var s' q \<and>
          (\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT))"
  proof -
    from rest_old show ?thesis
    proof
      assume pref_old: "\<forall>k. k < Idx s a \<longrightarrow> Q_arr s k = BOT"
      have "\<forall>k. k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
      proof (intro allI impI)
        fix k
        assume "k < Idx s' a"
        then have "k < Idx s a"
          using Sys_E1_Idx_eq[OF STEP, of a] by simp
        then have "Q_arr s k = BOT"
          using pref_old by simp
        then show "Q_arr s' k = BOT"
          using Sys_E1_qarr_eq[OF STEP, of k] by simp
      qed
      then show ?thesis by blast
    next
      assume ex_old:
        "\<exists>q. program_counter s q = ''D3'' \<and>
             j_var s q \<le> Idx s a \<and> Idx s a < l_var s q \<and>
             (\<forall>k. j_var s q \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)"
      then obtain q where
        q_pc_old: "program_counter s q = ''D3''"
        and q_bounds_old: "j_var s q \<le> Idx s a"
        and q_upper_old: "Idx s a < l_var s q"
        and q_pref_old: "\<forall>k. j_var s q \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT"
        by blast
      have q_pc_new: "program_counter s' q = ''D3''"
      proof (cases "q = p")
        case True
        then show ?thesis
          using q_pc_old Sys_E1_pc_before[OF STEP] by simp
      next
        case False
        then show ?thesis
          using q_pc_old Sys_E1_pc_eq[OF STEP, of q] by simp
      qed
      have q_bounds_new: "j_var s' q \<le> Idx s' a"
        using q_bounds_old Sys_E1_j_eq[OF STEP, of q] Sys_E1_Idx_eq[OF STEP, of a] by simp
      have q_upper_new: "Idx s' a < l_var s' q"
        using q_upper_old Sys_E1_l_eq[OF STEP, of q] Sys_E1_Idx_eq[OF STEP, of a] by simp
      have q_pref_new: "\<forall>k. j_var s' q \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
      proof (intro allI impI)
        fix k
        assume "j_var s' q \<le> k \<and> k < Idx s' a"
        then have "j_var s q \<le> k \<and> k < Idx s a"
          using Sys_E1_j_eq[OF STEP, of q] Sys_E1_Idx_eq[OF STEP, of a] by simp
        then have "Q_arr s k = BOT"
          using q_pref_old by simp
        then show "Q_arr s' k = BOT"
          using Sys_E1_qarr_eq[OF STEP, of k] by simp
      qed
      show ?thesis
        using q_pc_new q_bounds_new q_upper_new q_pref_new by blast
    qed
  qed
  show "TypeBT s' a"
    using type_new inq_new rest_new unfolding TypeBT_def by blast
qed





(* ========================================================================= *)
(* Auxiliary lemma: E1 across the hI3_L0_E_Phase_Bounds preservation *)
(* Key idea: the global history, V_var, the concrete queue, and the old v_var remain unchanged and can be transported directly *)
(* ========================================================================= *)
lemma hI3_L0_E_Phase_Bounds_E1_step:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "Sys_E1 p s s'"
  shows "hI3_L0_E_Phase_Bounds s'"
proof -
  (* Step 0: extract the invariants of the pre-state *)
  have hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    using INV unfolding system_invariant_def by auto

  (* Step 1: extract the key concrete facts of the E1 transition *)
  note bridge = program_counter_def X_var_def V_var_def Q_arr_def
                Qback_arr_def i_var_def j_var_def l_var_def x_var_def v_var_def
                s_var_def lin_seq_def his_seq_def

  have pc_p_old: "program_counter s p = ''E1'' "
    using STEP unfolding Sys_E1_def C_E1_def bridge by auto
  have pc_p_new: "program_counter s' p = ''E2'' "
    using STEP unfolding Sys_E1_def C_E1_def Let_def bridge by (auto simp: fun_eq_iff)

  have his_eq: "his_seq s' = his_seq s"
    using STEP unfolding Sys_E1_def his_seq_def bridge
    using STEP Sys_E1_history_unchanged his_seq_def by auto
  have s_var_eq: "s_var s' = s_var s"
    using STEP unfolding Sys_E1_def C_E1_def U_E2_def Let_def bridge by auto
  have V_eq: "V_var s' = V_var s"
    using STEP unfolding Sys_E1_def C_E1_def U_E2_def Let_def bridge by auto
  have qback_eq: "Qback_arr s' = Qback_arr s"
    using STEP unfolding Sys_E1_def C_E1_def U_E2_def Let_def bridge by auto

  have pc_other: "\<And>q. q \<noteq> p \<Longrightarrow> program_counter s' q = program_counter s q"
    using STEP unfolding Sys_E1_def C_E1_def Let_def bridge by (auto simp: fun_eq_iff)
  have v_var_eq: "v_var s' = v_var s"
    using STEP unfolding Sys_E1_def C_E1_def U_E2_def Let_def bridge by auto

  (* Step 2: prove the five conjuncts of hI3_L0_E_Phase_Bounds one by one *)
  show ?thesis
  proof (intro hI3_L0_E_Phase_BoundsI allI impI, goal_cases)
    case (1 q)
    (* An L0 process has no pending enqueue. Since p moves to E2, any L0 witness must be some other process q, so the fact transports directly. *)
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
    (* The dequeue-balance fact for L0 is handled in the same way: q must be a different process. *)
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
    (* For processes in the enqueue phase, v_var stays strictly below V_var; p remains in the enqueue phase. *)
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
    (* Call tickets in the history remain strictly below V_var, so the property is transported directly. *)
    have old_k: "k < length (his_seq s)"
      using 4 his_eq by simp
    show ?case
      using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s old_k] 4 his_eq V_eq by auto

  next
    case (5 k)
    (* Tickets stored in Qback_arr remain strictly below V_var, so the property is transported directly. *)
    have "Qback_arr s' k = Qback_arr s k"
      using qback_eq by simp
    thus ?case
      using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s, of k] 5 V_eq by auto
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for hI27_Pending_PC_Sync s' . *)
(* Note: the proof script below is taken verbatim from the original file and only packaged as a separate lemma. *)
lemma E1_pending_pc_sync:
  fixes s s' :: SysState and p :: nat
  assumes hI27_Pending_PC_Sync_s: "hI27_Pending_PC_Sync s"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and pc_eqs [simp]:
      "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<or> q = p)"
      "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
      "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
      "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
      "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'')"
      "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'')"
      "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
      "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
  shows "hI27_Pending_PC_Sync s'"
proof (unfold hI27_Pending_PC_Sync_def, intro conjI allI impI)
  fix q
  assume pend_deq': "HasPendingDeq s' q"

  have his_eq: "his_seq s' = his_seq s" using step_facts by simp
  have s_var_eq: "s_var s' = s_var s" using step_facts by (simp add: s_var_def)

  have pend_deq_s: "HasPendingDeq s q"
    using pend_deq' his_eq s_var_eq unfolding HasPendingDeq_def DeqCallInHis_def Let_def by simp

  have inv_deq: "\<forall>p. HasPendingDeq s p \<longrightarrow> program_counter s p \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using hI27_Pending_PC_Sync_s unfolding hI27_Pending_PC_Sync_def by blast

  have pc_q_s: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using inv_deq pend_deq_s by blast

  have q_neq_p: "q \<noteq> p"
  proof
    assume "q = p"
    with pc_q_s have "program_counter s p \<in> {''D1'', ''D2'', ''D3'', ''D4''}" by simp
    moreover have "program_counter s p = ''E1''" using step_facts by simp
    ultimately show False by simp
  qed

  have pc_q_s': "program_counter s' q = program_counter s q"
    using step_facts q_neq_p pc_eqs by auto

  show "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using pc_q_s pc_q_s' by simp

next
  fix q
  assume pend_enq': "HasPendingEnq s' q (v_var s' q)"

  show "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
  proof (cases "q = p")
    case True
    have "program_counter s' p = ''E2''" using step_facts by simp
    then show ?thesis using True by simp
  next
    case False
    have his_eq: "his_seq s' = his_seq s" using step_facts by simp
    have s_var_eq: "s_var s' = s_var s" using step_facts by (simp add: s_var_def)
    have v_var_eq: "v_var s' q = v_var s q" using step_facts False by auto

    have pend_enq_s: "HasPendingEnq s q (v_var s q)"
      using pend_enq' his_eq s_var_eq v_var_eq unfolding HasPendingEnq_def EnqCallInHis_def Let_def by simp

    have inv_enq: "\<forall>p. HasPendingEnq s p (v_var s p) \<longrightarrow> program_counter s p \<in> {''E1'', ''E2'', ''E3''}"
      using hI27_Pending_PC_Sync_s unfolding hI27_Pending_PC_Sync_def by blast

    have pc_q_s: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using inv_enq pend_enq_s by blast

    have pc_q_s': "program_counter s' q = program_counter s q"
      using step_facts False pc_eqs by auto

    show ?thesis using pc_q_s pc_q_s' by simp
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for hI29_E2_Scanner_Immunity s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_e2_scanner_immune:
  fixes s s' :: SysState and p p_inv q :: nat and a v :: nat
  assumes INV: "system_invariant s"
    and not_InQBack_v: "\<not> InQBack s v"
    and v_def: "v = v_var s p"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and pc_eqs [simp]:
      "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<or> q = p)"
      "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
      "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
      "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
      "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'')"
      "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'')"
      "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
      "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
  shows "hI29_E2_Scanner_Immunity s'"
proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI, goal_cases)
  case (1 p_inv a q)

  from 1 have pc_p_E2': "program_counter s' p_inv = ''E2''" by blast
  from 1 have inqa': "InQBack s' a" by blast
  from 1 have tba': "TypeB s' a" by blast
  from 1 have pend_q': "HasPendingDeq s' q" by blast
  from 1 have pc_q_D3': "program_counter s' q = ''D3''" by blast
  from 1 have idx1': "Idx s' a < j_var s' q" by blast
  from 1 have idx2': "j_var s' q \<le> i_var s' p_inv" by blast
  from 1 have idx3': "i_var s' p_inv < l_var s' q" by blast

  have hI21_s: "hI29_E2_Scanner_Immunity s" using INV unfolding system_invariant_def by blast
  have sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" using INV unfolding system_invariant_def by blast

  have his_eq: "his_seq s' = his_seq s" using step_facts by simp
  have s_var_eq: "s_var s' = s_var s" using step_facts by (simp add: s_var_def)

  have q_neq_p: "q \<noteq> p"
  proof
    assume "q = p"
    with pc_q_D3' have "program_counter s' p = ''D3''" by simp
    moreover have "program_counter s' p = ''E2''" using step_facts by simp
    ultimately show False by simp
  qed

  have pc_q_s: "program_counter s q = ''D3''" using pc_q_D3' step_facts pc_eqs q_neq_p by auto
  have l_var_eq: "l_var s' q = l_var s q" using step_facts q_neq_p by auto

  show ?case
  proof (cases "p_inv = p")
    case True
    have "l_var s q \<le> X_var s" using sI6_D3_Scan_Pointers_s pc_q_s unfolding sI6_D3_Scan_Pointers_def by blast

    moreover have "l_var s' q = l_var s q" using l_var_eq by simp
    moreover have "i_var s' p = CState.X_var (fst s)" using step_facts unfolding C_E1_def
      using True calculation(1) idx3' by auto

    ultimately have "l_var s' q \<le> i_var s' p" by simp

    with idx3' True show "\<not> HB_EnqRetCall s' a (v_var s' p_inv)" by simp

  next
    case False
    have hb_eq: "HB_EnqRetCall s' a (v_var s' p_inv) = HB_EnqRetCall s a (v_var s p_inv)"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq step_facts False by auto

    have pc_p_s: "program_counter s p_inv = ''E2''" using pc_p_E2' False step_facts pc_eqs by auto
    have inqa_s: "InQBack s a" using inqa' step_facts unfolding InQBack_def by simp
    have tba_s: "TypeB s a" using tba' step_facts pc_eqs unfolding TypeB_def QHas_def
      by (metis inqa_s not_InQBack_v v_def)

    have pend_q_s: "HasPendingDeq s q" using pend_q' his_eq s_var_eq unfolding HasPendingDeq_def DeqCallInHis_def Let_def by simp
    have j_var_eq: "j_var s' q = j_var s q" using step_facts q_neq_p by auto

    have idx_eq: "\<And>x. Idx s' x = Idx s x" using step_facts unfolding Idx_def AtIdx_def by simp
    have i_var_eq: "i_var s' p_inv = i_var s p_inv" using step_facts False by auto

    have bound1: "Idx s a < j_var s q" using idx1' idx_eq j_var_eq by simp
    have bound2: "j_var s q \<le> i_var s p_inv" using idx2' j_var_eq i_var_eq by simp
    have bound3: "i_var s p_inv < l_var s q" using idx3' i_var_eq l_var_eq by simp

    have "\<not> HB_EnqRetCall s a (v_var s p_inv)"
      using hI21_s pc_p_s inqa_s tba_s pend_q_s pc_q_s bound1 bound2 bound3
      unfolding hI29_E2_Scanner_Immunity_def by blast

    then show "\<not> HB_EnqRetCall s' a (v_var s' p_inv)" using hb_eq by simp
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for hI30_Ticket_HB_Immunity s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_ticket_hb_immune:
  fixes s s' :: SysState and p q :: nat and b v :: nat
  assumes INV: "system_invariant s"
    and TypeB_s'_v: "TypeB s' v"
    and v_in_Val: "v \<in> Val"
    and not_InQBack_v: "\<not> InQBack s v"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and pc_eqs [simp]:
      "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<or> q = p)"
      "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
      "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
      "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
      "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'')"
      "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'')"
      "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
      "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
  shows "hI30_Ticket_HB_Immunity s'"
proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI, goal_cases)
  case (1 b q)

  from 1 have pc_q': "program_counter s' q \<in> {''E2'', ''E3''}" by blast
  from 1 have inqb': "InQBack s' b" by blast
  from 1 have b_not_bot': "b \<noteq> BOT" by blast
  from 1 have b_neq_v': "b \<noteq> v_var s' q" by blast
  from 1 have hb': "HB_EnqRetCall s' b (v_var s' q)" by blast

  have hI22_old: "hI30_Ticket_HB_Immunity s" using INV unfolding system_invariant_def by blast

  have his_eq: "his_seq s' = his_seq s" using step_facts by simp
  have T_eq: "Qback_arr s' = Qback_arr s" using step_facts by auto
  have idx_b_eq: "Idx s' b = Idx s b" unfolding Idx_def AtIdx_def using T_eq by simp

  show "Idx s' b < i_var s' q"
  proof (cases "q = p")
    case True
    have i_var_p_new: "i_var s' p = CState.X_var (fst s)"
      using step_facts unfolding C_E1_def by (simp add: Model.X_var_def)

    have inqb_s: "InQBack s b" using inqb' T_eq unfolding InQBack_def by simp

    have ai1: "sI2_X_var_Upper_Bound s" using INV unfolding system_invariant_def by blast

    have idx_lt_X: "Idx s b < CState.X_var (fst s)"
    proof (rule ccontr)
      assume "\<not> (Idx s b < CState.X_var (fst s))"
      hence ge_X: "Idx s b \<ge> CState.X_var (fst s)" by simp

      have "Qback_arr s (Idx s b) = BOT"
        using ai1 ge_X unfolding sI2_X_var_Upper_Bound_def
        using i_var_p_new by fastforce

      moreover have "Qback_arr s (Idx s b) = b"
      proof -
        from inqb_s obtain k_idx where "Qback_arr s k_idx = b" unfolding InQBack_def by blast
        thus ?thesis unfolding Idx_def AtIdx_def by (metis (mono_tags) someI_ex)
      qed
      ultimately show False using b_not_bot' by simp
    qed

    thus ?thesis using True i_var_p_new idx_b_eq by simp

  next
    case False
    have q_neq_p: "q \<noteq> p" using False by simp

    have pc_q_s: "program_counter s q \<in> {''E2'', ''E3''}"
      using pc_q' q_neq_p step_facts pc_eqs by auto
    have v_var_eq: "v_var s' q = v_var s q" using q_neq_p step_facts by auto
    have i_var_eq: "i_var s' q = i_var s q" using q_neq_p step_facts by auto

    have inqb_s: "InQBack s b" using inqb' T_eq unfolding InQBack_def by simp
    have b_neq_v_s: "b \<noteq> v_var s q" using b_neq_v' v_var_eq by simp

    have hb_eq: "HB_EnqRetCall s' b (v_var s' q) = HB_EnqRetCall s b (v_var s q)"
      unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
      using his_eq v_var_eq by auto
    have hb_s: "HB_EnqRetCall s b (v_var s q)" using hb' hb_eq by simp

    have "Idx s b < i_var s q"
      using hI22_old pc_q_s inqb_s b_not_bot' b_neq_v_s hb_s
      unfolding hI30_Ticket_HB_Immunity_def by blast

    thus ?thesis using idx_b_eq i_var_eq by simp
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for OP_B_enq_new . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_op_b_enq_new:
  fixes s s' :: SysState and p :: nat and v :: nat and new_act :: OpRec
  assumes his_eq: "his_seq s' = his_seq s"
    and setB_new: "SetB s' = insert v (SetB s)"
    and hI8_Val_Unique_s: "hI8_Val_Unique s"
    and call_p: "EnqCallInHis s p v (s_var s p)"
    and v_in_Val: "v \<in> Val"
    and TypeB_s'_v: "TypeB s' v"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "OP_B_enq s' = insert new_act (OP_B_enq s)"
proof (intro equalityI subsetI, goal_cases)
  case (1 act)

  from 1 obtain q b sn where
    act_eq: "act = mk_op enq b q sn" and
    b_in': "b \<in> SetB s'" and
    call_b': "EnqCallInHis s' q b sn"
    unfolding OP_B_enq_def by blast

  show ?case
  proof (cases "b = v")
    case True
    have call_b: "EnqCallInHis s q v sn"
      using call_b' True EnqCallInHis_his_eq[OF his_eq] by simp

    have "q = p \<and> sn = s_var s p"
      using hI8_Val_Unique_s call_p call_b unfolding hI8_Val_Unique_def
      by (smt (verit, best) EnqCallInHis_def in_set_conv_nth)

    hence "act = mk_op enq v p (s_var s p)" using act_eq True by simp
    hence "act = new_act" unfolding new_act_def by simp

    thus ?thesis by simp
  next
    case False
    have b_in_s: "b \<in> SetB s" using b_in' setB_new False by auto
    have call_b_s: "EnqCallInHis s q b sn" using call_b' EnqCallInHis_his_eq[OF his_eq] by simp

    have "act \<in> OP_B_enq s"
      unfolding OP_B_enq_def using act_eq b_in_s call_b_s by blast
    thus ?thesis by simp
  qed

next
  case (2 act)

  show ?case
  proof (cases "act = new_act")
    case True
    have act_eq: "new_act = mk_op enq v p (s_var s p)" unfolding new_act_def by simp
    have v_in': "v \<in> SetB s'" using v_in_Val TypeB_s'_v unfolding SetB_def by simp
    have call_v': "EnqCallInHis s' p v (s_var s p)" using call_p EnqCallInHis_his_eq[OF his_eq] by simp

    show ?thesis using True act_eq v_in' call_v' unfolding OP_B_enq_def by blast
  next
    case False
    from 2 False have "act \<in> OP_B_enq s" by simp
    then obtain q b sn where
      act_eq: "act = mk_op enq b q sn" and
      b_in: "b \<in> SetB s" and
      call_b: "EnqCallInHis s q b sn"
      unfolding OP_B_enq_def by blast

    have b_in': "b \<in> SetB s'" using b_in setB_new by auto
    have call_b': "EnqCallInHis s' q b sn" using call_b EnqCallInHis_his_eq[OF his_eq] by simp

    show ?thesis unfolding OP_B_enq_def using act_eq b_in' call_b' by blast
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for lI2_Op_Cardinality_s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_op_cardinality:
  fixes s s' :: SysState and p :: nat and v :: nat and new_act :: OpRec
  assumes INV: "system_invariant s"
    and setA_eq: "SetA s' = SetA s"
    and setB_new: "SetB s' = insert v (SetB s)"
    and TypeB_s'_v: "TypeB s' v"
    and v_in_Val: "v \<in> Val"
    and not_InQBack_v: "\<not> InQBack s v"
    and pc_p_E1: "program_counter s p = ''E1''"
    and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s"
    and hI8_Val_Unique_s: "hI8_Val_Unique s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
    and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
    and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s"
    and di_lin_s: "data_independent (lin_seq s)"
    and call_p: "EnqCallInHis s p v (s_var s p)"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "lI2_Op_Cardinality s'"
  unfolding lI2_Op_Cardinality_def
proof (rule conjI)
  show "\<forall>a. a \<in> SetA s' \<longrightarrow> card (EnqIdxs s' a) = 1 \<and> card (DeqIdxs s' a) = 1"
  proof (intro allI impI)
    fix a assume a_in_s': "a \<in> SetA s'"
    have a_in_s: "a \<in> SetA s" using a_in_s' setA_eq by simp
    have lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" using INV unfolding system_invariant_def by blast
    from lI2_Op_Cardinality_s a_in_s have enq_old: "card (EnqIdxs s a) = 1" and deq_old: "card (DeqIdxs s a) = 1"
      unfolding lI2_Op_Cardinality_def by blast+

    have a_neq_v: "a \<noteq> v"
    proof (rule ccontr)
      assume "\<not> a \<noteq> v" hence "a = v" by simp
      with a_in_s have "v \<in> SetA s" by simp
      moreover have "v \<in> SetB s'" using v_in_Val TypeB_s'_v unfolding SetB_def by simp
      ultimately show False using SetA_def SetB_def setB_new
        using TypeA_def not_InQBack_v by blast
    qed

    have "EnqIdxs s' a = EnqIdxs s a"
      unfolding EnqIdxs_def lin_eq new_act_def mk_op_def op_name_def op_val_def
      using a_neq_v by (auto simp: nth_append less_Suc_eq)
    moreover have "DeqIdxs s' a = DeqIdxs s a"
      unfolding DeqIdxs_def lin_eq new_act_def mk_op_def op_name_def op_val_def
      by (auto simp: nth_append less_Suc_eq)
    ultimately show "card (EnqIdxs s' a) = 1 \<and> card (DeqIdxs s' a) = 1"
      using enq_old deq_old by simp
  qed

next
  show "\<forall>b. b \<in> SetB s' \<longrightarrow> card (EnqIdxs s' b) = 1 \<and> card (DeqIdxs s' b) = 0"
  proof (intro allI impI)
    fix b assume b_in_s': "b \<in> SetB s'"
    have lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" using INV unfolding system_invariant_def by blast

    show "card (EnqIdxs s' b) = 1 \<and> card (DeqIdxs s' b) = 0"
    proof (cases "b = v")
      case True
      have enq_old_empty: "EnqIdxs s v = {}"
      proof (rule equals0I)
        fix k assume "k \<in> EnqIdxs s v"
        hence k_prop: "k < length (lin_seq s)" "op_name (lin_seq s ! k) = enq" "op_val (lin_seq s ! k) = v"
          unfolding EnqIdxs_def by simp_all

        have v_not_in_SetB_s: "v \<notin> SetB s"
        proof
          assume "v \<in> SetB s"
          then have "TypeB s v" unfolding SetB_def by blast
          thus False
          proof (cases "QHas s v")
            case True
            then have "InQBack s v" using sI8_Q_Qback_Sync_s unfolding QHas_def InQBack_def sI8_Q_Qback_Sync_def
              by (metis sI1_Zero_Index_BOT_def sI1_Zero_Index_BOT_s)
            thus ?thesis using not_InQBack_v by blast
          next
            case False
            then obtain q where "program_counter s q = ''E2''" and "v_var s q = v"
              using \<open>TypeB s v\<close> unfolding TypeB_def by blast
            have "q \<noteq> p" using pc_p_E1 \<open>program_counter s q = ''E2''\<close> by auto
            have "HasPendingEnq s q v" using hI1_E_Phase_Pending_Enq_s \<open>program_counter s q = ''E2''\<close> unfolding hI1_E_Phase_Pending_Enq_def
              using \<open>Model.v_var s q = v\<close> by blast
            then have "EnqCallInHis s q v (s_var s q)" unfolding HasPendingEnq_def
              by metis
            also have "EnqCallInHis s p v (s_var s p)" using call_p by simp
            with hI8_Val_Unique_s have "q = p" unfolding hI8_Val_Unique_def
              using EnqCallInHis_unique_pid calculation hI8_Val_Unique_s
              by blast
            with \<open>q \<noteq> p\<close> show False by contradiction
          qed
        qed

        have v_fresh: "\<forall>i < length (lin_seq s). op_name (lin_seq s ! i) = enq \<longrightarrow> op_val (lin_seq s ! i) \<noteq> v"
        proof (intro allI impI)
          fix i assume i_lt: "i < length (lin_seq s)" and enq_i: "op_name (lin_seq s ! i) = enq"
          have "lin_seq s ! i \<in> OPLin s" using i_lt unfolding OPLin_def by auto
          hence "lin_seq s ! i \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
            using lI1_Op_Sets_Equivalence_s unfolding lI1_Op_Sets_Equivalence_def by blast
          hence "op_val (lin_seq s ! i) \<in> SetA s \<or> op_val (lin_seq s ! i) \<in> SetB s"
            unfolding OP_A_enq_def OP_A_deq_def OP_B_enq_def
            using enq_i
            using i_lt lI1_Op_Sets_Equivalence_s lin_seq_no_value_if_not_in_SetA_SetB
            by blast
          moreover have "v \<notin> SetA s"
            using not_InQBack_v unfolding SetA_def TypeA_def by auto
          moreover have "v \<notin> SetB s" using v_not_in_SetB_s .
          ultimately show "op_val (lin_seq s ! i) \<noteq> v" by blast
        qed

        have di_s': "data_independent (lin_seq s')"
          using data_independent_append_enq_fresh[OF di_lin_s v_fresh, of p "s_var s p"]
          unfolding new_act_def
          by (simp add: new_act_def)

        have card_le_1: "card {i. i < length (lin_seq s') \<and> op_name (lin_seq s' ! i) = enq \<and> op_val (lin_seq s' ! i) = v} \<le> 1"
          using di_s' unfolding data_independent_def by auto
        have set_eq: "{i. i < length (lin_seq s') \<and> op_name (lin_seq s' ! i) = enq \<and> op_val (lin_seq s' ! i) = v} = EnqIdxs s' v"
          unfolding EnqIdxs_def by blast
        have card_bound: "card (EnqIdxs s' v) \<le> 1" using card_le_1 set_eq by simp
        have fin_set: "finite (EnqIdxs s' v)" unfolding EnqIdxs_def by simp
        have "lin_seq s' ! k = lin_seq s ! k" using lin_eq k_prop(1) by (simp add: nth_append)
        hence k_in_new: "k \<in> EnqIdxs s' v" unfolding EnqIdxs_def using k_prop lin_eq by auto
        have new_idx_in_new: "length (lin_seq s) \<in> EnqIdxs s' v"
          unfolding EnqIdxs_def using new_act_def lin_eq mk_op_def op_name_def op_val_def by (auto simp: nth_append)
        have "EnqIdxs s' v = {} \<or> (\<exists>x. EnqIdxs s' v = {x})"
          using card_bound fin_set
          by (metis card_1_singletonE card_eq_0_iff dual_order.order_iff_strict less_one)
        moreover have "EnqIdxs s' v \<noteq> {}" using k_in_new by blast
        ultimately obtain x where "EnqIdxs s' v = {x}" by blast
        hence "k = x" and "length (lin_seq s) = x" using k_in_new new_idx_in_new by blast+
        hence "k = length (lin_seq s)" by simp
        thus False using k_prop(1) by simp
      qed

      have deq_old_empty: "DeqIdxs s v = {}"
      proof (rule equals0I)
        fix k assume "k \<in> DeqIdxs s v"
        hence k_prop: "k < length (lin_seq s)" "op_name (lin_seq s ! k) = deq" "op_val (lin_seq s ! k) = v"
          unfolding DeqIdxs_def by simp_all
        have "\<exists>k2 < k. op_name (lin_seq s ! k2) = enq \<and> op_val (lin_seq s ! k2) = v"
          using lI4_FIFO_Semantics_s k_prop unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def Let_def by blast
        then obtain k2 where "k2 < k" "op_name (lin_seq s ! k2) = enq" "op_val (lin_seq s ! k2) = v" by blast
        hence "k2 \<in> EnqIdxs s v" unfolding EnqIdxs_def using k_prop(1) by simp
        thus False using enq_old_empty by blast
      qed

      have "EnqIdxs s' v = {length (lin_seq s)}"
        using enq_old_empty unfolding EnqIdxs_def lin_eq new_act_def mk_op_def op_name_def op_val_def
        by (auto simp: nth_append less_Suc_eq)
      moreover have "DeqIdxs s' v = {}"
        using deq_old_empty unfolding DeqIdxs_def lin_eq new_act_def mk_op_def op_name_def op_val_def
        by (auto simp: nth_append less_Suc_eq)
      ultimately show ?thesis using True by simp
    next
      case False
      have b_in_s: "b \<in> SetB s" using b_in_s' False by (simp add: setB_new)

      have v_not_in_SetB_s: "v \<notin> SetB s"
      proof
        assume "v \<in> SetB s"
        then have "TypeB s v" unfolding SetB_def by blast
        thus False
        proof (cases "QHas s v")
          case True
          then have "InQBack s v" using sI8_Q_Qback_Sync_s unfolding QHas_def InQBack_def sI8_Q_Qback_Sync_def
            by (metis sI1_Zero_Index_BOT_def sI1_Zero_Index_BOT_s)
          thus ?thesis using not_InQBack_v by blast
        next
          case False
          then obtain q where "program_counter s q = ''E2''" and "v_var s q = v"
            using \<open>TypeB s v\<close> unfolding TypeB_def by blast
          have "q \<noteq> p" using pc_p_E1 \<open>program_counter s q = ''E2''\<close> by auto
          have "HasPendingEnq s q v" using hI1_E_Phase_Pending_Enq_s \<open>program_counter s q = ''E2''\<close> unfolding hI1_E_Phase_Pending_Enq_def
            using \<open>Model.v_var s q = v\<close> by blast
          then have "EnqCallInHis s q v (s_var s q)" unfolding HasPendingEnq_def
            by meson
          also have "EnqCallInHis s p v (s_var s p)" using call_p by simp
          with hI8_Val_Unique_s have "q = p" unfolding hI8_Val_Unique_def
            using EnqCallInHis_unique_pid calculation hI8_Val_Unique_s
            by blast
          with \<open>q \<noteq> p\<close> show False by contradiction
        qed
      qed

      from lI2_Op_Cardinality_s b_in_s have enq_old: "card (EnqIdxs s b) = 1" and deq_old: "card (DeqIdxs s b) = 0"
        unfolding lI2_Op_Cardinality_def by blast+
      have "EnqIdxs s' b = EnqIdxs s b"
        unfolding EnqIdxs_def lin_eq new_act_def mk_op_def op_name_def op_val_def
        using False by (auto simp: nth_append less_Suc_eq)
      moreover have "DeqIdxs s' b = DeqIdxs s b"
        unfolding DeqIdxs_def lin_eq new_act_def mk_op_def op_name_def op_val_def
        by (auto simp: nth_append less_Suc_eq)
      ultimately show ?thesis using enq_old deq_old by simp
    qed
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for lI3_HB_Ret_Lin_Sync s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_hb_ret_lin_sync:
  fixes s s' :: SysState and p :: nat and v :: nat and new_act :: OpRec
  assumes INV: "system_invariant s"
    and step_facts [simp]: "his_seq s' = his_seq s"
    and his_eq: "his_seq s' = his_seq s"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and pend_p: "HasPendingEnq s p v"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "lI3_HB_Ret_Lin_Sync s'"
proof (unfold lI3_HB_Ret_Lin_Sync_def, intro conjI allI impI, goal_cases)
  case (1 k1 k2)
  from 1 have k1_lt: "k1 < length (lin_seq s')" and k2_lt: "k2 < length (lin_seq s')" by blast+
  from 1 have hb_new: "HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2)" by blast

  have lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" using INV unfolding system_invariant_def by blast

  have no_ret_v: "\<not> (\<exists>h < length (his_seq s'). match_ret (his_seq s') h new_act)"
  proof (rule notI, elim exE conjE)
    fix h assume h_lt: "h < length (his_seq s')"
             and h_match: "match_ret (his_seq s') h new_act"

    have h_pid: "act_pid (his_seq s' ! h) = p"
     and h_ssn: "act_ssn (his_seq s' ! h) = s_var s p"
     and h_ret: "act_cr (his_seq s' ! h) = ret"
      using h_match unfolding match_ret_def new_act_def mk_op_def Let_def
      by (auto simp: op_pid_def op_ssn_def op_name_def op_val_def)

    have "h < length (his_seq s) \<or> h = length (his_seq s)"
      using h_lt by (auto simp: less_Suc_eq)
    thus False
    proof
      assume h_old: "h < length (his_seq s)"
      hence "act_pid (his_seq s ! h) = p"
        and "act_ssn (his_seq s ! h) = s_var s p"
        and "act_cr (his_seq s ! h) = ret"
        using h_pid h_ssn h_ret h_old his_eq by (simp_all add: nth_append)

      with pend_p show False
        unfolding HasPendingEnq_def Let_def
        using h_old by fastforce
    next
      assume h_new: "h = length (his_seq s)"
      hence "act_cr (his_seq s' ! h) = call"
        using step_facts his_eq
        using h_lt by auto
      with h_ret show False by simp
    qed
  qed

  show "k1 < k2"
  proof (cases "k2 = length (lin_seq s)")
    case True
    have "k1 \<noteq> k2"
    proof
      assume "k1 = k2"
      hence "lin_seq s' ! k1 = new_act" and "lin_seq s' ! k2 = new_act"
        using True by simp_all
      with hb_new have hb_self: "HB_Act s' new_act new_act" by simp

      from hb_self obtain h1  where
        "h1 < length (his_seq s')" and "match_ret (his_seq s') h1 new_act"
        unfolding HB_Act_def HB_def
        using match_ret_def by blast

      with \<open>match_ret (his_seq s') h1 new_act\<close> and \<open>h1 < length (his_seq s')\<close>
      show False
        using no_ret_v by auto
    qed

    then show ?thesis using k1_lt True by simp
  next
    case False
    hence k2_old: "k2 < length (lin_seq s)" using k2_lt by simp

    have k1_old: "k1 < length (lin_seq s)"
    proof (rule ccontr)
      assume "\<not> k1 < length (lin_seq s)"
      hence "k1 = length (lin_seq s)" using k1_lt by simp
      hence "lin_seq s' ! k1 = new_act" by simp
      with hb_new have "HB_Act s' new_act (lin_seq s' ! k2)" by simp

      moreover have "\<not> (\<exists>act_target. HB_Act s' new_act act_target)"
      proof (rule notI)
        assume "\<exists>act_target. HB_Act s' new_act act_target"
        then obtain act_target where hb: "HB_Act s' new_act act_target" by blast

        then obtain h1 where "h1 < length (his_seq s')" and "match_ret (his_seq s') h1 new_act"
          unfolding HB_Act_def HB_def
          using match_ret_def by blast

        with no_ret_v show False by blast
      qed

      ultimately show False by blast
    qed

    have "HB_Act s (lin_seq s ! k1) (lin_seq s ! k2)"
      using hb_new k1_old k2_old his_eq lin_eq
      unfolding HB_Act_def HB_def match_ret_def match_call_def Let_def
      by (metis nth_append_left)

    thus ?thesis using lI3_HB_Ret_Lin_Sync_s k1_old k2_old unfolding lI3_HB_Ret_Lin_Sync_def by blast
  qed

next
  case (2 p a sn)
  have "EnqRetInHis s' p a sn = EnqRetInHis s p a sn"
    unfolding EnqRetInHis_def using his_eq by auto
  hence "EnqRetInHis s p a sn" using 2 by simp

  then obtain k where "k < length (lin_seq s)" "lin_seq s ! k = mk_op enq a p sn"
    using INV unfolding system_invariant_def lI3_HB_Ret_Lin_Sync_def by blast
  thus ?case using lin_eq by (auto simp: nth_append)

next
  case (3 p a sn)
  have "DeqRetInHis s' p a sn = DeqRetInHis s p a sn"
    unfolding DeqRetInHis_def using his_eq by auto
  hence "DeqRetInHis s p a sn" using 3 by simp

  then obtain k where "k < length (lin_seq s)" "lin_seq s ! k = mk_op deq a p sn"
    using INV unfolding system_invariant_def lI3_HB_Ret_Lin_Sync_def by blast
  thus ?case using lin_eq by (auto simp: nth_append)
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for lI4_FIFO_Semantics s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_fifo_semantics:
  fixes s s' :: SysState and p :: nat and v :: nat and new_act :: OpRec
  assumes INV: "system_invariant s"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "lI4_FIFO_Semantics s'"
  unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def Let_def
proof (intro allI impI)
  fix k
  assume k_lt_s': "k < length (lin_seq s')"
  assume deq_k: "op_name (lin_seq s' ! k) = deq"

  have lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" using INV unfolding system_invariant_def by blast

  show "\<exists>k2<k. op_name (lin_seq s' ! k2) = enq \<and>
               op_val (lin_seq s' ! k2) = op_val (lin_seq s' ! k) \<and>
               (\<forall>k3<k2. op_name (lin_seq s' ! k3) = enq \<longrightarrow>
                   (\<exists>k4>k3. k4 < k \<and> op_name (lin_seq s' ! k4) = deq \<and> op_val (lin_seq s' ! k4) = op_val (lin_seq s' ! k3)))"
  proof (cases "k < length (lin_seq s)")
    case False
    have k_eq: "k = length (lin_seq s)"
      using k_lt_s' False by (simp add: less_Suc_eq)

    have "op_name (lin_seq s' ! k) = enq"
      using k_eq new_act_def lin_eq mk_op_def op_name_def by (simp add: nth_append)

    with deq_k show ?thesis by simp
  next
    case True
    have fifo_s: "op_name (lin_seq s ! k) = deq \<longrightarrow>
      (\<exists>k2<k. op_name (lin_seq s ! k2) = enq \<and> op_val (lin_seq s ! k2) = op_val (lin_seq s ! k) \<and>
        (\<forall>k3<k2. op_name (lin_seq s ! k3) = enq \<longrightarrow>
          (\<exists>k4>k3. k4 < k \<and> op_name (lin_seq s ! k4) = deq \<and> op_val (lin_seq s ! k4) = op_val (lin_seq s ! k3))))"
      using lI4_FIFO_Semantics_s True unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def Let_def by blast

    have deq_s_k: "op_name (lin_seq s ! k) = deq"
      using deq_k True lin_eq by (simp add: nth_append)

    from fifo_s deq_s_k obtain k2 where
      k2_lt: "k2 < k" and
      k2_enq: "op_name (lin_seq s ! k2) = enq" and
      k2_val: "op_val (lin_seq s ! k2) = op_val (lin_seq s ! k)" and
      k2_fifo: "\<forall>k3<k2. op_name (lin_seq s ! k3) = enq \<longrightarrow>
                 (\<exists>k4>k3. k4 < k \<and> op_name (lin_seq s ! k4) = deq \<and> op_val (lin_seq s ! k4) = op_val (lin_seq s ! k3))"
      by blast

    show ?thesis
    proof (intro exI[where x=k2] conjI)
      show "k2 < k" using k2_lt .
      show "op_name (lin_seq s' ! k2) = enq"
        using k2_enq k2_lt True lin_eq by (simp add: nth_append)
      show "op_val (lin_seq s' ! k2) = op_val (lin_seq s' ! k)"
        using k2_val k2_lt True lin_eq by (simp add: nth_append)
      show "\<forall>k3<k2. op_name (lin_seq s' ! k3) = enq \<longrightarrow>
             (\<exists>k4>k3. k4 < k \<and> op_name (lin_seq s' ! k4) = deq \<and> op_val (lin_seq s' ! k4) = op_val (lin_seq s' ! k3))"
      proof (intro allI impI)
        fix k3 assume k3_lt: "k3 < k2" and enq_s'_k3: "op_name (lin_seq s' ! k3) = enq"
        have k3_lt_k: "k3 < k" using k3_lt k2_lt by simp
        have enq_s_k3: "op_name (lin_seq s ! k3) = enq"
          using enq_s'_k3 k3_lt_k True lin_eq by (simp add: nth_append)
        from k2_fifo k3_lt enq_s_k3 obtain k4 where
          k4_gt: "k3 < k4" and k4_lt: "k4 < k" and
          deq_s_k4: "op_name (lin_seq s ! k4) = deq" and
          val_s_k4: "op_val (lin_seq s ! k4) = op_val (lin_seq s ! k3)"
          by blast
        show "\<exists>k4>k3. k4 < k \<and> op_name (lin_seq s' ! k4) = deq \<and> op_val (lin_seq s' ! k4) = op_val (lin_seq s' ! k3)"
        proof (intro exI[where x=k4] conjI)
          show "k3 < k4" using k4_gt .
          show "k4 < k" using k4_lt .
          show "op_name (lin_seq s' ! k4) = deq"
            using deq_s_k4 k4_lt True lin_eq by (simp add: nth_append)
          show "op_val (lin_seq s' ! k4) = op_val (lin_seq s' ! k3)"
            using val_s_k4 k4_lt k3_lt_k True lin_eq by (simp add: nth_append)
        qed
      qed
    qed
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for lI5_SA_Prefix s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_sa_prefix:
  fixes s s' :: SysState and p :: nat and v :: nat and new_act :: OpRec
  assumes INV: "system_invariant s"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
    and TypeB_s'_v: "TypeB s' v"
    and v_in_Val: "v \<in> Val"
    and lI2_Op_Cardinality_s': "lI2_Op_Cardinality s'"
    and lI1_Op_Sets_Equivalence_s': "lI1_Op_Sets_Equivalence s'"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
    and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s"
    and setA_eq: "SetA s' = SetA s"
    and not_InQBack_v: "\<not> InQBack s v"
  shows "lI5_SA_Prefix s'"
proof (unfold lI5_SA_Prefix_def lI5_SA_Prefix_list_def, intro allI impI, goal_cases)
  case (1 k)
  then have k_lt: "k < length (lin_seq s')"
        and enq_k: "op_name (lin_seq s' ! k) = enq"
    by simp_all

  let ?L = "lin_seq s"
  let ?L' = "lin_seq s'"
  let ?new = "new_act"
  let ?v = "v"

  have L'_def: "?L' = ?L @ [?new]" using lin_eq by simp
  have new_is_enq: "op_name ?new = enq" unfolding new_act_def mk_op_def op_name_def by simp

  have v_not_SA: "\<not> in_SA v ?L'"
  proof -
    have "v \<in> SetB s'"
      using TypeB_s'_v unfolding SetB_def by (simp add: v_in_Val)
    hence card_0: "card (DeqIdxs s' v) = 0"
      using lI2_Op_Cardinality_s' unfolding lI2_Op_Cardinality_def by blast
    have fin_deq: "finite (DeqIdxs s' v)"
      unfolding DeqIdxs_def by auto
    have empty_deq: "DeqIdxs s' v = {}"
      using fin_deq card_0 by auto
    have no_deq_elem: "\<forall>a \<in> set ?L'. \<not> (op_name a = deq \<and> op_val a = v)"
      using empty_deq unfolding DeqIdxs_def set_conv_nth by auto
    thus ?thesis
      unfolding in_SA_def find_unique_index_def Let_def
      by (smt (verit) find_unique_index_def find_unique_index_prop nth_mem
          option.simps(4,5))
  qed

  have last_SA_eq: "find_last_SA ?L' = find_last_SA ?L"
  proof -
    let ?P = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) ?L'"
    let ?Q = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) ?L"

    have PQ_eq: "\<forall>a \<in> set ?L. ?P a = ?Q a"
    proof (intro ballI)
      fix a assume a_in: "a \<in> set ?L"
      show "?P a = ?Q a"
      proof (cases "op_val a = v", goal_cases)
        case 1
        then have a_is_v: "op_val a = v" by simp
        have "\<not> ?Q a" using lI2_Op_Cardinality_s unfolding lI2_Op_Cardinality_def
          by (metis SetA_equivalent_in_SA \<open>lI1_Op_Sets_Equivalence s'\<close> a_is_v lI1_Op_Sets_Equivalence_s lI2_Op_Cardinality_s lI2_Op_Cardinality_s' setA_eq v_not_SA)
        moreover have "\<not> ?P a" using v_not_SA a_is_v by (auto simp: in_SA_def)
        ultimately show ?case by auto
      next
        case 2
        then have a_not_v: "op_val a \<noteq> v" by simp
        thus ?case using SetA_equivalent_in_SA \<open>lI1_Op_Sets_Equivalence s'\<close> lI1_Op_Sets_Equivalence_s lI2_Op_Cardinality_s lI2_Op_Cardinality_s' setA_eq by blast
      qed
    qed

    have not_P_new: "\<not> ?P ?new"
      using v_not_SA new_is_enq unfolding new_act_def mk_op_def op_val_def by simp

    have idx_eq: "\<forall>i < length ?L'. ?P (?L' ! i) \<longleftrightarrow> (i < length ?L \<and> ?Q (?L ! i))"
    proof (intro allI impI)
      fix i assume "i < length ?L'"
      show "?P (?L' ! i) \<longleftrightarrow> (i < length ?L \<and> ?Q (?L ! i))"
      proof (cases "i < length ?L")
        case True
        have "?L' ! i = ?L ! i" using True L'_def by (simp add: nth_append)
        moreover have "?L ! i \<in> set ?L" using True by simp
        ultimately show ?thesis using PQ_eq True by simp
      next
        case False
        hence "i = length ?L" using \<open>i < length ?L'\<close> by simp
        hence "?L' ! i = ?new" by simp
        thus ?thesis using not_P_new False by simp
      qed
    qed

    have "find_indices ?P ?L' = find_indices ?Q ?L"
    proof -
      have "find_indices ?P ?L' = [i \<leftarrow> [0..<length ?L'] . ?P (?L' ! i)]"
        unfolding find_indices_def ..
      also have "... = [i \<leftarrow> [0..<length ?L] @ [length ?L] . ?P (?L' ! i)]"
        using L'_def by simp
      also have "... = [i \<leftarrow> [0..<length ?L] . ?P (?L' ! i)] @ [i \<leftarrow> [length ?L] . ?P (?L' ! i)]"
        by simp
      also have "... = [i \<leftarrow> [0..<length ?L] . ?Q (?L ! i)] @ []"
      proof -
        have part1: "[i \<leftarrow> [0..<length ?L] . ?P (?L' ! i)] = [i \<leftarrow> [0..<length ?L] . ?Q (?L ! i)]"
        proof (rule filter_cong)
          show "[0..<length ?L] = [0..<length ?L]" ..
          fix x assume "x \<in> set [0..<length ?L]"
          hence "x < length ?L" by simp
          thus "?P (?L' ! x) = ?Q (?L ! x)" using idx_eq by simp
        qed
        have part2: "[i \<leftarrow> [length ?L] . ?P (?L' ! i)] = []"
        proof -
          have "?L' ! (length ?L) = ?new"
            using L'_def by (simp add: nth_append)
          thus ?thesis using not_P_new by simp
        qed
        show ?thesis using part1 part2 by simp
      qed
      also have "... = find_indices ?Q ?L"
        unfolding find_indices_def by simp
      finally show ?thesis .
    qed

    thus ?thesis unfolding find_last_SA_def Let_def by simp
  qed

  show ?case
  proof (cases "k < length ?L", goal_cases)
    case 1
    then have k_old: "k < length ?L" by simp
    have act_k: "?L' ! k = ?L ! k" by (simp add: nth_append k_old)
    let ?a = "op_val (?L ! k)"
    let ?op = "op_name (?L ! k)"

    have lI5_SA_Prefix_s: "lI5_SA_Prefix s" using INV unfolding system_invariant_def by blast
    have equiv_old: "?op = enq \<longrightarrow> (in_SA ?a ?L \<longleftrightarrow> int k \<le> find_last_SA ?L)"
      using lI5_SA_Prefix_s k_old unfolding lI5_SA_Prefix_def lI5_SA_Prefix_list_def by blast

    have in_SA_eq: "in_SA ?a ?L' = in_SA ?a ?L"
    proof (cases "?a = v", goal_cases)
      case 1
      then have a_is_v: "?a = v" by simp

      have "EnqIdxs s v = {}"
      proof (rule equals0I)
        fix i assume "i \<in> EnqIdxs s v"
        hence i_lt: "i < length ?L"
          and enq_i: "op_name (?L ! i) = enq"
          and val_i: "op_val (?L ! i) = v"
          unfolding EnqIdxs_def by auto

        have "i < length ?L'" using i_lt L'_def by simp
        moreover have "?L' ! i = ?L ! i" using i_lt L'_def by (simp add: nth_append)
        ultimately have i_in_s': "i \<in> EnqIdxs s' v"
          using enq_i val_i unfolding EnqIdxs_def by auto

        let ?new_idx = "length ?L"
        have "?new_idx < length ?L'" using L'_def by simp
        moreover have "?L' ! ?new_idx = ?new" using L'_def by (simp add: nth_append)
        ultimately have new_in_s': "?new_idx \<in> EnqIdxs s' v"
          unfolding EnqIdxs_def new_act_def mk_op_def op_val_def op_name_def by simp

        have i_neq: "i \<noteq> ?new_idx" using i_lt by simp

        have "v \<in> SetB s'" using TypeB_s'_v unfolding SetB_def by (simp add: v_in_Val)
        hence card_1: "card (EnqIdxs s' v) = 1" using lI2_Op_Cardinality_s' unfolding lI2_Op_Cardinality_def by auto

        have fin: "finite (EnqIdxs s' v)" unfolding EnqIdxs_def by auto
        have sub: "{i, ?new_idx} \<subseteq> EnqIdxs s' v" using i_in_s' new_in_s' by auto

        have "card {i, ?new_idx} = 2" using i_neq by simp
        moreover have "card {i, ?new_idx} \<le> card (EnqIdxs s' v)"
          using card_mono[OF fin sub] by simp
        ultimately show False using card_1 by simp
      qed

      hence "\<nexists>i. i < length ?L \<and> op_name (?L ! i) = enq \<and> op_val (?L ! i) = v" unfolding EnqIdxs_def by auto
      hence "\<not> in_SA v ?L" unfolding in_SA_def
        using a_is_v act_k enq_k k_old by force
      moreover have "\<not> in_SA v ?L'" using v_not_SA by simp
      ultimately show ?case using a_is_v by simp
    next
      case 2
      then have a_not_v: "?a \<noteq> v" by simp
      have in_SA_eq: "in_SA ?a ?L' = in_SA ?a ?L"
      proof -
        let ?P_enq = "\<lambda>a. op_name a = enq \<and> op_val a = ?a"
        let ?P_deq = "\<lambda>a. op_name a = deq \<and> op_val a = ?a"

        have enq_idx: "find_indices ?P_enq ?L' = find_indices ?P_enq ?L"
        proof -
          have "find_indices ?P_enq ?L' = [i \<leftarrow> [0..<length ?L'] . ?P_enq (?L' ! i)]"
            unfolding find_indices_def ..
          also have "... = [i \<leftarrow> [0..<length ?L] @ [length ?L] . ?P_enq (?L' ! i)]"
            by simp
         also have "... = [i \<leftarrow> [0..<length ?L] . ?P_enq (?L' ! i)] @ [i \<leftarrow> [length ?L] . ?P_enq (?L' ! i)]"
            by simp
          also have "... = [i \<leftarrow> [0..<length ?L] . ?P_enq (?L ! i)] @ [i \<leftarrow> [length ?L] . ?P_enq (?new)]"
          proof -
            have "[i \<leftarrow> [0..<length ?L] . ?P_enq (?L' ! i)] = [i \<leftarrow> [0..<length ?L] . ?P_enq (?L ! i)]"
            proof (rule filter_cong)
              show "[0..<length ?L] = [0..<length ?L]" ..
              fix i assume "i \<in> set [0..<length ?L]"
              hence "i < length ?L" by simp
              thus "?P_enq (?L' ! i) = ?P_enq (?L ! i)"
                using L'_def by (simp add: nth_append)
            qed
            moreover have "[i \<leftarrow> [length ?L] . ?P_enq (?L' ! i)] = [i \<leftarrow> [length ?L] . ?P_enq (?new)]"
              using L'_def by (simp add: nth_append)
            ultimately show ?thesis by simp
          qed
          also have "... = find_indices ?P_enq ?L @ []"
            using a_not_v new_is_enq
            unfolding find_indices_def new_act_def mk_op_def op_val_def by simp
          finally show ?thesis by simp
        qed

        have deq_idx: "find_indices ?P_deq ?L' = find_indices ?P_deq ?L"
        proof -
          have "find_indices ?P_deq ?L' = [i \<leftarrow> [0..<length ?L'] . ?P_deq (?L' ! i)]"
            unfolding find_indices_def ..
          also have "... = [i \<leftarrow> [0..<length ?L] @ [length ?L] . ?P_deq (?L' ! i)]"
            by simp
          also have "... = [i \<leftarrow> [0..<length ?L] . ?P_deq (?L' ! i)] @ [i \<leftarrow> [length ?L] . ?P_deq (?L' ! i)]"
            by simp
          also have "... = [i \<leftarrow> [0..<length ?L] . ?P_deq (?L ! i)] @ [i \<leftarrow> [length ?L] . ?P_deq (?new)]"
          proof -
            have "[i \<leftarrow> [0..<length ?L] . ?P_deq (?L' ! i)] = [i \<leftarrow> [0..<length ?L] . ?P_deq (?L ! i)]"
            proof (rule filter_cong)
              show "[0..<length ?L] = [0..<length ?L]" ..
              fix i assume "i \<in> set [0..<length ?L]"
              hence "i < length ?L" by simp
              thus "?P_deq (?L' ! i) = ?P_deq (?L ! i)"
                using L'_def by (simp add: nth_append)
            qed
            moreover have "[i \<leftarrow> [length ?L] . ?P_deq (?L' ! i)] = [i \<leftarrow> [length ?L] . ?P_deq (?new)]"
              using L'_def by (simp add: nth_append)
            ultimately show ?thesis by simp
          qed
          also have "... = find_indices ?P_deq ?L @ []"
            unfolding find_indices_def new_act_def mk_op_def op_name_def by simp
          finally show ?thesis by simp
        qed

        have "find_unique_index ?P_enq ?L' = find_unique_index ?P_enq ?L"
          using enq_idx by (auto simp: find_unique_index_def Let_def)
        moreover have "find_unique_index ?P_deq ?L' = find_unique_index ?P_deq ?L"
          using deq_idx by (auto simp: find_unique_index_def Let_def)
        ultimately show ?thesis unfolding in_SA_def by (auto split: option.splits)
      qed
      thus ?case by simp
    qed

    show ?case
      using equiv_old in_SA_eq last_SA_eq
      using act_k enq_k by auto
  next
    case 2
    then have not_k_old: "\<not> (k < length ?L)" by simp
    have k_eq: "k = length ?L" using k_lt not_k_old by simp
    have act_k: "?L' ! k = ?new" by (simp add: nth_append k_eq)
    have v_val: "op_val (?L' ! k) = ?v" using act_k new_act_def mk_op_def op_val_def by simp
    have rhs_false: "\<not> (int k \<le> find_last_SA ?L')"
    proof -
      have "find_last_SA ?L < int (length ?L)" using find_last_SA_lt_length[of ?L] by simp
      thus ?thesis using k_eq last_SA_eq by linarith
    qed
    have lhs_false: "\<not> in_SA (op_val (?L' ! k)) ?L'" using v_val v_not_SA by simp
    thus ?case using rhs_false by simp
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for lI7_D4_Deq_Deq_HB s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_d4_deq_deq_hb:
  fixes s s' :: SysState and p :: nat and new_act :: OpRec
  assumes INV: "system_invariant s"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and his_eq: "his_seq s' = his_seq s"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "lI7_D4_Deq_Deq_HB s'"
proof (unfold lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def, intro allI impI, goal_cases)
  case (1 k1 k2 q)

  then have k1_lt: "k1 < length (lin_seq s')"
        and k2_lt: "k2 < length (lin_seq s')"
        and oper_k1: "op_name (lin_seq s' ! k1) = deq"
        and act_k2: "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
        and k2_last: "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q"
        and pc_q: "program_counter s' q = ''D4''"
        and hb_s': "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
    by auto

  have lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" using INV unfolding system_invariant_def by blast

  have "q \<noteq> p"
  proof
    assume "q = p"
    hence "program_counter s' p = ''D4''" using pc_q by simp
    moreover have "program_counter s' p = ''E2''" using step_facts by simp
    ultimately show False by simp
  qed

  have pc_q_s: "program_counter s q = ''D4''" using pc_q \<open>q \<noteq> p\<close> step_facts by auto
  have x_q_s: "x_var s' q = x_var s q" using \<open>q \<noteq> p\<close> step_facts by auto
  have s_q_s: "s_var s' q = s_var s q" using \<open>q \<noteq> p\<close> step_facts by auto

  have k2_lt_s: "k2 < length (lin_seq s)"
  proof (rule ccontr)
    assume "\<not> k2 < length (lin_seq s)"
    hence k2_eq: "k2 = length (lin_seq s)" using k2_lt by simp

    have "op_name (lin_seq s' ! k2) = enq"
      using k2_eq lin_eq new_act_def mk_op_def op_name_def by (simp add: nth_append)
    moreover have "op_name (lin_seq s' ! k2) = deq"
      using act_k2 unfolding op_name_def mk_op_def by simp
    ultimately show False by simp
  qed

  have k1_lt_s: "k1 < length (lin_seq s)"
  proof (rule ccontr)
    assume "\<not> k1 < length (lin_seq s)"
    hence k1_eq: "k1 = length (lin_seq s)" using k1_lt by simp

    have "op_name (lin_seq s' ! k1) = enq"
      using k1_eq lin_eq new_act_def mk_op_def op_name_def by (simp add: nth_append)
    with oper_k1 show False by simp
  qed

  have oper_k1_s: "op_name (lin_seq s ! k1) = deq"
    using oper_k1 k1_lt_s lin_eq by (simp add: nth_append)

  have act_k2_s: "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
    using act_k2 k2_lt_s x_q_s s_q_s lin_eq by (simp add: nth_append)

  have k2_last_s: "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
  proof (intro allI impI)
    fix k3 assume "k3 > k2" and "k3 < length (lin_seq s)"
    hence "k3 < length (lin_seq s')" using lin_eq by simp
    with k2_last \<open>k3 > k2\<close> have "op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q" by blast
    thus "op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
      using \<open>k3 < length (lin_seq s)\<close> lin_eq by (simp add: nth_append)
  qed

  have hb_s: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
    using hb_s' k1_lt_s k2_lt_s his_eq lin_eq
    unfolding HB_def match_ret_def match_call_def Let_def
    by (metis nth_append_left)

  from lI7_D4_Deq_Deq_HB_s k1_lt_s k2_lt_s oper_k1_s act_k2_s k2_last_s pc_q_s hb_s
  show ?case unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def by blast
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for lI10_D4_Enq_Deq_HB s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_d4_enq_deq_hb:
  fixes s s' :: SysState and p :: nat and v :: nat and new_act :: OpRec
  assumes INV: "system_invariant s"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and his_eq: "his_seq s' = his_seq s"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and pend_p: "HasPendingEnq s p v"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "lI10_D4_Enq_Deq_HB s'"
proof (unfold lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def, intro allI impI, goal_cases)
  case (1 k1 k2 q)

  then have k1_lt: "k1 < length (lin_seq s')"
        and k2_lt: "k2 < length (lin_seq s')"
        and oper_k1: "op_name (lin_seq s' ! k1) = enq"
        and act_k2: "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
        and k2_last: "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q"
        and pc_q: "program_counter s' q = ''D4''"
        and hb_s': "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
    by auto

  have lI10_D4_Enq_Deq_HB_s: "lI10_D4_Enq_Deq_HB s" using INV unfolding system_invariant_def by blast

  have "q \<noteq> p"
  proof
    assume "q = p"
    hence "program_counter s' p = ''D4''" using pc_q by simp
    moreover have "program_counter s' p = ''E2''" using step_facts by simp
    ultimately show False by simp
  qed

  have pc_q_s: "program_counter s q = ''D4''" using pc_q \<open>q \<noteq> p\<close> step_facts by auto
  have x_q_s: "x_var s' q = x_var s q" using \<open>q \<noteq> p\<close> step_facts by auto
  have s_q_s: "s_var s' q = s_var s q" using \<open>q \<noteq> p\<close> step_facts by auto

  have k2_lt_s: "k2 < length (lin_seq s)"
  proof (rule ccontr)
    assume "\<not> k2 < length (lin_seq s)"
    hence k2_eq: "k2 = length (lin_seq s)" using k2_lt by simp
    have "op_name (lin_seq s' ! k2) = enq"
      using k2_eq lin_eq new_act_def mk_op_def op_name_def by (simp add: nth_append)
    moreover have "op_name (lin_seq s' ! k2) = deq"
      using act_k2 unfolding op_name_def mk_op_def by simp
    ultimately show False by simp
  qed

  have k1_lt_s: "k1 < length (lin_seq s)"
  proof (rule ccontr)
    assume "\<not> k1 < length (lin_seq s)"
    hence k1_eq: "k1 = length (lin_seq s)" using k1_lt by simp
    hence k1_is_new: "lin_seq s' ! k1 = new_act"
      using lin_eq by (simp add: nth_append)

    from hb_s' k1_is_new obtain h1 where
      "h1 < length (his_seq s')" and "match_ret (his_seq s') h1 new_act"
      unfolding HB_def HB_Act_def
      using match_ret_def by blast

    have "\<not> (\<exists>h < length (his_seq s'). match_ret (his_seq s') h new_act)"
    proof (rule notI, elim exE conjE)
      fix h assume h_lt: "h < length (his_seq s')"
               and h_match: "match_ret (his_seq s') h new_act"

      have h_pid: "act_pid (his_seq s' ! h) = p"
       and h_ssn: "act_ssn (his_seq s' ! h) = s_var s p"
       and h_ret: "act_cr (his_seq s' ! h) = ret"
        using h_match unfolding match_ret_def new_act_def mk_op_def Let_def
        by (auto simp: op_pid_def op_ssn_def op_name_def op_val_def)

      have "h < length (his_seq s) \<or> h = length (his_seq s)"
        using h_lt by (auto simp: less_Suc_eq)
      thus False
      proof
        assume h_old: "h < length (his_seq s)"
        hence "act_pid (his_seq s ! h) = p"
          and "act_ssn (his_seq s ! h) = s_var s p"
          and "act_cr (his_seq s ! h) = ret"
          using h_pid h_ssn h_ret his_eq by (simp_all add: nth_append)
        with pend_p show False
          unfolding HasPendingEnq_def Let_def
          using h_old nth_mem by blast
      next
        assume h_new: "h = length (his_seq s)"
        hence "act_cr (his_seq s' ! h) = call"
          using step_facts his_eq
          using h_lt by auto
        with h_ret show False by simp
      qed
    qed
    with \<open>match_ret (his_seq s') h1 new_act\<close> \<open>h1 < length (his_seq s')\<close> show False by blast
  qed

  have oper_k1_s: "op_name (lin_seq s ! k1) = enq"
    using oper_k1 k1_lt_s lin_eq by (simp add: nth_append)

  have act_k2_s: "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
    using act_k2 k2_lt_s x_q_s s_q_s lin_eq by (simp add: nth_append)

  have k2_last_s: "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
  proof (intro allI impI)
    fix k3 assume "k3 > k2" and "k3 < length (lin_seq s)"
    hence "k3 < length (lin_seq s')" using lin_eq by simp
    with k2_last \<open>k3 > k2\<close> have "op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q" by blast
    thus "op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
      using \<open>k3 < length (lin_seq s)\<close> lin_eq by (simp add: nth_append)
  qed

  have hb_s: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
    using hb_s' k1_lt_s k2_lt_s his_eq lin_eq
    unfolding HB_def match_ret_def match_call_def Let_def
    by (metis nth_append_left)

  from lI10_D4_Enq_Deq_HB_s k1_lt_s k2_lt_s oper_k1_s act_k2_s k2_last_s pc_q_s hb_s
  show ?case unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def by blast
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for lI11_D4_Deq_Unique s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_d4_deq_unique:
  fixes s s' :: SysState and p :: nat and new_act :: OpRec
  assumes INV: "system_invariant s"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and his_eq: "his_seq s' = his_seq s"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "lI11_D4_Deq_Unique s'"
proof (unfold lI11_D4_Deq_Unique_def, intro allI impI, goal_cases)
  case (1 q)
  then have pc_q: "program_counter s' q = ''D4''" by simp

  have q_neq_p: "q \<noteq> p"
  proof
    assume "q = p"
    with pc_q have "program_counter s' p = ''D4''" by simp
    with step_facts show False by simp
  qed

  have pc_q_s: "program_counter s q = ''D4''"
    using pc_q q_neq_p step_facts by (auto simp: fun_upd_def)

  have lI11_D4_Deq_Unique_s: "lI11_D4_Deq_Unique s" using INV unfolding system_invariant_def by blast
  from lI11_D4_Deq_Unique_s pc_q_s obtain k2 where
    k2_lt: "k2 < length (lin_seq s)" and
    k2_act: "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)" and
    k2_prop: "\<forall>k3 < length (lin_seq s). op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
              k3 < k2 \<and> DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
    unfolding lI11_D4_Deq_Unique_def by blast

  have x_eq: "x_var s' q = x_var s q" and s_eq: "s_var s' q = s_var s q"
    using step_facts q_neq_p by simp_all

  show ?case
  proof (intro exI conjI, goal_cases)
    case 1
    show "k2 < length (lin_seq s')"
      using k2_lt lin_eq by simp
  next
    case 2
    show "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
      using k2_act x_eq s_eq lin_eq k2_lt by (simp add: nth_append)
  next
    case 3
    show "\<forall>k3<length (lin_seq s').
            op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
            k3 < k2 \<and> DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
    proof (intro allI impI, goal_cases)
      case (1 k3)
      then have k3_lt': "k3 < length (lin_seq s')"
            and cond: "op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2"
        by auto

      have k3_old: "k3 < length (lin_seq s)"
      proof (rule ccontr)
        assume "\<not> k3 < length (lin_seq s)"
        hence "k3 = length (lin_seq s)" using k3_lt' lin_eq by auto
        hence "lin_seq s' ! k3 = new_act" using lin_eq by (simp add: nth_append)
        hence "op_name (lin_seq s' ! k3) = enq"
          unfolding new_act_def mk_op_def op_name_def by simp
        with cond show False by simp
      qed

      have act_eq: "lin_seq s' ! k3 = lin_seq s ! k3"
        using lin_eq k3_old by (simp add: nth_append)

      have old_concl: "k3 < k2 \<and> DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
        using k2_prop k3_old cond act_eq by auto

      show ?case
        using old_concl his_eq act_eq unfolding DeqRetInHis_def by auto
    qed
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for data_independent (lin_seq s') . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_data_independent:
  fixes s s' :: SysState and p :: nat and v :: nat and new_act :: OpRec
  assumes not_InQBack_v: "\<not> InQBack s v"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
    and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and pc_p_E1: "program_counter s p = ''E1''"
    and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s"
    and call_p: "EnqCallInHis s p v (s_var s p)"
    and hI8_Val_Unique_s: "hI8_Val_Unique s"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
    and di_lin_s: "data_independent (lin_seq s)"
    and TypeB_s'_v: "TypeB s' v"
    and v_in_Val: "v \<in> Val"
    and lin_eq [simp]: "lin_seq s' = lin_seq s @ [new_act]"
    and new_act_def: "new_act = mk_op enq v p (s_var s p)"
  shows "data_independent (lin_seq s')"
proof -
  have v_not_in_SetB_s: "v \<notin> SetB s"
  proof
    assume "v \<in> SetB s"
    then have "TypeB s v" unfolding SetB_def by blast
    thus False
    proof (cases "QHas s v")
      case True
      then have "InQBack s v"
        using sI8_Q_Qback_Sync_s unfolding QHas_def InQBack_def sI8_Q_Qback_Sync_def
        by (metis sI1_Zero_Index_BOT_def sI1_Zero_Index_BOT_s)
      thus ?thesis using not_InQBack_v by blast
    next
      case False
      then obtain q where "program_counter s q = ''E2''" and "v_var s q = v"
        using \<open>TypeB s v\<close> unfolding TypeB_def by blast
      have "q \<noteq> p" using pc_p_E1 \<open>program_counter s q = ''E2''\<close> by auto

      have "HasPendingEnq s q v"
        using hI1_E_Phase_Pending_Enq_s \<open>program_counter s q = ''E2''\<close> unfolding hI1_E_Phase_Pending_Enq_def
        using \<open>v_var s q = v\<close> by blast
      then have "EnqCallInHis s q v (s_var s q)"
        unfolding HasPendingEnq_def by metis

      have "EnqCallInHis s q v (s_var s q)"
        using hI1_E_Phase_Pending_Enq_s \<open>program_counter s q = ''E2''\<close> unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def
        using \<open>v_var s q = v\<close>
        using \<open>EnqCallInHis s q v (s_var s q)\<close> by blast

      moreover have "EnqCallInHis s p v (s_var s p)"
        using call_p by simp

      ultimately have "q = p"
        using hI8_Val_Unique_s unfolding hI8_Val_Unique_def
        using EnqCallInHis_unique_pid hI8_Val_Unique_s by auto

      with \<open>q \<noteq> p\<close> show False by contradiction
    qed
  qed

  have v_fresh: "\<forall>i < length (lin_seq s). op_name (lin_seq s ! i) = enq \<longrightarrow> op_val (lin_seq s ! i) \<noteq> v"
  proof (intro allI impI, goal_cases)
    case (1 i)
    then have i_lt: "i < length (lin_seq s)" and enq_i: "op_name (lin_seq s ! i) = enq" by simp_all

    have "lin_seq s ! i \<in> OPLin s"
      using i_lt unfolding OPLin_def by auto
    hence "lin_seq s ! i \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
      using lI1_Op_Sets_Equivalence_s unfolding lI1_Op_Sets_Equivalence_def by blast

    hence "op_val (lin_seq s ! i) \<in> SetA s \<or> op_val (lin_seq s ! i) \<in> SetB s"
      unfolding OP_A_enq_def OP_A_deq_def OP_B_enq_def
      using enq_i i_lt lI1_Op_Sets_Equivalence_s lin_seq_no_value_if_not_in_SetA_SetB
      by blast

    moreover have "v \<notin> SetA s"
      using not_InQBack_v unfolding SetA_def TypeA_def by auto
    moreover have "v \<notin> SetB s" using v_not_in_SetB_s .

    ultimately show "op_val (lin_seq s ! i) \<noteq> v" by blast
  qed

  show ?thesis
    using data_independent_append_enq_fresh[OF di_lin_s v_fresh, of p "s_var s p"]
    using lin_eq
    unfolding new_act_def by (simp add: new_act_def)
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for sI3_E2_Slot_Exclusive s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_e2_slot_exclusive:
  fixes s s' :: SysState and p :: nat
  assumes sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s"
    and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s"
    and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s"
    and X_in_Val: "X_var s \<in> Val"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and pc_eqs [simp]:
      "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<or> q = p)"
      "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
      "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
      "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
      "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'')"
      "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'')"
      "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
      "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
  shows "sI3_E2_Slot_Exclusive s'"
proof (unfold sI3_E2_Slot_Exclusive_def, intro allI impI)
  fix q assume qE2': "program_counter s' q = ''E2''"
  show "i_var s' q \<in> Val \<and> i_var s' q < X_var s' \<and> Q_arr s' (i_var s' q) = BOT \<and> Qback_arr s' (i_var s' q) = BOT \<and>
        (\<forall>r. r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' q \<noteq> i_var s' r)"
  proof (cases "q = p", goal_cases)
    case 1
    have q_i_eq: "i_var s' q = X_var s" using 1 step_facts by simp
    have qarr_bot: "Q_arr s (X_var s) = BOT" using sI2_X_var_Upper_Bound_s unfolding sI2_X_var_Upper_Bound_def by simp
    have qback_bot: "Qback_arr s (X_var s) = BOT" using sI2_X_var_Upper_Bound_s unfolding sI2_X_var_Upper_Bound_def by simp

    have all_distinct: "\<forall>r. r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' q \<noteq> i_var s' r"
    proof (intro allI impI)
      fix r assume rq: "r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''}"
      have r_ne_p: "r \<noteq> p" using 1 rq by simp
      have r_old: "program_counter s r \<in> {''E2'', ''E3''}" using rq r_ne_p pc_eqs by auto

      have r_lt: "i_var s r < X_var s"
      proof (cases "program_counter s r = ''E2''", goal_cases)
        case 1 then show ?case using sI3_E2_Slot_Exclusive_s unfolding sI3_E2_Slot_Exclusive_def by auto
      next
        case 2
        with r_old have "program_counter s r = ''E3''" by auto
        then show ?case using sI4_E3_Qback_Written_s unfolding sI4_E3_Qback_Written_def by auto
      qed

      show "i_var s' q \<noteq> i_var s' r"
        using 1 r_ne_p r_lt step_facts by simp
    qed

    show ?case
      using q_i_eq X_in_Val step_facts 1 qarr_bot qback_bot all_distinct
      unfolding Val_def by auto
  next
    case 2
    have qE2: "program_counter s q = ''E2''" using qE2' 2 pc_eqs by simp

    from sI3_E2_Slot_Exclusive_s qE2 have sI3_E2_Slot_Exclusive_q_all:
      "i_var s q \<in> Val \<and> i_var s q < X_var s \<and> Q_arr s (i_var s q) = BOT \<and> Qback_arr s (i_var s q) = BOT \<and>
       (\<forall>q'. q' \<noteq> q \<and> program_counter s q' \<in> {''E2'', ''E3''} \<longrightarrow> i_var s q \<noteq> i_var s q')"
      unfolding sI3_E2_Slot_Exclusive_def by blast

    have all_distinct: "\<forall>r. r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' q \<noteq> i_var s' r"
    proof (intro allI impI)
      fix r assume rq: "r \<noteq> q \<and> program_counter s' r \<in> {''E2'', ''E3''}"
      show "i_var s' q \<noteq> i_var s' r"
      proof (cases "r = p", goal_cases)
        case 1
        then show ?case using sI3_E2_Slot_Exclusive_q_all 2 step_facts by simp
      next
        case 2
        have r_old: "program_counter s r \<in> {''E2'', ''E3''}" using rq 2 pc_eqs by auto
        then show ?case using sI3_E2_Slot_Exclusive_q_all rq(1) 2 step_facts
          using qE2 by auto
      qed
    qed

    show ?case
      using sI3_E2_Slot_Exclusive_q_all 2 step_facts all_distinct by auto
  qed
qed

(* Source: E1Proof.thy / E1_preserves_invariant *)
(* Original location: the long proof block for hI19_Scanner_Catches_Later_Enq s' . *)
(* Note: the proof script below is taken verbatim from the original file, without changing the proof logic. *)
lemma E1_scanner_catches_later_enq:
  fixes s s' :: SysState and p v :: nat
  assumes hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s"
    and not_InQBack_v: "\<not> InQBack s v"
    and v_def: "v = v_var s p"
    and step_facts [simp]:
      "program_counter s p = ''E1''"
      "program_counter s' = (program_counter s)(p := ''E2'')"
      "i_var s' = (i_var s)(p := X_var s)"
      "X_var s' = X_var s + 1"
      "Q_arr s' = Q_arr s" "Qback_arr s' = Qback_arr s"
      "x_var s' = x_var s" "j_var s' = j_var s" "l_var s' = l_var s"
      "V_var s' = V_var s" "v_var s' = v_var s" "s_var s' = s_var s"
      "his_seq s' = his_seq s"
    and pc_eqs [simp]:
      "\<And>q. (program_counter s' q = ''E2'') = (program_counter s q = ''E2'' \<or> q = p)"
      "\<And>q. (program_counter s' q = ''E1'') = (program_counter s q = ''E1'' \<and> q \<noteq> p)"
      "\<And>q. (program_counter s' q = ''E3'') = (program_counter s q = ''E3'')"
      "\<And>q. (program_counter s' q = ''L0'') = (program_counter s q = ''L0'')"
      "\<And>q. (program_counter s' q = ''D1'') = (program_counter s q = ''D1'')"
      "\<And>q. (program_counter s' q = ''D2'') = (program_counter s q = ''D2'')"
      "\<And>q. (program_counter s' q = ''D3'') = (program_counter s q = ''D3'')"
      "\<And>q. (program_counter s' q = ''D4'') = (program_counter s q = ''D4'')"
    and his_eq: "his_seq s' = his_seq s"
  shows "hI19_Scanner_Catches_Later_Enq s'"
proof (unfold hI19_Scanner_Catches_Later_Enq_def, intro allI impI, goal_cases)
  case (1 a b)

  from 1 have inqa': "InQBack s' a" by blast
  from 1 have inqb': "InQBack s' b" by blast
  from 1 have tba': "TypeB s' a" by blast
  from 1 have tbb': "TypeB s' b" by blast
  from 1 have idx_lt': "Idx s' a < Idx s' b" by blast
  from 1 have ex_q': "\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
                          Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q" by blast

  have inqa: "InQBack s a" using inqa' step_facts unfolding InQBack_def by simp
  have inqb: "InQBack s b" using inqb' step_facts unfolding InQBack_def by simp
  have idx_lt: "Idx s a < Idx s b" using idx_lt' step_facts unfolding Idx_def AtIdx_def by simp

  have a_ne_v: "a \<noteq> v" using inqa not_InQBack_v by auto
  have b_ne_v: "b \<noteq> v" using inqb not_InQBack_v by auto

  have tba: "TypeB s a"
    using tba' a_ne_v step_facts pc_eqs unfolding TypeB_def QHas_def v_def by auto
  have tbb: "TypeB s b"
    using tbb' b_ne_v step_facts pc_eqs unfolding TypeB_def QHas_def v_def by auto

  have deq_old: "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and>
                     Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
  proof -
    from ex_q' obtain q where
      q_pend': "HasPendingDeq s' q" and q_D3': "program_counter s' q = ''D3''" and
      q_idx1': "Idx s' a < j_var s' q" and q_idx2': "j_var s' q \<le> Idx s' b" and q_idx3': "Idx s' b < l_var s' q"
      by blast

    have q_ne_p: "q \<noteq> p"
    proof
      assume "q = p"
      with q_D3' have "program_counter s' p = ''D3''" by simp
      with step_facts show False by simp
    qed

    have q_pend: "HasPendingDeq s q"
      using q_pend' step_facts unfolding HasPendingDeq_def DeqCallInHis_def DeqRetInHis_def Let_def by simp
    have q_D3: "program_counter s q = ''D3''"
      using q_D3' q_ne_p step_facts by simp
    have q_idx1: "Idx s a < j_var s q" using q_idx1' step_facts unfolding Idx_def AtIdx_def by simp
    have q_idx2: "j_var s q \<le> Idx s b" using q_idx2' step_facts unfolding Idx_def AtIdx_def by simp
    have q_idx3: "Idx s b < l_var s q" using q_idx3' step_facts unfolding Idx_def AtIdx_def by simp

    show ?thesis using q_pend q_D3 q_idx1 q_idx2 q_idx3 by blast
  qed

  have hb_eq: "HB_EnqRetCall s' a b = HB_EnqRetCall s a b"
    unfolding HB_EnqRetCall_def HB_Act_def HB_def Let_def match_ret_def match_call_def mk_op_def op_name_def op_val_def
    using his_eq by auto

  have "\<not> HB_EnqRetCall s a b"
    using hI19_Scanner_Catches_Later_Enq_s inqa inqb tba tbb idx_lt deq_old unfolding hI19_Scanner_Catches_Later_Enq_def by blast

  then show ?case using hb_eq by simp
qed

end
