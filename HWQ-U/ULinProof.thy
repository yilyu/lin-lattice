theory ULinProof
  imports
    Main
    "HOL-Library.Multiset"
    Model
    SysInvProof
begin

(* ========================================================== *)
(* Linearization-sequence reasoning. *)
(* ========================================================== *)

(* History well-formedness and call/return reasoning. *)
definition Equivalent_History :: "ActRec list \<Rightarrow> OpRec list \<Rightarrow> bool" where
  "Equivalent_History H L \<equiv>
    (\<forall>k < length H. act_cr (H ! k) = ret \<longrightarrow>
      (\<exists>m < length L.
        op_name (L ! m) = act_name (H ! k) \<and>
        op_pid (L ! m) = act_pid (H ! k) \<and>
        op_ssn (L ! m) = act_ssn (H ! k) \<and>
        op_val (L ! m) = act_val (H ! k))) \<and>
    (\<forall>m < length L.
      (\<exists>k < length H.
        act_cr (H ! k) = call \<and>
        act_pid (H ! k) = op_pid (L ! m) \<and>
        act_ssn (H ! k) = op_ssn (L ! m) \<and>
        act_name (H ! k) = op_name (L ! m) \<and>
        act_val (H ! k) = (if op_name (L ! m) = deq then BOT else op_val (L ! m))))"

(* Auxiliary proof step. *)
definition Legal_Queue_Seq :: "OpRec list \<Rightarrow> bool" where
  "Legal_Queue_Seq L \<equiv> lI4_FIFO_Semantics_list L \<and> lI5_SA_Prefix_list L \<and> data_independent L"

(* Linearization-sequence reasoning. *)
definition IsLinearizable :: "ActRec list \<Rightarrow> bool" where
  "IsLinearizable H \<equiv> \<exists>L.
     Equivalent_History H L \<and>
     HB_consistent L H \<and>
     Legal_Queue_Seq L"

(* ================================================================= *)
(* History well-formedness and call/return reasoning. Related symbols: system_invariant. *)
(* ================================================================= *)
theorem U_is_linearizable:
  assumes "system_invariant s"
  shows "IsLinearizable (his_seq s)"
proof -
  (* Step 1: extract the required facts. Related symbols: lin_seq. *)
  let ?S = "lin_seq s"
  let ?H = "his_seq s"

  (* Step 2: extract the required facts. *)
  have I_lin1: "lI1_Op_Sets_Equivalence s" using assms unfolding system_invariant_def by blast
  have I_lin3: "lI3_HB_Ret_Lin_Sync s" using assms unfolding system_invariant_def by blast
  have I_lin4: "lI4_FIFO_Semantics s" using assms unfolding system_invariant_def by blast
  have I_lin5: "lI5_SA_Prefix s" using assms unfolding system_invariant_def by blast
  have I_di: "data_independent ?S" using assms unfolding system_invariant_def by blast

  (* --------------------------------------------------------------- *)
  (* Stability/equivalence argument. *)
  (* --------------------------------------------------------------- *)
  have goal_A: "Equivalent_History ?H ?S"
  proof -
    have completeness: "\<forall>k < length ?H. act_cr (?H ! k) = ret \<longrightarrow>
      (\<exists>m < length ?S. op_name (?S ! m) = act_name (?H ! k) \<and>
                       op_pid (?S ! m) = act_pid (?H ! k) \<and>
                       op_ssn (?S ! m) = act_ssn (?H ! k) \<and>
                       op_val (?S ! m) = act_val (?H ! k))"
    proof (intro allI impI)
      fix k
      assume hk_len: "k < length ?H"
      assume hk_ret: "act_cr (?H ! k) = ret"

      let ?e = "?H ! k"
      have "act_name ?e = enq \<or> act_name ?e = deq"
        using act_name_def mname.exhaust by metis

      then show "\<exists>m < length ?S. op_name (?S ! m) = act_name ?e \<and>
                                 op_pid (?S ! m) = act_pid ?e \<and>
                                 op_ssn (?S ! m) = act_ssn ?e \<and>
                                 op_val (?S ! m) = act_val ?e"
      proof
        assume "act_name ?e = enq"
        (* Extract the corresponding operation from the invariant. *)
        then have "Model.EnqRetInHis s (act_pid ?e) (act_val ?e) (act_ssn ?e)"
          unfolding Model.EnqRetInHis_def Let_def using hk_len hk_ret by auto

        then obtain m where "m < length ?S"
                        and "?S ! m = mk_op enq (act_val ?e) (act_pid ?e) (act_ssn ?e)"
          using I_lin3 unfolding lI3_HB_Ret_Lin_Sync_def by blast

        then show ?thesis
          using \<open>act_name ?e = enq\<close>
          unfolding op_name_def op_pid_def op_val_def op_ssn_def mk_op_def
          by force
      next
        assume "act_name ?e = deq"
        (* Auxiliary proof step. *)
        then have "Model.DeqRetInHis s (act_pid ?e) (act_val ?e) (act_ssn ?e)"
          unfolding Model.DeqRetInHis_def Let_def using hk_len hk_ret by auto

        then obtain m where "m < length ?S"
                        and "?S ! m = mk_op deq (act_val ?e) (act_pid ?e) (act_ssn ?e)"
          using I_lin3 unfolding lI3_HB_Ret_Lin_Sync_def by blast

        then show ?thesis
          using \<open>act_name ?e = deq\<close>
          unfolding op_name_def op_pid_def op_val_def op_ssn_def mk_op_def
          by force
      qed
    qed

    have soundness: "\<forall>m < length ?S.
      (\<exists>k < length ?H. act_cr (?H ! k) = call \<and>
                       act_pid (?H ! k) = op_pid (?S ! m) \<and>
                       act_ssn (?H ! k) = op_ssn (?S ! m) \<and>
                       act_name (?H ! k) = op_name (?S ! m) \<and>
                       act_val (?H ! k) = (if op_name (?S ! m) = deq then BOT else op_val (?S ! m)))"
    proof (intro allI impI)
      fix m assume m_len: "m < length ?S"
      let ?act = "?S ! m"

      show "\<exists>k < length ?H. act_cr (?H ! k) = call \<and>
                            act_pid (?H ! k) = op_pid ?act \<and>
                            act_ssn (?H ! k) = op_ssn ?act \<and>
                            act_name (?H ! k) = op_name ?act \<and>
                            act_val (?H ! k) = (if op_name ?act = deq then BOT else op_val ?act)"
      proof -
        have act_in_OPLin: "?act \<in> OPLin s"
          unfolding OPLin_def using m_len by auto

        have act_cases: "?act \<in> OP_A_enq s \<or> ?act \<in> OP_B_enq s \<or> ?act \<in> OP_A_deq s"
          using I_lin1 act_in_OPLin unfolding lI1_Op_Sets_Equivalence_def by blast

        have case1: "?act \<in> OP_A_enq s \<Longrightarrow> ?thesis"
        proof -
          assume "?act \<in> OP_A_enq s"
          (* Extract the corresponding operation from the invariant. *)
          then obtain p a sn where "?act = mk_op enq a p sn" and "Model.EnqCallInHis s p a sn"
            unfolding OP_A_enq_def by blast
          (* Discharge the record-field equalities. *)
          then show ?thesis
            unfolding Model.EnqCallInHis_def mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
            by (force simp: in_set_conv_nth)
        qed

        have case2: "?act \<in> OP_B_enq s \<Longrightarrow> ?thesis"
        proof -
          assume "?act \<in> OP_B_enq s"
          then obtain p b sn where "?act = mk_op enq b p sn" and "Model.EnqCallInHis s p b sn"
            unfolding OP_B_enq_def by blast
          (* Discharge the record-field equalities. *)
          then show ?thesis
            unfolding Model.EnqCallInHis_def mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
            by (force simp: in_set_conv_nth)
        qed

        have case3: "?act \<in> OP_A_deq s \<Longrightarrow> ?thesis"
        proof -
          assume "?act \<in> OP_A_deq s"
          then have "op_name ?act = deq" and "Model.DeqCallInHis s (op_pid ?act) (op_ssn ?act)"
            unfolding OP_A_deq_def by auto
          (* Discharge the record-field equalities. *)
          then show ?thesis
            unfolding Model.DeqCallInHis_def Let_def
            by (force simp: in_set_conv_nth)
        qed

        show ?thesis using act_cases case1 case2 case3 by blast
      qed
    qed

    show ?thesis
      unfolding Equivalent_History_def
      using completeness soundness by blast
  qed

  (* --------------------------------------------------------------- *)
  (* Happens-before reasoning. *)
  (* --------------------------------------------------------------- *)
  moreover have goal_B: "HB_consistent ?S ?H"
  proof -
    show ?thesis using I_lin3 unfolding lI3_HB_Ret_Lin_Sync_def
      by (simp add: HB_Act_def HB_consistent_def)
  qed

  (* --------------------------------------------------------------- *)
  (* Auxiliary proof step. *)
  (* --------------------------------------------------------------- *)
  moreover have goal_C: "Legal_Queue_Seq ?S"
  proof -
    have req1: "lI4_FIFO_Semantics_list ?S" using I_lin4 unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def by blast
    have req2: "lI5_SA_Prefix_list ?S" using I_lin5 unfolding lI5_SA_Prefix_def by simp
    show ?thesis
      unfolding Legal_Queue_Seq_def
      using req1 req2 I_di by blast
  qed

  (* --------------------------------------------------------------- *)
  (* Linearization-sequence reasoning. Related symbols: ?S. *)
  (* --------------------------------------------------------------- *)
  ultimately show ?thesis
    unfolding IsLinearizable_def
    by blast
qed

(* ========================================================== *)
(* Proof note. Related symbols: conf_h, conf_u. *)
(* Auxiliary proof step. *)
(* Auxiliary proof step. *)
(* ========================================================== *)
definition SimRel_U :: "CState \<Rightarrow> UState \<Rightarrow> bool" where
  "SimRel_U cs us \<equiv> system_invariant (cs, us)"

(* ========================================================== *)
(* Auxiliary proof step. *)
(* Auxiliary proof step. *)
(*   [[O_HWQ, n]] \<preceq>_(c,r) [[U_Queue, n]]                     *)
(* Initialization-related reasoning. *)
(* State-transition reasoning. *)
(* ========================================================== *)
theorem HWQ_is_simulated_by_UQueue:
  shows
    "(\<forall>cs us. Init (cs, us) \<longrightarrow> SimRel_U cs us) \<and>
     (\<forall>cs us cs' us'. SimRel_U cs us \<and> Next (cs, us) (cs', us') \<longrightarrow> SimRel_U cs' us')"
proof (intro conjI allI impI)
  fix cs us
  assume init: "Init (cs, us)"
  show "SimRel_U cs us"
    unfolding SimRel_U_def
    using system_invariant_Init[OF init] .
next
  fix cs us cs' us'
  assume prems: "SimRel_U cs us \<and> Next (cs, us) (cs', us')"
  then have rel: "SimRel_U cs us" and step: "Next (cs, us) (cs', us')"
    by blast+
  show "SimRel_U cs' us'"
    unfolding SimRel_U_def
    using rel step Sys_Inv_Step
    unfolding SimRel_U_def by blast
qed

(* ========================================================== *)
(* State-transition reasoning. *)
(* Auxiliary proof step. *)
(* ========================================================== *)
corollary Reachable_Sys_in_SimRel_U:
  assumes "Reachable_Sys s"
  shows "system_invariant s"
using assms
proof (induction rule: Reachable_Sys.induct)
  case (init s)
  thus ?case
    using system_invariant_Init
    by simp
next
  case (step s s')
  thus ?case
    using Sys_Inv_Step
    by simp
qed

(* ========================================================== *)
(* History well-formedness and call/return reasoning. *)
(* Auxiliary proof step. *)
(*   O_HWQ is linearizable w.r.t. queue for n processes        *)
(* ========================================================== *)
corollary HWQ_is_linearizable:
  assumes "Reachable_Sys s"
  shows "IsLinearizable (his_seq s)"
proof -
  have "system_invariant s"
    using Reachable_Sys_in_SimRel_U[OF assms] .
  thus ?thesis
    using U_is_linearizable by blast
qed

theorem HWQU_invariant_implies_recorded_history_linearizable:
  assumes INV: "system_invariant s"
  shows "IsLinearizable (his_seq s)"
  using INV
  by (rule U_is_linearizable)


theorem reachable_HWQU_state_satisfies_invariant:
  assumes REACH: "Reachable_Sys s"
  shows "system_invariant s"
  using REACH
  by (rule Reachable_Sys_in_SimRel_U)


theorem reachable_HWQU_recorded_history_linearizable:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable (his_seq s)"
  using REACH
  by (rule HWQ_is_linearizable)


theorem HWQU_refines_UQueue_invariant_form:
  shows
    "(\<forall>cs us. Init (cs, us) \<longrightarrow> SimRel_U cs us) \<and>
     (\<forall>cs us cs' us'.
        SimRel_U cs us \<and> Next (cs, us) (cs', us')
        \<longrightarrow> SimRel_U cs' us')"
  using HWQ_is_simulated_by_UQueue
  by simp


theorem HWQU_initial_states_satisfy_simulation_relation:
  assumes INIT: "Init (cs, us)"
  shows "SimRel_U cs us"
  using HWQ_is_simulated_by_UQueue INIT
  by blast


theorem HWQU_simulation_relation_preserved_by_step:
  assumes REL: "SimRel_U cs us"
      and STEP: "Next (cs, us) (cs', us')"
  shows "SimRel_U cs' us'"
  using HWQ_is_simulated_by_UQueue REL STEP
  by blast


end
