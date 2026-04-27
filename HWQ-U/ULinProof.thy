theory ULinProof
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    SysInvProof
begin

(* ========================================================== *)
(* Top-level specification of linearizability               *)
(* ========================================================== *)

(* Equivalence between a concurrent history H and a sequential operation list L. *)
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

(* Sequential queue specification: L must satisfy the FIFO discipline. *)
definition Legal_Queue_Seq :: "OpRec list \<Rightarrow> bool" where
  "Legal_Queue_Seq L \<equiv> lI4_FIFO_Semantics_list L \<and> lI5_SA_Prefix_list L \<and> data_independent L"

(* A history is linearizable if there exists a legal witness sequence L. *)
definition IsLinearizable :: "ActRec list \<Rightarrow> bool" where
  "IsLinearizable H \<equiv> \<exists>L. 
     Equivalent_History H L \<and>   
     HB_consistent L H \<and>        
     Legal_Queue_Seq L"

(* ================================================================= *)
(* Main theorem: system_invariant implies linearizability of the recorded history. *)
(* ================================================================= *)
theorem U_is_linearizable:
  assumes "system_invariant s"
  shows "IsLinearizable (his_seq s)"
proof -
  (* Step 1: choose the maintained linearization lin_seq s as the witness. *)
  let ?S = "lin_seq s"
  let ?H = "his_seq s"

  (* Step 2: extract the required invariants once and reuse them globally. *)
  have I_lin1: "lI1_Op_Sets_Equivalence s" using assms unfolding system_invariant_def by blast
  have I_lin3: "lI3_HB_Ret_Lin_Sync s" using assms unfolding system_invariant_def by blast
  have I_lin4: "lI4_FIFO_Semantics s" using assms unfolding system_invariant_def by blast
  have I_lin5: "lI5_SA_Prefix s" using assms unfolding system_invariant_def by blast
  have I_di: "data_independent ?S" using assms unfolding system_invariant_def by blast

  (* --------------------------------------------------------------- *)
  (* Goal A: prove equivalence between the history and the witness sequence. *)
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
        (* Use the four-argument Model namespace predicate to avoid legacy name clashes. *)
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
        (* Use the corresponding four-argument predicate from Model. *)
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
          (* Use Model.EnqCallInHis explicitly. *)
          then obtain p a sn where "?act = mk_op enq a p sn" and "Model.EnqCallInHis s p a sn" 
            unfolding OP_A_enq_def by blast
          (* Use force here to instantiate the existential witnesses directly. *)
          then show ?thesis 
            unfolding Model.EnqCallInHis_def mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
            by (force simp: in_set_conv_nth)
        qed
        
        have case2: "?act \<in> OP_B_enq s \<Longrightarrow> ?thesis"
        proof -
          assume "?act \<in> OP_B_enq s"
          then obtain p b sn where "?act = mk_op enq b p sn" and "Model.EnqCallInHis s p b sn" 
            unfolding OP_B_enq_def by blast
          (* Use force for the same witness-instantiation reason. *)
          then show ?thesis 
            unfolding Model.EnqCallInHis_def mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
            by (force simp: in_set_conv_nth)
        qed
        
        have case3: "?act \<in> OP_A_deq s \<Longrightarrow> ?thesis"
        proof -
          assume "?act \<in> OP_A_deq s"
          then have "op_name ?act = deq" and "Model.DeqCallInHis s (op_pid ?act) (op_ssn ?act)" 
            unfolding OP_A_deq_def by auto
          (* Use force for the same witness-instantiation reason. *)
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
  (* Goal B: prove consistency with the happens-before relation. *)
  (* --------------------------------------------------------------- *)
  moreover have goal_B: "HB_consistent ?S ?H" 
  proof -
    show ?thesis using I_lin3 unfolding lI3_HB_Ret_Lin_Sync_def
      by (simp add: HB_Act_def HB_consistent_def)
  qed

  (* --------------------------------------------------------------- *)
  (* Goal C: show that the witness satisfies the sequential queue specification. *)
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
  (* Final step: assemble the three goals and conclude linearizability by definition. *)
  (* --------------------------------------------------------------- *)
  ultimately show ?thesis
    unfolding IsLinearizable_def
    by blast
qed

(* ========================================================== *)
(* Simulation relation corresponding to the paper's relation R(conf_h, conf_u). *)
(* In this formalization the joint HWQ/UQueue configuration is represented as SysState. *)
(* It is therefore natural to expose the relation as a binary predicate over CState and UState. *)
(* ========================================================== *)
definition SimRel_U :: "CState \<Rightarrow> UState \<Rightarrow> bool" where
  "SimRel_U cs us \<equiv> system_invariant (cs, us)"

(* ========================================================== *)
(* Main theorem: HWQ is simulated by UQueue in the forward call/return sense. *)
(* This theorem corresponds to the simulation claim stated in the paper. *)
(*   [[O_HWQ, n]] \<preceq>_(c,r) [[U_Queue, n]]                     *)
(* In the current formalization this is expressed by initial-state coverage and step preservation. *)
(* The relation is preserved by every combined transition Next. *)
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
(* Corollary: every reachable joint state satisfies the simulation relation. *)
(* This matches the statement that all reachable configurations lie in R. *)
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
(* Final corollary: the history of HWQ is linearizable. *)
(* This corollary matches the paper's linearizability statement. *)
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

end
