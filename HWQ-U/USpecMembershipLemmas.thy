theory USpecMembershipLemmas
  imports HistoryTransferProof
begin

(* ========================================================== *)
(* Auxiliary lemmas for the USpec component of HWQ-U.          *)
(* ========================================================== *)

subsection \<open>USpec-generated linearizations for Queue\<close>

definition USpec_GenLin_TrueQueue ::
  "ActRec list \<Rightarrow> OpRec set \<Rightarrow> OpRec \<Rightarrow> OpRec list \<Rightarrow> bool" where
  "USpec_GenLin_TrueQueue H S oid L \<equiv>
     USpec_GenLin H S oid L \<and>
     QueueValueOK L \<and>
     L \<in> HWQ_QueueSeqSpec"

lemma USpec_GenLin_to_TrueQueue_if_value_ok:
  assumes GEN: "USpec_GenLin H S oid L"
      and OK: "QueueValueOK L"
  shows "USpec_GenLin_TrueQueue H S oid L"
proof -
  have SQ: "L \<in> HWQ_SqSpec"
    using GEN
    unfolding USpec_GenLin_def QueueSpecLin_def HWQ_SqSpec_def
    by blast

  have STRONG: "L \<in> HWQ_SqSpec_Strong"
    using SQ OK
    unfolding HWQ_SqSpec_Strong_def
    by blast

  have QSPEC: "L \<in> HWQ_QueueSeqSpec"
    using STRONG HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec
    by blast

  show ?thesis
    using GEN OK QSPEC
    unfolding USpec_GenLin_TrueQueue_def
    by blast
qed


subsection \<open>Operations called in histories\<close>

lemma Equivalent_History_imp_all_ops_called:
  assumes EQ: "Equivalent_History H L"
      and A: "a \<in> set L"
  shows "OpCalledInHis H a"
proof -
  obtain m where M: "m < length L" and ADEF: "L ! m = a"
    using A
    by (auto simp: in_set_conv_nth)

  obtain k where K:
    "k < length H"
    "act_cr (H ! k) = call"
    "act_pid (H ! k) = op_pid a"
    "act_ssn (H ! k) = op_ssn a"
    "act_name (H ! k) = op_name a"
    "act_val (H ! k) = (if op_name a = deq then BOT else op_val a)"
    using EQ M ADEF
    unfolding Equivalent_History_def
    by blast

  show ?thesis
    unfolding OpCalledInHis_def match_call_def
    using K
    by (auto simp: Let_def)
qed


subsection \<open>HWQ-U membership obligations for USpec\<close>

definition HWQU_U_satisfies_USpec :: "SysState \<Rightarrow> bool" where
  "HWQU_U_satisfies_USpec s \<equiv>
     uI1_USpec_EffOps_Lin s \<and>
     uI2_USpec_E1UE2 s \<and>
     uI3_USpec_D3UD2 s \<and>

     uspec_effOps s = set (lin_seq s) \<and>
     finite (uspec_effOps s) \<and>

     (\<forall>a \<in> set (lin_seq s). OpCalledInHis (his_seq s) a) \<and>
     HB_consistent (lin_seq s) (his_seq s) \<and>
     lin_seq s \<in> HWQ_QueueSeqSpec \<and>
     data_independent (lin_seq s)"

end
