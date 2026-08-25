theory HistoryTransferProof
  imports HistoryTransferLemmas
begin

(* ========================================================== *)
(* HWQ-U-specific transfer from recorded history to real trace. *)
(* ========================================================== *)

subsection \<open>Transfer from recorded histories to real histories\<close>

theorem recorded_linearization_imp_real_linearization_HWQ:
  assumes REC_EQ: "Equivalent_History recdH L"
      and REC_HB: "HB_consistent L recdH"
      and SPEC: "L \<in> HWQ_QueueSeqSpec"
      and REAL_EQ: "Equivalent_History realH L"
      and HB_SUB: "HB_subsumed realH recdH"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
proof -
  have REAL_HB: "HB_consistent L realH"
    using HB_SUB REC_HB
    by (rule HB_consistent_mono)

  show ?thesis
    unfolding IsLinearizable_HWQ_QueueSeqSpec_def
    using REAL_EQ REAL_HB SPEC
    by blast
qed

theorem recorded_linearizable_imp_real_linearizable_HWQ:
  assumes REC_LIN: "IsLinearizable_HWQ_QueueSeqSpec recdH"
      and REAL_EQ_TRANSFER:
        "\<And>L. Equivalent_History recdH L \<Longrightarrow>
              L \<in> HWQ_QueueSeqSpec \<Longrightarrow>
              Equivalent_History realH L"
      and HB_SUB: "HB_subsumed realH recdH"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
proof -
  obtain L where
    REC_EQ: "Equivalent_History recdH L" and
    REC_HB: "HB_consistent L recdH" and
    SPEC: "L \<in> HWQ_QueueSeqSpec"
    using REC_LIN
    unfolding IsLinearizable_HWQ_QueueSeqSpec_def
    by blast

  have REAL_EQ: "Equivalent_History realH L"
    using REC_EQ SPEC
    by (rule REAL_EQ_TRANSFER)

  show ?thesis
    using REC_EQ REC_HB SPEC REAL_EQ HB_SUB
    by (rule recorded_linearization_imp_real_linearization_HWQ)
qed

theorem real_history_linearizable_if_recorded_linearization_transfers:
  assumes REC_EQ: "Equivalent_History recdH L"
      and REC_HB: "HB_consistent L recdH"
      and SPEC: "L \<in> HWQ_QueueSeqSpec"
      and REAL_EQ: "Equivalent_History realH L"
      and HB_SUB: "HB_subsumed realH recdH"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
  using REC_EQ REC_HB SPEC REAL_EQ HB_SUB
  by (rule recorded_linearization_imp_real_linearization_HWQ)

theorem real_history_linearizable_if_recorded_history_linearizable:
  assumes REC_LIN: "IsLinearizable_HWQ_QueueSeqSpec recdH"
      and REAL_EQ_TRANSFER:
        "\<And>L. Equivalent_History recdH L \<Longrightarrow>
              L \<in> HWQ_QueueSeqSpec \<Longrightarrow>
              Equivalent_History realH L"
      and HB_SUB: "HB_subsumed realH recdH"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
  using REC_LIN REAL_EQ_TRANSFER HB_SUB
  by (rule recorded_linearizable_imp_real_linearizable_HWQ)


subsection \<open>Application to HWQ-U invariant states\<close>

theorem system_invariant_real_history_true_queue_linearizable_if_transfer:
  assumes INV: "system_invariant s"
      and REAL_EQ: "Equivalent_History realH (lin_seq s)"
      and HB_SUB: "HB_subsumed realH (his_seq s)"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
proof -
  have REC_EQ: "Equivalent_History (his_seq s) (lin_seq s)"
    using INV
    by (rule system_invariant_his_lin_equiv)

  have REC_HB: "HB_consistent (lin_seq s) (his_seq s)"
    using INV
    by (rule system_invariant_lin_seq_HB_consistent)

  have SPEC: "lin_seq s \<in> HWQ_QueueSeqSpec"
    using INV
    by (rule system_invariant_lin_seq_in_HWQ_QueueSeqSpec)

  show ?thesis
    using REC_EQ REC_HB SPEC REAL_EQ HB_SUB
    by (rule recorded_linearization_imp_real_linearization_HWQ)
qed

corollary reachable_real_history_true_queue_linearizable_if_transfer:
  assumes REACH: "Reachable_Sys s"
      and REAL_EQ: "Equivalent_History realH (lin_seq s)"
      and HB_SUB: "HB_subsumed realH (his_seq s)"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
proof -
  have INV: "system_invariant s"
    using REACH
    by (rule Reachable_Sys_in_SimRel_U)

  show ?thesis
    using INV REAL_EQ HB_SUB
    by (rule system_invariant_real_history_true_queue_linearizable_if_transfer)
qed


subsection \<open>Projected real history interface\<close>

definition RealHistoryProjection :: "ActRec list \<Rightarrow> SysState \<Rightarrow> bool" where
  "RealHistoryProjection realH s \<equiv>
     Equivalent_History realH (lin_seq s) \<and>
     HB_subsumed realH (his_seq s)"

theorem system_invariant_projected_real_history_true_queue_linearizable:
  assumes INV: "system_invariant s"
      and PROJ: "RealHistoryProjection realH s"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
proof -
  have REAL_EQ: "Equivalent_History realH (lin_seq s)"
    using PROJ
    unfolding RealHistoryProjection_def
    by blast

  have HB_SUB: "HB_subsumed realH (his_seq s)"
    using PROJ
    unfolding RealHistoryProjection_def
    by blast

  show ?thesis
    using INV REAL_EQ HB_SUB
    by (rule system_invariant_real_history_true_queue_linearizable_if_transfer)
qed

corollary reachable_projected_real_history_true_queue_linearizable:
  assumes REACH: "Reachable_Sys s"
      and PROJ: "RealHistoryProjection realH s"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
proof -
  have INV: "system_invariant s"
    using REACH
    by (rule Reachable_Sys_in_SimRel_U)

  show ?thesis
    using INV PROJ
    by (rule system_invariant_projected_real_history_true_queue_linearizable)
qed

theorem system_invariant_projected_history_linearizable_wrt_Queue:
  assumes INV: "system_invariant s"
      and PROJ: "RealHistoryProjection realH s"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
  using INV PROJ
  by (rule system_invariant_projected_real_history_true_queue_linearizable)

theorem reachable_projected_history_linearizable_wrt_Queue:
  assumes REACH: "Reachable_Sys s"
      and PROJ: "RealHistoryProjection realH s"
  shows "IsLinearizable_HWQ_QueueSeqSpec realH"
  using REACH PROJ
  by (rule reachable_projected_real_history_true_queue_linearizable)

end
