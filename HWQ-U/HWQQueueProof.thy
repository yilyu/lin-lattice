theory HWQQueueProof
  imports HWQQueueLemmas
begin

(* ========================================================== *)
(* Main mechanized statements for the HWQ/UQueue case study.  *)
(* ========================================================== *)

subsection \<open>Theorem 6.1: HWQ is simulated by UQueue\<close>

theorem HWQ_is_CR_simulated_by_UQueue:
  shows
    "(\<forall>cs us. Init (cs, us) \<longrightarrow> SimRel_U cs us) \<and>
     (\<forall>cs us cs' us'.
        SimRel_U cs us \<and> Next (cs, us) (cs', us')
        \<longrightarrow> SimRel_U cs' us')"
  by (rule HWQ_is_simulated_by_UQueue)


subsection \<open>Corollary 6.2: HWQ is linearizable with respect to Queue\<close>

corollary HWQ_linearizable_wrt_Queue:
  assumes REACH: "Reachable_Sys s"
      and PROJ: "RealHistoryProjection realH s"
  shows
    "IsLinearizable_HWQ_QueueSeqSpec (his_seq s) \<and>
     IsLinearizable_HWQ_QueueSeqSpec realH"
proof (intro conjI)
  show "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
    using REACH
    by (rule HWQ_recorded_history_linearizable_wrt_queue_spec)

  show "IsLinearizable_HWQ_QueueSeqSpec realH"
    using REACH PROJ
    by (rule HWQ_projected_real_history_linearizable_wrt_queue_spec)
qed

end
