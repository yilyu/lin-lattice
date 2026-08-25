theory HistoryTransferLemmas
  imports QueueSpecTransfer
begin

(* ========================================================== *)
(* Auxiliary definitions for transferring HWQ-U histories.     *)
(* ========================================================== *)

subsection \<open>Per-process history projections\<close>

definition subhistory_of_pid :: "ActRec list \<Rightarrow> nat \<Rightarrow> ActRec list" where
  "subhistory_of_pid H p \<equiv> filter (\<lambda>a. act_pid a = p) H"

definition is_call_action :: "ActRec \<Rightarrow> bool" where
  "is_call_action a \<equiv> act_cr a = call"

definition is_return_action :: "ActRec \<Rightarrow> bool" where
  "is_return_action a \<equiv> act_cr a = ret"

definition PerProcessHistoryCompatible ::
  "ActRec list \<Rightarrow> ActRec list \<Rightarrow> nat \<Rightarrow> bool" where
  "PerProcessHistoryCompatible realH recdH p \<equiv>
     (let hp1 = subhistory_of_pid realH p;
          hp2 = subhistory_of_pid recdH p
      in
        hp1 = hp2
        \<or> (\<exists>a. is_call_action a \<and> act_pid a = p \<and> hp1 = hp2 @ [a])
        \<or> (\<exists>a. is_return_action a \<and> act_pid a = p \<and> hp2 = hp1 @ [a]))"

definition HistoryCompatible ::
  "ActRec list \<Rightarrow> ActRec list \<Rightarrow> bool" where
  "HistoryCompatible realH recdH \<equiv>
     (\<forall>p \<in> ProcSet. PerProcessHistoryCompatible realH recdH p)"


subsection \<open>Happens-before preservation\<close>

definition HB_subsumed ::
  "ActRec list \<Rightarrow> ActRec list \<Rightarrow> bool" where
  "HB_subsumed H1 H2 \<equiv>
     (\<forall>op1 op2. HB H1 op1 op2 \<longrightarrow> HB H2 op1 op2)"

lemma HB_subsumed_refl [simp]:
  "HB_subsumed H H"
  unfolding HB_subsumed_def
  by blast

lemma HB_consistent_mono:
  assumes SUB: "HB_subsumed H1 H2"
      and CONS: "HB_consistent L H2"
  shows "HB_consistent L H1"
  using SUB CONS
  unfolding HB_subsumed_def HB_consistent_def
  by blast

end
