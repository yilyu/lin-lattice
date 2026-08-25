theory QueueSpecLemmas
  imports ULinProof
begin

text \<open>
This theory builds the queue-specification bridge used by the HWQ-U proof.
The development deliberately separates two layers: an auxiliary legality
predicate used by the original proof script, and the standard FIFO queue
sequential specification used in the paper-facing statements.  The final
reviewer-facing theorem names are exported from `QueueSpecTransfer`.
\<close>

subsection \<open>Queue sequential specification\<close>

(* ========================================================== *)
(* Standard queue sequential specification for HWQ-U ops.      *)
(*                                                            *)
(* HWQ-U uses OpRec = (method, value, pid, ssn).  The queue    *)
(* state keeps values that have been enqueued but not yet      *)
(* dequeued, in FIFO order.                                   *)
(* ========================================================== *)

type_synonym QState = "nat list"

definition HWQ_QueueStep :: "QState \<Rightarrow> OpRec \<Rightarrow> QState \<Rightarrow> bool" where
  "HWQ_QueueStep q op q' \<equiv>
     (if op_name op = enq then
        q' = q @ [op_val op]
      else if op_name op = deq \<and> op_val op = BOT then
        q = [] \<and> q' = []
      else if op_name op = deq then
        (\<exists>q0. q = op_val op # q0 \<and> q' = q0)
      else
        False)"

lemma HWQ_QueueStep_Enq:
  assumes "op_name op = enq"
  shows "HWQ_QueueStep q op (q @ [op_val op])"
  using assms unfolding HWQ_QueueStep_def by simp

lemma HWQ_QueueStep_Deq:
  assumes "op_name op = deq"
      and "op_val op \<noteq> BOT"
  shows "HWQ_QueueStep (op_val op # q) op q"
  using assms unfolding HWQ_QueueStep_def by simp

lemma HWQ_QueueStep_Deq_BOT:
  assumes "op_name op = deq"
      and "op_val op = BOT"
  shows "HWQ_QueueStep [] op []"
  using assms unfolding HWQ_QueueStep_def by simp

inductive HWQ_QueueRun :: "QState \<Rightarrow> OpRec list \<Rightarrow> QState \<Rightarrow> bool" where
  HWQ_QueueRun_Nil:
    "HWQ_QueueRun q [] q"
| HWQ_QueueRun_Snoc:
    "HWQ_QueueRun q L q1 \<Longrightarrow>
     HWQ_QueueStep q1 op q2 \<Longrightarrow>
     HWQ_QueueRun q (L @ [op]) q2"

definition HWQ_QueueSeqSpec :: "OpRec list set" where
  "HWQ_QueueSeqSpec \<equiv> {L. \<exists>q. HWQ_QueueRun [] L q}"

lemma HWQ_QueueSeqSpec_Nil [simp]:
  "[] \<in> HWQ_QueueSeqSpec"
  unfolding HWQ_QueueSeqSpec_def
  using HWQ_QueueRun_Nil by blast

subsection \<open>Queue-state extraction from operation sequences\<close>

(* ========================================================== *)
(* Semantic queue-state extraction.                            *)
(*                                                            *)
(* This is the formal counterpart of the discussion:           *)
(*   +a +b +c +d -a +e -b  maps to  bcde.                     *)
(*                                                            *)
(* A value is pending after L iff its enqueue occurs in L and  *)
(* no dequeue with the same value occurs in L.  The resulting  *)
(* queue state lists pending enqueue values in their enqueue   *)
(* order.                                                     *)
(* ========================================================== *)

definition value_dequeued :: "nat \<Rightarrow> OpRec list \<Rightarrow> bool" where
  "value_dequeued v L \<equiv>
     (\<exists>i < length L. op_name (L ! i) = deq \<and> op_val (L ! i) = v)"

definition pending_enq_idx :: "OpRec list \<Rightarrow> nat \<Rightarrow> bool" where
  "pending_enq_idx L i \<equiv>
     i < length L \<and>
     op_name (L ! i) = enq \<and>
     \<not> value_dequeued (op_val (L ! i)) L"

definition opsToQState :: "OpRec list \<Rightarrow> QState" where
  "opsToQState L \<equiv>
     map (\<lambda>i. op_val (L ! i)) (filter (pending_enq_idx L) [0..<length L])"

lemma opsToQState_Nil [simp]:
  "opsToQState [] = []"
  unfolding opsToQState_def pending_enq_idx_def value_dequeued_def by simp


subsection \<open>Value well-formedness\<close>

(* ========================================================== *)
(* Value well-formedness for queue operation sequences.        *)
(*                                                            *)
(* This strengthened predicate is kept separate from           *)
(* HWQ_SqSpec so that the existing bridge remains available.   *)
(* Later, once lin_seq value well-formedness is connected to   *)
(* the HWQ-U invariants, HWQ_SqSpec_Strong is the intended     *)
(* queue specification used for the final queue-spec theorem.  *)
(* ========================================================== *)

definition QueueValueOK :: "OpRec list \<Rightarrow> bool" where
  "QueueValueOK L \<equiv> (\<forall>i < length L. op_val (L ! i) \<in> Val)"

lemma QueueValueOK_Nil [simp]:
  "QueueValueOK []"
  unfolding QueueValueOK_def by simp

lemma QueueValueOK_prefix_snoc:
  assumes OK: "QueueValueOK (L @ [op])"
  shows "QueueValueOK L"
  unfolding QueueValueOK_def
proof (intro allI impI)
  fix i
  assume I: "i < length L"
  have IA: "i < length (L @ [op])"
    using I by simp
  have "op_val ((L @ [op]) ! i) \<in> Val"
    using OK IA unfolding QueueValueOK_def by blast
  moreover have "(L @ [op]) ! i = L ! i"
    using I by (simp add: nth_append)
  ultimately show "op_val (L ! i) \<in> Val"
    by simp
qed

lemma QueueValueOK_snoc_last:
  assumes OK: "QueueValueOK (L @ [op])"
  shows "op_val op \<in> Val"
proof -
  have IDX: "length L < length (L @ [op])"
    by simp
  have "op_val ((L @ [op]) ! length L) \<in> Val"
    using OK IDX unfolding QueueValueOK_def by blast
  then show ?thesis
    by simp
qed

lemma QueueValueOK_snoc_last_not_BOT:
  assumes OK: "QueueValueOK (L @ [op])"
  shows "op_val op \<noteq> BOT"
proof -
  have "op_val op \<in> Val"
    using OK by (rule QueueValueOK_snoc_last)
  then show ?thesis
    unfolding Val_def BOT_def by auto
qed

lemma pending_enq_idx_snoc_enq_prefix:
  assumes ENQ: "op_name op = enq"
      and I: "i < length L"
  shows "pending_enq_idx (L @ [op]) i = pending_enq_idx L i"
  using assms
  unfolding pending_enq_idx_def value_dequeued_def
  by (auto simp add: nth_append)

lemma opsToQState_snoc_enq_if_no_deq:
  assumes ENQ: "op_name op = enq"
      and ND: "\<not> value_dequeued (op_val op) L"
  shows "opsToQState (L @ [op]) = opsToQState L @ [op_val op]"
proof -
  have RANGE:
    "[0..<length (L @ [op])] = [0..<length L] @ [length L]"
    by simp

  have FILTER:
    "filter (pending_enq_idx (L @ [op])) [0..<length L] =
     filter (pending_enq_idx L) [0..<length L]"
  proof (rule filter_cong)
    show "[0..<length L] = [0..<length L]"
      by simp
  next
    fix i
    assume I: "i \<in> set [0..<length L]"
    then have IL: "i < length L"
      by simp
    show "pending_enq_idx (L @ [op]) i = pending_enq_idx L i"
      using ENQ IL by (rule pending_enq_idx_snoc_enq_prefix)
  qed

  have MAP:
    "map (\<lambda>i. op_val ((L @ [op]) ! i))
        (filter (pending_enq_idx L) [0..<length L]) =
     map (\<lambda>i. op_val (L ! i))
        (filter (pending_enq_idx L) [0..<length L])"
    by (rule map_cong[OF refl]) (auto simp add: nth_append)

  have LAST: "pending_enq_idx (L @ [op]) (length L)"
    using ENQ ND
    unfolding pending_enq_idx_def value_dequeued_def
    by (auto simp add: nth_append)

  show ?thesis
    unfolding opsToQState_def
    using RANGE FILTER MAP LAST
    by simp
qed

subsection \<open>HWQ-U local sequential predicate\<close>

(* ========================================================== *)
(* The current HWQ-U local sequential predicate.               *)
(*                                                            *)
(* For the queue-spec bridge we use exactly the two properties *)
(* needed for queue behaviour: FIFO semantics and data         *)
(* independence.  lI5_SA_Prefix_list remains an internal HWQ-U *)
(* invariant and is not needed for this bridge.                *)
(* ========================================================== *)

definition HWQ_SqSpec :: "OpRec list set" where
  "HWQ_SqSpec \<equiv> {L. lI4_FIFO_Semantics_list L \<and> data_independent L}"

lemma system_invariant_lin_seq_Legal_Queue_Seq:
  assumes INV: "system_invariant s"
  shows "Legal_Queue_Seq (lin_seq s)"
proof -
  have I_lin4: "lI4_FIFO_Semantics s"
    using INV unfolding system_invariant_def by blast
  have I_lin5: "lI5_SA_Prefix s"
    using INV unfolding system_invariant_def by blast
  have I_di: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by blast

  have FIFO: "lI4_FIFO_Semantics_list (lin_seq s)"
    using I_lin4 unfolding lI4_FIFO_Semantics_def by simp
  have SA: "lI5_SA_Prefix_list (lin_seq s)"
    using I_lin5 unfolding lI5_SA_Prefix_def by simp

  show ?thesis
    unfolding Legal_Queue_Seq_def
    using FIFO SA I_di by blast
qed

lemma system_invariant_lin_seq_in_HWQ_SqSpec:
  assumes INV: "system_invariant s"
  shows "lin_seq s \<in> HWQ_SqSpec"
proof -
  have I_lin4: "lI4_FIFO_Semantics s"
    using INV unfolding system_invariant_def by blast
  have I_di: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by blast
  have FIFO: "lI4_FIFO_Semantics_list (lin_seq s)"
    using I_lin4 unfolding lI4_FIFO_Semantics_def by simp
  show ?thesis
    unfolding HWQ_SqSpec_def
    using FIFO I_di by blast
qed

corollary reachable_lin_seq_in_HWQ_SqSpec:
  assumes "Reachable_Sys s"
  shows "lin_seq s \<in> HWQ_SqSpec"
  using assms Reachable_Sys_in_SimRel_U system_invariant_lin_seq_in_HWQ_SqSpec
  by blast








subsection \<open>Generic bridge to the queue sequential specification\<close>

(* ========================================================== *)
(* Generic bridge from a snoc-closed specification to QSpec.   *)
(* ========================================================== *)

locale HWQ_QueueSubSpec_ByStep =
  fixes sqSpec :: "OpRec list set"
  assumes sqSpec_Nil: "[] \<in> sqSpec"
      and sqSpec_prefix_snoc: "L @ [op] \<in> sqSpec \<Longrightarrow> L \<in> sqSpec"
      and sqSpec_step:
        "L @ [op] \<in> sqSpec \<Longrightarrow>
         HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
begin

lemma sqSpec_run:
  assumes "L \<in> sqSpec"
  shows "HWQ_QueueRun [] L (opsToQState L)"
proof -
  have AUX: "L \<in> sqSpec \<longrightarrow> HWQ_QueueRun [] L (opsToQState L)"
  proof (induct L rule: rev_induct)
    case Nil
    show ?case
      by (intro impI, simp add: HWQ_QueueRun_Nil)
  next
    case (snoc op L)
    show ?case
    proof
      assume A: "L @ [op] \<in> sqSpec"
      have PRE: "L \<in> sqSpec"
        using A by (rule sqSpec_prefix_snoc)
      have IH: "HWQ_QueueRun [] L (opsToQState L)"
        using snoc.hyps PRE by blast
      have STEP: "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
        using A by (rule sqSpec_step)
      show "HWQ_QueueRun [] (L @ [op]) (opsToQState (L @ [op]))"
        using HWQ_QueueRun_Snoc[OF IH STEP] .
    qed
  qed
  then show ?thesis
    using assms by blast
qed

theorem sqSpec_subset_HWQ_QueueSeqSpec:
  "sqSpec \<subseteq> HWQ_QueueSeqSpec"
  unfolding HWQ_QueueSeqSpec_def
  using sqSpec_run by blast

end

theorem HWQ_SqSpec_subset_HWQ_QueueSeqSpec_if_step:
  assumes "HWQ_QueueSubSpec_ByStep HWQ_SqSpec"
  shows "HWQ_SqSpec \<subseteq> HWQ_QueueSeqSpec"
  using assms HWQ_QueueSubSpec_ByStep.sqSpec_subset_HWQ_QueueSeqSpec by blast

subsection \<open>Prefix closure\<close>

(* ========================================================== *)
(* Prefix closure of HWQ_SqSpec.                               *)
(* ========================================================== *)

lemma HWQ_SqSpec_Nil:
  "[] \<in> HWQ_SqSpec"
  unfolding HWQ_SqSpec_def
            lI4_FIFO_Semantics_list_def
            data_independent_def
  by simp

lemma data_independent_prefix_snoc:
  assumes DI: "data_independent (L @ [op])"
  shows "data_independent L"
  unfolding data_independent_def
proof (intro conjI allI)
  fix v

  let ?A = "{i. i < length L \<and>
                 op_name (L ! i) = enq \<and>
                 op_val (L ! i) = v}"
  let ?B = "{i. i < length (L @ [op]) \<and>
                 op_name ((L @ [op]) ! i) = enq \<and>
                 op_val ((L @ [op]) ! i) = v}"

  have SUB: "?A \<subseteq> ?B"
    by (auto simp add: nth_append)

  have FIN: "finite ?B"
    by (rule finite_subset[of ?B "{i. i < length (L @ [op])}"]) auto

  have "card ?A \<le> card ?B"
    by (rule card_mono[OF FIN SUB])
  also have "... \<le> 1"
    using DI unfolding data_independent_def by blast
  finally show "card ?A \<le> 1" .
next
  fix v

  let ?A = "{i. i < length L \<and>
                 op_name (L ! i) = deq \<and>
                 op_val (L ! i) = v}"
  let ?B = "{i. i < length (L @ [op]) \<and>
                 op_name ((L @ [op]) ! i) = deq \<and>
                 op_val ((L @ [op]) ! i) = v}"

  have SUB: "?A \<subseteq> ?B"
    by (auto simp add: nth_append)

  have FIN: "finite ?B"
    by (rule finite_subset[of ?B "{i. i < length (L @ [op])}"]) auto

  have "card ?A \<le> card ?B"
    by (rule card_mono[OF FIN SUB])
  also have "... \<le> 1"
    using DI unfolding data_independent_def by blast
  finally show "card ?A \<le> 1" .
qed

lemma lI4_FIFO_Semantics_list_prefix_snoc:
  assumes I4: "lI4_FIFO_Semantics_list (L @ [op])"
  shows "lI4_FIFO_Semantics_list L"
  unfolding lI4_FIFO_Semantics_list_def Let_def
proof (intro allI impI)
  fix k1
  assume K1: "k1 < length L"
  let ?act1 = "L ! k1"
  assume DEQ1: "op_name ?act1 = deq"

  have K1A: "k1 < length (L @ [op])"
    using K1 by simp
  have N1: "(L @ [op]) ! k1 = L ! k1"
    using K1 by (simp add: nth_append)

  have I4_all:
    "\<forall>i<length (L @ [op]).
       op_name ((L @ [op]) ! i) = deq \<longrightarrow>
       (\<exists>j<i.
          op_name ((L @ [op]) ! j) = enq \<and>
          op_val ((L @ [op]) ! j) = op_val ((L @ [op]) ! i) \<and>
          (\<forall>k<j.
             op_name ((L @ [op]) ! k) = enq \<longrightarrow>
             (\<exists>r.
                k < r \<and> r < i \<and>
                op_name ((L @ [op]) ! r) = deq \<and>
                op_val ((L @ [op]) ! r) = op_val ((L @ [op]) ! k))))"
    using I4
    unfolding lI4_FIFO_Semantics_list_def Let_def
    by simp

  have DEQ1A: "op_name ((L @ [op]) ! k1) = deq"
    using DEQ1 N1 by simp

  have I4_k1:
    "\<exists>k2<k1.
       op_name ((L @ [op]) ! k2) = enq \<and>
       op_val ((L @ [op]) ! k2) = op_val ((L @ [op]) ! k1) \<and>
       (\<forall>k3<k2.
          op_name ((L @ [op]) ! k3) = enq \<longrightarrow>
          (\<exists>k4.
             k3 < k4 \<and> k4 < k1 \<and>
             op_name ((L @ [op]) ! k4) = deq \<and>
             op_val ((L @ [op]) ! k4) =
             op_val ((L @ [op]) ! k3)))"
    using I4_all K1A DEQ1A by blast

  obtain k2 where
    K2: "k2 < k1" and
    ENQ2A: "op_name ((L @ [op]) ! k2) = enq" and
    VAL2A: "op_val ((L @ [op]) ! k2) = op_val ((L @ [op]) ! k1)" and
    ALLA:
      "\<forall>k3<k2.
          op_name ((L @ [op]) ! k3) = enq \<longrightarrow>
          (\<exists>k4.
             k3 < k4 \<and> k4 < k1 \<and>
             op_name ((L @ [op]) ! k4) = deq \<and>
             op_val ((L @ [op]) ! k4) =
             op_val ((L @ [op]) ! k3))"
    using I4_k1 by auto

  have K2L: "k2 < length L"
    using K2 K1 by simp

  have ENQ2: "op_name (L ! k2) = enq"
    using ENQ2A K2L by (simp add: nth_append)

  have VAL2: "op_val (L ! k2) = op_val (L ! k1)"
    using VAL2A K1 K2L by (simp add: nth_append)

  have ALL:
    "\<forall>k3<k2.
       op_name (L ! k3) = enq \<longrightarrow>
       (\<exists>k4.
          k3 < k4 \<and> k4 < k1 \<and>
          op_name (L ! k4) = deq \<and>
          op_val (L ! k4) = op_val (L ! k3))"
  proof (intro allI impI)
    fix k3
    assume K3: "k3 < k2"
    assume ENQ3: "op_name (L ! k3) = enq"

    have K3L: "k3 < length L"
      using K3 K2 K1 by simp
    have ENQ3A: "op_name ((L @ [op]) ! k3) = enq"
      using ENQ3 K3L by (simp add: nth_append)

    obtain k4 where
      K34: "k3 < k4" and
      K41: "k4 < k1" and
      DEQ4A: "op_name ((L @ [op]) ! k4) = deq" and
      VAL4A: "op_val ((L @ [op]) ! k4) =
              op_val ((L @ [op]) ! k3)"
      using ALLA K3 ENQ3A by blast

    have K4L: "k4 < length L"
      using K41 K1 by simp

    have DEQ4: "op_name (L ! k4) = deq"
      using DEQ4A K4L by (simp add: nth_append)

    have VAL4: "op_val (L ! k4) = op_val (L ! k3)"
      using VAL4A K3L K4L by (simp add: nth_append)

    show "\<exists>k4.
          k3 < k4 \<and> k4 < k1 \<and>
          op_name (L ! k4) = deq \<and>
          op_val (L ! k4) = op_val (L ! k3)"
      using K34 K41 DEQ4 VAL4 by blast
  qed

  show "\<exists>k2<k1.
          op_name (L ! k2) = enq \<and>
          op_val (L ! k2) = op_val (L ! k1) \<and>
          (\<forall>k3<k2.
             op_name (L ! k3) = enq \<longrightarrow>
             (\<exists>k4.
                k3 < k4 \<and> k4 < k1 \<and>
                op_name (L ! k4) = deq \<and>
                op_val (L ! k4) = op_val (L ! k3)))"
    using K2 ENQ2 VAL2 ALL by blast
qed

lemma HWQ_SqSpec_prefix_snoc:
  assumes A: "L @ [op] \<in> HWQ_SqSpec"
  shows "L \<in> HWQ_SqSpec"
proof -
  have I4: "lI4_FIFO_Semantics_list (L @ [op])"
    using A unfolding HWQ_SqSpec_def by blast
  have DI: "data_independent (L @ [op])"
    using A unfolding HWQ_SqSpec_def by blast

  have I4L: "lI4_FIFO_Semantics_list L"
    using I4 by (rule lI4_FIFO_Semantics_list_prefix_snoc)
  have DIL: "data_independent L"
    using DI by (rule data_independent_prefix_snoc)

  show ?thesis
    unfolding HWQ_SqSpec_def
    using I4L DIL by blast
qed


subsection \<open>Strengthened HWQ-U sequential predicate\<close>

(* ========================================================== *)
(* Strengthened HWQ-U sequential predicate with value sanity.  *)
(* ========================================================== *)

definition HWQ_SqSpec_Strong :: "OpRec list set" where
  "HWQ_SqSpec_Strong \<equiv> {L. L \<in> HWQ_SqSpec \<and> QueueValueOK L}"

lemma HWQ_SqSpec_StrongD1:
  assumes "L \<in> HWQ_SqSpec_Strong"
  shows "L \<in> HWQ_SqSpec"
  using assms
  unfolding HWQ_SqSpec_Strong_def
  by simp

lemma HWQ_SqSpec_StrongD2:
  assumes "L \<in> HWQ_SqSpec_Strong"
  shows "QueueValueOK L"
  using assms
  unfolding HWQ_SqSpec_Strong_def
  by simp


lemma HWQ_SqSpec_Strong_Nil:
  "[] \<in> HWQ_SqSpec_Strong"
  unfolding HWQ_SqSpec_Strong_def
  using HWQ_SqSpec_Nil by simp

lemma HWQ_SqSpec_Strong_prefix_snoc:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
  shows "L \<in> HWQ_SqSpec_Strong"
proof -
  have A0: "L @ [op] \<in> HWQ_SqSpec"
    using A unfolding HWQ_SqSpec_Strong_def by blast
  have OK: "QueueValueOK (L @ [op])"
    using A unfolding HWQ_SqSpec_Strong_def by blast
  have PRE0: "L \<in> HWQ_SqSpec"
    using A0 by (rule HWQ_SqSpec_prefix_snoc)
  have PREOK: "QueueValueOK L"
    using OK by (rule QueueValueOK_prefix_snoc)
  show ?thesis
    unfolding HWQ_SqSpec_Strong_def
    using PRE0 PREOK by blast
qed

lemma HWQ_SqSpec_Strong_last_value:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
  shows "op_val op \<in> Val"
  using A unfolding HWQ_SqSpec_Strong_def
  by (blast intro: QueueValueOK_snoc_last)

lemma HWQ_SqSpec_Strong_last_not_BOT:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
  shows "op_val op \<noteq> BOT"
proof -
  have QOK: "QueueValueOK (L @ [op])"
    using A unfolding HWQ_SqSpec_Strong_def by simp
  show ?thesis
    using QueueValueOK_snoc_last_not_BOT[OF QOK] .
qed

lemma HWQ_SqSpec_Strong_enq_no_deq_value:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and ENQ: "op_name op = enq"
  shows "\<not> value_dequeued (op_val op) L"
proof
  assume VD: "value_dequeued (op_val op) L"

  have A0: "L @ [op] \<in> HWQ_SqSpec"
    using A by (rule HWQ_SqSpec_StrongD1)

  have I4: "lI4_FIFO_Semantics_list (L @ [op])"
    using A0 unfolding HWQ_SqSpec_def by blast

  have DI: "data_independent (L @ [op])"
    using A0 unfolding HWQ_SqSpec_def by blast

  obtain k where
    K: "k < length L" and
    DEQK: "op_name (L ! k) = deq" and
    VALK: "op_val (L ! k) = op_val op"
    using VD unfolding value_dequeued_def by blast

  have KA: "k < length (L @ [op])"
    using K by simp
  have DEQKA: "op_name ((L @ [op]) ! k) = deq"
    using K DEQK by (simp add: nth_append)
  have VALKA: "op_val ((L @ [op]) ! k) = op_val op"
    using K VALK by (simp add: nth_append)

  have I4_all:
    "\<forall>i<length (L @ [op]).
       op_name ((L @ [op]) ! i) = deq \<longrightarrow>
       (\<exists>j<i.
          op_name ((L @ [op]) ! j) = enq \<and>
          op_val ((L @ [op]) ! j) = op_val ((L @ [op]) ! i) \<and>
          (\<forall>k<j.
             op_name ((L @ [op]) ! k) = enq \<longrightarrow>
             (\<exists>r.
                k < r \<and> r < i \<and>
                op_name ((L @ [op]) ! r) = deq \<and>
                op_val ((L @ [op]) ! r) = op_val ((L @ [op]) ! k))))"
    using I4
    unfolding lI4_FIFO_Semantics_list_def Let_def
    by simp

  obtain j where
    J: "j < k" and
    ENQJ: "op_name ((L @ [op]) ! j) = enq" and
    VALJ: "op_val ((L @ [op]) ! j) = op_val ((L @ [op]) ! k)"
    using I4_all KA DEQKA by blast

  let ?S = "{i. i < length (L @ [op]) \<and>
                op_name ((L @ [op]) ! i) = enq \<and>
                op_val ((L @ [op]) ! i) = op_val op}"

  have JIN: "j \<in> ?S"
    using J K ENQJ VALJ VALKA by simp

  have LIN: "length L \<in> ?S"
    using ENQ by simp

  have JNE: "j \<noteq> length L"
    using J K by simp

  have SUB: "{j, length L} \<subseteq> ?S"
    using JIN LIN by blast

  have FIN: "finite ?S"
    by (rule finite_subset[of ?S "{i. i < length (L @ [op])}"]) auto

  have "card {j, length L} \<le> card ?S"
    by (rule card_mono[OF FIN SUB])
  then have TWO: "2 \<le> card ?S"
    using JNE by simp

  have ONE: "card ?S \<le> 1"
    using DI unfolding data_independent_def by blast

  show False
    using TWO ONE by linarith
qed

lemma HWQ_SqSpec_Strong_enq_step:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and ENQ: "op_name op = enq"
  shows "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
proof -
  have ND: "\<not> value_dequeued (op_val op) L"
    using A ENQ by (rule HWQ_SqSpec_Strong_enq_no_deq_value)
  have EQ: "opsToQState (L @ [op]) = opsToQState L @ [op_val op]"
    using ENQ ND by (rule opsToQState_snoc_enq_if_no_deq)
  show ?thesis
    using ENQ EQ
    by (simp add: HWQ_QueueStep_def)
qed


lemma value_dequeued_snoc_deq:
  assumes DEQ: "op_name op = deq"
  shows "value_dequeued v (L @ [op]) =
         (value_dequeued v L \<or> v = op_val op)"
proof
  assume A: "value_dequeued v (L @ [op])"

  obtain i where
    I: "i < length (L @ [op])" and
    DEQI: "op_name ((L @ [op]) ! i) = deq" and
    VALI: "op_val ((L @ [op]) ! i) = v"
    using A unfolding value_dequeued_def by blast

  have CASES: "i < length L \<or> i = length L"
    using I by (simp add: less_Suc_eq)

  show "value_dequeued v L \<or> v = op_val op"
  proof (cases "i < length L")
    case True
    have DEQL: "op_name (L ! i) = deq"
      using True DEQI by (simp add: nth_append)
    have VALL: "op_val (L ! i) = v"
      using True VALI by (simp add: nth_append)
    have "value_dequeued v L"
      unfolding value_dequeued_def
      using True DEQL VALL by blast
    then show ?thesis by blast
  next
    case False
    have IEQ: "i = length L"
      using CASES False by blast
    have "op_val op = v"
      using IEQ VALI by simp
    then show ?thesis by blast
  qed
next
  assume A: "value_dequeued v L \<or> v = op_val op"

  show "value_dequeued v (L @ [op])"
  proof (cases "value_dequeued v L")
    case True
    obtain i where
      I: "i < length L" and
      DEQI: "op_name (L ! i) = deq" and
      VALI: "op_val (L ! i) = v"
      using True unfolding value_dequeued_def by blast

    have IA: "i < length (L @ [op])"
      using I by simp
    have DEQA: "op_name ((L @ [op]) ! i) = deq"
      using I DEQI by (simp add: nth_append)
    have VALA: "op_val ((L @ [op]) ! i) = v"
      using I VALI by (simp add: nth_append)

    show ?thesis
      unfolding value_dequeued_def
      using IA DEQA VALA by blast
  next
    case False
    have V: "v = op_val op"
      using A False by blast

    have IDX: "length L < length (L @ [op])"
      by simp
    have DEQA: "op_name ((L @ [op]) ! length L) = deq"
      using DEQ by simp
    have VALA: "op_val ((L @ [op]) ! length L) = v"
      using V by simp

    show ?thesis
      unfolding value_dequeued_def
      using IDX DEQA VALA by blast
  qed
qed

lemma pending_enq_idx_snoc_deq_prefix:
  assumes DEQ: "op_name op = deq"
      and I: "i < length L"
  shows "pending_enq_idx (L @ [op]) i =
         (pending_enq_idx L i \<and> op_val (L ! i) \<noteq> op_val op)"
  using assms
  unfolding pending_enq_idx_def
  by (simp add: nth_append value_dequeued_snoc_deq)

lemma HWQ_SqSpec_Strong_deq_has_match:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and DEQ: "op_name op = deq"
  shows "\<exists>j < length L.
           op_name (L ! j) = enq \<and>
           op_val (L ! j) = op_val op \<and>
           (\<forall>k < j.
              op_name (L ! k) = enq \<longrightarrow>
              value_dequeued (op_val (L ! k)) L)"
proof -
  have A0: "L @ [op] \<in> HWQ_SqSpec"
    using A by (rule HWQ_SqSpec_StrongD1)

  have I4: "lI4_FIFO_Semantics_list (L @ [op])"
    using A0 unfolding HWQ_SqSpec_def by blast

  have I4_all:
    "\<forall>i<length (L @ [op]).
       op_name ((L @ [op]) ! i) = deq \<longrightarrow>
       (\<exists>j<i.
          op_name ((L @ [op]) ! j) = enq \<and>
          op_val ((L @ [op]) ! j) = op_val ((L @ [op]) ! i) \<and>
          (\<forall>k<j.
             op_name ((L @ [op]) ! k) = enq \<longrightarrow>
             (\<exists>r.
                k < r \<and> r < i \<and>
                op_name ((L @ [op]) ! r) = deq \<and>
                op_val ((L @ [op]) ! r) = op_val ((L @ [op]) ! k))))"
    using I4
    unfolding lI4_FIFO_Semantics_list_def Let_def
    by simp

  have IDX: "length L < length (L @ [op])"
    by simp

  have DEQA: "op_name ((L @ [op]) ! length L) = deq"
    using DEQ by simp

  obtain j where
    J: "j < length L" and
    ENQJ_A: "op_name ((L @ [op]) ! j) = enq" and
    VALJ_A: "op_val ((L @ [op]) ! j) = op_val ((L @ [op]) ! length L)" and
    ALLA:
      "\<forall>k<j.
          op_name ((L @ [op]) ! k) = enq \<longrightarrow>
          (\<exists>r.
             k < r \<and> r < length L \<and>
             op_name ((L @ [op]) ! r) = deq \<and>
             op_val ((L @ [op]) ! r) = op_val ((L @ [op]) ! k))"
    using I4_all IDX DEQA by blast

  have ENQJ: "op_name (L ! j) = enq"
    using J ENQJ_A by (simp add: nth_append)

  have VALJ: "op_val (L ! j) = op_val op"
    using J VALJ_A by (simp add: nth_append)

  have ALL:
    "\<forall>k<j.
       op_name (L ! k) = enq \<longrightarrow>
       value_dequeued (op_val (L ! k)) L"
  proof (intro allI impI)
    fix k
    assume K: "k < j"
    assume ENQK: "op_name (L ! k) = enq"

    have KL: "k < length L"
      using K J by simp

    have ENQK_A: "op_name ((L @ [op]) ! k) = enq"
      using KL ENQK by (simp add: nth_append)

    obtain r where
      KR: "k < r" and
      RL: "r < length L" and
      DEQR_A: "op_name ((L @ [op]) ! r) = deq" and
      VALR_A: "op_val ((L @ [op]) ! r) = op_val ((L @ [op]) ! k)"
      using ALLA K ENQK_A by blast

    have DEQR: "op_name (L ! r) = deq"
      using RL DEQR_A by (simp add: nth_append)

    have VALR: "op_val (L ! r) = op_val (L ! k)"
      using RL KL VALR_A by (simp add: nth_append)

    show "value_dequeued (op_val (L ! k)) L"
      unfolding value_dequeued_def
      using RL DEQR VALR by blast
  qed

  show ?thesis
    using J ENQJ VALJ ALL by blast
qed

lemma HWQ_SqSpec_Strong_deq_no_old_deq:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and DEQ: "op_name op = deq"
  shows "\<not> value_dequeued (op_val op) L"
proof
  assume VD: "value_dequeued (op_val op) L"

  have A0: "L @ [op] \<in> HWQ_SqSpec"
    using A by (rule HWQ_SqSpec_StrongD1)

  have DI: "data_independent (L @ [op])"
    using A0 unfolding HWQ_SqSpec_def by blast

  obtain k where
    K: "k < length L" and
    DEQK: "op_name (L ! k) = deq" and
    VALK: "op_val (L ! k) = op_val op"
    using VD unfolding value_dequeued_def by blast

  let ?S = "{i. i < length (L @ [op]) \<and>
                op_name ((L @ [op]) ! i) = deq \<and>
                op_val ((L @ [op]) ! i) = op_val op}"

  have KIN: "k \<in> ?S"
    using K DEQK VALK by (simp add: nth_append)

  have LIN: "length L \<in> ?S"
    using DEQ by simp

  have KNE: "k \<noteq> length L"
    using K by simp

  have SUB: "{k, length L} \<subseteq> ?S"
    using KIN LIN by blast

  have FIN: "finite ?S"
    by (rule finite_subset[of ?S "{i. i < length (L @ [op])}"]) auto

  have "card {k, length L} \<le> card ?S"
    by (rule card_mono[OF FIN SUB])
  then have TWO: "2 \<le> card ?S"
    using KNE by simp

  have ONE: "card ?S \<le> 1"
    using DI unfolding data_independent_def by blast

  show False
    using TWO ONE by linarith
qed

lemma HWQ_SqSpec_Strong_deq_pending_match:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and DEQ: "op_name op = deq"
  shows "\<exists>j < length L.
           pending_enq_idx L j \<and>
           op_val (L ! j) = op_val op \<and>
           (\<forall>k < j. \<not> pending_enq_idx L k)"
proof -
  obtain j where
    J: "j < length L" and
    ENQJ: "op_name (L ! j) = enq" and
    VALJ: "op_val (L ! j) = op_val op" and
    ALL:
      "\<forall>k < j.
         op_name (L ! k) = enq \<longrightarrow>
         value_dequeued (op_val (L ! k)) L"
    using HWQ_SqSpec_Strong_deq_has_match[OF A DEQ] by blast

  have NOLD: "\<not> value_dequeued (op_val op) L"
    using A DEQ by (rule HWQ_SqSpec_Strong_deq_no_old_deq)

  have PENDJ: "pending_enq_idx L j"
    using J ENQJ VALJ NOLD
    unfolding pending_enq_idx_def
    by simp

  have BEFORE: "\<forall>k < j. \<not> pending_enq_idx L k"
  proof (intro allI impI)
    fix k
    assume K: "k < j"

    show "\<not> pending_enq_idx L k"
    proof
      assume P: "pending_enq_idx L k"

      have ENQK: "op_name (L ! k) = enq"
        using P unfolding pending_enq_idx_def by blast

      have VD: "value_dequeued (op_val (L ! k)) L"
        using ALL K ENQK by blast

      have NVD: "\<not> value_dequeued (op_val (L ! k)) L"
        using P unfolding pending_enq_idx_def by blast

      show False
        using VD NVD by blast
    qed
  qed

  show ?thesis
    using J PENDJ VALJ BEFORE by blast
qed

lemma filter_upt_first_true:
  assumes J: "j < n"
      and PJ: "P j"
      and BEFORE: "\<And>k. k < j \<Longrightarrow> \<not> P k"
  shows "\<exists>xs. filter P [0..<n] = j # xs"
proof -
  have ADD: "j + (n - j) = n"
    using J by simp

  have SPLIT1: "[0..<n] = [0..<j] @ [j..<n]"
  proof -
    have "[0..<j + (n - j)] = [0..<j] @ [j..<j + (n - j)]"
          by (rule upt_add_eq_append, simp)
    then show ?thesis
      using ADD by simp
  qed

  have SPLIT2: "[j..<n] = j # [Suc j..<n]"
    using J by (simp add: upt_rec)

  have F0: "filter P [0..<j] = []"
    using BEFORE by auto

  have "filter P [0..<n] =
        filter P ([0..<j] @ (j # [Suc j..<n]))"
    using SPLIT1 SPLIT2 by simp
  also have "... = filter P [0..<j] @ filter P (j # [Suc j..<n])"
    by simp
  also have "... = j # filter P [Suc j..<n]"
    using F0 PJ by simp
  finally show ?thesis
    by blast
qed

lemma HWQ_SqSpec_Strong_deq_old_state_head:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and DEQ: "op_name op = deq"
  shows "\<exists>q. opsToQState L = op_val op # q"
proof -
  obtain j where
    J: "j < length L" and
    PENDJ: "pending_enq_idx L j" and
    VALJ: "op_val (L ! j) = op_val op" and
    BEFORE: "\<forall>k < j. \<not> pending_enq_idx L k"
    using HWQ_SqSpec_Strong_deq_pending_match[OF A DEQ] by blast

  have BEFORE':
    "\<And>k. k < j \<Longrightarrow> \<not> pending_enq_idx L k"
    using BEFORE by blast

  have EX:
    "\<exists>xs. filter (pending_enq_idx L) [0..<length L] = j # xs"
    by (rule filter_upt_first_true[
          where P = "pending_enq_idx L"
            and j = j
            and n = "length L",
          OF J PENDJ BEFORE'])

  obtain xs where
    F: "filter (pending_enq_idx L) [0..<length L] = j # xs"
    using EX by blast

  have EQ0:
    "opsToQState L = op_val (L ! j) # map (\<lambda>i. op_val (L ! i)) xs"
    unfolding opsToQState_def
    using F by simp

  have EQ:
    "opsToQState L = op_val op # map (\<lambda>i. op_val (L ! i)) xs"
    using EQ0 VALJ by simp

  show ?thesis
    using EQ by blast
qed

lemma data_independent_enq_same_val_eq:
  assumes DI: "data_independent L"
      and I: "i < length L"
      and J: "j < length L"
      and ENQI: "op_name (L ! i) = enq"
      and ENQJ: "op_name (L ! j) = enq"
      and VALI: "op_val (L ! i) = v"
      and VALJ: "op_val (L ! j) = v"
  shows "i = j"
proof (rule ccontr)
  assume NE: "i \<noteq> j"

  let ?S = "{k. k < length L \<and>
                op_name (L ! k) = enq \<and>
                op_val (L ! k) = v}"

  have IIN: "i \<in> ?S"
    using I ENQI VALI by simp
  have JIN: "j \<in> ?S"
    using J ENQJ VALJ by simp

  have SUB: "{i, j} \<subseteq> ?S"
    using IIN JIN by blast

  have FIN: "finite ?S"
    by (rule finite_subset[of ?S "{k. k < length L}"]) auto

  have "card {i, j} \<le> card ?S"
    by (rule card_mono[OF FIN SUB])
  then have TWO: "2 \<le> card ?S"
    using NE by simp

  have ONE: "card ?S \<le> 1"
    using DI unfolding data_independent_def by blast

  show False
    using TWO ONE by linarith
qed

lemma pending_enq_idx_snoc_deq_last_false:
  assumes DEQ: "op_name op = deq"
  shows "\<not> pending_enq_idx (L @ [op]) (length L)"
  using DEQ
  unfolding pending_enq_idx_def
  by simp

lemma opsToQState_snoc_deq_from_first_pending:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and DEQ: "op_name op = deq"
      and J: "j < length L"
      and F: "filter (pending_enq_idx L) [0..<length L] = j # xs"
      and VALJ: "op_val (L ! j) = op_val op"
  shows "opsToQState (L @ [op]) = map (\<lambda>i. op_val (L ! i)) xs"
proof -
  have A0: "L @ [op] \<in> HWQ_SqSpec"
    using A by (rule HWQ_SqSpec_StrongD1)

  have DI: "data_independent (L @ [op])"
    using A0 unfolding HWQ_SqSpec_def by blast

  have DISTINCT_FILTER:
    "distinct (filter (pending_enq_idx L) [0..<length L])"
    by (rule distinct_filter, simp)

  have DISTINCT: "distinct (j # xs)"
    using DISTINCT_FILTER F by simp

  have J_NOT_XS: "j \<notin> set xs"
    using DISTINCT by simp

  have XS_PROP:
    "\<forall>i \<in> set xs. i < length L \<and> pending_enq_idx L i"
  proof
    fix i
    assume IX: "i \<in> set xs"

    have IN_CONS: "i \<in> set (j # xs)"
      using IX by simp

    have IN_FILTER:
      "i \<in> set (filter (pending_enq_idx L) [0..<length L])"
      using F IN_CONS by simp

    have IL: "i < length L"
      using IN_FILTER by simp

    have PI: "pending_enq_idx L i"
      using IN_FILTER by simp

    show "i < length L \<and> pending_enq_idx L i"
      using IL PI by blast
  qed

  have XS_NOVAL:
    "\<forall>i \<in> set xs. op_val (L ! i) \<noteq> op_val op"
  proof
    fix i
    assume IX: "i \<in> set xs"

    have IL: "i < length L"
      using XS_PROP IX by blast
    have PI: "pending_enq_idx L i"
      using XS_PROP IX by blast

    have ENQI: "op_name (L ! i) = enq"
      using PI unfolding pending_enq_idx_def by blast

    have J_IN_FILTER:
      "j \<in> set (filter (pending_enq_idx L) [0..<length L])"
      using F by simp

    have PENDJ: "pending_enq_idx L j"
      using J_IN_FILTER by simp

    have ENQJ: "op_name (L ! j) = enq"
      using PENDJ unfolding pending_enq_idx_def by blast

    have INE: "i \<noteq> j"
      using IX J_NOT_XS by blast

    show "op_val (L ! i) \<noteq> op_val op"
    proof
      assume VALI: "op_val (L ! i) = op_val op"

      have IA: "i < length (L @ [op])"
        using IL by simp
      have JA: "j < length (L @ [op])"
        using J by simp

      have ENQI_A: "op_name ((L @ [op]) ! i) = enq"
        using IL ENQI by (simp add: nth_append)
      have ENQJ_A: "op_name ((L @ [op]) ! j) = enq"
        using J ENQJ by (simp add: nth_append)

      have VALI_A: "op_val ((L @ [op]) ! i) = op_val op"
        using IL VALI by (simp add: nth_append)
      have VALJ_A: "op_val ((L @ [op]) ! j) = op_val op"
        using J VALJ by (simp add: nth_append)

      have EQ: "i = j"
        by (rule data_independent_enq_same_val_eq[
              OF DI IA JA ENQI_A ENQJ_A VALI_A VALJ_A])

      show False
        using INE EQ by blast
    qed
  qed

  have FPREFIX:
    "filter (pending_enq_idx (L @ [op])) [0..<length L] =
     filter (\<lambda>i. op_val (L ! i) \<noteq> op_val op)
       (filter (pending_enq_idx L) [0..<length L])"
  proof -
    have "filter (pending_enq_idx (L @ [op])) [0..<length L] =
          filter (\<lambda>i. pending_enq_idx L i \<and>
                     op_val (L ! i) \<noteq> op_val op) [0..<length L]"
    proof (rule filter_cong)
      show "[0..<length L] = [0..<length L]"
        by simp
    next
      fix i
      assume I: "i \<in> set [0..<length L]"
      then have IL: "i < length L"
        by simp
      show "pending_enq_idx (L @ [op]) i =
            (pending_enq_idx L i \<and> op_val (L ! i) \<noteq> op_val op)"
        using DEQ IL by (rule pending_enq_idx_snoc_deq_prefix)
    qed
    also have "... =
          filter (\<lambda>i. op_val (L ! i) \<noteq> op_val op)
            (filter (pending_enq_idx L) [0..<length L])"
      by simp
    finally show ?thesis .
  qed

  have FILTER_XS:
    "filter (\<lambda>i. op_val (L ! i) \<noteq> op_val op) xs = xs"
    using XS_NOVAL by (induct xs) auto

  have FX:
    "filter (pending_enq_idx (L @ [op])) [0..<length L] = xs"
  proof -
    have "filter (pending_enq_idx (L @ [op])) [0..<length L] =
          filter (\<lambda>i. op_val (L ! i) \<noteq> op_val op) (j # xs)"
      using FPREFIX F by simp
    also have "... = xs"
      using VALJ FILTER_XS by simp
    finally show ?thesis .
  qed

  have LAST_FALSE:
    "\<not> pending_enq_idx (L @ [op]) (length L)"
    using DEQ by (rule pending_enq_idx_snoc_deq_last_false)

  have RANGE:
    "[0..<length (L @ [op])] = [0..<length L] @ [length L]"
    by simp

  have XSLEN: "\<forall>i \<in> set xs. i < length L"
    using XS_PROP by blast

  have MAPXS:
    "map (\<lambda>i. op_val ((L @ [op]) ! i)) xs =
     map (\<lambda>i. op_val (L ! i)) xs"
    using XSLEN by (induct xs) (auto simp add: nth_append)

  show ?thesis
    unfolding opsToQState_def
    using RANGE FX LAST_FALSE MAPXS
    by simp
qed

lemma HWQ_SqSpec_Strong_deq_step:
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
      and DEQ: "op_name op = deq"
  shows "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
proof -
  obtain j where
    J: "j < length L" and
    PENDJ: "pending_enq_idx L j" and
    VALJ: "op_val (L ! j) = op_val op" and
    BEFORE: "\<forall>k < j. \<not> pending_enq_idx L k"
    using HWQ_SqSpec_Strong_deq_pending_match[OF A DEQ] by blast

  have BEFORE':
    "\<And>k. k < j \<Longrightarrow> \<not> pending_enq_idx L k"
    using BEFORE by blast

  obtain xs where
    F: "filter (pending_enq_idx L) [0..<length L] = j # xs"
    using filter_upt_first_true[
      where P = "pending_enq_idx L"
        and j = j
        and n = "length L",
      OF J PENDJ BEFORE'] by blast

  have OLD:
    "opsToQState L = op_val op # map (\<lambda>i. op_val (L ! i)) xs"
  proof -
    have "opsToQState L =
          op_val (L ! j) # map (\<lambda>i. op_val (L ! i)) xs"
      unfolding opsToQState_def
      using F by simp
    then show ?thesis
      using VALJ by simp
  qed

  have NEW:
    "opsToQState (L @ [op]) = map (\<lambda>i. op_val (L ! i)) xs"
    using A DEQ J F VALJ
    by (rule opsToQState_snoc_deq_from_first_pending)

  have NBOT: "op_val op \<noteq> BOT"
    using A by (rule HWQ_SqSpec_Strong_last_not_BOT)

  show ?thesis
    using DEQ NBOT OLD NEW
    unfolding HWQ_QueueStep_def
    by simp
qed

theorem HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec_if_step:
  assumes STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec_Strong \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  shows "HWQ_SqSpec_Strong \<subseteq> HWQ_QueueSeqSpec"
proof -
  have INTERP: "HWQ_QueueSubSpec_ByStep HWQ_SqSpec_Strong"
  proof
    show "[] \<in> HWQ_SqSpec_Strong"
      by (rule HWQ_SqSpec_Strong_Nil)
  next
    fix L op
    assume A: "L @ [op] \<in> HWQ_SqSpec_Strong"
    then show "L \<in> HWQ_SqSpec_Strong"
      by (rule HWQ_SqSpec_Strong_prefix_snoc)
  next
    fix L op
    assume A: "L @ [op] \<in> HWQ_SqSpec_Strong"
    show "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
      using STEP[OF A] .
  qed

  show ?thesis
    using HWQ_QueueSubSpec_ByStep.sqSpec_subset_HWQ_QueueSeqSpec[OF INTERP] .
qed

lemma HWQ_SqSpec_Strong_step_if_enq_deq_step:
  assumes ENQ_STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec_Strong \<Longrightarrow>
              op_name op = enq \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  assumes DEQ_STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec_Strong \<Longrightarrow>
              op_name op = deq \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  assumes A: "L @ [op] \<in> HWQ_SqSpec_Strong"
  shows "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
proof (cases "op_name op")
  case enq
  then show ?thesis
    using ENQ_STEP[OF A] by blast
next
  case deq
  then show ?thesis
    using DEQ_STEP[OF A] by blast
qed

theorem HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec_if_enq_deq:
  assumes ENQ_STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec_Strong \<Longrightarrow>
              op_name op = enq \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  assumes DEQ_STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec_Strong \<Longrightarrow>
              op_name op = deq \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  shows "HWQ_SqSpec_Strong \<subseteq> HWQ_QueueSeqSpec"
proof (rule HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec_if_step)
  fix L op
  assume A: "L @ [op] \<in> HWQ_SqSpec_Strong"
  show "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
    by (rule HWQ_SqSpec_Strong_step_if_enq_deq_step[OF ENQ_STEP DEQ_STEP A])
qed


theorem HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec:
  "HWQ_SqSpec_Strong \<subseteq> HWQ_QueueSeqSpec"
proof (rule HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec_if_enq_deq)
  fix L op
  assume A: "L @ [op] \<in> HWQ_SqSpec_Strong"
  assume ENQ: "op_name op = enq"
  show "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
    using A ENQ by (rule HWQ_SqSpec_Strong_enq_step)
next
  fix L op
  assume A: "L @ [op] \<in> HWQ_SqSpec_Strong"
  assume DEQ: "op_name op = deq"
  show "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
    using A DEQ by (rule HWQ_SqSpec_Strong_deq_step)
qed

corollary system_invariant_lin_seq_in_HWQ_SqSpec_Strong_if_value_ok:
  assumes INV: "system_invariant s"
      and OK: "QueueValueOK (lin_seq s)"
  shows "lin_seq s \<in> HWQ_SqSpec_Strong"
  unfolding HWQ_SqSpec_Strong_def
  using INV OK system_invariant_lin_seq_in_HWQ_SqSpec by blast

corollary reachable_lin_seq_in_HWQ_SqSpec_Strong_if_value_ok:
  assumes REACH: "Reachable_Sys s"
      and OK: "QueueValueOK (lin_seq s)"
  shows "lin_seq s \<in> HWQ_SqSpec_Strong"
  unfolding HWQ_SqSpec_Strong_def
  using REACH OK reachable_lin_seq_in_HWQ_SqSpec by blast

corollary system_invariant_lin_seq_in_HWQ_QueueSeqSpec_if_value_ok:
  assumes INV: "system_invariant s"
      and OK: "QueueValueOK (lin_seq s)"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
proof -
  have STRONG: "lin_seq s \<in> HWQ_SqSpec_Strong"
    using INV OK
    by (rule system_invariant_lin_seq_in_HWQ_SqSpec_Strong_if_value_ok)

  show ?thesis
    using STRONG HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec
    by blast
qed

corollary reachable_lin_seq_in_HWQ_QueueSeqSpec_if_value_ok:
  assumes REACH: "Reachable_Sys s"
      and OK: "QueueValueOK (lin_seq s)"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
proof -
  have STRONG: "lin_seq s \<in> HWQ_SqSpec_Strong"
    using REACH OK
    by (rule reachable_lin_seq_in_HWQ_SqSpec_Strong_if_value_ok)

  show ?thesis
    using STRONG HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec
    by blast
qed

lemma QueueValueOK_lin_seq:
  assumes INV: "system_invariant s"
  shows "QueueValueOK (lin_seq s)"
  unfolding QueueValueOK_def
proof (intro allI impI)
  fix i
  assume I: "i < length (lin_seq s)"

  let ?op = "lin_seq s ! i"

  have IN: "?op \<in> set (lin_seq s)"
    using I by simp

  show "op_val ?op \<in> Val"
  proof (cases "op_name ?op")
    case enq
    then show ?thesis
      using LinSeq_Enq_Val_Valid[OF INV IN enq]
      by blast
  next
    case deq
    then show ?thesis
      using LinSeq_Deq_Val_Valid[OF INV IN deq]
      by blast
  qed
qed

corollary system_invariant_lin_seq_in_HWQ_QueueSeqSpec:
  assumes INV: "system_invariant s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
proof -
  have OK: "QueueValueOK (lin_seq s)"
    using INV by (rule QueueValueOK_lin_seq)

  show ?thesis
    using INV OK
    by (rule system_invariant_lin_seq_in_HWQ_QueueSeqSpec_if_value_ok)
qed

corollary reachable_lin_seq_in_HWQ_QueueSeqSpec:
  assumes REACH: "Reachable_Sys s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
proof -
  have INV: "system_invariant s"
    using REACH by (rule Reachable_Sys_in_SimRel_U)

  have OK: "QueueValueOK (lin_seq s)"
    using INV by (rule QueueValueOK_lin_seq)

  show ?thesis
    using REACH OK
    by (rule reachable_lin_seq_in_HWQ_QueueSeqSpec_if_value_ok)
qed

theorem system_invariant_lin_seq_satisfies_old_and_true_queue_spec:
  assumes INV: "system_invariant s"
  shows "Legal_Queue_Seq (lin_seq s) \<and>
         lin_seq s \<in> HWQ_QueueSeqSpec"
proof -
  have OLD: "Legal_Queue_Seq (lin_seq s)"
    using INV by (rule system_invariant_lin_seq_Legal_Queue_Seq)

  have TRUE_QUEUE: "lin_seq s \<in> HWQ_QueueSeqSpec"
    using INV by (rule system_invariant_lin_seq_in_HWQ_QueueSeqSpec)

  show ?thesis
    using OLD TRUE_QUEUE by blast
qed

theorem reachable_lin_seq_satisfies_old_and_true_queue_spec:
  assumes REACH: "Reachable_Sys s"
  shows "Legal_Queue_Seq (lin_seq s) \<and>
         lin_seq s \<in> HWQ_QueueSeqSpec"
proof -
  have INV: "system_invariant s"
    using REACH by (rule Reachable_Sys_in_SimRel_U)

  show ?thesis
    using INV by (rule system_invariant_lin_seq_satisfies_old_and_true_queue_spec)
qed

subsection \<open>Linearizability with respect to the queue sequential specification\<close>

definition IsLinearizable_HWQ_QueueSeqSpec :: "ActRec list \<Rightarrow> bool" where
  "IsLinearizable_HWQ_QueueSeqSpec H \<equiv>
     \<exists>L.
       Equivalent_History H L \<and>
       HB_consistent L H \<and>
       L \<in> HWQ_QueueSeqSpec"

lemma system_invariant_lin_seq_HB_consistent:
  assumes INV: "system_invariant s"
  shows "HB_consistent (lin_seq s) (his_seq s)"
proof -
  have I_lin3: "lI3_HB_Ret_Lin_Sync s"
    using INV unfolding system_invariant_def by blast

  show ?thesis
    using I_lin3
    unfolding lI3_HB_Ret_Lin_Sync_def
    by (simp add: HB_Act_def HB_consistent_def)
qed

lemma system_invariant_his_seq_true_queue_linearizable_if_equiv:
  assumes INV: "system_invariant s"
      and EQ: "Equivalent_History (his_seq s) (lin_seq s)"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
proof -
  have HB: "HB_consistent (lin_seq s) (his_seq s)"
    using INV by (rule system_invariant_lin_seq_HB_consistent)

  have QSPEC: "lin_seq s \<in> HWQ_QueueSeqSpec"
    using INV by (rule system_invariant_lin_seq_in_HWQ_QueueSeqSpec)

  show ?thesis
    unfolding IsLinearizable_HWQ_QueueSeqSpec_def
    using EQ HB QSPEC by blast
qed

corollary reachable_his_seq_true_queue_linearizable_if_equiv:
  assumes REACH: "Reachable_Sys s"
      and EQ: "Equivalent_History (his_seq s) (lin_seq s)"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
proof -
  have INV: "system_invariant s"
    using REACH by (rule Reachable_Sys_in_SimRel_U)

  show ?thesis
    using INV EQ
    by (rule system_invariant_his_seq_true_queue_linearizable_if_equiv)
qed

lemma system_invariant_his_lin_equiv:
  assumes INV: "system_invariant s"
  shows "Equivalent_History (his_seq s) (lin_seq s)"
proof -
  let ?H = "his_seq s"
  let ?S = "lin_seq s"

  have I_lin1: "lI1_Op_Sets_Equivalence s"
    using INV unfolding system_invariant_def by blast

  have I_lin3: "lI3_HB_Ret_Lin_Sync s"
    using INV unfolding system_invariant_def by blast

  have completeness:
    "\<forall>k < length ?H. act_cr (?H ! k) = ret \<longrightarrow>
      (\<exists>m < length ?S.
        op_name (?S ! m) = act_name (?H ! k) \<and>
        op_pid (?S ! m) = act_pid (?H ! k) \<and>
        op_ssn (?S ! m) = act_ssn (?H ! k) \<and>
        op_val (?S ! m) = act_val (?H ! k))"
  proof (intro allI impI)
    fix k
    assume hk_len: "k < length ?H"
    assume hk_ret: "act_cr (?H ! k) = ret"

    let ?e = "?H ! k"

    have CASE: "act_name ?e = enq \<or> act_name ?e = deq"
      using act_name_def mname.exhaust by metis

    show "\<exists>m < length ?S.
        op_name (?S ! m) = act_name ?e \<and>
        op_pid (?S ! m) = act_pid ?e \<and>
        op_ssn (?S ! m) = act_ssn ?e \<and>
        op_val (?S ! m) = act_val ?e"
    proof (cases "act_name ?e = enq")
      case True

      have RET: "Model.EnqRetInHis s (act_pid ?e) (act_val ?e) (act_ssn ?e)"
        using hk_len hk_ret True
        unfolding Model.EnqRetInHis_def Let_def
        by auto

      obtain m where
        M: "m < length ?S" and
        OP: "?S ! m = mk_op enq (act_val ?e) (act_pid ?e) (act_ssn ?e)"
        using RET I_lin3 unfolding lI3_HB_Ret_Lin_Sync_def by blast

      show ?thesis
        using M OP True
        unfolding op_name_def op_pid_def op_val_def op_ssn_def mk_op_def
        by force
    next
      case False

      have DEQ: "act_name ?e = deq"
        using CASE False by blast

      have RET: "Model.DeqRetInHis s (act_pid ?e) (act_val ?e) (act_ssn ?e)"
        using hk_len hk_ret DEQ
        unfolding Model.DeqRetInHis_def Let_def
        by auto

      obtain m where
        M: "m < length ?S" and
        OP: "?S ! m = mk_op deq (act_val ?e) (act_pid ?e) (act_ssn ?e)"
        using RET I_lin3 unfolding lI3_HB_Ret_Lin_Sync_def by blast

      show ?thesis
        using M OP DEQ
        unfolding op_name_def op_pid_def op_val_def op_ssn_def mk_op_def
        by force
    qed
  qed

  have soundness:
    "\<forall>m < length ?S.
      (\<exists>k < length ?H.
        act_cr (?H ! k) = call \<and>
        act_pid (?H ! k) = op_pid (?S ! m) \<and>
        act_ssn (?H ! k) = op_ssn (?S ! m) \<and>
        act_name (?H ! k) = op_name (?S ! m) \<and>
        act_val (?H ! k) =
          (if op_name (?S ! m) = deq then BOT else op_val (?S ! m)))"
  proof (intro allI impI)
    fix m
    assume m_len: "m < length ?S"

    let ?op = "?S ! m"

    have OPIN: "?op \<in> OPLin s"
      unfolding OPLin_def
      using m_len by auto

    have CASES:
      "?op \<in> OP_A_enq s \<or> ?op \<in> OP_B_enq s \<or> ?op \<in> OP_A_deq s"
      using I_lin1 OPIN
      unfolding lI1_Op_Sets_Equivalence_def
      by blast

    show "\<exists>k < length ?H.
        act_cr (?H ! k) = call \<and>
        act_pid (?H ! k) = op_pid ?op \<and>
        act_ssn (?H ! k) = op_ssn ?op \<and>
        act_name (?H ! k) = op_name ?op \<and>
        act_val (?H ! k) =
          (if op_name ?op = deq then BOT else op_val ?op)"
    proof -
      have CASE_A_ENQ:
        "?op \<in> OP_A_enq s \<Longrightarrow>
         \<exists>k < length ?H.
          act_cr (?H ! k) = call \<and>
          act_pid (?H ! k) = op_pid ?op \<and>
          act_ssn (?H ! k) = op_ssn ?op \<and>
          act_name (?H ! k) = op_name ?op \<and>
          act_val (?H ! k) =
            (if op_name ?op = deq then BOT else op_val ?op)"
      proof -
        assume AENQ: "?op \<in> OP_A_enq s"

        obtain p a sn where
          OP: "?op = mk_op enq a p sn" and
          CALL: "Model.EnqCallInHis s p a sn"
          using AENQ unfolding OP_A_enq_def by blast

        show ?thesis
          using OP CALL
          unfolding Model.EnqCallInHis_def mk_op_def
                    op_name_def op_pid_def op_val_def op_ssn_def
          by (force simp: in_set_conv_nth)
      qed

      have CASE_B_ENQ:
        "?op \<in> OP_B_enq s \<Longrightarrow>
         \<exists>k < length ?H.
          act_cr (?H ! k) = call \<and>
          act_pid (?H ! k) = op_pid ?op \<and>
          act_ssn (?H ! k) = op_ssn ?op \<and>
          act_name (?H ! k) = op_name ?op \<and>
          act_val (?H ! k) =
            (if op_name ?op = deq then BOT else op_val ?op)"
      proof -
        assume BENQ: "?op \<in> OP_B_enq s"

        obtain p a sn where
          OP: "?op = mk_op enq a p sn" and
          CALL: "Model.EnqCallInHis s p a sn"
          using BENQ unfolding OP_B_enq_def by blast

        show ?thesis
          using OP CALL
          unfolding Model.EnqCallInHis_def mk_op_def
                    op_name_def op_pid_def op_val_def op_ssn_def
          by (force simp: in_set_conv_nth)
      qed

      have CASE_DEQ:
        "?op \<in> OP_A_deq s \<Longrightarrow>
         \<exists>k < length ?H.
          act_cr (?H ! k) = call \<and>
          act_pid (?H ! k) = op_pid ?op \<and>
          act_ssn (?H ! k) = op_ssn ?op \<and>
          act_name (?H ! k) = op_name ?op \<and>
          act_val (?H ! k) =
            (if op_name ?op = deq then BOT else op_val ?op)"
      proof -
        assume ADEQ: "?op \<in> OP_A_deq s"

        have NAME: "op_name ?op = deq"
          using ADEQ unfolding OP_A_deq_def by auto

        have CALL: "Model.DeqCallInHis s (op_pid ?op) (op_ssn ?op)"
          using ADEQ unfolding OP_A_deq_def by auto

        show ?thesis
          using NAME CALL
          unfolding Model.DeqCallInHis_def Let_def
          by (force simp: in_set_conv_nth)
      qed

      show ?thesis
        using CASES CASE_A_ENQ CASE_B_ENQ CASE_DEQ by blast
    qed
  qed

  show ?thesis
    unfolding Equivalent_History_def
    using completeness soundness by blast
qed

theorem system_invariant_his_seq_true_queue_linearizable:
  assumes INV: "system_invariant s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
proof -
  have EQ: "Equivalent_History (his_seq s) (lin_seq s)"
    using INV by (rule system_invariant_his_lin_equiv)

  show ?thesis
    using INV EQ
    by (rule system_invariant_his_seq_true_queue_linearizable_if_equiv)
qed

corollary reachable_his_seq_true_queue_linearizable:
  assumes REACH: "Reachable_Sys s"
  shows "IsLinearizable_HWQ_QueueSeqSpec (his_seq s)"
proof -
  have INV: "system_invariant s"
    using REACH by (rule Reachable_Sys_in_SimRel_U)

  show ?thesis
    using INV by (rule system_invariant_his_seq_true_queue_linearizable)
qed



theorem HWQ_SqSpec_subset_HWQ_QueueSeqSpec_if_HWQ_SqSpec_step:
  assumes STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  shows "HWQ_SqSpec \<subseteq> HWQ_QueueSeqSpec"
proof -
  have INTERP: "HWQ_QueueSubSpec_ByStep HWQ_SqSpec"
  proof
    show "[] \<in> HWQ_SqSpec"
      by (rule HWQ_SqSpec_Nil)
  next
    fix L op
    assume A: "L @ [op] \<in> HWQ_SqSpec"
    then show "L \<in> HWQ_SqSpec"
      by (rule HWQ_SqSpec_prefix_snoc)
  next
    fix L op
    assume A: "L @ [op] \<in> HWQ_SqSpec"
    show "HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
      using STEP[OF A] .
  qed

  show ?thesis
    using HWQ_SqSpec_subset_HWQ_QueueSeqSpec_if_step[OF INTERP] .
qed

corollary system_invariant_lin_seq_in_HWQ_QueueSeqSpec_if_HWQ_SqSpec_step:
  assumes STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  assumes INV: "system_invariant s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
  using INV system_invariant_lin_seq_in_HWQ_SqSpec
        HWQ_SqSpec_subset_HWQ_QueueSeqSpec_if_HWQ_SqSpec_step[OF STEP]
  by blast

corollary reachable_lin_seq_in_HWQ_QueueSeqSpec_if_HWQ_SqSpec_step:
  assumes STEP:
    "\<And>L op. L @ [op] \<in> HWQ_SqSpec \<Longrightarrow>
              HWQ_QueueStep (opsToQState L) op (opsToQState (L @ [op]))"
  assumes REACH: "Reachable_Sys s"
  shows "lin_seq s \<in> HWQ_QueueSeqSpec"
  using REACH reachable_lin_seq_in_HWQ_SqSpec
        HWQ_SqSpec_subset_HWQ_QueueSeqSpec_if_HWQ_SqSpec_step[OF STEP]
  by blast


subsection \<open>Paper-facing aliases for the queue specification\<close>

lemmas standard_queue_spec_empty_history = HWQ_QueueSeqSpec_Nil
lemmas auxiliary_queue_invariants_subset_standard_queue_spec =
  HWQ_SqSpec_subset_HWQ_QueueSeqSpec_if_step
lemmas HWQ_auxiliary_queue_spec_subset_standard_queue_spec =
  HWQ_SqSpec_subset_HWQ_QueueSeqSpec_if_step
lemmas HWQ_strong_auxiliary_queue_spec_subset_standard_queue_spec =
  HWQ_SqSpec_Strong_subset_HWQ_QueueSeqSpec_if_step
lemmas HWQ_reachable_linearization_sequence_satisfies_auxiliary_queue_spec =
  reachable_lin_seq_in_HWQ_SqSpec
lemmas HWQ_reachable_linearization_sequence_satisfies_standard_queue_spec =
  reachable_lin_seq_in_HWQ_QueueSeqSpec
lemmas HWQ_recorded_history_linearizable_against_standard_queue_spec =
  reachable_his_seq_true_queue_linearizable

end
