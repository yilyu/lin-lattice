theory EnqLib
 imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    DistLib
    Termination
    DeqLib
begin


lemma EnqCallInHis_his_eq:
  assumes HIS: "his_seq s' = his_seq s"
  shows "EnqCallInHis s' p a sn \<longleftrightarrow> EnqCallInHis s p a sn"
  using HIS unfolding EnqCallInHis_def by simp

lemma EnqRetInHis_his_eq:
  assumes HIS: "his_seq s' = his_seq s"
  shows "EnqRetInHis s' p a sn \<longleftrightarrow> EnqRetInHis s p a sn"
  using HIS unfolding EnqRetInHis_def by simp

lemma DeqCallInHis_his_eq:
  assumes HIS: "his_seq s' = his_seq s"
  shows "DeqCallInHis s' p sn \<longleftrightarrow> DeqCallInHis s p sn"
  using HIS unfolding DeqCallInHis_def by simp

lemma DeqRetInHis_his_eq:
  assumes HIS: "his_seq s' = his_seq s"
  shows "DeqRetInHis s' p a sn \<longleftrightarrow> DeqRetInHis s p a sn"
  using HIS unfolding DeqRetInHis_def by simp

lemma HasPendingEnq_his_eq:
  assumes HIS: "his_seq s' = his_seq s"
  assumes SVAR: "s_var s' p = s_var s p"
  shows "HasPendingEnq s' p a \<longleftrightarrow> HasPendingEnq s p a"
  using HIS SVAR unfolding HasPendingEnq_def
  by (metis EnqCallInHis_his_eq)

lemma HasPendingDeq_his_eq:
  assumes HIS: "his_seq s' = his_seq s"
  assumes SVAR: "s_var s' p = s_var s p"
  shows "HasPendingDeq s' p \<longleftrightarrow> HasPendingDeq s p"
  using HIS SVAR unfolding HasPendingDeq_def
  by (metis DeqCallInHis_his_eq)

lemma hI7_His_WF_his_eq:
  assumes HIS: "his_seq s' = his_seq s"
  shows "hI7_His_WF s' \<longleftrightarrow> hI7_His_WF s"
  using HIS unfolding hI7_His_WF_def by simp

(* Happens-before reasoning. Related symbols: HB. *)
lemma HasPendingEnq_implies_EnqCallInHis:
  assumes PEND: "HasPendingEnq s p a"
  shows "EnqCallInHis s p a (s_var s p)"
  using PEND unfolding HasPendingEnq_def Let_def by blast

lemma EnqCallInHis_unique_pid:
  assumes UNIQ: "hI8_Val_Unique s"
  assumes CALL1: "EnqCallInHis s p1 a sn1"
  assumes CALL2: "EnqCallInHis s p2 a sn2"
  shows "p1 = p2"
proof -
  from CALL1 obtain i where
    i_lt: "i < length (his_seq s)"
    and i_props: "act_pid (his_seq s ! i) = p1" "act_name (his_seq s ! i) = enq"
                 "act_cr (his_seq s ! i) = call" "act_val (his_seq s ! i) = a"
    unfolding EnqCallInHis_def Let_def
    by (metis in_set_conv_nth)

  from CALL2 obtain j where
    j_lt: "j < length (his_seq s)"
    and j_props: "act_pid (his_seq s ! j) = p2" "act_name (his_seq s ! j) = enq"
                 "act_cr (his_seq s ! j) = call" "act_val (his_seq s ! j) = a"
    unfolding EnqCallInHis_def Let_def
    by (metis in_set_conv_nth)

  have "i = j"
    using UNIQ i_lt j_lt i_props j_props unfolding hI8_Val_Unique_def by blast

  then show ?thesis
    using i_props j_props by simp
qed

lemma EnqRetInHis_implies_EnqCallInHis:
  assumes WF: "hI7_His_WF s"
  assumes RET: "EnqRetInHis s p a sn"
  shows "EnqCallInHis s p a sn"
proof -
  (* Original source location. *)
  from RET obtain k where
    k_lt: "k < length (his_seq s)"
    and k_props: "act_pid (his_seq s ! k) = p" "act_name (his_seq s ! k) = enq"
                 "act_cr (his_seq s ! k) = ret" "act_val (his_seq s ! k) = a"
                 "act_ssn (his_seq s ! k) = sn"
    unfolding EnqRetInHis_def Let_def
    by (metis in_set_conv_nth)

  (* Use the relevant invariant, lemma, or hypothesis. Related symbols: WF. *)
  have "\<exists>j < k. act_pid (his_seq s ! j) = p \<and> act_name (his_seq s ! j) = enq \<and>
                act_cr (his_seq s ! j) = call \<and> act_val (his_seq s ! j) = a \<and>
                act_ssn (his_seq s ! j) = sn"
    using WF k_lt k_props unfolding hI7_His_WF_def Let_def by force

  (* History well-formedness and call/return reasoning. *)
  thus ?thesis
    using k_lt unfolding EnqCallInHis_def Let_def by force
qed

lemma no_enq_ret_for_pending_value:
  assumes WF: "hI7_His_WF s"
  assumes UNIQ: "hI8_Val_Unique s"
  assumes PEND: "HasPendingEnq s p a"
  shows "\<forall>q sn. \<not> EnqRetInHis s q a sn"
proof (intro allI notI)
  fix q sn
  assume RET: "EnqRetInHis s q a sn"

  (* Step 1 of the proof. *)
  have call_q: "EnqCallInHis s q a sn"
    using EnqRetInHis_implies_EnqCallInHis[OF WF RET] .

  (* Step 2 of the proof. *)
  have call_p: "EnqCallInHis s p a (s_var s p)"
    using HasPendingEnq_implies_EnqCallInHis[OF PEND] .

  (* Step 3 of the proof. *)
  have eq: "q = p \<and> sn = s_var s p"
    using UNIQ call_q call_p unfolding hI8_Val_Unique_def EnqCallInHis_def Let_def
    by (metis in_set_conv_nth)

  (* Pending-state definitions. *)
  show False
    using PEND RET eq unfolding HasPendingEnq_def EnqRetInHis_def Let_def by force
qed

(* Happens-before reasoning. Related symbols: HB. *)
lemma HB_Act_enq_first_implies_EnqRetInHis:
  assumes HB1: "HB_Act s (mk_op enq a p sn) act2"
  shows "EnqRetInHis s p a sn"
proof -
  (* Happens-before reasoning. Related symbols: HB_Act, mk_op. *)
  from HB1 obtain k1 where
    "k1 < length (his_seq s)"
    "act_name (his_seq s ! k1) = enq"
    "act_pid (his_seq s ! k1) = p"
    "act_val (his_seq s ! k1) = a"
    "act_ssn (his_seq s ! k1) = sn"
    "act_cr (his_seq s ! k1) = ret"
    unfolding HB_Act_def HB_def match_ret_def Let_def mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
    by force

  (* History well-formedness and call/return reasoning. *)
  thus ?thesis
    unfolding EnqRetInHis_def Let_def by force
qed

(* Happens-before reasoning. Related symbols: HB_EnqRetCall. *)
lemma HB_EnqRetCall_implies_EnqRetInHis:
  assumes HB1: "HB_EnqRetCall s a b"
  shows "\<exists>p sn. EnqRetInHis s p a sn"
proof -
  (* Happens-before reasoning. Related symbols: HB, p1, p2, sn1, sn2. *)
  from HB1 obtain p1 p2 sn1 sn2 where
    hb_act: "HB_Act s (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    unfolding HB_EnqRetCall_def by blast

  have "EnqRetInHis s p1 a sn1"
    using HB_Act_enq_first_implies_EnqRetInHis[OF hb_act] .

  then show ?thesis by blast
qed

(* Happens-before reasoning. Related symbols: HB_EnqRetCall. *)
lemma no_enq_ret_implies_no_HB_EnqRetCall:
  assumes NORET: "\<forall>q sn. \<not> EnqRetInHis s q a sn"
  shows "\<not> HB_EnqRetCall s a b"
proof
  assume HB1: "HB_EnqRetCall s a b"
  then obtain p sn where "EnqRetInHis s p a sn"
    using HB_EnqRetCall_implies_EnqRetInHis by blast
  then show False
    using NORET by blast
qed

lemma lin_seq_no_value_if_not_in_SetA_SetB:
  assumes LIN1: "lI1_Op_Sets_Equivalence s"
  assumes NOTA: "a \<notin> SetA s"
  assumes NOTB: "a \<notin> SetB s"
  assumes K: "k < length (lin_seq s)"
  shows "op_val (lin_seq s ! k) \<noteq> a"
proof
  assume EQ: "op_val (lin_seq s ! k) = a"

  have "lin_seq s ! k \<in> OPLin s"
    using K unfolding OPLin_def by auto

  hence "lin_seq s ! k \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using LIN1 unfolding lI1_Op_Sets_Equivalence_def by simp

  (* Proof-automation note. Related symbols: OP, SetA, SetB. *)
  thus False
    using EQ NOTA NOTB
    unfolding OP_A_enq_def OP_A_deq_def OP_B_enq_def
    by (auto simp: op_val_def mk_op_def)
qed

lemma find_indices_append_enq_other:
  assumes X_NE: "x \<noteq> v"
  shows
    "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x) (L @ [mk_op enq v p sn]) =
     find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x) L"
proof -
  let ?P = "\<lambda>a. op_name a = enq \<and> op_val a = x"
  have old_part_eq:
    "filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [0..<length L] =
     filter (\<lambda>i. ?P (L ! i)) [0..<length L]"
  proof (rule filter_cong[OF refl])
    fix i
    assume "i \<in> set [0..<length L]"
    then have i_lt: "i < length L" by simp
    show "(?P ((L @ [mk_op enq v p sn]) ! i)) = (?P (L ! i))"
      using i_lt by (simp add: nth_append)
  qed
  have last_part_empty:
    "filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [length L] = []"
    using X_NE by (simp add: mk_op_def op_name_def op_val_def)
  have range_split:
    "[0..<length (L @ [mk_op enq v p sn])] = [0..<length L] @ [length L]"
    by simp
  have
    "find_indices ?P (L @ [mk_op enq v p sn]) =
     filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) ([0..<length L] @ [length L])"
    unfolding find_indices_def using range_split by simp
  also have
    "... =
     filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [0..<length L] @
     filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [length L]"
    by simp
  also have
    "... = filter (\<lambda>i. ?P (L ! i)) [0..<length L] @ []"
    using old_part_eq last_part_empty by simp
  also have
    "... = find_indices ?P L"
    unfolding find_indices_def by simp
  finally show ?thesis .
qed

lemma find_unique_index_append_enq_other:
  assumes X_NE: "x \<noteq> v"
  shows
    "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) (L @ [mk_op enq v p sn]) =
     find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L"
  using find_indices_append_enq_other[OF X_NE, of L p]
  unfolding find_unique_index_def by simp

lemma find_indices_append_deq_other:
  shows
    "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x) (L @ [mk_op enq v p sn]) =
     find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x) L"
proof -
  let ?P = "\<lambda>a. op_name a = deq \<and> op_val a = x"
  have old_part_eq:
    "filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [0..<length L] =
     filter (\<lambda>i. ?P (L ! i)) [0..<length L]"
  proof (rule filter_cong[OF refl])
    fix i
    assume "i \<in> set [0..<length L]"
    then have i_lt: "i < length L" by simp
    show "(?P ((L @ [mk_op enq v p sn]) ! i)) = (?P (L ! i))"
      using i_lt by (simp add: nth_append)
  qed
  have last_part_empty:
    "filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [length L] = []"
    by (simp add: mk_op_def op_name_def)
  have range_split:
    "[0..<length (L @ [mk_op enq v p sn])] = [0..<length L] @ [length L]"
    by simp
  have
    "find_indices ?P (L @ [mk_op enq v p sn]) =
     filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) ([0..<length L] @ [length L])"
    unfolding find_indices_def using range_split by simp
  also have
    "... =
     filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [0..<length L] @
     filter (\<lambda>i. ?P ((L @ [mk_op enq v p sn]) ! i)) [length L]"
    by simp
  also have
    "... = filter (\<lambda>i. ?P (L ! i)) [0..<length L] @ []"
    using old_part_eq last_part_empty by simp
  also have
    "... = find_indices ?P L"
    unfolding find_indices_def by simp
  finally show ?thesis .
qed

lemma find_unique_index_append_deq_other:
  shows
    "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) (L @ [mk_op enq v p sn]) =
     find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) L"
  using find_indices_append_deq_other[of x L v p]
  unfolding find_unique_index_def by simp

lemma in_SA_append_enq_other:
  assumes X_NE: "x \<noteq> v"
  shows "in_SA x (L @ [mk_op enq v p sn]) \<longleftrightarrow> in_SA x L"
proof -
  have enq_eq:
    "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) (L @ [mk_op enq v p sn]) =
     find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L"
    using find_unique_index_append_enq_other[OF X_NE, of L p] by simp
  have deq_eq:
    "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) (L @ [mk_op enq v p sn]) =
     find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) L"
    using find_unique_index_append_deq_other[of x L v p] by simp
  have lhs_rewrite:
    "in_SA x (L @ [mk_op enq v p sn]) =
     (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L of
        None \<Rightarrow> False
      | Some enq_idx \<Rightarrow>
          (case find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) L of
             None \<Rightarrow> False
           | Some deq_idx \<Rightarrow> True))"
  proof -
    have
      "in_SA x (L @ [mk_op enq v p sn]) =
       (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) (L @ [mk_op enq v p sn]) of
          None \<Rightarrow> False
        | Some enq_idx \<Rightarrow>
            (case find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) (L @ [mk_op enq v p sn]) of
               None \<Rightarrow> False
             | Some deq_idx \<Rightarrow> True))"
      unfolding in_SA_def by simp
    also have
      "... =
       (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L of
          None \<Rightarrow> False
        | Some enq_idx \<Rightarrow>
            (case find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x) L of
               None \<Rightarrow> False
             | Some deq_idx \<Rightarrow> True))"
    proof (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L")
      case None
      then show ?thesis using enq_eq by simp
    next
      case (Some enq_idx)
      then show ?thesis using enq_eq deq_eq by simp
    qed
    finally show ?thesis .
  qed
  show ?thesis
    using lhs_rewrite unfolding in_SA_def by simp
qed

lemma in_SA_append_enq_fresh_false:
  assumes FRESH: "\<forall>i < length L. op_val (L ! i) \<noteq> v"
  shows "\<not> in_SA v (L @ [mk_op enq v p sn])"
proof -
  have no_deq_v:
    "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) (L @ [mk_op enq v p sn]) = None"
  proof -
    have no_old: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) L = None"
      unfolding find_unique_index_def find_indices_def using FRESH by auto
    show ?thesis
      using find_unique_index_append_deq_other[of v L v p] no_old by simp
  qed
  show ?thesis
  proof
    assume in_sa: "in_SA v (L @ [mk_op enq v p sn])"
    show False
      using in_sa no_deq_v unfolding in_SA_def
      by (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) (L @ [mk_op enq v p sn])"; simp)
  qed
qed

lemma find_last_SA_append_enq_fresh:
  assumes FRESH: "\<forall>i < length L. op_val (L ! i) \<noteq> v"
  shows "find_last_SA (L @ [mk_op enq v p sn]) = find_last_SA L"
proof -
  let ?L' = "L @ [mk_op enq v p sn]"
  let ?P' = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) ?L'"
  let ?P = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L"

  have prefix_eq:
    "find_indices ?P' ?L' = find_indices ?P L"
  proof -
    have step:
      "filter (\<lambda>i. ?P' (?L' ! i)) [0..<length ?L'] =
       filter (\<lambda>i. ?P (L ! i)) [0..<length L]"
    proof -
      (* Proof note. *)
      have not_in_sa_v: "\<not> in_SA v ?L'"
        using in_SA_append_enq_fresh_false[OF FRESH] by simp

      (* Key proof fix. *)
      have last_false: "\<not> ?P' (mk_op enq v p sn)"
      proof
        assume p_last: "?P' (mk_op enq v p sn)"
        then have "in_SA (op_val (mk_op enq v p sn)) ?L'" by simp
        then have "in_SA v ?L'" by (simp add: op_val_def mk_op_def)
        then show False using not_in_sa_v by contradiction
      qed

      have old_eq:
        "filter (\<lambda>i. ?P' (?L' ! i)) [0..<length L] =
         filter (\<lambda>i. ?P (L ! i)) [0..<length L]"
      proof (rule filter_cong)
        show "[0..<length L] = [0..<length L]" by simp
      next
        fix i
        assume i_in: "i \<in> set [0..<length L]"
        then have i_lt: "i < length L" by simp
        have val_ne: "op_val (L ! i) \<noteq> v"
          using FRESH i_lt by simp
        (* Proof note. *)
        show "?P' (?L' ! i) = ?P (L ! i)"
          using i_lt val_ne in_SA_append_enq_other[OF val_ne] by (simp add: nth_append)
      qed

      have "filter (\<lambda>i. ?P' (?L' ! i)) [0..<length ?L'] =
            filter (\<lambda>i. ?P' (?L' ! i)) ([0..<length L] @ [length L])" by simp
      also have "... = filter (\<lambda>i. ?P' (?L' ! i)) [0..<length L]" using last_false by simp
      also have "... = filter (\<lambda>i. ?P (L ! i)) [0..<length L]" using old_eq by simp
      finally show ?thesis .
    qed
    show ?thesis
      unfolding find_indices_def using step by simp
  qed
  show ?thesis
    unfolding find_last_SA_def using prefix_eq by simp
qed

lemma find_last_SA_lt_length:
  shows "find_last_SA L < int (length L)"
proof (cases "find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L = []")
  case True
  then show ?thesis unfolding find_last_SA_def by simp
next
  case False
  let ?idxs = "find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L"
  have last_in: "last ?idxs \<in> set ?idxs" using False by simp
  have all_lt: "\<forall>i \<in> set ?idxs. i < length L" unfolding find_indices_def by auto
  then have "last ?idxs < length L" using last_in by blast
  then show ?thesis using False unfolding find_last_SA_def by simp
qed


(* ========================================================================= *)
(* Set, cardinality, and uniqueness reasoning. *)
(* Proof note. Related symbols: E1, E2, E3, v_var. *)
(* ========================================================================= *)
lemma enq_v_var_unique:
  assumes INV: "system_invariant s"
      and pc_p: "program_counter s p \<in> {''E1'', ''E2'', ''E3''}"
      and pc_q: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      and neq: "p \<noteq> q"
  shows "v_var s p \<noteq> v_var s q"
proof -
  (* Extract the required witnesses and facts. *)
  from INV have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and hI8_Val_Unique_s: "hI8_Val_Unique s"
    unfolding system_invariant_def by auto

  (* Enqueue-side reasoning. Related symbols: hI1_E_Phase_Pending_Enq. *)
  from hI1_E_Phase_Pending_Enq_s pc_p have pend_p: "HasPendingEnq s p (v_var s p)" unfolding hI1_E_Phase_Pending_Enq_def by auto
  from hI1_E_Phase_Pending_Enq_s pc_q have pend_q: "HasPendingEnq s q (v_var s q)" unfolding hI1_E_Phase_Pending_Enq_def by auto

  (* Extract the required witnesses and facts. *)
  from pend_p obtain ep where ep_in: "ep \<in> set (his_seq s)"
    and ep_pid: "act_pid ep = p" and ep_val: "act_val ep = v_var s p"
    and ep_op: "act_name ep = enq" and ep_cr: "act_cr ep = call"
    unfolding HasPendingEnq_def EnqCallInHis_def Let_def by force

  from pend_q obtain eq where eq_in: "eq \<in> set (his_seq s)"
    and eq_pid: "act_pid eq = q" and eq_val: "act_val eq = v_var s q"
    and eq_op: "act_name eq = enq" and eq_cr: "act_cr eq = call"
    unfolding HasPendingEnq_def EnqCallInHis_def Let_def by force

  (* Contradiction argument. *)
  have ep_neq_eq: "ep \<noteq> eq" using neq ep_pid eq_pid by auto

  (* Use the relevant invariant, lemma, or hypothesis. Related symbols: hI8_Val_Unique. *)
  from hI8_Val_Unique_s ep_in eq_in ep_neq_eq ep_op eq_op ep_cr eq_cr
  have "act_val ep \<noteq> act_val eq"
    unfolding hI8_Val_Unique_def by (metis in_set_conv_nth)

  thus ?thesis using ep_val eq_val by simp
qed

lemma Q_arr_Call_Consistency_E2:
  assumes INV: "system_invariant s" and STEP: "Sys_E2 p s s'"
      and VAL: "a \<in> Val"
      and EX_K: "\<exists>k. Q_arr s' k = a"
  shows "\<exists>q sn. EnqCallInHis s' q a sn"
proof (goal_cases)
  case 1
  (* Step 1: extract the required facts. Related symbols: system_invariant_def. *)
  from INV have h_consistent: "hI10_Enq_Call_Existence s" unfolding system_invariant_def by auto
  from INV have ai13: "hI1_E_Phase_Pending_Enq s" unfolding system_invariant_def by auto

  have step_phys: "his_seq s' = his_seq s" "program_counter s p = ''E2'' "
    using STEP unfolding Sys_E2_def C_E2_def program_counter_def his_seq_def by auto

  from EX_K obtain k where k_def: "Q_arr s' k = a" by auto

  (* Step 2: split on the relevant cases. *)
  show ?case
  proof (cases "k = i_var s p")
    case True
    (* Case A. *)
    hence "a = v_var s p"
      using STEP k_def unfolding Sys_E2_def C_E2_def Q_arr_def v_var_def i_var_def Let_def by auto
    with ai13 step_phys(2) have "\<exists>sn. EnqCallInHis s p a sn"
      unfolding hI1_E_Phase_Pending_Enq_def HasPendingEnq_def Let_def by blast
    thus ?thesis using step_phys(1) unfolding EnqCallInHis_def by auto

  next
    case False
    (* Case B. *)
    hence old_a: "a = Q_arr s k"
      using STEP k_def unfolding Sys_E2_def C_E2_def Q_arr_def i_var_def Let_def by auto

    from INV have sync: "sI8_Q_Qback_Sync s"
      unfolding system_invariant_def by auto
    from VAL have not_bot: "a \<noteq> BOT"
      unfolding Val_def BOT_def by auto
    from sync have sync_k: "Q_arr s k = Qback_arr s k \<or> Q_arr s k = BOT"
      unfolding sI8_Q_Qback_Sync_def by blast
    from sync_k old_a not_bot have qback_a: "Qback_arr s k = a"
      by auto
    from h_consistent VAL qback_a have "\<exists>q sn. EnqCallInHis s q a sn"
      unfolding hI10_Enq_Call_Existence_def by blast

    (* History well-formedness and call/return reasoning. *)
    thus ?thesis using step_phys(1) unfolding EnqCallInHis_def by auto
  qed
qed

(* ========================================================================= *)
(* History well-formedness and call/return reasoning. *)
(* Enqueue-side reasoning. Related symbols: E1, E2, E3. *)
(* History well-formedness and call/return reasoning. Related symbols: v_var. *)
(* ========================================================================= *)
lemma pending_enq_val_has_no_ret:
  assumes INV: "system_invariant s"
      and PC_p: "program_counter s p \<in> {''E1'', ''E2'', ''E3''}"
  shows "\<not> (\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and>
                                         act_val (his_seq s ! k_ret) = v_var s p \<and>
                                         act_cr (his_seq s ! k_ret) = ret)"
proof
  assume "\<exists>k_ret < length (his_seq s). act_name (his_seq s ! k_ret) = enq \<and>
                                       act_val (his_seq s ! k_ret) = v_var s p \<and>
                                       act_cr (his_seq s ! k_ret) = ret"
  then obtain k_ret where k_ret_len: "k_ret < length (his_seq s)"
                      and k_ret_op: "act_name (his_seq s ! k_ret) = enq"
                      and k_ret_val: "act_val (his_seq s ! k_ret) = v_var s p"
                      and k_ret_cr: "act_cr (his_seq s ! k_ret) = ret" by blast

  from INV have hI7_His_WF_s: "hI7_His_WF s" unfolding system_invariant_def by blast
  have "\<exists>k_call < k_ret. act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret) \<and>
                         act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret) \<and>
                         act_name (his_seq s ! k_call) = enq \<and>
                         act_cr (his_seq s ! k_call) = call \<and>
                         act_val (his_seq s ! k_call) = v_var s p"
    using hI7_His_WF_s k_ret_len k_ret_op k_ret_val k_ret_cr unfolding hI7_His_WF_def Let_def by force
  then obtain k_call where k_call_len: "k_call < length (his_seq s)"
                       and k_call_op: "act_name (his_seq s ! k_call) = enq"
                       and k_call_val: "act_val (his_seq s ! k_call) = v_var s p"
                       and k_call_cr: "act_cr (his_seq s ! k_call) = call"
                       and k_call_pid: "act_pid (his_seq s ! k_call) = act_pid (his_seq s ! k_ret)"
                       and k_call_ssn: "act_ssn (his_seq s ! k_call) = act_ssn (his_seq s ! k_ret)"
    using k_ret_len dual_order.strict_trans by auto

  from INV have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" unfolding system_invariant_def by blast
  have pending_p: "HasPendingEnq s p (v_var s p)" using hI1_E_Phase_Pending_Enq_s PC_p unfolding hI1_E_Phase_Pending_Enq_def by blast

  have "\<exists>j_call < length (his_seq s). act_name (his_seq s ! j_call) = enq \<and>
                                      act_val (his_seq s ! j_call) = v_var s p \<and>
                                      act_cr (his_seq s ! j_call) = call \<and>
                                      act_pid (his_seq s ! j_call) = p \<and>
                                      act_ssn (his_seq s ! j_call) = s_var s p"
    using pending_p unfolding HasPendingEnq_def EnqCallInHis_def Let_def match_call_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
    by (metis in_set_conv_nth)
  then obtain j_call where j_call_len: "j_call < length (his_seq s)"
                       and j_call_op: "act_name (his_seq s ! j_call) = enq"
                       and j_call_val: "act_val (his_seq s ! j_call) = v_var s p"
                       and j_call_cr: "act_cr (his_seq s ! j_call) = call"
                       and j_call_pid: "act_pid (his_seq s ! j_call) = p"
                       and j_call_ssn: "act_ssn (his_seq s ! j_call) = s_var s p" by blast

  from INV have hI8_Val_Unique_s: "hI8_Val_Unique s" unfolding system_invariant_def by blast
  have "k_call = j_call"
    using hI8_Val_Unique_s k_call_len j_call_len k_call_op j_call_op k_call_cr j_call_cr k_call_val j_call_val
    unfolding hI8_Val_Unique_def
    by auto

  hence "act_pid (his_seq s ! k_ret) = p" and "act_ssn (his_seq s ! k_ret) = s_var s p"
    using k_call_pid j_call_pid k_call_ssn j_call_ssn by simp_all

  moreover have "\<not> (\<exists>k < length (his_seq s). act_pid (his_seq s ! k) = p \<and> act_ssn (his_seq s ! k) = s_var s p \<and> act_cr (his_seq s ! k) = ret)"
    using pending_p unfolding HasPendingEnq_def EnqRetInHis_def Let_def match_ret_def mk_op_def op_name_def op_val_def op_pid_def op_ssn_def
    by force

  ultimately show False using k_ret_len k_ret_cr by blast
qed

(* ========================================================================= *)
(* HB stability argument. Related symbols: HB, E3. *)
(* ========================================================================= *)

lemma HB_deq_stable_enq_append:
  fixes H :: "ActRec list" and a b :: nat
  assumes h_eq: "H' = H @ [mk_act enq v p sn ret]"
  shows "(\<exists>p1 sn1 p2 sn2. HB H' (mk_op deq a p1 sn1) (mk_op deq b p2 sn2)) \<longleftrightarrow>
         (\<exists>p1 sn1 p2 sn2. HB H (mk_op deq a p1 sn1) (mk_op deq b p2 sn2))"
proof
  (* Direction 1 of the proof. Related symbols: \<longrightarrow>. *)
  assume "\<exists>p1 sn1 p2 sn2. HB H' (mk_op deq a p1 sn1) (mk_op deq b p2 sn2)"
  then obtain p1 sn1 p2 sn2 k1 k2 where k:
    "k1 < k2" "k1 < length H'" "k2 < length H'"
    "act_name (H' ! k1) = deq" "act_pid (H' ! k1) = p1" "act_val (H' ! k1) = a"
    "act_ssn (H' ! k1) = sn1" "act_cr (H' ! k1) = ret"
    "act_name (H' ! k2) = deq" "act_pid (H' ! k2) = p2"
    "act_val (H' ! k2) = BOT"  (* Key proof fix. Related symbols: BOT. *)
    "act_ssn (H' ! k2) = sn2" "act_cr (H' ! k2) = call"
    unfolding HB_def Let_def match_call_def match_ret_def mk_op_def
    by (auto simp: op_name_def op_val_def op_pid_def op_ssn_def)

  (* History well-formedness and call/return reasoning. Related symbols: k2. *)
  have k2_old: "k2 < length H"
  proof (rule ccontr)
    assume "\<not> k2 < length H"
    hence "k2 = length H" using k(3) h_eq by simp
    hence "act_name (H' ! k2) = enq"
      using h_eq by (simp add: nth_append act_name_def mk_act_def)
    thus False using k(9) by simp
  qed
  hence k1_old: "k1 < length H" using k(1) by linarith

  show "\<exists>p1 sn1 p2 sn2. HB H (mk_op deq a p1 sn1) (mk_op deq b p2 sn2)"
  proof -
    show ?thesis
      unfolding HB_def
    proof (intro exI conjI)
      show "k1 < k2" by (rule k(1))
      show "match_ret H k1 (mk_op deq a p1 sn1)"
        unfolding match_ret_def mk_op_def
        using k(4,5,6,7,8) k1_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                       op_name_def op_val_def op_pid_def op_ssn_def)
      show "match_call H k2 (mk_op deq b p2 sn2)"
        unfolding match_call_def mk_op_def
        using k(9,10,11,12,13) k2_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                       op_name_def op_val_def op_pid_def op_ssn_def)
    qed
  qed
next
  (* Direction 2 of the proof. Related symbols: \<longrightarrow>. *)
  assume "\<exists>p1 sn1 p2 sn2. HB H (mk_op deq a p1 sn1) (mk_op deq b p2 sn2)"
  then obtain p1 sn1 p2 sn2 k1 k2 where k_old:
    "k1 < k2" "k1 < length H" "k2 < length H"
    "act_name (H ! k1) = deq" "act_cr (H ! k1) = ret" "act_pid (H ! k1) = p1"
    "act_val (H ! k1) = a" "act_ssn (H ! k1) = sn1"
    "act_name (H ! k2) = deq" "act_cr (H ! k2) = call" "act_pid (H ! k2) = p2"
    "act_val (H ! k2) = BOT"  (* Key proof fix. Related symbols: BOT. *)
    "act_ssn (H ! k2) = sn2"
    unfolding HB_def Let_def match_call_def match_ret_def mk_op_def
    by (auto simp: op_name_def op_val_def op_pid_def op_ssn_def)

  show "\<exists>p1 sn1 p2 sn2. HB H' (mk_op deq a p1 sn1) (mk_op deq b p2 sn2)"
  proof -
    show ?thesis
      unfolding HB_def
    proof (intro exI conjI)
      show "k1 < k2" by (rule k_old(1))
      show "match_ret H' k1 (mk_op deq a p1 sn1)"
        unfolding match_ret_def mk_op_def
        using k_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                       op_name_def op_val_def op_pid_def op_ssn_def)
      show "match_call H' k2 (mk_op deq b p2 sn2)"
        unfolding match_call_def mk_op_def
        using k_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                       op_name_def op_val_def op_pid_def op_ssn_def)
    qed
  qed
qed

(* ========================================================================= *)
(* Happens-before reasoning. Related symbols: HB. *)
(* ========================================================================= *)
lemma HB_enq_stable_ret_append:
  fixes H H' :: "ActRec list" and a b :: nat
  assumes h_eq: "H' = H @ [mk_act enq v p sn ret]"
  shows "(\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)) \<longleftrightarrow>
         (\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2))"
proof
  assume "\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  (* Happens-before reasoning. Related symbols: HB_def, mk_op. *)
  then obtain p1 sn1 p2 sn2 k1 k2 where k:
    "k1 < k2"
    "match_ret H' k1 (mk_op enq a p1 sn1)"
    "match_call H' k2 (mk_op enq b p2 sn2)"
    unfolding HB_def by blast

  (* Step 2 of the proof. *)
  have k2_lt: "k2 < length H'"
    using k(3) unfolding match_call_def Let_def by simp
  have k1_lt: "k1 < length H'"
    using k(2) unfolding match_ret_def Let_def by simp

  (* Step 3: prove the required intermediate property. Related symbols: k2. *)
  have k2_old: "k2 < length H"
  proof (rule ccontr)
    assume "\<not> k2 < length H"
    hence "k2 = length H" using k2_lt h_eq by simp
    hence "H' ! k2 = mk_act enq v p sn ret" by (simp add: h_eq nth_append)
    hence "act_cr (H' ! k2) = ret" by (simp add: mk_act_def act_cr_def)
    with k(3) show False unfolding match_call_def Let_def by simp
  qed

  (* Step 4 of the proof. Related symbols: k1_old, m1, m2. *)
  have k1_old: "k1 < length H" using k(1) k2_old by linarith
  have m1: "match_ret H k1 (mk_op enq a p1 sn1)"
    using k1_old k(2) h_eq unfolding match_ret_def Let_def by (auto simp: nth_append)
  have m2: "match_call H k2 (mk_op enq b p2 sn2)"
    using k2_old k(3) h_eq unfolding match_call_def Let_def by (auto simp: nth_append)
  thus "\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    unfolding HB_def using k(1) m1 m2 by blast

next
  (* Unfold the relevant definition and expose the required facts. *)
  assume "\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  then obtain p1 sn1 p2 sn2 k1 k2 where k_old:
    "k1 < k2" "match_ret H k1 (mk_op enq a p1 sn1)" "match_call H k2 (mk_op enq b p2 sn2)"
    unfolding HB_def by blast

  have m1: "match_ret H' k1 (mk_op enq a p1 sn1)"
    using k_old(2) h_eq unfolding match_ret_def Let_def by (auto simp: nth_append)
  have m2: "match_call H' k2 (mk_op enq b p2 sn2)"
    using k_old(3) h_eq unfolding match_call_def Let_def by (auto simp: nth_append)
  thus "\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    unfolding HB_def using k_old(1) m1 m2 by blast
qed


(* ========================================================================= *)
(* History well-formedness and call/return reasoning. *)
(* Proof note. Related symbols: hI2_SSN_Bounds, SSN, hI6_SSN_Order. *)
(* ========================================================================= *)
lemma pending_enq_is_last:
  assumes pending: "HasPendingEnq s p a"
    and ai11: "hI2_SSN_Bounds s"
    and ssn_order: "hI6_SSN_Order s"
  shows "last (filter (\<lambda>e. act_pid e = p) (his_seq s)) = mk_act enq a p (s_var s p) call"
proof -
  let ?p_his = "filter (\<lambda>e. act_pid e = p) (his_seq s)"

  (* Step 1 of the proof. *)
  have "mk_act enq a p (s_var s p) call \<in> set (his_seq s)"
    using pending
    unfolding HasPendingEnq_def EnqCallInHis_def Let_def
              mk_act_def act_pid_def act_name_def act_cr_def act_val_def act_ssn_def
    by force

  then obtain c where c_in: "c \<in> set (his_seq s)"
    and c_def: "c = mk_act enq a p (s_var s p) call"
    by blast

  have c_mem: "c \<in> set ?p_his"
    using c_in c_def by (auto simp: mk_act_def act_pid_def)

  have p_his_not_empty: "?p_his \<noteq> []"
    using c_mem by (auto simp: filter_empty_conv)

  (* Step 2 of the proof. Related symbols: hI2_SSN_Bounds. *)
  have ssn_bound: "\<forall>e \<in> set ?p_his. act_ssn e \<le> s_var s p"
    using ai11 unfolding hI2_SSN_Bounds_def Let_def by auto

  (* Step 3: extract the required facts. *)
  have no_ret: "\<not> (\<exists>e \<in> set ?p_his. act_ssn e = s_var s p \<and> act_cr e = ret)"
    using pending unfolding HasPendingEnq_def EnqCallInHis_def Let_def by auto

  (* Step 4: use the available invariant or hypothesis. Related symbols: hI6_SSN_Order. *)
  show ?thesis
  proof (rule ccontr)
    assume not_last: "last ?p_his \<noteq> mk_act enq a p (s_var s p) call"

    have last_is_mem: "last ?p_his \<in> set ?p_his"
      using p_his_not_empty last_in_set by blast

    have c_neq_last: "c \<noteq> last ?p_his" using not_last c_def by simp

    from filter_last_index_order[OF c_mem c_neq_last]
    obtain i j where idx_props:
      "i < j" "j < length (his_seq s)"
      "his_seq s ! i = c"
      "his_seq s ! j = last ?p_his"
      by blast

    have pid_eq: "act_pid (his_seq s ! i) = act_pid (his_seq s ! j)"
      using idx_props(3,4) c_mem last_is_mem by auto

    (* Proof note. Related symbols: hI6_SSN_Order. *)
    from ssn_order[unfolded hI6_SSN_Order_def, rule_format, OF _ idx_props(2)] idx_props(1) pid_eq
    have "act_ssn c < act_ssn (last ?p_his) \<or>
          (act_ssn c = act_ssn (last ?p_his) \<and> act_cr c = call \<and> act_cr (last ?p_his) = ret)"
      using idx_props(3,4)
      using idx_props(2) by auto

    (* Branch A. Related symbols: hI2_SSN_Bounds. *)
    moreover have "\<not> (act_ssn c < act_ssn (last ?p_his))"
    proof -
      have "act_ssn (last ?p_his) \<le> s_var s p"
        using ssn_bound last_is_mem by blast
      moreover have "act_ssn c = s_var s p"
        using c_def by (simp add: mk_act_def act_ssn_def)
      ultimately show ?thesis by simp
    qed

    (* Branch B. *)
    moreover have "\<not> (act_ssn c = act_ssn (last ?p_his) \<and> act_cr c = call \<and> act_cr (last ?p_his) = ret)"
    proof -
      have c_props: "act_ssn c = s_var s p" "act_cr c = call"
        using c_def by (simp_all add: mk_act_def act_ssn_def act_cr_def)
      moreover have "\<not> (act_ssn (last ?p_his) = s_var s p \<and> act_cr (last ?p_his) = ret)"
        using no_ret last_is_mem by blast
      ultimately show ?thesis using c_props by simp
    qed

    ultimately show False by blast
  qed
qed

(* ------------------------------------------------------------------------- *)
(* Reusable enqueue-candidate helper lemmas for USpec preservation.          *)
(* Historical E1-prefixed lemma names are retained for compatibility;        *)
(* the actual abstract enqueue update is performed by Sys_E2 / U_E2.         *)
(* ------------------------------------------------------------------------- *)

lemma E1_QueueSpecLin_append_enq:
  assumes QS: "QueueSpecLin L"
  shows "QueueSpecLin (L @ [mk_op enq v q sn])"
proof -
  have I4: "lI4_FIFO_Semantics_list L"
    using QS unfolding QueueSpecLin_def by simp

  have I4': "lI4_FIFO_Semantics_list (L @ [mk_op enq v q sn])"
    unfolding lI4_FIFO_Semantics_list_def Let_def
  proof (intro allI impI)
    fix k1
    assume k1_lt: "k1 < length (L @ [mk_op enq v q sn])"
    assume k1_deq: "op_name ((L @ [mk_op enq v q sn]) ! k1) = deq"

    have k1_old: "k1 < length L"
    proof (rule ccontr)
      assume "\<not> k1 < length L"
      hence k1_eq: "k1 = length L"
        using k1_lt by simp
      hence "op_name ((L @ [mk_op enq v q sn]) ! k1) = enq"
        by (simp add: mk_op_def op_name_def)
      thus False
        using k1_deq by simp
    qed

    have old_deq: "op_name (L ! k1) = deq"
      using k1_old k1_deq by (simp add: nth_append)

    obtain k2 where
      k2_lt: "k2 < k1"
      and k2_enq: "op_name (L ! k2) = enq"
      and k2_val: "op_val (L ! k2) = op_val (L ! k1)"
      and k2_prior:
        "\<forall>k3<k2.
            op_name (L ! k3) = enq \<longrightarrow>
            (\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                  op_name (L ! k4) = deq \<and>
                  op_val (L ! k4) = op_val (L ! k3))"
      using I4 k1_old old_deq
      unfolding lI4_FIFO_Semantics_list_def Let_def
      by blast

    show "\<exists>k2<k1.
            op_name ((L @ [mk_op enq v q sn]) ! k2) = enq \<and>
            op_val ((L @ [mk_op enq v q sn]) ! k2) =
              op_val ((L @ [mk_op enq v q sn]) ! k1) \<and>
            (\<forall>k3<k2.
              op_name ((L @ [mk_op enq v q sn]) ! k3) = enq \<longrightarrow>
              (\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                    op_name ((L @ [mk_op enq v q sn]) ! k4) = deq \<and>
                    op_val ((L @ [mk_op enq v q sn]) ! k4) =
                      op_val ((L @ [mk_op enq v q sn]) ! k3)))"
    proof (intro exI conjI)
      show "k2 < k1"
        using k2_lt .
    next
      show "op_name ((L @ [mk_op enq v q sn]) ! k2) = enq"
        using k2_lt k1_old k2_enq by (simp add: nth_append)
    next
      show "op_val ((L @ [mk_op enq v q sn]) ! k2) =
            op_val ((L @ [mk_op enq v q sn]) ! k1)"
        using k2_lt k1_old k2_val by (simp add: nth_append)
    next
      show "\<forall>k3<k2.
              op_name ((L @ [mk_op enq v q sn]) ! k3) = enq \<longrightarrow>
              (\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                    op_name ((L @ [mk_op enq v q sn]) ! k4) = deq \<and>
                    op_val ((L @ [mk_op enq v q sn]) ! k4) =
                      op_val ((L @ [mk_op enq v q sn]) ! k3))"
      proof (intro allI impI)
        fix k3
        assume k3_lt_k2: "k3 < k2"
        assume app_enq:
          "op_name ((L @ [mk_op enq v q sn]) ! k3) = enq"

        have k3_lt_k1:
          "k3 < k1"
          using k3_lt_k2 k2_lt
          by simp

        have k3_lt_L:
          "k3 < length L"
          using k3_lt_k1 k1_old
          by simp

        have old_enq:
          "op_name (L ! k3) = enq"
          using app_enq k3_lt_L
          by (simp add: nth_append)

        obtain k4 where
          k4_gt: "k3 < k4"
          and k4_lt_k1: "k4 < k1"
          and k4_deq: "op_name (L ! k4) = deq"
          and k4_val: "op_val (L ! k4) = op_val (L ! k3)"
          using k2_prior k3_lt_k2 old_enq
          by blast

        have k4_lt_L:
          "k4 < length L"
          using k4_lt_k1 k1_old
          by simp

        have app_k4_deq:
          "op_name ((L @ [mk_op enq v q sn]) ! k4) = deq"
          using k4_deq k4_lt_L
          by (simp add: nth_append)

        have app_k4_val:
          "op_val ((L @ [mk_op enq v q sn]) ! k4) =
           op_val ((L @ [mk_op enq v q sn]) ! k3)"
          using k4_val k4_lt_L k3_lt_L
          by (simp add: nth_append)

        show "\<exists>k4. k3 < k4 \<and>
                    k4 < k1 \<and>
                    op_name ((L @ [mk_op enq v q sn]) ! k4) = deq \<and>
                    op_val ((L @ [mk_op enq v q sn]) ! k4) =
                    op_val ((L @ [mk_op enq v q sn]) ! k3)"
        proof (rule exI[where x = k4])
          show "k3 < k4 \<and>
                k4 < k1 \<and>
                op_name ((L @ [mk_op enq v q sn]) ! k4) = deq \<and>
                op_val ((L @ [mk_op enq v q sn]) ! k4) =
                op_val ((L @ [mk_op enq v q sn]) ! k3)"
            using k4_gt k4_lt_k1 app_k4_deq app_k4_val
            by simp
        qed
      qed
    qed
  qed

  show ?thesis
    using I4' unfolding QueueSpecLin_def by simp
qed

lemma E1_append_enq_fresh_from_DI:
  assumes DI: "data_independent (L @ [mk_op enq v q sn])"
  shows "\<forall>a\<in>set L. op_name a = enq \<longrightarrow> op_val a \<noteq> v"
proof (intro ballI impI)
  fix a
  assume a_in: "a \<in> set L"
  assume a_enq: "op_name a = enq"

  obtain i where i_lt: "i < length L" and a_eq: "a = L ! i"
    using a_in by (metis in_set_conv_nth)

  let ?L = "L @ [mk_op enq v q sn]"

  have i_lt': "i < length ?L"
    using i_lt by simp
  have last_lt': "length L < length ?L"
    by simp
  have i_ne_last: "i \<noteq> length L"
    using i_lt by simp
  have enq_i: "op_name (?L ! i) = enq"
    using i_lt a_eq a_enq by (simp add: nth_append)
  have enq_last: "op_name (?L ! length L) = enq"
    by (simp add: nth_append mk_op_def op_name_def)

  have neq:
    "op_val (?L ! i) \<noteq> op_val (?L ! length L)"
    using unique_enq_value[OF DI i_lt' last_lt' i_ne_last enq_i enq_last] .

  thus "op_val a \<noteq> v"
    using i_lt a_eq
    by (simp add: nth_append mk_op_def op_val_def)
qed

end
