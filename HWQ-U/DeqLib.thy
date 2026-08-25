theory DeqLib
 imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    DistLib
    Termination
begin




(* 2: invariant, Idx of definition and AtIdx one *)
lemma Idx_implies_AtIdx:
  assumes "system_invariant s"
  assumes "InQBack s a"
  shows "AtIdx s a (Idx s a)"
proof -
  from assms(2) have "\<exists>k. AtIdx s a k" unfolding AtIdx_def InQBack_def by auto
  then show ?thesis unfolding Idx_def by (rule someI_ex)
qed

(* 3: AtIdx Qback_arr equal to this value *)
lemma AtIdx_implies_Qback_eq:
  assumes "AtIdx s a k"
  shows "Qback_arr s k = a"
  using assms unfolding AtIdx_def by simp

(* 4: invariant, if a in Qback in and a \<noteq> BOT, then a \<in> Val *)
lemma InQBack_non_BOT_implies_Val:
  assumes "system_invariant s"
  assumes "InQBack s a"
  assumes "a \<noteq> BOT"
  shows "a \<in> Val"
proof -
  from assms(1) have TypeOK_s: "TypeOK s" unfolding system_invariant_def by simp
  from assms(2) obtain k where "Qback_arr s k = a" unfolding InQBack_def by auto
  with TypeOK_s have "Qback_arr s k \<in> Val \<union> {BOT}" unfolding TypeOK_def
    by auto
  with assms(3) show "a \<in> Val" by (auto simp: BOT_def Val_def)
qed

(* 5: invariant, E2 HasPendingEnq *)
lemma E2_implies_HasPendingEnq:
  assumes "system_invariant s"
  assumes "program_counter s p = ''E2''"
  shows "HasPendingEnq s p (v_var s p)"
proof -
  (* 1. from invariant in extract hI1_E_Phase_Pending_Enq *)
  from assms(1) have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" unfolding system_invariant_def by simp

  (* 2. E2 in E set *)
  from assms(2) have "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" by simp

  (* 3. apply hI1_E_Phase_Pending_Enq *)
  with hI1_E_Phase_Pending_Enq_s show ?thesis unfolding hI1_E_Phase_Pending_Enq_def by blast
qed

(* 7: D3 in j of slot of property *)
lemma D3_Q_at_j:
  assumes "system_invariant s"
  assumes "program_counter s p = ''D3''"
  shows "Q_arr s (j_var s p) = Qback_arr s (j_var s p) \<or> Q_arr s (j_var s p) = BOT"
proof -
  from assms(1) have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" unfolding system_invariant_def by simp
  show ?thesis using sI8_Q_Qback_Sync_s unfolding sI8_Q_Qback_Sync_def by simp
qed

(* Core fix (original 8 and 9 has):
   If a in T in of j corresponds to of Q slot is BOT,
   Then a impossible is TypeB (a in Q in, also in E2)
*)
lemma Idx_eq_j_and_Q_BOT_implies_not_TypeB:
  assumes "system_invariant s"
  assumes "InQBack s a"
  assumes "Idx s a = j"
  assumes "Q_arr s j = BOT"   (* Keypremise: Q[j] must is BOT *)
  assumes "a \<noteq> BOT"
  shows "\<not> TypeB s a"
proof
  assume TypeB_a: "TypeB s a"
  from assms(1) have
    sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and
    sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s"
    unfolding system_invariant_def by simp_all

  (* 1. Idx definition can T[j] = a *)
  have T_j_eq_a: "Qback_arr s j = a"
    using AtIdx_implies_Qback_eq Idx_implies_AtIdx assms(1,2,3) by blast

  from TypeB_a obtain k where Q_k: "Q_arr s k = a"
    unfolding TypeB_def QHas_def by blast

    (* SI8_Q_Qback_Sync: Q[k]=a (BOT) ==> T[k]=a *)
    have "Qback_arr s k = a"
    proof -
      have "Q_arr s k \<noteq> BOT" using Q_k assms(5) by simp
      with sI8_Q_Qback_Sync_s have "Q_arr s k = Qback_arr s k" unfolding sI8_Q_Qback_Sync_def by fastforce
      with Q_k show ?thesis by simp
    qed

    (* SI10_Qback_Unique_Vals: T in value one ==> k = j *)
    have "k = j"
    proof (rule ccontr)
      assume "k \<noteq> j"
      (* a \<in> Val *)
      have "a \<in> Val" using InQBack_non_BOT_implies_Val[OF assms(1) assms(2) assms(5)] .
      with sI10_Qback_Unique_Vals_s `Qback_arr s k = a` T_j_eq_a `k \<noteq> j`
      show False unfolding sI10_Qback_Unique_Vals_def
        by (metis assms(5))
    qed

  have "Q_arr s j = a" using Q_k `k = j` by simp
  with assms(4) assms(5) show False by simp
qed

(* ========================================================================= *)
(* Core: prove modify_lin only is for list (preserve) *)
(* ========================================================================= *)


lemma mset_modify_eq_case:
  (* Global: only has L of decompose is allcase use of *)
  assumes L_decomp: "mset L = mset (l1 @ l2 @ [bt_act] @ l3)"
  shows
    (* Case 1: only need l2 nonempty *)
    case1: "l2 \<noteq> [] \<Longrightarrow> mset (l1 @ butlast l2 @ [bt_act] @ [last l2] @ l3) = mset L"

    (* Case 2: need l2 decompose, l22 nonempty, o1 definition *)
    and case2: "\<lbrakk> l2 = l21 @ [b_act] @ l22; l22 \<noteq> []; o1 = hd l22 \<rbrakk> \<Longrightarrow>
                mset (l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3) = mset L"

    (* Case 3: only need l2 decompose *)
    and case3: "\<lbrakk> l2 = l21 @ [b_act] @ l22 \<rbrakk> \<Longrightarrow>
                mset (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) = mset L"

    (* Case 4: need l2 decompose, l22 nonempty, ou definition *)
    and case4: "\<lbrakk> l2 = l21 @ [b_act] @ l22; l22 \<noteq> []; ou = last l22 \<rbrakk> \<Longrightarrow>
                mset (l1 @ l21 @ [b_act] @ butlast l22 @ [bt_act] @ [ou] @ l3) = mset L"

    (* Case 5: only need l2 decompose *)
    and case5: "\<lbrakk> l2 = l21 @ [b_act] @ l22 \<rbrakk> \<Longrightarrow>
                mset (l1 @ l21 @ l22 @ [bt_act] @ [b_act] @ l3) = mset L"
proof -
  (* Prove Case 1 *)
  {
    assume "l2 \<noteq> []"
    have "l2 = butlast l2 @ [last l2]" using `l2 \<noteq> []` by simp
    then have "mset l2 = mset (butlast l2) + {#last l2#}"
      by (metis mset_append mset_single_iff_right)
    then have "mset (l1 @ butlast l2 @ [bt_act] @ [last l2] @ l3)
               = mset l1 + mset (butlast l2) + {#last l2#} + {#bt_act#} + mset l3"
      by (simp add: ac_simps)
    also have "... = mset l1 + mset l2 + {#bt_act#} + mset l3"
      using `l2 = butlast l2 @ [last l2]`
      by (simp add: \<open>mset l2 = mset (butlast l2) + {#last l2#}\<close>)
    also have "... = mset L"
      using L_decomp by (simp add: ac_simps)
    finally show "mset (l1 @ butlast l2 @ [bt_act] @ [last l2] @ l3) = mset L" .
  }

  (* Prove Case 2 *)
  {
    assume "l2 = l21 @ [b_act] @ l22" "l22 \<noteq> []" "o1 = hd l22"
    then have "l22 = o1 # tl l22" by simp
    have "mset (l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3)
          = mset l1 + mset l21 + {#o1#} + {#b_act#} + mset (tl l22) + {#bt_act#} + mset l3"
      by (simp add: ac_simps)
    also have "... = mset l1 + mset l21 + {#b_act#} + ({#o1#} + mset (tl l22)) + {#bt_act#} + mset l3"
      by (simp add: ac_simps)
    also have "... = mset l1 + mset l21 + {#b_act#} + mset l22 + {#bt_act#} + mset l3"
      using `l22 = o1 # tl l22`
      by (metis add_mset_add_single mset.simps(2) union_commute)
    also have "... = mset L"
      using L_decomp `l2 = l21 @ [b_act] @ l22` by (simp add: ac_simps)
    finally show "mset (l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3) = mset L" .
  }

  (* Prove Case 3 *)
  {
    assume "l2 = l21 @ [b_act] @ l22"
    have "mset (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) = mset L"
      using L_decomp `l2 = l21 @ [b_act] @ l22` by (simp add: ac_simps)
    then show "mset (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) = mset L" .
  }

  (* Prove Case 4 *)
  {
    assume "l2 = l21 @ [b_act] @ l22" "l22 \<noteq> []" "ou = last l22"
    then have "l22 = butlast l22 @ [ou]" by simp
    have "mset (l1 @ l21 @ [b_act] @ butlast l22 @ [bt_act] @ [ou] @ l3)
          = mset l1 + mset l21 + {#b_act#} + mset (butlast l22) + {#bt_act#} + {#ou#} + mset l3"
      by (simp add: ac_simps)
    also have "... = mset l1 + mset l21 + {#b_act#} + (mset (butlast l22) + {#ou#}) + {#bt_act#} + mset l3"
      by (simp add: ac_simps)
    also have "... = mset l1 + mset l21 + {#b_act#} + mset l22 + {#bt_act#} + mset l3"
      using `l22 = butlast l22 @ [ou]`
      by (metis mset.simps(1,2) mset_append)
    also have "... = mset L"
      using L_decomp `l2 = l21 @ [b_act] @ l22` by (simp add: ac_simps)
    finally show "mset (l1 @ l21 @ [b_act] @ butlast l22 @ [bt_act] @ [ou] @ l3) = mset L" .
  }

  (* Prove Case 5 *)
  {
    assume "l2 = l21 @ [b_act] @ l22"
    have "mset (l1 @ l21 @ l22 @ [bt_act] @ [b_act] @ l3) = mset L"
      using L_decomp `l2 = l21 @ [b_act] @ l22` by (simp add: ac_simps)
    then show "mset (l1 @ l21 @ l22 @ [bt_act] @ [b_act] @ l3) = mset L" .
  }
qed

(* Prove: if find_unique_index return Some idx, then idx < length L *)
lemma find_unique_index_Some_less_length:
  assumes "find_unique_index P L = Some idx"
  shows "idx < length L"
  using assms
  unfolding find_unique_index_def find_indices_def
  using assms find_unique_index_prop by blast

lemma modify_preserves_mset:
  "mset (modify_lin L H bt_val) = mset L"
proof (induct L H bt_val rule: modify_lin.induct)
  case (1 L H bt_val)

  (* --- 1. No. one: is change --- *)
  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    (* Base Case: change, return L, *)
    then show ?thesis by (subst modify_lin.simps, simp)
  next
    case True
    (* Inductive Step: enter change *)
    note do_modify = True

    (* --- 2. definition (modify_lin source) --- *)
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define remaining where "remaining = drop (nat (last_sa_pos + 1)) L"

    (* Prove bt_idx in, for after 'the' *)
    have idx_exists: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
      using True unfolding should_modify_def last_sa_pos_def remaining_def by (metis option.simps(4))

    obtain bt_idx where bt_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      using idx_exists by blast

    (* Proof step: prove *)
    have bt_idx_valid: "bt_idx < length remaining"
      using bt_idx_def by (rule find_unique_index_Some_less_length)

    define l1 where "l1 = take (nat (last_sa_pos + 1)) L"
    define l2 where "l2 = take bt_idx remaining"
    define l3 where "l3 = drop (bt_idx + 1) remaining"
    define bt_act where "bt_act = remaining ! bt_idx"


    (* --- 3. keystep: prove l2 empty --- *)
    have l2_not_nil: "l2 \<noteq> []"
    proof (cases "l2 = []")
      case True
      (* Step A: prove remaining empty *)
      (* Proof step: in auto in find_unique_index.simps, make it empty-list return None *)
      have "remaining \<noteq> []"
        using bt_idx_def
        apply (cases remaining)
         apply (auto simp: find_unique_index_def)
        using bt_idx_def find_unique_index_Some_less_length by force

      (* Step B: use of take_eq_Nil (Isabelle) *)
      have "bt_idx = 0"
        using True l2_def `remaining \<noteq> []`
        by (metis take_eq_Nil)

      (* Step C: derivationcontradiction *)
      have False
        using do_modify
        unfolding should_modify_def find_last_enq_def
        unfolding last_sa_pos_def remaining_def l1_def l2_def
        using `bt_idx = 0` bt_idx_def True
        by (simp add: last_sa_pos_def remaining_def)

      then show ?thesis ..
    next
      case False
      then show ?thesis by simp
    qed

    define l2_last where "l2_last = last l2"

    (* --- 4. No. two: l2 last one operation --- *)
    show ?thesis
    proof (cases "op_name l2_last = enq")

      (* === Case A: operation is Enq (enter then branch) === *)
      case True

      (* Definitionnew of list *)
      define new_L where "new_L = l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3"

      (* A.1: prove modify_lin equal *)
      have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
      proof -
        have "modify_lin L H bt_val = modify_lin (l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3) H bt_val"
          (* Unfold modify_lin and all definition *)
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def do_modify True
          apply (subst modify_lin.simps) (* Unfold *)
          apply (simp only: Let_def case_prod_unfold) (* Proof note *)
          apply (subst if_not_P, simp)
          by (simp add: l2_def l2_last_def last_sa_pos_def
              remaining_def)

        then show ?thesis unfolding new_L_def .
      qed

      have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
        using bt_idx_valid l2_def l3_def bt_act_def
        using Cons_nth_drop_Suc by fastforce

      have L_decomp: "mset L = mset (l1 @ l2 @ [bt_act] @ l3)"
        using append_take_drop_id[of "(nat (last_sa_pos + 1))" L]
        unfolding l1_def remaining_def remaining_decomp
        using remaining_decomp remaining_def by force

      (* A.2: prove mset equal (use mset_modify_eq_case oruse directly simp) *)
      have mset_eq: "mset new_L = mset L"
        unfolding new_L_def l2_last_def (* Unfolddefinition, make last l2 out *)
        apply (rule mset_modify_eq_case(1)[OF L_decomp])
        by (simp add: l2_not_nil)

      (* Out conclusion *)
      show ?thesis
        using mod_eq mset_eq 1(1) True do_modify
        (* Need new_L unfold original match *)
        unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        using bt_idx_def
        by (metis last_sa_pos_def option.sel remaining_def)

    next

      (* === Case B: operation is Enq (enter else branch) === *)
      case False
      note not_enq = False

      (* Prove find_last_enq empty *)
      have find_enq_valid: "find_last_enq l2 \<noteq> None"
        using do_modify False l2_not_nil
        unfolding should_modify_def
        unfolding l2_def remaining_def last_sa_pos_def l2_last_def
        using bt_idx_def
        by (smt (verit, best) case_optionE last_sa_pos_def option.distinct(1) option.inject remaining_def)

      obtain l21 b_act l22 where l2_split: "find_last_enq l2 = Some (l21, b_act, l22)"
        using find_enq_valid by (cases "find_last_enq l2", auto)

      define o1 where "o1 = hd l22"
      define ou where "ou = last l22"


      (* --- key: use consider 3 IF case, avoid timeout --- *)
      (* Large of also have, andcomplete match newversion modify_lin of *)
      consider
          (c1) "happens_before o1 bt_act H"
        | (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H"
        | (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast

      then show ?thesis
      proof cases
        (* --- subcase 1 --- *)
        case c1
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        (* 1. prove l22 nonempty *)
        have l22_not_nil: "l22 \<noteq> []"
          using do_modify not_enq l2_last_def
          using l2_split l2_not_nil
          unfolding find_last_enq_def
          using l2_def remaining_def
          by (metis find_last_enq_props(1,2) l2_split last_snoc self_append_conv)


        (* 2. prove modify_lin equal *)
        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c1 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)

        (* 3. prove mset equal *)
        have perm_eq: "mset new_L = mset L"
        proof -
          have idx_valid: "bt_idx < length remaining"
            using bt_idx_def unfolding find_unique_index_def using bt_idx_valid by auto

          have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
            unfolding l2_def l3_def bt_act_def using idx_valid by (simp add: id_take_nth_drop)

          have step_L: "L = l1 @ l2 @ [bt_act] @ l3"
            unfolding l1_def remaining_def using remaining_decomp remaining_def by fastforce

          have step_l2: "l2 = l21 @ [b_act] @ l22"
            using l2_split unfolding find_last_enq_def using find_last_enq_props(1) l2_split by auto

          have step_l22: "l22 = o1 # tl l22"
            using l22_not_nil o1_def by (cases l22) auto

          show ?thesis
            unfolding new_L_def
            using step_L step_l2 step_l22
            by (metis case2 l22_not_nil o1_def)
        qed

        (* 4. *)
        show ?thesis
          using mod_eq perm_eq
          using 1
          using c1 False do_modify l2_split bt_idx_def
          using l22_not_nil
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (no_types, lifting) option.sel)

      next
        (* --- subcase 2 --- *)
        case c2
        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"

        (* 1. prove modify_lin equal *)
        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c2 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)

        (* 2. prove mset equal *)
        have perm_eq: "mset new_L = mset L"
        proof -
          have idx_valid: "bt_idx < length remaining"
            using bt_idx_def unfolding find_unique_index_def by (simp add: bt_idx_valid)

          have "remaining = l2 @ [bt_act] @ l3"
             unfolding l2_def l3_def bt_act_def using idx_valid by (simp add: id_take_nth_drop)

          have step_L: "L = l1 @ l2 @ [bt_act] @ l3"
             unfolding l1_def remaining_def using `remaining = l2 @ [bt_act] @ l3` using remaining_def by fastforce

          have step_l2: "l2 = l21 @ [b_act] @ l22"
            using l2_split unfolding find_last_enq_def using find_last_enq_props(1) l2_split by auto

          show ?thesis
            unfolding new_L_def
            using step_L step_l2
            by simp
        qed

        (* 3. *)
        show ?thesis
          using perm_eq mod_eq
          using 1(3)
          using c2 False do_modify l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (no_types, lifting) option.sel)

      next
        (* --- subcase 3 (corresponds tooriginal in new of else if \<not> happens_before b_act o1 H) --- *)
        case c3
        (* Action and c1 complete one: o1 and b_act *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        (* 1. prove l22 nonempty *)
        have l22_not_nil: "l22 \<noteq> []"
          using do_modify not_enq l2_last_def
          using l2_split l2_not_nil
          unfolding find_last_enq_def
          using l2_def remaining_def
          by (metis find_last_enq_props(1,2) l2_split last_snoc self_append_conv)

        (* 2. prove modify_lin equal *)
        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c3 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)

        (* 3. prove mset equal (use c1 of prove) *)
        have perm_eq: "mset new_L = mset L"
        proof -
          have idx_valid: "bt_idx < length remaining"
            using bt_idx_def unfolding find_unique_index_def using bt_idx_valid by auto

          have remaining_decomp: "remaining = l2 @ [bt_act] @ l3"
            unfolding l2_def l3_def bt_act_def using idx_valid by (simp add: id_take_nth_drop)

          have step_L: "L = l1 @ l2 @ [bt_act] @ l3"
            unfolding l1_def remaining_def using remaining_decomp remaining_def by fastforce

          have step_l2: "l2 = l21 @ [b_act] @ l22"
            using l2_split unfolding find_last_enq_def using find_last_enq_props(1) l2_split by auto

          have step_l22: "l22 = o1 # tl l22"
            using l22_not_nil o1_def by (cases l22) auto

          show ?thesis
            unfolding new_L_def
            using step_L step_l2 step_l22
            by (metis case2 l22_not_nil o1_def)
        qed

        (* 4. (notehere use 1(4)) *)
        show ?thesis
          using mod_eq perm_eq
          using 1(4)
          using c3 False do_modify l2_split bt_idx_def
          using l22_not_nil
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (no_types, lifting) option.sel)
      qed
    qed
  qed
qed


(* ========================================================================= *)
(* Prove: modify preserve data_independent *)
(* ========================================================================= *)

lemma modify_preserves_data_independent:
  assumes "data_independent L"
  shows "data_independent (modify_lin  L H v)"
proof -
  have "mset (modify_lin  L H v) = mset L"
    by (rule modify_preserves_mset)
  then show ?thesis
    using data_independent_cong assms by blast
qed

(* ------------------------------------------------------------------------- *)
(* Helper lemma: if one value in SetB (queue in), it in when before of in one has Deq operation *)
(* Is prove lI2_Op_Cardinality (uniqueness) of key *)
(* ------------------------------------------------------------------------- *)
lemma SetB_implies_no_deq_in_lin:
  assumes "system_invariant s"
  assumes "x \<in> SetB s"
  shows "DeqIdxs s x = {}"
proof (rule ccontr)
  assume "DeqIdxs s x \<noteq> {}"
  then obtain k where k_in: "k \<in> DeqIdxs s x" by blast

  (* 1. extract *)
  have lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and typeOK_s: "TypeOK s"
    using assms(1) unfolding system_invariant_def by auto

  (* 2. analyze k in DeqIdxs in of *)
  have k_bound: "k < length (lin_seq s)"
   and act_deq: "op_name (lin_seq s ! k) = deq"
   and op_val: "op_val (lin_seq s ! k) = x"
    using k_in unfolding DeqIdxs_def by auto

  let ?act = "lin_seq s ! k"
  have "?act \<in> OPLin s"
    unfolding OPLin_def using k_bound by auto

  (* 3. use lI1_Op_Sets_Equivalence?act of *)
  have "?act \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_Op_Sets_Equivalence_s `?act \<in> OPLin s` unfolding lI1_Op_Sets_Equivalence_def by blast

  (* 4. enq set (because?act is deq) *)
  moreover have "?act \<notin> OP_A_enq s"
    unfolding OP_A_enq_def using act_deq
    using SetB_implies_no_deq_in_lin op_val assms(1,2) k_bound
    by auto

  moreover have "?act \<notin> OP_B_enq s"
    unfolding OP_B_enq_def using act_deq
    using SetB_implies_no_deq_in_lin op_val assms(1,2) k_bound
    by auto

  (* 5. in: ?act must in OP_A_deq *)
  ultimately have "?act \<in> OP_A_deq s" by blast

  (* 6. OP_A_deq x \<in> SetA *)
  then obtain p a sn where "?act = mk_op deq a p sn" "a \<in> SetA s"
    unfolding OP_A_deq_def
    using OPLin_def SetB_implies_no_deq_in_lin op_val assms(1,2)
    by blast

  have "a = x"
    using `?act = mk_op deq a p sn` op_val unfolding mk_op_def op_val_def by simp

  hence "x \<in> SetA s" using `a \<in> SetA s` by simp

  (* 7. contradiction: TypeOK SetA and SetB *)
  have "SetA s \<inter> SetB s = {}"
    unfolding SetA_def SetB_def TypeA_def TypeB_def by auto

  (* 8. *)
  thus False using `x \<in> SetA s` assms(2) by blast
qed


(* ========================================================== *)
(* Helper lemma 1: element preserve HB consistency (version) *)
(* ========================================================== *)
lemma HB_swap_adjacent:
  assumes consistent_L1: "HB_consistent (pre @ [a] @ [b] @ post) H"
  assumes not_HB_ab: "\<not> HB H a b"
  shows "HB_consistent (pre @ [b] @ [a] @ post) H"
proof -
  (* 1. definitionlocal *)
  let ?L1 = "pre @ [a] @ [b] @ post"
  let ?L2 = "pre @ [b] @ [a] @ post"
  let ?k = "length pre"

  (* 2. definitionmapping *)
  let ?f = "\<lambda>idx. if idx = ?k then ?k + 1 else if idx = ?k + 1 then ?k else idx"

  (* 3. provemappingproperty *)
  have eq_nth: "\<And>idx. idx < length ?L2 \<Longrightarrow> ?L2 ! idx = ?L1 ! (?f idx)"
  proof -
    fix idx assume "idx < length ?L2"
    consider "idx < ?k" | "idx = ?k" | "idx = ?k + 1" | "idx > ?k + 1" by linarith
    then show "?L2 ! idx = ?L1 ! (?f idx)"
      by cases (simp_all add: nth_append)
  qed

  (* 4. unfolddefinition and prove *)
  show ?thesis
    unfolding HB_consistent_def
  proof (intro allI impI)
    (* Here in and *)
    fix i j
    assume valid_and_hb: "i < length ?L2 \<and> j < length ?L2 \<and> HB H (?L2 ! i) (?L2 ! j)"

    (* Split *)
    have valid_i: "i < length ?L2" using valid_and_hb by simp
    have valid_j: "j < length ?L2" using valid_and_hb by simp
    have hb_ij: "HB H (?L2 ! i) (?L2 ! j)" using valid_and_hb by simp

    (* --- with is the of core, precise in --- *)

    (* 4.1 mapping HB *)
    have hb_mapped: "HB H (?L1 ! (?f i)) (?L1 ! (?f j))"
      using hb_ij eq_nth[OF valid_i] eq_nth[OF valid_j] by simp

    (* 4.2 use L1 consistencyderive *)
    have f_i_less_f_j: "?f i < ?f j"
    proof -
      have len_eq: "length ?L1 = length ?L2" by simp
      have v1: "?f i < length ?L1" using valid_i len_eq by (auto split: if_splits)
      have v2: "?f j < length ?L1" using valid_j len_eq by (auto split: if_splits)

      show ?thesis
        using consistent_L1[unfolded HB_consistent_def]
        using hb_mapped v1 v2
        by blast
    qed

    (* 4.3 provegoal i < j *)
    show "i < j"
    proof (rule ccontr)
      assume "\<not> i < j"
      hence "j \<le> i" by simp

      (* Contradiction *)
      have "i \<noteq> ?k + 1 \<or> j \<noteq> ?k"
      proof (rule ccontr)
        (* 1. conclusion into (: i = k+1 and j = k) *)
        assume "\<not> (i \<noteq> ?k + 1 \<or> j \<noteq> ?k)"
        hence conflict_case: "i = ?k + 1 \<and> j = ?k" by simp

        (* 2. derivationat this point L2 of value *)
        (* When i=k+1 L2!i is a; when j=k L2!j is b *)
        (* Note: L2 is [..., b, a,...], k is b, k+1 is a *)
        have "HB H a b"
          using conflict_case hb_ij
          by (simp add: nth_append) (* Match out L2!i=a, L2!j=b *)

        (* 3. and premise not_HB_ab (\<not> HB H a b) contradiction *)
        thus False using not_HB_ab by simp
      qed

      (* Usemappingmonotonicityderive a contradiction *)
      have "?f j \<le> ?f i"
        using `j \<le> i` `i \<noteq> ?k + 1 \<or> j \<noteq> ?k`
        by (auto split: if_splits)

      thus False using f_i_less_f_j by simp
    qed
  qed
qed

(* ========================================================== *)
(* Helper lemma 2: element left (Jump Left) - version *)
(* ========================================================== *)
lemma HB_jump_left:
  assumes consistent_L1: "HB_consistent (pre @ middle @ [x] @ post) H"
  assumes not_HB_middle_x: "\<forall>m \<in> set middle. \<not> HB H m x" (* Use HB preserve one *)
  shows "HB_consistent (pre @ [x] @ middle @ post) H"
proof -
  (* 1. definitionlocal *)
  let ?L1 = "pre @ middle @ [x] @ post"
  let ?L2 = "pre @ [x] @ middle @ post"
  let ?k = "length pre"
  let ?mid_len = "length middle"

  (* 2. definition mapping f: L2 -> L1 *)
  (* L2: [pre...][x][middle...][post...] *)
  (* 0..k-1  k  k+1..k+m   k+m+1.. *)
  (* L1: [pre...][middle...][x][post...] *)
  (* 0..k-1  k..k+m-1  k+m k+m+1.. *)

  let ?f = "\<lambda>idx. if idx < ?k then idx
                  else if idx = ?k then ?k + ?mid_len
                  else if idx \<le> ?k + ?mid_len then idx - 1
                  else idx"

  (* 3. provemappingproperty *)
  have eq_nth: "\<And>idx. idx < length ?L2 \<Longrightarrow> ?L2 ! idx = ?L1 ! (?f idx)"
  proof -
    fix idx assume "idx < length ?L2"
    consider "idx < ?k" | "idx = ?k" | "idx > ?k \<and> idx \<le> ?k + ?mid_len" | "idx > ?k + ?mid_len"
      by linarith
then show "?L2 ! idx = ?L1 ! (?f idx)"
    proof cases
      case 1 (* idx < k *)
      then show ?thesis by (simp add: nth_append)
    next
      case 2 (* idx = k *)
      then show ?thesis by (simp add: nth_append)
    next
      case 3 (* k < idx <= k + mid_len *)
      (* Is one key, we need *)

      (* 1.?L2! idx *)
      (* ?L2 = pre @ [x] @ middle @ post *)
      (* Idx > k (length pre), and idx - (k+1) < length middle *)
      (* Therefore?L2! idx in middle *)
      have "idx > length pre" using 3 by simp
      have idx_in_mid_L2: "idx - (length pre + 1) < length middle"
        using 3 by arith

      have lhs: "?L2 ! idx = middle ! (idx - (length pre + 1))"
        using 3
        by (metis (mono_tags, lifting) Cons_eq_appendI append_self_conv2
            diff_diff_left idx_in_mid_L2 nat_less_le nth_Cons_pos nth_append_left
            nth_append_right zero_less_diff)

      (* 2.?L1! (?f idx) *)
      (* ?f idx = idx - 1 *)
      (* ?L1 = pre @ middle @ [x] @ post *)
      (* idx - 1 >= k (length pre) *)
      (* (idx - 1) - k < length middle *)
      let ?idx' = "idx - 1"
      have "?idx' \<ge> length pre" using 3 by arith
      have idx_in_mid_L1: "?idx' - length pre < length middle"
        using 3 by arith

      have rhs: "?L1 ! ?idx' = middle ! (?idx' - length pre)"
        using 3
        by (metis \<open>length pre \<le> idx - 1\<close> idx_in_mid_L1 nth_append_left
            nth_append_right)

      (* 3. prove two equal *)
      (* (idx - (k+1)) vs (idx - 1 - k) *)
      have "idx - (length pre + 1) = ?idx' - length pre"
        using 3 by arith

      show ?thesis
        using lhs rhs 3 by simp
    next
      case 4 (* idx > k + mid_len *)
      then show ?thesis by (simp add: nth_append)
    qed
  qed

  (* 4. coreprove *)
  show ?thesis
    unfolding HB_consistent_def
  proof (intro allI impI)
    fix i j
    assume valid_and_hb: "i < length ?L2 \<and> j < length ?L2 \<and> HB H (?L2 ! i) (?L2 ! j)"

    (* Split *)
    have valid_i: "i < length ?L2" using valid_and_hb by simp
    have valid_j: "j < length ?L2" using valid_and_hb by simp
    have hb_ij: "HB H (?L2 ! i) (?L2 ! j)" using valid_and_hb by simp

    (* 4.1 mapping HB L1 *)
    have hb_mapped: "HB H (?L1 ! (?f i)) (?L1 ! (?f j))"
      using hb_ij eq_nth[OF valid_i] eq_nth[OF valid_j] by simp

    (* 4.2 use L1 consistencyderive f(i) < f(j) *)
    have f_i_less_f_j: "?f i < ?f j"
    proof -
      have len_eq: "length ?L1 = length ?L2" by simp
      have v1: "?f i < length ?L1" using valid_i len_eq by (auto split: if_splits)
      have v2: "?f j < length ?L1" using valid_j len_eq by (auto split: if_splits)

      show ?thesis
        using consistent_L1[unfolded HB_consistent_def]
        using hb_mapped v1 v2
        by blast
    qed

    (* 4.3 prove i < j *)
    show "i < j"
    proof (rule ccontr)
      assume "\<not> i < j"
      hence "j \<le> i" by simp

      (* Case: is of? *)
      (* One of is: j x (k), and i middle in of element (k+1.. k+m) *)
      (* Because x from after to before *)

      have "\<not> (j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len)"
      proof
        assume conflict: "j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len"
        (* At this point L2!j = x, L2!i \<in> middle *)
        let ?m = "?L2 ! i"

        (* Prove?m in middle in *)
        have "?m \<in> set middle"
        proof -
          (* 1. local *)
          (* I in L2 in of: pre (k) + [x] (1) + middle... *)
          (* Therefore middle of start is k + 1 *)
          let ?local_idx = "i - (?k + 1)"

          (* 2. provelocal has *)
          (* Conflict: i <= k + mid_len *)
          have in_bounds: "?local_idx < length middle"
            using conflict by arith

          (* 3. prove L2! i equal to middle! local_idx *)
          (* Because i > k, therefore it pre and x *)
          have match: "?L2 ! i = middle ! ?local_idx"
            using conflict in_bounds
            by (simp add: nth_append)

          (* 4. use nth_mem: if is list of has element, then it in set in *)
          show ?thesis
            unfolding match
            using in_bounds by (rule nth_mem)
        qed

        (* Premise hb_ij HB H m x *)
        (* But L2!j is x *)
        have "HB H ?m x" using hb_ij conflict by (simp add: nth_append)

        (* And not_HB_middle_x contradiction *)
        thus False using not_HB_middle_x `?m \<in> set middle` by blast
      qed

      (* If is case, mapping f this is preserve of *)
      (* : j <= i ==> f(j) <= f(i) *)
      have "j \<le> i \<Longrightarrow> \<not> (j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len) \<Longrightarrow> ?f j \<le> ?f i"
        by (auto split: if_splits)

      (* F(i) < f(j) derive a contradiction *)
      hence "?f j \<le> ?f i" using `j \<le> i` `\<not> (j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len)` by simp
      thus False using f_i_less_f_j by simp
    qed
  qed
qed


(* ========================================================== *)
(* Helper lemma 3: element right (Jump Right) - version *)
(* ========================================================== *)
lemma HB_jump_right:
  assumes consistent_L1: "HB_consistent (pre @ [x] @ middle @ post) H"
  assumes not_HB_x_middle: "\<forall>m \<in> set middle. \<not> HB H x m" (* Use HB preserve one *)
  shows "HB_consistent (pre @ middle @ [x] @ post) H"
proof -
  (* 1. definitionlocal *)
  let ?L1 = "pre @ [x] @ middle @ post"
  let ?L2 = "pre @ middle @ [x] @ post"
  let ?k = "length pre"
  let ?mid_len = "length middle"

  (* 2. definition mapping f: L2 -> L1 *)
  (* L2: [pre...][middle...][x][post...] *)
  (* 0..k-1  k..k+m-1   k+m k+m+1.. *)
  (* L1: [pre...][x][middle...][post...] *)
  (* 0..k-1  k  k+1..k+m   k+m+1.. *)

  let ?f = "\<lambda>idx. if idx < ?k then idx
                  else if idx = ?k + ?mid_len then ?k
                  else if idx < ?k + ?mid_len then idx + 1
                  else idx"

  (* 3. provemappingproperty *)
  have eq_nth: "\<And>idx. idx < length ?L2 \<Longrightarrow> ?L2 ! idx = ?L1 ! (?f idx)"
  proof -
    fix idx assume "idx < length ?L2"
    consider "idx < ?k" | "idx \<ge> ?k \<and> idx < ?k + ?mid_len" | "idx = ?k + ?mid_len" | "idx > ?k + ?mid_len"
      by linarith
    then show "?L2 ! idx = ?L1 ! (?f idx)"
    proof cases
      case 1 then show ?thesis by (simp add: nth_append)
    next
      case 2 (* Middle: k <= idx < k + mid_len *)
      (* Goal: ?L2! idx =?L1! (idx + 1) *)

      (* 1.?L2! idx *)
      (* ?L2 = pre @ middle @ ... *)
      (* Idx >= k, therefore pre. for: idx - k *)
      (* Known idx < k + mid_len => idx - k < mid_len, therefore in middle in *)
      have idx_in_mid_L2: "idx - ?k < length middle" using 2 by arith

      have l2_val: "?L2 ! idx = middle ! (idx - ?k)"
        using 2 idx_in_mid_L2 by (simp add: nth_append)


      let ?idx_plus_1 = "idx + 1"
      have idx_plus_1_ge: "?idx_plus_1 \<ge> ?k + 1" using 2 by arith
      have idx_plus_1_in_mid_L1: "?idx_plus_1 - (?k + 1) < length middle"
        using 2 by arith

      have l1_val: "?L1 ! ?idx_plus_1 = middle ! (?idx_plus_1 - (?k + 1))"
        using idx_plus_1_ge idx_plus_1_in_mid_L1
        by (simp add: nth_append)

      (* 3. prove equal *)
      have "idx - ?k = ?idx_plus_1 - (?k + 1)" by arith

      show ?thesis using l2_val l1_val `idx - ?k = ?idx_plus_1 - (?k + 1)`
        by (smt (verit, ccfv_threshold) "2" leD not_less_iff_gr_or_eq)
    next
      case 3 then show ?thesis by (simp add: nth_append)
    next
      case 4 then show ?thesis by (simp add: nth_append)
    qed
  qed

  (* 4. coreprove *)
  show ?thesis
    unfolding HB_consistent_def
  proof (intro allI impI)
    fix i j
    assume valid_and_hb: "i < length ?L2 \<and> j < length ?L2 \<and> HB H (?L2 ! i) (?L2 ! j)"

    have valid_i: "i < length ?L2" using valid_and_hb by simp
    have valid_j: "j < length ?L2" using valid_and_hb by simp
    have hb_ij: "HB H (?L2 ! i) (?L2 ! j)" using valid_and_hb by simp

    (* 4.1 mapping HB L1 *)
    have hb_mapped: "HB H (?L1 ! (?f i)) (?L1 ! (?f j))"
      using hb_ij eq_nth[OF valid_i] eq_nth[OF valid_j] by simp

    (* 4.2 use L1 consistencyderive f(i) < f(j) *)
    have f_i_less_f_j: "?f i < ?f j"
    proof -
      have len_eq: "length ?L1 = length ?L2" by simp
      have v1: "?f i < length ?L1" using valid_i len_eq by (auto split: if_splits)
      have v2: "?f j < length ?L1" using valid_j len_eq by (auto split: if_splits)

      show ?thesis
        using consistent_L1[unfolded HB_consistent_def]
        using hb_mapped v1 v2
        by blast
    qed

    (* 4.3 prove i < j *)
    show "i < j"
    proof (rule ccontr)
      assume "\<not> i < j"
      hence "j \<le> i" by simp

      (* Case: is of? *)
      (* One of is: i x (k+mid), and j middle in of element (k..k+mid-1) *)
      (* Because x from before to after *)

      have "\<not> (i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len)"
      proof
        assume conflict: "i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len"
        (* At this point L2!i = x, L2!j \<in> middle *)
        let ?m = "?L2 ! j"

        (* Prove?m in middle in *)
        (* Prove *)
        have mid_idx: "j - ?k < length middle" using conflict by arith
        have m_is_mid: "?m = middle ! (j - ?k)"
          using conflict mid_idx by (simp add: nth_append)

        have "?m \<in> set middle"
          unfolding m_is_mid using mid_idx by (rule nth_mem)

        (* Premise hb_ij HB H x m *)
        (* But L2!i is x *)
        have "HB H x ?m" using hb_ij conflict by (simp add: nth_append)

        (* And not_HB_x_middle contradiction *)
        thus False using not_HB_x_middle `?m \<in> set middle` by blast
      qed

      (* If is case, mapping f this is preserve of *)
      (* : j <= i ==> f(j) <= f(i) *)
      have "j \<le> i \<Longrightarrow> \<not> (i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len) \<Longrightarrow> ?f j \<le> ?f i"
        by (auto split: if_splits)

      (* F(i) < f(j) derive a contradiction *)
      hence "?f j \<le> ?f i" using `j \<le> i` `\<not> (i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len)` by simp
      thus False using f_i_less_f_j by simp
    qed
  qed
qed


lemma TypeBT_implies_no_HB:
  assumes sys_inv: "system_invariant s"
  assumes type_bt: "TypeBT s (op_val bt_act)"
  assumes x_active: "x \<in> active_enqs s"
  assumes not_eq: "x \<noteq> bt_act"
  assumes x_is_enq: "op_name x = enq"
  assumes bt_is_enq: "op_name bt_act = enq"
  assumes bt_val_valid: "op_val bt_act \<in> Val"
  assumes val_in_sets: "op_val x \<in> SetBO s \<or> op_val x \<in> SetBT s"
  shows "\<not> HB_Act s x bt_act"
proof (rule notI) (* First step: preserve the of, onlyapply *)

  (* 1. in *)
  assume hb: "HB_Act s x bt_act"

  (* 2.: extract and local *)
  from sys_inv have hi8: "hI16_BO_BT_No_HB s" unfolding system_invariant_def by auto
  from sys_inv have hi9: "hI17_BT_BT_No_HB s" unfolding system_invariant_def by auto
  let ?v = "op_val x"
  let ?bt_v = "op_val bt_act"

  have bt_in_SetBT: "?bt_v \<in> SetBT s"
    using type_bt bt_val_valid unfolding SetBT_def by simp

  (* 3. prove HB_EnqRetCall *)
  (* Here of prove, need then extract k1 k2, from and avoid timeout *)
  have val_hb: "HB_EnqRetCall s ?v ?bt_v"
  proof -
    (* Newdefinition, HB_EnqRetCall only need in two pid HB_Act into *)
    (* We already has hb: HB_Act s x bt_act *)
    (* Only need prove x and bt_act match (mk_op enq v p) of form *)

    show ?thesis
      unfolding HB_EnqRetCall_def
      apply (rule exI[where x="op_pid x"])
      apply (rule exI[where x="op_pid bt_act"])
      using hb x_is_enq bt_is_enq
      (* Of unfold can, need of auto *)
      unfolding mk_op_def
      by (metis op_name_def op_pid_def op_val_def split_pairs)
  qed

  (* 4. use val_in_sets case *)
  (* Complete the of original, change *)
  show False
    using val_in_sets
  proof (rule disjE) (* At this point disjE val_in_sets and goal *)

    (* === Case 1: x in SetBO in === *)
    assume in_BO: "op_val x \<in> SetBO s"
    have "\<not> HB_EnqRetCall s ?v ?bt_v"
      using hi8 in_BO bt_in_SetBT unfolding hI16_BO_BT_No_HB_def by blast
    then show False using val_hb by simp

  next (* Enter one branch *)

    (* === Case 2: x in SetBT in === *)
    assume in_BT: "op_val x \<in> SetBT s"
    have "\<not> HB_EnqRetCall s ?v ?bt_v"
      using hi9 in_BT bt_in_SetBT unfolding hI17_BT_BT_No_HB_def by blast
    then show False using val_hb by simp
  qed
qed


(* ------------------------------------------------------------------------- *)
(* : in, enq operation of value in SetA \<union> SetB *)
(* ------------------------------------------------------------------------- *)
lemma lin_seq_enq_in_sets:
  assumes INV: "system_invariant s"
  assumes x_in_seq: "x \<in> set (lin_seq s)"
  assumes is_enq: "op_name x = enq"
  shows "op_val x \<in> SetA s \<union> SetB s"
proof -
  (* 1. from invariant in extract lI1_Op_Sets_Equivalence *)
  have lin_inv: "lI1_Op_Sets_Equivalence s"
    using INV unfolding system_invariant_def by auto

  (* 2. use lI1_Op_Sets_Equivalence x of sourceset *)
  have "x \<in> OPLin s"
    using x_in_seq unfolding OPLin_def by simp

  then have x_union: "x \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lin_inv unfolding lI1_Op_Sets_Equivalence_def by simp

  (* 3. OP_A_deq (, usecontradiction direct closure) *)
  have "x \<notin> OP_A_deq s"
    unfolding OP_A_deq_def using is_enq
    by simp

  then have x_source: "x \<in> OP_A_enq s \<union> OP_B_enq s"
    using x_union by blast

  (* 4. case, extract of 4 *)
  show ?thesis
  proof (cases "x \<in> OP_A_enq s")
    case True
    (* Match newdefinition of 4 (op, val, pid, sn) *)
    then obtain p a sn where "x = mk_op enq a p sn" "a \<in> SetA s"
      unfolding OP_A_enq_def by blast

    (* Extract op_val *)
    then have "op_val x = a"
      unfolding mk_op_def op_val_def by simp

    thus ?thesis using `a \<in> SetA s` by blast
  next
    case False
    (* If in OP_A_enq, thennecessarily in OP_B_enq *)
    with x_source have "x \<in> OP_B_enq s" by blast

    (* For extract OP_B_enq of 4 *)
    then obtain p b sn where "x = mk_op enq b p sn" "b \<in> SetB s"
      unfolding OP_B_enq_def by blast

    (* Extract op_val *)
    then have "op_val x = b"
      unfolding mk_op_def op_val_def by simp

    thus ?thesis using `b \<in> SetB s` by blast
  qed
qed

lemma LinSeq_Enq_State_Mapping:
  assumes INV: "system_invariant s"
  assumes a_in_seq: "a \<in> set (lin_seq s)"
  assumes is_enq: "op_name a = enq"
  assumes not_in_SetA: "op_val a \<notin> SetA s"
  shows "op_val a \<in> SetBO s \<or> op_val a \<in> SetBT s"
proof -
  (* 1. use lin_seq_enq_in_sets a of value in SetA or SetB in *)
  have val_range: "op_val a \<in> SetA s \<union> SetB s"
    using lin_seq_enq_in_sets[OF INV a_in_seq is_enq] .

  (* 2. premise op_val a \<notin> SetA s, SetA *)
  have "op_val a \<in> SetB s"
    using val_range not_in_SetA by auto

  (* 3. use SetB of (SetB = SetBO \<union> SetBT) *)
  then show ?thesis
    unfolding SetB_partition by auto
qed

lemma TypeBT_No_HB_Target:
  (* Proof note *)
  assumes INV: "system_invariant s"
  assumes L_def: "L = lin_seq s"
  assumes H_def: "H = his_seq s"

  (* Goal bt_act of property *)
  assumes bt_in_L: "bt_act \<in> set L"
  assumes bt_is_enq: "op_name bt_act = enq"
  assumes bt_is_TypeBT: "TypeBT s (op_val bt_act)"

  (* For a of property *)
  assumes a_in_L: "a \<in> set L"
  assumes a_is_enq: "op_name a = enq"
  assumes a_not_bt: "a \<noteq> bt_act"

  (* Key: a must is Active of *)
  assumes a_not_SetA: "op_val a \<notin> SetA s"

  (* Conclusion: a impossible HB bt_act *)
  shows "\<not> HB H a bt_act"
proof (rule notI)
  (* HB into *)
  assume hb_rel: "HB H a bt_act"

  (* 1. prove a of value in SetBO or SetBT in *)
  have val_in_sets: "op_val a \<in> SetBO s \<or> op_val a \<in> SetBT s"
  proof -
    (* : a in LinSeq in and is Enq -> a of value in SetA or SetB in *)
    (* Known a in SetA -> a in SetB in *)
    (* SetB = SetBO \<union> SetBT *)

    (* Here as, we use lI1_Op_Sets_Equivalence and OP definition *)
    have "op_val a \<in> SetA s \<union> SetB s"
      using INV a_in_L a_is_enq
      unfolding system_invariant_def lI1_Op_Sets_Equivalence_def OP_A_enq_def OP_B_enq_def OPLin_def L_def
      using INV lin_seq_enq_in_sets by blast

    thus ?thesis
      using a_not_SetA
      unfolding SetB_def SetBO_def SetBT_def
      by (simp add: TypeBO_def)
  qed

  (* 2. prove a is of Enq operation (a \<in> active_enqs s) *)
  have a_is_active: "a \<in> active_enqs s"
  proof -
    (* A in OPLin *)
    have "a \<in> OPLin s" using a_in_L unfolding OPLin_def L_def by simp

    (* LI1_Op_Sets_Equivalence, a in OP_A_enq, OP_A_deq, or OP_B_enq *)
    have "a \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
      using INV unfolding system_invariant_def lI1_Op_Sets_Equivalence_def
      using \<open>a \<in> OPLin s\<close> by blast

    (* A is Deq *)
    have "a \<notin> OP_A_deq s"
      using a_is_enq unfolding OP_A_deq_def mk_op_def op_name_def by auto

    (* A is OP_A_enq (becausevalue in SetA) *)
    have "a \<notin> OP_A_enq s"
      using a_not_SetA unfolding OP_A_enq_def mk_op_def op_val_def by auto

    (* Therefore a must in OP_B_enq in, active_enqs *)
    hence "a \<in> OP_B_enq s"
      using `a \<in> OPLin s` `a \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s` `a \<notin> OP_A_deq s`
      by auto

    thus ?thesis unfolding active_enqs_def .
  qed

  (* 3. prove bt_act of value has *)
  have bt_val_valid: "op_val bt_act \<in> Val"
  proof -
    (* Bt_act in OPLin and is Enq, it corresponds to has value *)
    have "op_val bt_act \<in> SetA s \<union> SetB s"
      using INV bt_in_L bt_is_enq
      unfolding system_invariant_def lI1_Op_Sets_Equivalence_def OP_A_enq_def OP_B_enq_def OPLin_def L_def
      using INV lin_seq_enq_in_sets by blast
    thus ?thesis unfolding SetA_def SetB_def by auto
  qed

  (* 4. apply TypeBT_implies_no_HB *)
  (* With before here need, now HB H a bt_act then is HB_Act of unfold *)

  have "\<not> HB_Act s a bt_act"
  proof (rule TypeBT_implies_no_HB[OF INV])
    show "TypeBT s (op_val bt_act)" using bt_is_TypeBT .
    show "a \<in> active_enqs s" using a_is_active .
    show "a \<noteq> bt_act" using a_not_bt .
    show "op_name a = enq" using a_is_enq .
    show "op_name bt_act = enq" using bt_is_enq .
    show "op_val bt_act \<in> Val" using bt_val_valid .
    show "op_val a \<in> SetBO s \<or> op_val a \<in> SetBT s" using val_in_sets .
  qed

  (* 5. derive a contradiction *)
  (* hb_rel: HB H a bt_act *)
  (* not_hb: \<not> HB_Act s a bt_act *)
  show False
    using hb_rel `\<not> HB_Act s a bt_act` H_def
    unfolding HB_Act_def
    by simp
qed



(* ========================================================== *)
(* Helper lemma: and HB of contradiction *)
(* ========================================================== *)
lemma pos_order_contra_HB:
  assumes consist: "HB_consistent L H"
  assumes valid_idx: "i < length L" "j < length L"
  assumes at_i: "L ! i = a"
  assumes at_j: "L ! j = b"
  assumes order: "i < j"
  shows "\<not> HB H b a"
proof (rule notI)
  (* 1. HB H b a into *)
  assume hb_ba: "HB H b a"

  (* 2. use HB_consistent of definition out *)
  (* HB_consistent L H \<equiv> \<forall>k1 k2. ... HB H (L!k1) (L!k2) \<longrightarrow> k1 < k2 *)
  (* K1=j, k2=i *)
  have "j < i"
    using consist hb_ba valid_idx at_i at_j
    unfolding HB_consistent_def
    by blast (* Blast k1=j, k2=i and apply *)

  (* 3. derive a contradiction *)
  thus False using order by simp
qed

lemma SetA_implies_in_SA:
  assumes sys_inv: "system_invariant s"
  assumes a_in_SetA: "a \<in> SetA s"
  shows "in_SA a (lin_seq s)"
proof -
  (* 1. from in extract lI2_Op_Cardinality *)
  (* LI2_Op_Cardinality SetA in of elementoperation of uniqueness *)
  have lI2_Op_Cardinality: "lI2_Op_Cardinality s"
    using sys_inv unfolding system_invariant_def by auto

  (* 2. lI2_Op_Cardinality of definition, property *)
  (* \<forall>a \<in> SetA s. card (EnqIdxs s a) = 1 \<and> card (DeqIdxs s a) = 1 *)
  have card_enq: "card (EnqIdxs s a) = 1"
    using lI2_Op_Cardinality a_in_SetA unfolding lI2_Op_Cardinality_def by auto

  have card_deq: "card (DeqIdxs s a) = 1"
    using lI2_Op_Cardinality a_in_SetA unfolding lI2_Op_Cardinality_def by auto

  let ?L = "lin_seq s"

  (* 3. prove find_unique_index for in Enq return Some *)
  have enq_exists: "find_unique_index (\<lambda>x. op_name x = enq \<and> op_val x = a) ?L \<noteq> None"
  proof -
    let ?P = "\<lambda>x. op_name x = enq \<and> op_val x = a"

    (* 3.1 find_indices and EnqIdxs of *)
    (* Find_indices returnlist, EnqIdxs is set. we need provelist set after equal to EnqIdxs *)
    have "set (find_indices ?P ?L) = EnqIdxs s a"
      unfolding find_indices_def EnqIdxs_def
      (* Use set_filter and set_upt listderivation as setderivation *)
      using set_filter[of "\<lambda>i. ?P (?L ! i)" "[0..<length ?L]"]
      by simp

    (* 3.2 use card = 1 derivation list length = 1 *)
    moreover have "distinct (find_indices ?P ?L)"
      unfolding find_indices_def by simp
    ultimately have "length (find_indices ?P ?L) = 1"
      using card_enq distinct_card by fastforce

    (* 3.3 as 1 find_unique_index as None *)
    thus ?thesis
      unfolding find_unique_index_def
      by (metis (mono_tags, lifting) emptyE empty_set less_one nth_mem
          option.discI)
  qed

  (* 4. prove find_unique_index for in Deq return Some () *)
  have deq_exists: "find_unique_index (\<lambda>x. op_name x = deq \<and> op_val x = a) ?L \<noteq> None"
  proof -
    let ?P = "\<lambda>x. op_name x = deq \<and> op_val x = a"

    have "set (find_indices ?P ?L) = DeqIdxs s a"
      unfolding find_indices_def DeqIdxs_def
      using set_filter[of "\<lambda>i. ?P (?L ! i)" "[0..<length ?L]"]
      by simp

    moreover have "distinct (find_indices ?P ?L)"
      unfolding find_indices_def by simp
    ultimately have "length (find_indices ?P ?L) = 1"
      using card_deq distinct_card by fastforce

    thus ?thesis
      unfolding find_unique_index_def
      by (metis (mono_tags, lifting) emptyE empty_set less_one nth_mem
          option.discI)
  qed

  (* 5. Enq and Deq of in, prove in_SA *)
  show ?thesis
    unfolding in_SA_def
    using enq_exists deq_exists
    (* Use case of unfold *)
    by (auto split: option.splits)
qed


(* ============================================================================ *)
(* Helper lemma 1: find_unique_index of only in list of Multiset *)
(* ============================================================================ *)

lemma find_unique_index_mset_eq:
  assumes "mset L1 = mset L2"
  shows "(find_unique_index P L1 \<noteq> None) \<longleftrightarrow> (find_unique_index P L2 \<noteq> None)"
proof -
  (* 1. definitionhelper lemma *)
  have aux: "find_unique_index P L \<noteq> None \<longleftrightarrow> (\<exists>i<length L. P (L ! i))" for L
    unfolding find_unique_index_def find_indices_def Let_def
    by (auto split: if_splits simp: filter_empty_conv)

  (* 2. provesetequal *)
  from assms have set_eq: "set L1 = set L2" by (metis mset_eq_setD)

  (* 3. key Proof step: 'then', and use '(rule iffI)' goal *)
  show ?thesis
  proof (rule iffI)
    (* 1: L1 -> L2 *)
    assume "find_unique_index P L1 \<noteq> None"
    then obtain i where "i < length L1" "P (L1 ! i)" using aux by blast
    then have "\<exists>a\<in>set L1. P a" using nth_mem by fastforce

    with set_eq obtain a where "a \<in> set L2" "P a" by auto
    (* For obtain of (j_props), after use, using \<open>...\<close> *)
    then obtain j where j_props: "j < length L2" "P (L2 ! j)"
      by (metis in_set_conv_nth)

    (* Here of show nowvalid, because (rule iffI) goal into "find_unique_index P L2 \<noteq> None" *)
    show "find_unique_index P L2 \<noteq> None"
      using aux j_props by auto

  next
    (* 2: L2 -> L1 *)
    assume "find_unique_index P L2 \<noteq> None"
    then obtain i where "i < length L2" "P (L2 ! i)" using aux by blast
    then have "\<exists>a\<in>set L2. P a" using nth_mem by fastforce

    with set_eq obtain a where "a \<in> set L1" "P a" by auto
    then obtain j where j_props: "j < length L1" "P (L1 ! j)"
      by (metis in_set_conv_nth)

    show "find_unique_index P L1 \<noteq> None"
      using aux j_props by auto
  qed
qed


(* New 2: in_SA in list preserve *)
lemma in_SA_mset_eq:
  assumes "mset L1 = mset L2"
  shows "in_SA v L1 \<longleftrightarrow> in_SA v L2"
proof -
  (* In_SA definition in find_unique_index of in *)
  let ?P_enq = "\<lambda>a. op_name a = enq \<and> op_val a = v"
  let ?P_deq = "\<lambda>a. op_name a = deq \<and> op_val a = v"

  have enq: "(find_unique_index ?P_enq L1 \<noteq> None) \<longleftrightarrow> (find_unique_index ?P_enq L2 \<noteq> None)"
    using find_unique_index_mset_eq[OF assms] by blast

  have deq: "(find_unique_index ?P_deq L1 \<noteq> None) \<longleftrightarrow> (find_unique_index ?P_deq L2 \<noteq> None)"
    using find_unique_index_mset_eq[OF assms] by blast

  show ?thesis
    unfolding in_SA_def
    using enq deq
    by (auto split: option.splits)
qed


lemma deq_in_l22_val_valid:
  assumes sys: "system_invariant s"
    and L_def: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
    and inv_mset: "mset L = mset (lin_seq s)"
    and d_in_l22: "d \<in> set l22"
    and l22_deqs: "\<forall>x \<in> set l22. op_name x = deq"
  shows "op_val d \<in> Val"
proof -
  (* 1. prove d in *)
  from d_in_l22 have "d \<in> set L" using L_def by auto
  then have d_in_lin: "d \<in> set (lin_seq s)"
    using inv_mset by (metis mset_eq_setD)

  (* 2. prove d is deq operation *)
  have d_is_deq: "op_name d = deq"
    using d_in_l22 l22_deqs by auto

  (* 3. use of has *)
  (* : if d in and is deq, then its value in Val *)
  show ?thesis
    using LinSeq_Deq_Val_Valid[OF sys d_in_lin d_is_deq] .
qed



lemma HB_barrier_protection:
  assumes hb_cons: "HB_consistent L H"
  and valid_idxs: "i < length L" "j < length L"
  and at_idxs: "L ! i = o1" "L ! j = d"
  and order_in_L: "i \<le> j"
  and hb_b_o1: "HB H b o1"
  and not_hb_b_bt: "\<not> HB H b bt"
  and bt_enq: "op_name bt = enq"
  and o1_deq: "op_name o1 = deq"
  shows "\<not> HB H d bt"
proof
  assume hb_d_bt: "HB H d bt"

  (* 1. of extract, unfoldall of matchdefinition *)
  from hb_d_bt obtain k1 k2 where k12:
    "k1 < k2"
    "match_ret H k1 d"
    "match_call H k2 bt"
    "k1 < length H" "k2 < length H"
    unfolding HB_def match_ret_def match_call_def
    by auto

  (* 2. for one HB similarly of operation *)
  from hb_b_o1 obtain k3 k4 where k34:
    "k3 < k4"
    "match_ret H k3 b"
    "match_call H k4 o1"
    "k3 < length H" "k4 < length H"
    unfolding HB_def match_ret_def match_call_def
    by auto

  (* 2. core derivation: prove *)
  have "k2 \<le> k3"
  proof (rule ccontr)
    assume "\<not> k2 \<le> k3"
    hence "k3 < k2" by simp
    (* If k3 < k2, then b HB bt *)
    with k34(3) k12(5) have "HB H b bt"
      unfolding HB_def
      using k12(3) k34(2) by auto
    with not_hb_b_bt show False by contradiction
  qed

  (* 3. obtain k1 < k4 *)
  hence "k1 < k4"
    using k12(1) k34(1) by linarith

  (* 4. construct HB H d o1 *)
  have "HB H d o1"
    unfolding HB_def
    using \<open>k1 < k4\<close> k12(2,4) k34(3,5) by blast

  (* 5. lastuseconsistency out contradiction *)
  hence "j < i"
    using hb_cons valid_idxs at_idxs
    unfolding HB_consistent_def by blast
  with order_in_L show False by simp
qed


lemma HB_jump_right_protection:
  assumes hb_cons: "HB_consistent L H"
  (* : d in ou before (or d then is ou) *)
  and valid_idxs: "i < length L" "j < length L"
  and at_idxs: "L ! i = d" "L ! j = ou"
  and order_in_L: "i \<le> j"
  (* HB *)
  and c4: "HB H ou bt"           (* ou -> bt *)
  and not_hb_b_bt: "\<not> HB H b bt" (* B HB bt *)
  (* Proof note *)
  and b_enq: "op_name b = enq"
  and bt_enq: "op_name bt = enq"
  and d_deq: "op_name d = deq"
  and ou_deq: "op_name ou = deq"
  shows "\<not> HB H b d"
proof
  assume hb_b_d: "HB H b d"

  (* 1. extract ou -> bt of timestamp (usenew of match_ret and match_call) *)
  obtain k_ou_ret k_bt_call where ou_bt:
    "k_ou_ret < k_bt_call"
    "match_ret H k_ou_ret ou"
    "match_call H k_bt_call bt"
    using c4 unfolding HB_def by blast

  (* 2. extract b -> d of timestamp *)
  obtain k_b_ret k_d_call where b_d:
    "k_b_ret < k_d_call"
    "match_ret H k_b_ret b"
    "match_call H k_d_call d"
    using hb_b_d unfolding HB_def by blast

  (* 3. provecorecontradiction: bt.call must in b.ret previouslyor and (bt.call \<le> b.ret) *)
  (* Then, if b.ret < bt.call, then HB definition, b necessarily HB bt, and knowncontradiction *)
  have "k_bt_call \<le> k_b_ret"
  proof (rule ccontr)
    assume "\<not> k_bt_call \<le> k_b_ret"
    hence "k_b_ret < k_bt_call" by simp

    (* Construct b -> bt of HB *)
    have "HB H b bt"
      unfolding HB_def
      using `k_b_ret < k_bt_call` b_d(2) ou_bt(3) by blast

    with not_hb_b_bt show False by contradiction
  qed

  (* 4. timestamp: k_ou_ret < k_bt_call \<le> k_b_ret < k_d_call *)
  (* From and out k_ou_ret < k_d_call *)
  have "k_ou_ret < k_d_call"
    using ou_bt(1) `k_bt_call \<le> k_b_ret` b_d(1) by linarith

  (* 5. construct ou -> d of HB *)
  (* Use match of *)
  have "HB H ou d"
    unfolding HB_def
    using `k_ou_ret < k_d_call` ou_bt(2) b_d(3) by blast

  (* 6. out contradiction *)
  (* HB_consistent, must HB *)
  (* HB H ou d ou in L in of mustless than d of (j < i) *)
  have "j < i"
    using hb_cons `HB H ou d` valid_idxs at_idxs
    unfolding HB_consistent_def by blast

  (* And premise order_in_L (i \<le> j) *)
  thus False using order_in_L by simp
qed


lemma modify_lin_structural_preservation:
  (* Fix 1: definition of precisealign *)
  defines "idx \<equiv> \<lambda>S. nat (find_last_SA S + 1)"
  shows "data_independent L \<Longrightarrow>
         take (idx L) (modify_lin L H bt_val) = take (idx L) L \<and>
         mset (drop (idx L) (modify_lin L H bt_val)) = mset (drop (idx L) L)"
proof (induct L H bt_val rule: modify_lin.induct)
  case (1 L H bt_val)
  note DI_L = "1.prems"
  (* Fix 2: local idx of precisealign *)
  let ?idx = "nat (find_last_SA L + 1)"

  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    then show ?thesis by (subst modify_lin.simps, simp)
  next
    case True
    note do_modify = True

    (* === 1. definitionlocal and decompose === *)
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define remaining where "remaining = drop ?idx L"
    define l1 where "l1 = take ?idx L"

    have L_decomp: "L = l1 @ remaining"
      unfolding l1_def remaining_def by simp

    (* Fix 3: use extract bt_idx, split *)
    have bt_in_rem: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = None" by simp
      thus False using do_modify unfolding should_modify_def Let_def remaining_def last_sa_pos_def by simp
    qed
    then obtain bt_idx where bt_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      by auto

    define l2 where "l2 = take bt_idx remaining"
    define l3 where "l3 = drop (bt_idx + 1) remaining"
    define bt_act where "bt_act = remaining ! bt_idx"
    define l2_last where "l2_last = last l2"

    have idx_valid: "bt_idx < length remaining"
      using bt_idx_def unfolding find_unique_index_def find_indices_def
      using bt_idx_def find_unique_index_prop by blast

    have rem_decomp: "remaining = l2 @ [bt_act] @ l3"
      unfolding l2_def l3_def bt_act_def using idx_valid
      by (metis Suc_eq_plus1 append.assoc append_take_drop_id take_Suc_conv_app_nth)

    have l2_not_nil: "l2 \<noteq> []"
    proof -
      (* L2 nonempty of prove, previously already *)
      (* Core: if l2 empty, bt_idx=0, but and should_modify (find_last_enq = Some) contradiction *)
      have "remaining \<noteq> []" using bt_idx_def
        using find_unique_index_Some_less_length by fastforce
      have "bt_idx \<noteq> 0"
      proof
        assume "bt_idx = 0"
        then have "l2 = []" unfolding l2_def by simp
        then have "find_last_enq l2 = None" unfolding find_last_enq_def
          using find_last_enq_def find_last_enq_props(1) neq_Nil_conv
          by fastforce
        then show False using do_modify unfolding should_modify_def l2_def remaining_def last_sa_pos_def
          using \<open>bt_idx = 0\<close> bt_idx_def remaining_def by auto
      qed
      then show ?thesis unfolding l2_def
        by (simp add: \<open>remaining \<noteq> []\<close>)
    qed

    have l2_decomp: "l2 = butlast l2 @ [l2_last]"
      unfolding l2_last_def using l2_not_nil
      by simp

    have len_l1: "length l1 = ?idx"
    proof -
      have "length remaining > 0" using idx_valid by auto
      then have "?idx \<le> length L" unfolding remaining_def by simp
      then show ?thesis unfolding l1_def by simp
    qed

    (* === 2. case === *)
    show ?thesis
    proof (cases "op_name l2_last = enq")
      case True
      (* Case A: Enq *)
      define new_L where "new_L = l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3"

      have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
        unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
        using bt_idx_def do_modify True
        apply (subst modify_lin.simps)
        apply (simp only: Let_def case_prod_unfold)
        apply (subst if_not_P, simp)
        by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def new_L_def
            remaining_def)

      have mset_new: "mset new_L = mset L"
        unfolding new_L_def using L_decomp rem_decomp l2_decomp
        by (metis case1 l2_last_def l2_not_nil)

      have len_eq: "length new_L = length L" using mset_new by (metis mset_eq_length)

      have DI_new: "data_independent new_L"
        using DI_L mset_new using "1.prems" data_independent_cong by blast

      have prefix_eq: "take ?idx new_L = take ?idx L"
        unfolding new_L_def using len_l1 unfolding l1_def by simp

      have sa_stable: "find_last_SA new_L = find_last_SA L"
      proof (rule find_last_SA_stable_prefix[OF len_eq prefix_eq])
        show "\<forall>i\<in>{?idx..<length L}. \<not> (op_name (L ! i) = enq \<and> in_SA (op_val (L ! i)) L)"
        proof -
          have "remaining \<noteq> []" using idx_valid by auto
          have "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
            apply (rule l1_contains_all_SA_in_L[OF DI_L L_decomp `remaining \<noteq> []`])
            using l1_def last_sa_pos_def len_l1 apply simp
            using last_sa_pos_def apply simp done
          then show ?thesis using len_l1 by auto
        qed

        show "\<forall>i\<in>{?idx..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
        proof -
          have mset_suffix_eq: "mset (drop ?idx new_L) = mset (drop ?idx L)"
            by (metis append_take_drop_id mset_append mset_new prefix_eq add_left_cancel)
          have set_eq: "set (drop ?idx new_L) = set (drop ?idx L)"
            using mset_suffix_eq by (metis set_mset_mset)

          { fix i assume i_range: "i \<in> {?idx..<length new_L}"
            let ?x = "new_L ! i"
            have "?x \<in> set (drop ?idx new_L)"
            proof -
              let ?k = "i - ?idx"
              have "?k < length (drop ?idx new_L)"
                using i_range
                by (simp add: diff_less_mono)

              have "(drop ?idx new_L) ! ?k = ?x"
                using i_range by simp

              then show ?thesis
                using `?k < length (drop ?idx new_L)`
                by (metis in_set_conv_nth)
            qed
            then have "?x \<in> set (drop ?idx L)" using set_eq by blast

            obtain j where j_props: "j < length (drop ?idx L)" "(drop ?idx L) ! j = ?x"
              using `?x \<in> set (drop ?idx L)` by (auto simp: in_set_conv_nth)

            let ?k = "?idx + j"

            have k_bounds: "?k \<ge> ?idx" "?k < length L"
              using j_props(1) by auto

            have k_val: "L ! ?k = ?x"
              using j_props
              by (metis L_decomp len_l1 nth_append_length_plus remaining_def)

            then obtain k where k_props: "k \<ge> ?idx" "k < length L" "L ! k = ?x"
              using k_bounds k_val by blast

            have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) L)"
            proof -

              have "remaining \<noteq> []" using idx_valid by auto

              have global_prop: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
                apply (rule l1_contains_all_SA_in_L)
                using DI_L
                using "1.prems" apply blast
                using L_decomp apply simp       (* L = l1 @ remaining *)
                using `remaining \<noteq> []` apply simp (* Suffix nonempty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* L1 definition match *)
                using last_sa_pos_def apply simp (* Last_sa_pos definition match *)
                done

              show ?thesis
                using global_prop k_props len_l1
                by auto
            qed

            (* In_SA equivalence *)
            then have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) new_L)"
               using in_SA_def
               using in_SA_mset_eq mset_new by blast
          }

          then show ?thesis by blast
        qed

        show "\<forall>v. in_SA v new_L = in_SA v L"
          using in_SA_def using in_SA_mset_eq mset_new by blast
      qed

      have suffix_mset: "mset (drop ?idx new_L) = mset (drop ?idx L)"
         using mset_new prefix_eq by (metis add_left_cancel append_take_drop_id mset_append)

      (* Fix 5: use 1.IH, *)
      have IH_res: "take (idx new_L) (modify_lin new_L H bt_val) = take (idx new_L) new_L \<and>
                    mset (drop (idx new_L) (modify_lin new_L H bt_val)) = mset (drop (idx new_L) new_L)"
        using do_modify DI_new True bt_idx_def
        unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        by (metis (no_types, lifting) "1.hyps"(1) option.sel)

      moreover have "mset (drop (idx L) (modify_lin L H bt_val)) = mset (drop (idx L) L)"
      proof -
        have "mset (drop (idx L) (modify_lin L H bt_val)) = mset (drop (idx L) (modify_lin new_L H bt_val))"
          using mod_eq by simp
        also have "... = mset (drop (idx new_L) (modify_lin new_L H bt_val))"
          using sa_stable idx_def by simp
        also have "... = mset (drop (idx new_L) new_L)"
          using IH_res by simp
        also have "... = mset (drop (idx L) new_L)"
          using sa_stable idx_def by simp
        also have "... = mset (drop (idx L) L)"
          using suffix_mset idx_def by simp
        finally show ?thesis .
      qed

      ultimately show ?thesis
        by (metis idx_def mod_eq prefix_eq sa_stable)

    next
      case False
      note not_enq = False

      have find_enq_valid: "find_last_enq l2 \<noteq> None"
        using do_modify False l2_not_nil
        unfolding should_modify_def l2_def remaining_def last_sa_pos_def l2_last_def
        using bt_idx_def
        by (smt (verit) option.simps(4,5) remaining_def)

      obtain l21 b_act l22 where l2_split: "find_last_enq l2 = Some (l21, b_act, l22)"
        using find_enq_valid by (cases "find_last_enq l2", auto)

      define o1 where "o1 = hd l22"
      define ou where "ou = last l22"

      have l2_full_decomp: "l2 = l21 @ [b_act] @ l22"
        by (meson find_last_enq_props(1) l2_split)

      have l22_not_nil: "l22 \<noteq> []"
        using do_modify not_enq l2_last_def l2_split l2_not_nil
        unfolding find_last_enq_def using l2_def remaining_def
        by (metis find_last_enq_props(2) l2_full_decomp l2_split last_snoc self_append_conv)

(* --- key: use consider 3 IF case, precisematchnew --- *)
      consider
          (c1) "happens_before o1 bt_act H"
        | (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H"
        | (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast

      then show ?thesis
      proof cases
        case c1
        (* === original the of c1 prove === *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c1 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def last_sa_pos_def new_L_def remaining_def)

        have mset_new: "mset new_L = mset L"
        proof -
          have "mset L = mset l1 + mset l2 + {#bt_act#} + mset l3"
            using L_decomp rem_decomp by (simp add: ac_simps)
          also have "... = mset l1 + (mset l21 + {#b_act#} + mset l22) + {#bt_act#} + mset l3"
            using l2_full_decomp by (simp add: ac_simps)
          also have "... = mset l1 + mset l21 + mset l22 + {#b_act#} + {#bt_act#} + mset l3"
            by (simp add: ac_simps)
          also have "... = mset new_L"
            unfolding new_L_def
            by (metis calculation mod_eq modify_preserves_mset new_L_def)
          finally show ?thesis by simp
        qed

        have len_eq: "length new_L = length L" using mset_new by (metis mset_eq_length)
        have DI_new: "data_independent new_L" using DI_L mset_new using "1.prems" data_independent_cong by blast
        have prefix_eq: "take ?idx new_L = take ?idx L" unfolding new_L_def using len_l1 unfolding l1_def by simp

        have sa_stable: "find_last_SA new_L = find_last_SA L"
        proof (rule find_last_SA_stable_prefix[OF len_eq prefix_eq])
          show "\<forall>i\<in>{?idx..<length L}. \<not> (op_name (L ! i) = enq \<and> in_SA (op_val (L ! i)) L)"
          proof -
             have "remaining \<noteq> []" using idx_valid by auto
             have "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
               apply (rule l1_contains_all_SA_in_L[OF DI_L L_decomp `remaining \<noteq> []`])
               using l1_def last_sa_pos_def len_l1 apply simp
               using last_sa_pos_def apply simp done
             then show ?thesis using len_l1 by auto
          qed

          show "\<forall>i\<in>{?idx..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
          proof -
            have mset_suffix_eq: "mset (drop ?idx new_L) = mset (drop ?idx L)"
              by (metis append_take_drop_id mset_append mset_new prefix_eq add_left_cancel)
            have set_eq: "set (drop ?idx new_L) = set (drop ?idx L)"
              using mset_suffix_eq by (metis set_mset_mset)

          { fix i assume i_range: "i \<in> {?idx..<length new_L}"
            let ?x = "new_L ! i"
            have "?x \<in> set (drop ?idx new_L)"
            proof -
              let ?k = "i - ?idx"
              have "?k < length (drop ?idx new_L)"
                using i_range
                by (simp add: diff_less_mono)

              have "(drop ?idx new_L) ! ?k = ?x"
                using i_range by simp

              then show ?thesis
                using `?k < length (drop ?idx new_L)`
                by (metis in_set_conv_nth)
            qed
            then have "?x \<in> set (drop ?idx L)" using set_eq by blast

            obtain j where j_props: "j < length (drop ?idx L)" "(drop ?idx L) ! j = ?x"
              using `?x \<in> set (drop ?idx L)` by (auto simp: in_set_conv_nth)

            let ?k = "?idx + j"
            have k_bounds: "?k \<ge> ?idx" "?k < length L"
              using j_props(1) by auto

            have k_val: "L ! ?k = ?x"
              using j_props
              by (metis L_decomp len_l1 nth_append_length_plus remaining_def)

            then obtain k where k_props: "k \<ge> ?idx" "k < length L" "L ! k = ?x"
              using k_bounds k_val by blast

            have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) L)"
            proof -
              have "remaining \<noteq> []" using idx_valid by auto
              have global_prop: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
                apply (rule l1_contains_all_SA_in_L)
                using DI_L
                using "1.prems" apply blast
                using L_decomp apply simp       (* L = l1 @ remaining *)
                using `remaining \<noteq> []` apply simp (* Suffix nonempty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* L1 definition match *)
                using last_sa_pos_def apply simp (* Last_sa_pos definition match *)
                done

              show ?thesis
                using global_prop k_props len_l1
                by auto
            qed

            (* In_SA equivalence *)
            then have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) new_L)"
               using in_SA_def
               using in_SA_mset_eq mset_new by blast
          }
            then show ?thesis by blast
          qed

          show "\<forall>v. in_SA v new_L = in_SA v L"
            using in_SA_def in_SA_mset_eq mset_new by blast
        qed

        have struct_pres: "take (nat (last_sa_pos + 1)) new_L = l1 \<and> mset (drop (nat (last_sa_pos + 1)) new_L) = mset (drop (nat (last_sa_pos + 1)) L)"
        proof -
          have pref: "take (nat (last_sa_pos + 1)) new_L = l1"
            unfolding new_L_def using len_l1 by (simp add: last_sa_pos_def)
          have suff: "mset (drop (nat (last_sa_pos + 1)) new_L) = mset remaining"
          proof -
             have "remaining = l2 @ [bt_act] @ l3"
               using bt_idx_def idx_valid l2_def l3_def bt_act_def by (simp add: id_take_nth_drop)
             moreover have "l2 = l21 @ [b_act] @ l22"
               using l2_split find_last_enq_props(1) l2_full_decomp by blast
             moreover have "l22 = o1 # tl l22"
               using l22_not_nil o1_def by (cases l22) auto
             ultimately have rem_mset: "mset remaining = mset (l21 @ [b_act] @ [o1] @ tl l22 @ [bt_act] @ l3)"
               by (metis append.left_neutral append_Cons append_assoc)
             have len_check: "length l1 = (nat (last_sa_pos + 1))"
               using len_l1 last_sa_pos_def by fastforce
             have drop_res: "drop (nat (last_sa_pos + 1)) new_L = l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"
             proof -
               have len_match: "(nat (last_sa_pos + 1)) = length l1" using len_check by simp
               show ?thesis unfolding new_L_def unfolding len_match [symmetric] using len_match by auto
             qed
             show ?thesis unfolding drop_res using rem_mset by (simp add: ac_simps)
          qed
          show ?thesis using pref suff unfolding remaining_def last_sa_pos_def by auto
        qed

        have idx_eq: "idx new_L = idx L" unfolding idx_def using sa_stable by simp

        have IH_res: "take (idx new_L) (modify_lin new_L H bt_val) = take (idx new_L) new_L \<and>
                      mset (drop (idx new_L) (modify_lin new_L H bt_val)) = mset (drop (idx new_L) new_L)"
          using do_modify DI_new c1 l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (no_types, lifting) "1.hyps"(2) l2_def l2_last_def not_enq
              option.sel remaining_def)

        show ?thesis
          using mod_eq IH_res idx_eq struct_pres
          unfolding idx_def last_sa_pos_def l1_def by argo

      next
        case c2
        (* === original the of c2 prove === *)
        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"

        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c2 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def last_sa_pos_def new_L_def remaining_def)

        have mset_new: "mset new_L = mset L"
        proof -
          have "mset L = mset l1 + mset l2 + {#bt_act#} + mset l3"
            using L_decomp rem_decomp by (simp add: ac_simps)
          also have "... = mset l1 + (mset l21 + {#b_act#} + mset l22) + {#bt_act#} + mset l3"
            using l2_full_decomp by (simp add: ac_simps)
          also have "... = mset l1 + mset l21 + mset l22 + {#b_act#} + {#bt_act#} + mset l3"
            by (simp add: ac_simps)
          also have "... = mset new_L"
            unfolding new_L_def by (simp add: ac_simps)
          finally show ?thesis by simp
        qed

        have len_eq: "length new_L = length L" using mset_new by (metis mset_eq_length)
        have DI_new: "data_independent new_L" using DI_L mset_new using "1.prems" data_independent_cong by blast
        have prefix_eq: "take ?idx new_L = take ?idx L" unfolding new_L_def using len_l1 unfolding l1_def by simp

        have sa_stable: "find_last_SA new_L = find_last_SA L"
        proof (rule find_last_SA_stable_prefix[OF len_eq prefix_eq])
          show "\<forall>i\<in>{?idx..<length L}. \<not> (op_name (L ! i) = enq \<and> in_SA (op_val (L ! i)) L)"
          proof -
             have "remaining \<noteq> []" using idx_valid by auto
             have "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
               apply (rule l1_contains_all_SA_in_L[OF DI_L L_decomp `remaining \<noteq> []`])
               using l1_def last_sa_pos_def len_l1 apply simp
               using last_sa_pos_def apply simp done
             then show ?thesis using len_l1 by auto
          qed

          show "\<forall>i\<in>{?idx..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
          proof -
            have mset_suffix_eq: "mset (drop ?idx new_L) = mset (drop ?idx L)"
              by (metis append_take_drop_id mset_append mset_new prefix_eq add_left_cancel)
            have set_eq: "set (drop ?idx new_L) = set (drop ?idx L)"
              using mset_suffix_eq by (metis set_mset_mset)

          { fix i assume i_range: "i \<in> {?idx..<length new_L}"
            let ?x = "new_L ! i"
            have "?x \<in> set (drop ?idx new_L)"
            proof -
              let ?k = "i - ?idx"
              have "?k < length (drop ?idx new_L)"
                using i_range
                by (simp add: diff_less_mono)

              have "(drop ?idx new_L) ! ?k = ?x"
                using i_range by simp

              then show ?thesis
                using `?k < length (drop ?idx new_L)`
                by (metis in_set_conv_nth)
            qed
            then have "?x \<in> set (drop ?idx L)" using set_eq by blast

            obtain j where j_props: "j < length (drop ?idx L)" "(drop ?idx L) ! j = ?x"
              using `?x \<in> set (drop ?idx L)` by (auto simp: in_set_conv_nth)

            let ?k = "?idx + j"
            have k_bounds: "?k \<ge> ?idx" "?k < length L"
              using j_props(1) by auto

            have k_val: "L ! ?k = ?x"
              using j_props
              by (metis L_decomp len_l1 nth_append_length_plus remaining_def)

            then obtain k where k_props: "k \<ge> ?idx" "k < length L" "L ! k = ?x"
              using k_bounds k_val by blast

            have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) L)"
            proof -
              have "remaining \<noteq> []" using idx_valid by auto
              have global_prop: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
                apply (rule l1_contains_all_SA_in_L)
                using DI_L
                using "1.prems" apply blast
                using L_decomp apply simp       (* L = l1 @ remaining *)
                using `remaining \<noteq> []` apply simp (* Suffix nonempty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* L1 definition match *)
                using last_sa_pos_def apply simp (* Last_sa_pos definition match *)
                done

              show ?thesis
                using global_prop k_props len_l1
                by auto
            qed

            (* In_SA equivalence *)
            then have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) new_L)"
               using in_SA_def
               using in_SA_mset_eq mset_new by blast
          }
            then show ?thesis by blast
          qed

          show "\<forall>v. in_SA v new_L = in_SA v L"
            using in_SA_def in_SA_mset_eq mset_new by blast
        qed

        have struct_pres: "take (nat (last_sa_pos + 1)) new_L = l1 \<and> mset (drop (nat (last_sa_pos + 1)) new_L) = mset (drop (nat (last_sa_pos + 1)) L)"
        proof -
          have pref: "take (nat (last_sa_pos + 1)) new_L = l1"
            unfolding new_L_def using len_l1 by (simp add: last_sa_pos_def)
          have suff: "mset (drop (nat (last_sa_pos + 1)) new_L) = mset remaining"
          proof -
             have "remaining = l2 @ [bt_act] @ l3"
               using bt_idx_def idx_valid l2_def l3_def bt_act_def by (simp add: id_take_nth_drop)
             moreover have "l2 = l21 @ [b_act] @ l22"
               using l2_split find_last_enq_props(1) l2_full_decomp by blast
             ultimately have rem_mset: "mset remaining = mset (l21 @ [b_act] @ l22 @ [bt_act] @ l3)"
               by auto
             have len_check: "length l1 = (nat (last_sa_pos + 1))"
               using len_l1 last_sa_pos_def by fastforce
             have drop_res: "drop (nat (last_sa_pos + 1)) new_L = l21 @ [bt_act] @ [b_act] @ l22 @ l3"
             proof -
               have len_match: "(nat (last_sa_pos + 1)) = length l1" using len_check by simp
               show ?thesis unfolding new_L_def unfolding len_match [symmetric] using len_match by auto
             qed
             show ?thesis unfolding drop_res using rem_mset by (simp add: ac_simps)
          qed
          show ?thesis using pref suff unfolding remaining_def last_sa_pos_def by auto
        qed

        have idx_eq: "idx new_L = idx L" unfolding idx_def using sa_stable by simp

        have IH_res: "take (idx new_L) (modify_lin new_L H bt_val) = take (idx new_L) new_L \<and>
                      mset (drop (idx new_L) (modify_lin new_L H bt_val)) = mset (drop (idx new_L) new_L)"
          using do_modify DI_new c2 l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (lifting) "1.hyps"(3) l2_def l2_last_def not_enq option.sel
              remaining_def)

        show ?thesis
          using mod_eq IH_res idx_eq struct_pres
          unfolding idx_def last_sa_pos_def l1_def by argo

      next
        case c3
        (* === new of c3 branchprove (and c1) === *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c3 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def last_sa_pos_def new_L_def remaining_def)

        have mset_new: "mset new_L = mset L"
        proof -
          have "mset L = mset l1 + mset l2 + {#bt_act#} + mset l3"
            using L_decomp rem_decomp by (simp add: ac_simps)
          also have "... = mset l1 + (mset l21 + {#b_act#} + mset l22) + {#bt_act#} + mset l3"
            using l2_full_decomp by (simp add: ac_simps)
          also have "... = mset l1 + mset l21 + mset l22 + {#b_act#} + {#bt_act#} + mset l3"
            by (simp add: ac_simps)
          also have "... = mset new_L"
            unfolding new_L_def
            by (metis calculation mod_eq modify_preserves_mset new_L_def)
          finally show ?thesis by simp
        qed

        have len_eq: "length new_L = length L" using mset_new by (metis mset_eq_length)
        have DI_new: "data_independent new_L" using DI_L mset_new using "1.prems" data_independent_cong by blast
        have prefix_eq: "take ?idx new_L = take ?idx L" unfolding new_L_def using len_l1 unfolding l1_def by simp

        have sa_stable: "find_last_SA new_L = find_last_SA L"
        proof (rule find_last_SA_stable_prefix[OF len_eq prefix_eq])
          show "\<forall>i\<in>{?idx..<length L}. \<not> (op_name (L ! i) = enq \<and> in_SA (op_val (L ! i)) L)"
          proof -
             have "remaining \<noteq> []" using idx_valid by auto
             have "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
               apply (rule l1_contains_all_SA_in_L[OF DI_L L_decomp `remaining \<noteq> []`])
               using l1_def last_sa_pos_def len_l1 apply simp
               using last_sa_pos_def apply simp done
             then show ?thesis using len_l1 by auto
          qed

          show "\<forall>i\<in>{?idx..<length new_L}. \<not> (op_name (new_L ! i) = enq \<and> in_SA (op_val (new_L ! i)) new_L)"
          proof -
            have mset_suffix_eq: "mset (drop ?idx new_L) = mset (drop ?idx L)"
              by (metis append_take_drop_id mset_append mset_new prefix_eq add_left_cancel)
            have set_eq: "set (drop ?idx new_L) = set (drop ?idx L)"
              using mset_suffix_eq by (metis set_mset_mset)

          { fix i assume i_range: "i \<in> {?idx..<length new_L}"
            let ?x = "new_L ! i"
            have "?x \<in> set (drop ?idx new_L)"
            proof -
              let ?k = "i - ?idx"
              have "?k < length (drop ?idx new_L)"
                using i_range
                by (simp add: diff_less_mono)

              have "(drop ?idx new_L) ! ?k = ?x"
                using i_range by simp

              then show ?thesis
                using `?k < length (drop ?idx new_L)`
                by (metis in_set_conv_nth)
            qed
            then have "?x \<in> set (drop ?idx L)" using set_eq by blast

            obtain j where j_props: "j < length (drop ?idx L)" "(drop ?idx L) ! j = ?x"
              using `?x \<in> set (drop ?idx L)` by (auto simp: in_set_conv_nth)

            let ?k = "?idx + j"
            have k_bounds: "?k \<ge> ?idx" "?k < length L"
              using j_props(1) by auto

            have k_val: "L ! ?k = ?x"
              using j_props
              by (metis L_decomp len_l1 nth_append_length_plus remaining_def)

            then obtain k where k_props: "k \<ge> ?idx" "k < length L" "L ! k = ?x"
              using k_bounds k_val by blast

            have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) L)"
            proof -
              have "remaining \<noteq> []" using idx_valid by auto
              have global_prop: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> \<not> in_SA (op_val (L ! i)) L"
                apply (rule l1_contains_all_SA_in_L)
                using DI_L
                using "1.prems" apply blast
                using L_decomp apply simp       (* L = l1 @ remaining *)
                using `remaining \<noteq> []` apply simp (* Suffix nonempty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* L1 definition match *)
                using last_sa_pos_def apply simp (* Last_sa_pos definition match *)
                done

              show ?thesis
                using global_prop k_props len_l1
                by auto
            qed

            (* In_SA equivalence *)
            then have "\<not> (op_name ?x = enq \<and> in_SA (op_val ?x) new_L)"
               using in_SA_def
               using in_SA_mset_eq mset_new by blast
          }
            then show ?thesis by blast
          qed

          show "\<forall>v. in_SA v new_L = in_SA v L"
            using in_SA_def in_SA_mset_eq mset_new by blast
        qed

        have struct_pres: "take (nat (last_sa_pos + 1)) new_L = l1 \<and> mset (drop (nat (last_sa_pos + 1)) new_L) = mset (drop (nat (last_sa_pos + 1)) L)"
        proof -
          have pref: "take (nat (last_sa_pos + 1)) new_L = l1"
            unfolding new_L_def using len_l1 by (simp add: last_sa_pos_def)
          have suff: "mset (drop (nat (last_sa_pos + 1)) new_L) = mset remaining"
          proof -
             have "remaining = l2 @ [bt_act] @ l3"
               using bt_idx_def idx_valid l2_def l3_def bt_act_def by (simp add: id_take_nth_drop)
             moreover have "l2 = l21 @ [b_act] @ l22"
               using l2_split find_last_enq_props(1) l2_full_decomp by blast
             moreover have "l22 = o1 # tl l22"
               using l22_not_nil o1_def by (cases l22) auto
             ultimately have rem_mset: "mset remaining = mset (l21 @ [b_act] @ [o1] @ tl l22 @ [bt_act] @ l3)"
               by (metis append.left_neutral append_Cons append_assoc)
             have len_check: "length l1 = (nat (last_sa_pos + 1))"
               using len_l1 last_sa_pos_def by fastforce
             have drop_res: "drop (nat (last_sa_pos + 1)) new_L = l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"
             proof -
               have len_match: "(nat (last_sa_pos + 1)) = length l1" using len_check by simp
               show ?thesis unfolding new_L_def unfolding len_match [symmetric] using len_match by auto
             qed
             show ?thesis unfolding drop_res using rem_mset by (simp add: ac_simps)
          qed
          show ?thesis using pref suff unfolding remaining_def last_sa_pos_def by auto
        qed

        have idx_eq: "idx new_L = idx L" unfolding idx_def using sa_stable by simp

        (* Note: here use of from "1.hyps"(2) into "1.hyps"(4) *)
        have IH_res: "take (idx new_L) (modify_lin new_L H bt_val) = take (idx new_L) new_L \<and>
                      mset (drop (idx new_L) (modify_lin new_L H bt_val)) = mset (drop (idx new_L) new_L)"
          using do_modify DI_new c3 l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (no_types, lifting) "1.hyps"(4) l2_def l2_last_def not_enq
              option.sel remaining_def)

        show ?thesis
          using mod_eq IH_res idx_eq struct_pres
          unfolding idx_def last_sa_pos_def l1_def by argo
      qed
    qed
  qed
qed

lemma modify_lin_preserves_orders:
  shows "filter (\<lambda>x. op_name x = enq \<and> op_val x \<noteq> bt_val) (modify_lin L H bt_val) =
         filter (\<lambda>x. op_name x = enq \<and> op_val x \<noteq> bt_val) L \<and>
         filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) (modify_lin L H bt_val) =
         filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) L"
proof (induct L H bt_val rule: modify_lin.induct)
  case (1 L H bt_val)
  (* Definition, *)
  let ?P_enq = "\<lambda>x. op_name x = enq \<and> op_val x \<noteq> bt_val"
  let ?P_deq = "\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val"

  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    then show ?thesis by (subst modify_lin.simps, simp)
  next
    case True
    note do_modify = True

    (* --- fix 1: align of --- *)
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define l1 where "l1 = take (nat (last_sa_pos + 1)) L"
    define remaining where "remaining = drop (nat (last_sa_pos + 1)) L"

    (* Fix 2: , avoid metis timeout *)
    have bt_in_rem: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = None" by simp
      thus False using do_modify unfolding should_modify_def Let_def remaining_def last_sa_pos_def by simp
    qed
    then obtain bt_idx where bt_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      by auto

    have bt_idx_valid: "bt_idx < length remaining"
      using bt_idx_def by (rule find_unique_index_Some_less_length)

    define l2 where "l2 = take bt_idx remaining"
    define l3 where "l3 = drop (bt_idx + 1) remaining"
    define bt_act where "bt_act = remaining ! bt_idx"
    define l2_last where "l2_last = last l2"

    (* Key: bt_act in two in all be *)
    have not_P_bt: "\<not> ?P_enq bt_act \<and> \<not> ?P_deq bt_act"
      unfolding bt_act_def using bt_idx_def find_unique_index_prop by auto

    have bt_gone_enq: "filter ?P_enq [bt_act] = []" using not_P_bt by simp
    have bt_gone_deq: "filter ?P_deq [bt_act] = []" using not_P_bt by simp

    (* Extract L of *)
    have remaining_eq: "remaining = l2 @ [bt_act] @ l3"
      using bt_idx_valid l2_def l3_def bt_act_def Cons_nth_drop_Suc by fastforce
    have L_struct: "L = l1 @ l2 @ [bt_act] @ l3"
      unfolding l1_def remaining_def using remaining_eq append_take_drop_id
      by (metis remaining_def)

    have l2_not_nil: "l2 \<noteq> []"
    proof (cases "l2 = []")
      case True
      have "remaining \<noteq> []"
        using bt_idx_def
        using bt_idx_valid by auto
      have "bt_idx = 0"
        using True l2_def `remaining \<noteq> []` by (metis take_eq_Nil)
      have False
        using do_modify unfolding should_modify_def find_last_enq_def last_sa_pos_def remaining_def l1_def l2_def
        using `bt_idx = 0` bt_idx_def True by (simp add: last_sa_pos_def remaining_def)
      then show ?thesis ..
    next
      case False then show ?thesis by simp
    qed

    show ?thesis
    proof (cases "op_name l2_last = enq")
      case True (* Case A: Enq branch *)
      define new_L where "new_L = l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3"

      have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
        unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
        using bt_idx_def do_modify True
        apply (subst modify_lin.simps)
        apply (simp only: Let_def case_prod_unfold)
        apply (subst if_not_P, simp)
        by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
            last_sa_pos_def new_L_def remaining_def)

      (* Extract L and new_L of *)
      have l2_struct: "l2 = butlast l2 @ [l2_last]" using l2_not_nil l2_last_def by simp
      have L_full: "L = l1 @ butlast l2 @ [l2_last] @ [bt_act] @ l3" using L_struct l2_struct by simp

      (* Fix 4: use simp direct closure filter, smt *)
      have filter_eq_enq: "filter ?P_enq new_L = filter ?P_enq L"
        unfolding new_L_def L_full using bt_gone_enq
        by force

      have filter_eq_deq: "filter ?P_deq new_L = filter ?P_deq L"
        unfolding new_L_def L_full using bt_gone_deq
        by force

      (* Fix 5: use of 1.IH *)
      have IH_res: "filter ?P_enq (modify_lin new_L H bt_val) = filter ?P_enq new_L \<and>
                    filter ?P_deq (modify_lin new_L H bt_val) = filter ?P_deq new_L"
        using  do_modify True bt_idx_def
        unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        by (metis (lifting) "1.hyps"(1) option.sel)

      show ?thesis using mod_eq filter_eq_enq filter_eq_deq IH_res
        by presburger

next
      case False (* Case B: Else branch *)
      note not_enq = False

      have find_enq_valid: "find_last_enq l2 \<noteq> None"
        using do_modify False l2_not_nil
        unfolding should_modify_def l2_def remaining_def last_sa_pos_def l2_last_def
        using bt_idx_def
        by (smt (verit) last_sa_pos_def option.simps(4,5) remaining_def)

      obtain l21 b_act l22 where l2_split: "find_last_enq l2 = Some (l21, b_act, l22)"
        using find_enq_valid by (cases "find_last_enq l2", auto)

      define o1 where "o1 = hd l22"

      have l2_struct: "l2 = l21 @ [b_act] @ l22" using find_last_enq_props(1) l2_split by blast
      have L_full_base: "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3" using L_struct l2_struct by simp

      have l22_not_nil: "l22 \<noteq> []"
        using do_modify not_enq l2_last_def l2_split l2_not_nil unfolding find_last_enq_def
        using l2_def remaining_def by (metis find_last_enq_props(1,2) l2_split last_snoc self_append_conv)

      have l22_all_deq: "\<forall>x \<in> set l22. op_name x = deq" using l22_are_all_deq[OF l2_split l22_not_nil] .
      have b_act_enq: "op_name b_act = enq" using find_last_enq_props(2) l2_split by auto
      have o1_deq: "op_name o1 = deq" using l22_all_deq l22_not_nil o1_def by auto

      (* All be of element *)
      have b_act_gone_deq: "filter ?P_deq [b_act] = []" using b_act_enq by simp
      have l22_gone_enq: "filter ?P_enq l22 = []" using l22_all_deq by (auto simp: filter_empty_conv)
      have o1_gone_enq: "filter ?P_enq [o1] = []" using o1_deq by simp

      (* --- newversion 3 branch --- *)
      consider
          (c1) "happens_before o1 bt_act H"
        | (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H"
        | (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast

      then show ?thesis
      proof cases
        (* === subcase 1: o1 -> bt_act === *)
        case c1
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c1 False do_modify o1_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def last_sa_pos_def new_L_def remaining_def)

        have l22_struct: "l22 = o1 # tl l22" using l22_not_nil o1_def by (cases l22) auto
        have L_full: "L = l1 @ l21 @ [b_act] @ [o1] @ tl l22 @ [bt_act] @ l3" using L_full_base l22_struct by simp

        have filter_eq_enq: "filter ?P_enq new_L = filter ?P_enq L"
          unfolding new_L_def L_full using bt_gone_enq o1_gone_enq
          by auto
        have filter_eq_deq: "filter ?P_deq new_L = filter ?P_deq L"
          unfolding new_L_def L_full using bt_gone_deq b_act_gone_deq
          by fastforce

        have IH_res: "filter ?P_enq (modify_lin new_L H bt_val) = filter ?P_enq new_L \<and> filter ?P_deq (modify_lin new_L H bt_val) = filter ?P_deq new_L"
          using do_modify False c1 l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def
          by (metis (lifting) "1.hyps"(2) option.sel)

        show ?thesis using mod_eq filter_eq_enq filter_eq_deq IH_res
          by argo

      next
        (* === subcase 2: b_act -> o1 === *)
        case c2
        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"

        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c2 False do_modify o1_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def last_sa_pos_def new_L_def remaining_def)

        have filter_eq_enq: "filter ?P_enq new_L = filter ?P_enq L"
          unfolding new_L_def L_full_base using bt_gone_enq
          by fastforce
        have filter_eq_deq: "filter ?P_deq new_L = filter ?P_deq L"
          unfolding new_L_def L_full_base using bt_gone_deq
          by auto

        have IH_res: "filter ?P_enq (modify_lin new_L H bt_val) = filter ?P_enq new_L \<and> filter ?P_deq (modify_lin new_L H bt_val) = filter ?P_deq new_L"
          using do_modify False c2 l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def
          by (metis (lifting) "1.hyps"(3) option.sel)

        show ?thesis using mod_eq filter_eq_enq filter_eq_deq IH_res
          by presburger

      next
        (* === subcase 3: newbranch (use c1) === *)
        case c3
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c3 False do_modify o1_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def last_sa_pos_def new_L_def remaining_def)

        have l22_struct: "l22 = o1 # tl l22" using l22_not_nil o1_def by (cases l22) auto
        have L_full: "L = l1 @ l21 @ [b_act] @ [o1] @ tl l22 @ [bt_act] @ l3" using L_full_base l22_struct by simp

        have filter_eq_enq: "filter ?P_enq new_L = filter ?P_enq L"
          unfolding new_L_def L_full using bt_gone_enq o1_gone_enq
          by fastforce
        have filter_eq_deq: "filter ?P_deq new_L = filter ?P_deq L"
          unfolding new_L_def L_full using bt_gone_deq b_act_gone_deq
          by fastforce

        (* Note: here use 1.hyps(4) corresponds tonewbranch *)
        have IH_res: "filter ?P_enq (modify_lin new_L H bt_val) = filter ?P_enq new_L \<and> filter ?P_deq (modify_lin new_L H bt_val) = filter ?P_deq new_L"
          using do_modify False c3 l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def
          by (metis (lifting) "1.hyps"(4) option.sel)

        show ?thesis using mod_eq filter_eq_enq filter_eq_deq IH_res by simp
      qed
    qed
  qed
qed


(* ----------------------------------------------------------------- *)
(* Modify_lin preserve lI5_SA_Prefix (synchronizeprefixcomplete) of final stepprove *)
(* ----------------------------------------------------------------- *)
lemma modify_preserves_lI5_SA_Prefix:
  fixes L L' :: "OpRec list" and H :: "ActRec list" and v :: nat
  assumes I4: "lI4_FIFO_Semantics_list L"
  assumes L'_def: "L' = modify_lin L H v"
  assumes DI: "data_independent L"
  assumes I5: "lI5_SA_Prefix_list L"
  assumes pending: "\<forall>k < length L. op_val (L!k) = v \<longrightarrow> op_name (L!k) \<noteq> deq"
  shows "lI5_SA_Prefix_list L'"
proof -
  let ?idx = "nat (find_last_SA L + 1)"

  (* 1. use core, all *)
  have take_eq: "take ?idx L' = take ?idx L"
    using modify_lin_structural_preservation[OF DI] unfolding L'_def by simp

  have drop_mset_eq: "mset (drop ?idx L') = mset (drop ?idx L)"
    using modify_lin_structural_preservation[OF DI] unfolding L'_def by simp

  have len_eq: "length L' = length L"
  proof -
    have drop_len_eq: "length (drop ?idx L') = length (drop ?idx L)"
      using drop_mset_eq by (rule mset_eq_length)
    have "length L' = length (take ?idx L') + length (drop ?idx L')" by simp
    also have "... = length (take ?idx L) + length (drop ?idx L)"
      using take_eq drop_len_eq by simp
    also have "... = length L" by simp
    finally show ?thesis .
  qed

  (* 2. derivationglobal *)
  have mset_eq: "mset L' = mset L"
  proof -
    have "mset L' = mset (take ?idx L') + mset (drop ?idx L')"
      by (metis append_take_drop_id mset_append)
    also have "... = mset (take ?idx L) + mset (drop ?idx L)"
      using take_eq drop_mset_eq by simp
    also have "... = mset L"
      by (metis append_take_drop_id mset_append)
    finally show ?thesis .
  qed

  have in_SA_eq: "\<And>x. in_SA x L' = in_SA x L"
    using in_SA_mset_eq[OF mset_eq] in_SA_def by auto

  (* 3. prove SA boundary (find_last_SA L' = find_last_SA L) *)
  have sa_stable: "find_last_SA L' = find_last_SA L"
  proof (rule find_last_SA_stable_prefix[OF len_eq take_eq])
    (* A. L suffixno SA *)
    show "\<forall>i\<in>{?idx..<length L}. \<not> (op_name (L ! i) = enq \<and> in_SA (op_val (L ! i)) L)"
    proof (intro ballI notI, elim conjE)
      fix i assume "i \<in> {?idx..<length L}" "op_name (L ! i) = enq" "in_SA (op_val (L ! i)) L"
      then have "int i \<le> find_last_SA L"
        using I5 unfolding lI5_SA_Prefix_list_def
        by simp
      moreover have "int i \<ge> int ?idx" using `i \<in> {?idx..<length L}` by auto
      moreover have "int ?idx > find_last_SA L" by auto
      ultimately show False by auto
    qed

    (* B. L' suffixno SA *)
    show "\<forall>i\<in>{?idx..<length L'}. \<not> (op_name (L' ! i) = enq \<and> in_SA (op_val (L' ! i)) L')"
    proof (intro ballI notI, elim conjE)
      fix i assume "i \<in> {?idx..<length L'}" "op_name (L' ! i) = enq" "in_SA (op_val (L' ! i)) L'"
      let ?x = "L' ! i"
      have "?x = (drop ?idx L') ! (i - ?idx)"
        using `i \<in> {?idx..<length L'}` by simp
      moreover have "i - ?idx < length (drop ?idx L')"
        using `i \<in> {?idx..<length L'}`
        by (simp add: diff_less_mono)
      ultimately have "?x \<in> set (drop ?idx L')"
        by (metis nth_mem)
      then have "?x \<in> set (drop ?idx L)"
        using drop_mset_eq by (metis set_mset_mset)
      then obtain j where "j < length (drop ?idx L)" "(drop ?idx L) ! j = ?x"
        by (auto simp: in_set_conv_nth)
      let ?k = "?idx + j"
      have "?k < length L" "L ! ?k = ?x"
        using `j < length (drop ?idx L)` `(drop ?idx L) ! j = ?x` by auto
      have "in_SA (op_val ?x) L"
        using `in_SA (op_val (L' ! i)) L'` in_SA_eq by simp
      then have "int ?k \<le> find_last_SA L"
        using I5 `op_name (L' ! i) = enq` `?k < length L` `L ! ?k = ?x`
        unfolding lI5_SA_Prefix_list_def
        by metis
      moreover have "int ?k \<ge> int ?idx" by auto
      moreover have "int ?idx > find_last_SA L" by auto
      ultimately show False by auto
    qed

    (* C. in_SA consistency *)
    show "\<forall>v. in_SA v L' = in_SA v L"
      using in_SA_eq by blast
  qed

  (* 4. lI5_SA_Prefix_list of definition *)
  show ?thesis
    unfolding lI5_SA_Prefix_list_def
  proof (intro allI impI)
    fix k assume "k < length L'" "op_name (L' ! k) = enq"
    show "in_SA (op_val (L' ! k)) L' \<longleftrightarrow> int k \<le> find_last_SA L'"
    proof (cases "k < ?idx")
      case True
      (* In prefix in: element, from L *)
      have "L' ! k = (take ?idx L') ! k" using True by simp
      also have "... = (take ?idx L) ! k" using take_eq by simp
      also have "... = L ! k" using True by simp
      finally have L'_k_eq: "L' ! k = L ! k" .

      have "k < length L" using True `length L' = length L`
        using \<open>k < length L'\<close> by auto

      show ?thesis
        using I5 `op_name (L' ! k) = enq` `k < length L`
        unfolding lI5_SA_Prefix_list_def
        using L'_k_eq sa_stable in_SA_eq by auto
    next
      case False
      (* In suffix in: necessarily > find_last_SA, andnecessarily in SA in, False *)
      have "int k \<ge> int ?idx" using False by auto
      moreover have "int ?idx > find_last_SA L" by auto
      ultimately have "int k > find_last_SA L'" using sa_stable by auto

      moreover have "\<not> in_SA (op_val (L' ! k)) L'"
      proof -
        let ?x = "L' ! k"
        have "?x = (drop ?idx L') ! (k - ?idx)"
          using False `k < length L'` by simp
        moreover have "k - ?idx < length (drop ?idx L')"
          using False `k < length L'` by simp
        ultimately have "?x \<in> set (drop ?idx L')"
          by (metis nth_mem)
        then have "?x \<in> set (drop ?idx L)"
          using drop_mset_eq by (metis set_mset_mset)
        then obtain j where "j < length (drop ?idx L)" "(drop ?idx L) ! j = ?x"
          by (auto simp: in_set_conv_nth)
        let ?k = "?idx + j"
        have "?k < length L" "L ! ?k = ?x"
          using `j < length (drop ?idx L)` `(drop ?idx L) ! j = ?x` by auto

        have "\<not> in_SA (op_val ?x) L"
        proof (rule ccontr)
          assume "\<not> \<not> in_SA (op_val ?x) L"
          then have "int ?k \<le> find_last_SA L"
            using I5 `op_name (L' ! k) = enq` `?k < length L` `L ! ?k = ?x`
            unfolding lI5_SA_Prefix_list_def
            by metis
          moreover have "int ?k \<ge> int ?idx" by auto
          moreover have "int ?idx > find_last_SA L" by auto
          ultimately show False by auto
        qed
        thus ?thesis using in_SA_eq by simp
      qed
      ultimately show ?thesis by simp
    qed
  qed
qed


lemma should_modify_completeness:
  assumes indep: "data_independent L"
  assumes lI5_SA_Prefix: "lI5_SA_Prefix_list L"
  assumes pending: "\<forall>k < length L. op_val (L!k) = v \<longrightarrow> op_name (L!k) \<noteq> deq"
  assumes ex_v: "\<exists>k < length L. op_name (L!k) = enq \<and> op_val (L!k) = v"
  assumes dist_not_zero: "Distance L v \<noteq> 0"
  shows "should_modify L H v"
proof -
  (* 1. definition *)
  define last_sa where "last_sa = find_last_SA L"
  define rem where "rem = drop (nat (last_sa + 1)) L"

  (* 2. prove v in SA in *)
  have v_not_in_SA: "\<not> in_SA v L"
  proof -
    have "find_indices (\<lambda>x. op_name x = deq \<and> op_val x = v) L = []"
      unfolding find_indices_def
    proof (rule filter_False, intro ballI)
      fix i assume "i \<in> set [0..<length L]"
      hence "i < length L" by simp
      thus "\<not> (op_name (L ! i) = deq \<and> op_val (L ! i) = v)"
        using pending by blast
    qed
    thus ?thesis unfolding in_SA_def find_unique_index_def Let_def by simp
  qed

  (* 3. prove v in remaining in and one (still need use data_independent) *)
  have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) rem \<noteq> None"
  proof -
    (* We of definition as P, simplify after *)
    define P where "P = (\<lambda>a. op_name a = enq \<and> op_val a = v)"

    (* A. v in L in *)
    obtain k where k_props: "k < length L" "op_name (L!k) = enq" "op_val (L!k) = v"
      using ex_v by blast
    hence P_Lk: "P (L ! k)" unfolding P_def by simp

    (* B. v in SA in, it of k in SA boundaryafterwards *)
    have k_ge: "k \<ge> nat (last_sa + 1)"
      using v_not_in_SA k_props(2,3) lI5_SA_Prefix[unfolded lI5_SA_Prefix_list_def] last_sa_def
      using k_props(1) by fastforce

    (* V in rem in of as k_rem *)
    define k_rem where "k_rem = k - nat (last_sa + 1)"
    have k_rem_len: "k_rem < length rem"
      using k_props(1) k_ge rem_def k_rem_def by simp

    (* C. usedata this element in L in is global one of *)
    have L_unique: "find_indices P L = [k]"
      using indep k_props(1) k_props(2) k_props(3) unique_enq_index unfolding P_def by blast

    have P_iff_k: "\<forall>i < length L. P (L ! i) \<longleftrightarrow> i = k"
    proof (intro allI impI iffI)
      (* === left right: P(L!i) ==> i=k === *)
      fix i assume "i < length L"
      assume "P (L ! i)"
      hence "i \<in> set (find_indices P L)"
        unfolding find_indices_def using `i < length L` by auto
      thus "i = k" using L_unique by simp
    next
      (* === right left: i=k ==> P(L!i) === *)
      fix i assume "i < length L"
      assume "i = k"
      thus "P (L ! i)" using P_Lk by simp
    qed

    (* D. derivation and prove in rem in of uniqueness *)
    have "find_indices P rem = [k_rem]"
    proof -
      (* D.1 prove of setonly k_rem *)
      have set_eq: "set (find_indices P rem) = {k_rem}"
      proof (rule set_eqI)
        fix j
        show "j \<in> set (find_indices P rem) \<longleftrightarrow> j \<in> {k_rem}"
        proof
          (* : if j, it necessarilyequal to k_rem *)
          assume "j \<in> set (find_indices P rem)"
          hence "j < length rem" and "P (rem ! j)" unfolding find_indices_def by auto
          hence "j + nat (last_sa + 1) < length L" unfolding rem_def by simp
          moreover have "P (L ! (j + nat (last_sa + 1)))"
            using `P (rem ! j)` unfolding rem_def
            by (metis add.commute add_leD2 calculation nat_less_le
                nth_drop)
          ultimately have "j + nat (last_sa + 1) = k"
            using P_def indep k_props(1,2,3) same_enq_value_same_index
            by blast
          thus "j \<in> {k_rem}" using k_rem_def by simp
        next
          (* : k_rem *)
          assume "j \<in> {k_rem}"
          hence "j = k_rem" by simp
          have "P (rem ! k_rem)"
            using P_Lk k_ge rem_def k_rem_def
            using k_props(1) by auto
          thus "j \<in> set (find_indices P rem)"
            unfolding find_indices_def using `j = k_rem` k_rem_len by auto
        qed
      qed

      (* D.2 list out of is no of (distinct) *)
      have dist: "distinct (find_indices P rem)"
        unfolding find_indices_def by simp

      (* D.3 derivation: if one no of list, its setonly one element, then listnecessarily is elementlist *)
      show ?thesis
      proof (cases "find_indices P rem")
        case Nil thus ?thesis using set_eq by simp
      next
        case (Cons a ys)
        with set_eq have "a = k_rem" and "set ys \<subseteq> {k_rem}" by auto
        with Cons dist have "k_rem \<notin> set ys" by simp
        with `set ys \<subseteq> {k_rem}` have "ys = []"
          by (metis insertI1 set_empty subset_singletonD)
        with Cons `a = k_rem` show ?thesis by simp
      qed
    qed

    (* E. since to of is elementlist, find_unique_index then one return Some, and is None *)
    thus ?thesis unfolding find_unique_index_def P_def by simp
  qed

  then obtain bt_idx where bt_idx_eq:
    "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) rem = Some bt_idx"
    by blast

  define l2 where "l2 = take bt_idx rem"

(* 4. prove l2 empty (Distance!= 0 derive) *)
  have l2_not_nil: "l2 \<noteq> []"
  proof (* Fix 1: use directly proof notI, use rule ccontr *)
    assume "l2 = []"

    (* A. since l2 = take bt_idx rem is empty list, note bt_idx must is 0 *)
    have "bt_idx = 0"
    proof (rule ccontr)
      assume "bt_idx \<noteq> 0"
      then have "bt_idx > 0" by simp
      have "bt_idx < length rem"
        using bt_idx_eq find_unique_index_prop by blast
      with `bt_idx > 0` have "take bt_idx rem \<noteq> []" by auto
      with `l2 = []` l2_def show False by simp
    qed

    (* B. v in originallist L in of definitely pos_v *)
    let ?pos_v = "nat (last_sa + 1)"

    have pos_v_lt: "?pos_v < length L"
    proof -
      have "bt_idx < length rem"
        using bt_idx_eq find_unique_index_prop by blast
      then have "length rem > 0" using `bt_idx = 0` by simp
      then show ?thesis unfolding rem_def by simp
    qed

    have "rem ! 0 = L ! ?pos_v"
      using rem_def pos_v_lt by simp

    (* Use find_unique_index_prop, we rem! 0 is v of enqueue operation *)
    have v_rem_props: "0 < length rem \<and> op_name (rem ! 0) = enq \<and> op_val (rem ! 0) = v"
      using find_unique_index_prop[OF bt_idx_eq] `bt_idx = 0` by auto

    have v_L_props: "op_name (L ! ?pos_v) = enq" "op_val (L ! ?pos_v) = v"
      using v_rem_props `rem ! 0 = L ! ?pos_v` by auto

    (* Usedata, prove v in L in of enqueue operation also is global one of *)
    have v_idx_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some ?pos_v"
      using unique_enq_index[OF indep v_L_props(1) v_L_props(2) pos_v_lt]
      unfolding find_unique_index_def Let_def by simp

    (* C. core: proveallelement to v of as 0 *)
    have all_dist_zero: "\<forall>x. distance_func x v L = 0"
    proof
      fix x
      show "distance_func x v L = 0"
      proof (cases "in_SA x L")
        case True
        then show ?thesis unfolding distance_func_def by simp
      next
        case False
        (* If x in SA in, we it is has Enq operation *)
        show ?thesis
        proof (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L")
          case None
          then show ?thesis unfolding distance_func_def using False by simp
        next
          case (Some pos_x)
          have px_props: "pos_x < length L" "op_name (L ! pos_x) = enq" "op_val (L ! pos_x) = x"
            using find_unique_index_prop[OF Some] by auto

          (* Use lI5_SA_Prefix prove: since x in SA in, it of necessarily in synchronizeboundaryafterwards *)
          have "int pos_x > last_sa"
          proof (rule ccontr)
            assume "\<not> (int pos_x > last_sa)"
            then have "int pos_x \<le> last_sa" by simp
            with lI5_SA_Prefix px_props(1,2) have "in_SA x L"
              unfolding lI5_SA_Prefix_list_def last_sa_def
              using px_props(3) by blast
            with False show False by contradiction
          qed

          (* And out: pos_x >= pos_v, x one in v of after *)
          then have "pos_x \<ge> ?pos_v" by linarith
          then have "\<not> (pos_x < ?pos_v)" by simp

          (* In distance_func original definition: because pos_x < pos_v as, therefore as 0 *)
          show ?thesis
            unfolding distance_func_def
            using False Some v_idx_L `\<not> (pos_x < ?pos_v)` by simp
        qed
      qed
    qed

    (* D. out Distance L v = 0 and out contradiction *)
    have "Distance L v = 0"
    proof -
      (* Use all_dist_zero, Distance of definition its *)
      have "\<forall>x. distance_func x v L = 0" using all_dist_zero .
      thus ?thesis
        unfolding Distance_def by simp
    qed

    (* Fix 3: use simp, for in!= of contradiction, simp is of *)
    thus False using dist_not_zero by simp
  qed

  (* 5. core: in prove (only l2 nonempty, necessarily in) *)
  have struct_ok: "(let l2_last = last l2 in
          op_name l2_last = enq \<or>
          (case find_last_enq l2 of
             None \<Rightarrow> False
           | Some (l21, b_act, l22) \<Rightarrow> l22 \<noteq> []))"
  proof (cases "op_name (last l2) = enq")
    case True thus ?thesis by simp
  next
    case False
    (* Goal: prove in case, find_last_enq necessarilyreturn Some and l22 nonempty *)

    (* A. prove l2 in necessarily one Enq operation *)
    have has_enq: "\<exists>x \<in> set l2. op_name x = enq"
    proof -
      (* 1. one in sum_list of, unfold Distance_def *)
      have sum_zero: "\<And>xs. (\<forall>x\<in>set xs. distance_func x v L = 0) \<Longrightarrow> sum_list (map (\<lambda>v'. distance_func v' v L) xs) = 0"
      proof -
        fix xs show "(\<forall>x\<in>set xs. distance_func x v L = 0) \<Longrightarrow> sum_list (map (\<lambda>v'. distance_func v' v L) xs) = 0"
          by (induct xs) auto
      qed

      (* 2. use Distance!= 0 provenecessarily in x_val, its greater than 0 *)
      have "\<exists>x_val. distance_func x_val v L > 0"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence all_zero_val: "\<forall>x. distance_func x v L = 0" by force
        have "Distance L v = 0"
          unfolding Distance_def Let_def
          using sum_zero[of "sorted_list_of_set (set (map op_val (filter (\<lambda>a. op_name a = enq) L)))"]
          using all_zero_val by simp
        thus False using dist_not_zero by simp
      qed
      then obtain x_val where x_dist: "distance_func x_val v L > 0" by blast

      (* 3. x_val of (complete distance_func, use SMT) *)
      have not_sa_x: "\<not> in_SA x_val L"
        using x_dist unfolding distance_func_def by (cases "in_SA x_val L") auto

      obtain pos_x where px_eq: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L = Some pos_x"
        using x_dist not_sa_x unfolding distance_func_def
        by (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L") auto

      obtain pos_v where pv_eq: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some pos_v"
        using x_dist not_sa_x px_eq unfolding distance_func_def
        by (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L") auto

      have px_lt_pv: "pos_x < pos_v"
        using x_dist not_sa_x px_eq pv_eq unfolding distance_func_def
        by (auto split: if_splits)

      have px_prop: "pos_x < length L" "op_name (L ! pos_x) = enq" "op_val (L ! pos_x) = x_val"
        using find_unique_index_prop[OF px_eq] by auto

      (* 4. precise v of definitelycoordinate pos_v = offset + bt_idx *)
      let ?offset = "nat (last_sa + 1)"

      have rem_bt: "bt_idx < length rem" "op_name (rem ! bt_idx) = enq" "op_val (rem ! bt_idx) = v"
        using find_unique_index_prop[OF bt_idx_eq] by auto

      have pos_v_alt: "?offset + bt_idx < length L" "op_name (L ! (?offset + bt_idx)) = enq" "op_val (L ! (?offset + bt_idx)) = v"
        using rem_bt unfolding rem_def by auto

      have pv_prop: "pos_v < length L" "op_name (L ! pos_v) = enq" "op_val (L ! pos_v) = v"
        using find_unique_index_prop[OF pv_eq] by auto

      have "pos_v = ?offset + bt_idx"
      proof (rule ccontr)
        assume "pos_v \<noteq> ?offset + bt_idx"
        (* Use PureLib.thy in of unique_enq_value derive a contradiction *)
        with indep pv_prop(1) pos_v_alt(1) pv_prop(2) pos_v_alt(2)
        have "op_val (L ! pos_v) \<noteq> op_val (L ! (?offset + bt_idx))"
          using unique_enq_value by blast
        thus False using pv_prop(3) pos_v_alt(3) by simp
      qed

      (* 5. pos_x of (use lI5_SA_Prefix prove it in SA outside) *)
      have "int pos_x > last_sa"
      proof (rule ccontr)
        assume "\<not> (int pos_x > last_sa)"
        hence "int pos_x \<le> last_sa" by simp
        with lI5_SA_Prefix px_prop(1,2) have "in_SA x_val L"
          unfolding lI5_SA_Prefix_list_def last_sa_def
          using px_prop(3) by blast
        with not_sa_x show False by simp
      qed
      hence px_ge: "pos_x \<ge> ?offset" by simp

      (* 6. mapping: pos_x mapping to l2 in *)
      let ?local_x = "pos_x - ?offset"

      have local_bounds: "?local_x < bt_idx"
        using px_ge px_lt_pv `pos_v = ?offset + bt_idx` by linarith

      have local_lt_rem: "?local_x < length rem"
        using local_bounds rem_bt(1) by linarith

      have "rem ! ?local_x = L ! pos_x"
        using px_ge px_prop(1) by (simp add: rem_def )
      hence local_is_enq: "op_name (rem ! ?local_x) = enq"
        using px_prop(2) by simp

      have "l2 ! ?local_x = rem ! ?local_x"
        unfolding l2_def using local_bounds local_lt_rem by simp
      hence "op_name (l2 ! ?local_x) = enq"
        using local_is_enq by simp

      have "?local_x < length l2"
        unfolding l2_def using local_bounds local_lt_rem by simp

      thus ?thesis
        using `op_name (l2 ! ?local_x) = enq` by (metis in_set_conv_nth)
    qed

    (* B. prove find_last_enq necessarilysuccess (return Some) *)
    obtain l21 b_act l22 where split: "find_last_enq l2 = Some (l21, b_act, l22)"
    proof -
      (* Unfold find_last_enq definition *)
      let ?indices = "find_indices (\<lambda>a. op_name a = enq) l2"

      (* Because in Enq, therefore listnonempty *)
      have "?indices \<noteq> []"
      proof -
        (* 1. extract out of element x *)
        from has_enq obtain x where "x \<in> set l2" and "op_name x = enq" by blast
        (* 2. use in_set_conv_nth element as of i *)
        then obtain i where "i < length l2" and "l2 ! i = x" by (metis in_set_conv_nth)
        (* 3. prove i precise *)
        hence "op_name (l2 ! i) = enq" using `op_name x = enq` by simp
        moreover have "i \<in> set [0..<length l2]" using `i < length l2` by simp
        (* 4. since has one valid of i, out of listimpossible is empty *)
        ultimately show ?thesis
          unfolding find_indices_def
          by (metis (mono_tags, lifting) empty_filter_conv)
        qed


      (* Definition, nonempty necessarilyreturn Some (...) *)
      have "find_last_enq l2 \<noteq> None"
        unfolding find_last_enq_def Let_def
        using `?indices \<noteq> []` by simp

      (* As None of extract as of res *)
      then obtain res where res_eq: "find_last_enq l2 = Some res"
        by auto

      (* Core: use of definition, its as 3 *)
      have "Some res = Some (fst res, fst (snd res), snd (snd res))"
        by simp
      hence "find_last_enq l2 = Some (fst res, fst (snd res), snd (snd res))"
        using res_eq by simp

      (* At this point precisematch that then of, close the goal directly *)
      thus ?thesis using that by blast
    qed

    (* C. prove l22 empty *)
    have "l22 \<noteq> []"
    proof (* Fix 1: rule ccontr, use directly proof notI *)
      assume "l22 = []"

      (* Use PureLib already has of property: L =... @ [enq_act] @ after *)
      have "l2 = l21 @ [b_act] @ l22"
        using find_last_enq_props(1)[OF split] .

      (* If l22 empty, then l2 of last one element then is b_act *)
      hence "last l2 = b_act"
        using `l22 = []` by simp

      (* And b_act necessarily is Enq (find_last_enq property) *)
      have "op_name b_act = enq"
        using find_last_enq_props(2)[OF split] .

      (* And premise False (op_name (last l2) \<noteq> enq) contradiction *)
      hence "op_name (last l2) = enq"
        using `last l2 = b_act` by simp

      (* Fix 2: use using False, use case of inside *)
      thus False using `\<not> op_name (last l2) = enq` by simp
    qed

    thus ?thesis using split by auto
  qed

  (* 6.: definition, precise originalgoal *)
  show ?thesis
    (* Unfold definition, out *)
    unfolding should_modify_def Let_def
    (* : use we definition of local replace of *)
    unfolding last_sa_def[symmetric] rem_def[symmetric]
    (* Match: find_unique_index replace as Some bt_idx *)
    unfolding bt_idx_eq
    (* : take bt_idx rem replace as l2 *)
    unfolding l2_def[symmetric]
    (* At this pointgoal already be as we proved previously of 4 corefact of, direct closure *)
    using indep dist_not_zero l2_not_nil struct_ok
    using l2_def by auto
qed


lemma HB_implies_InQBack:
  assumes INV: "system_invariant s"
  assumes HB_ab: "HB_EnqRetCall s a b"
  shows "InQBack s a"
proof -
  (* 1. unfold HB_EnqRetCall, extract *)
  obtain p1 p2 sn1 sn2 where hb_act: "HB_Act s (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    using HB_ab unfolding HB_EnqRetCall_def by auto

  let ?act_a = "mk_op enq a p1 sn1"
  have a_props: "op_name ?act_a = enq" "op_val ?act_a = a"
    by (simp_all add: mk_op_def op_name_def op_val_def)

  (* 2. from hb_act extract?act_a of ret event *)
  obtain k1 k2 where k_props: "k1 < k2" "match_ret (his_seq s) k1 ?act_a" "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
    using hb_act unfolding HB_Act_def HB_def by auto

  (* 3. from match_ret obtain directly SSN of EnqRetInHis *)
  have ret_in_his: "EnqRetInHis s p1 a sn1"
  proof -
    from k_props(2) have "k1 < length (his_seq s)"
      and "act_pid (his_seq s ! k1) = p1"
      and "act_ssn (his_seq s ! k1) = sn1"
      and "act_name (his_seq s ! k1) = enq"
      and "act_cr (his_seq s ! k1) = ret"
      and "act_val (his_seq s ! k1) = a"
      (* Usenewdefinition extractall *)
      unfolding match_ret_def Let_def mk_op_def
                op_name_def op_val_def op_pid_def op_ssn_def
      by auto

    moreover have "his_seq s ! k1 \<in> set (his_seq s)"
      using `k1 < length (his_seq s)` by simp
    ultimately show ?thesis
      unfolding EnqRetInHis_def by blast
  qed

  (* 4. simplification step: lI3_HB_Ret_Lin_Sync?act_a then in! *)
  have lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" using INV unfolding system_invariant_def by auto

  obtain k_lin where k_lin: "k_lin < length (lin_seq s)" "lin_seq s ! k_lin = ?act_a"
  proof -
    (* LI3_HB_Ret_Lin_Sync now complete mk_op enq a p1 sn1 of in *)
    from lI3_HB_Ret_Lin_Sync_s ret_in_his have "\<exists>k < length (lin_seq s). lin_seq s ! k = ?act_a"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
    thus ?thesis using that by blast
  qed

  have act_a_in_lin: "?act_a \<in> OPLin s"
    unfolding OPLin_def using k_lin(1) k_lin(2) by (metis nth_mem)

  (* 5. derivation: a \<in> SetA \<union> SetB (then outside helper lemma) *)
  have lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" using INV unfolding system_invariant_def by auto
  have a_in_sets: "a \<in> SetA s \<union> SetB s"
  proof -
    have "?act_a \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
      using lI1_Op_Sets_Equivalence_s act_a_in_lin unfolding lI1_Op_Sets_Equivalence_def by blast
    moreover have "?act_a \<notin> OP_A_deq s"
      unfolding OP_A_deq_def mk_op_def op_name_def by simp
    ultimately have "?act_a \<in> OP_A_enq s \<union> OP_B_enq s" by blast
    thus ?thesis unfolding OP_A_enq_def OP_B_enq_def mk_op_def by auto
  qed

  (* 6.: if a in QBack in, contradiction *)
  show "InQBack s a"
  proof (rule ccontr)
    assume "\<not> InQBack s a"

    (* If a in SetA in, then in SetB in *)
    have "a \<in> SetB s"
    proof (rule ccontr)
      assume "a \<notin> SetB s"
      with a_in_sets have "a \<in> SetA s" by auto
      then have "InQBack s a" unfolding SetA_def TypeA_def by simp
      with `\<not> InQBack s a` show False by contradiction
    qed

    then have TypeB_a: "TypeB s a" unfolding SetB_def by auto

    (* \<not> InQBack a in Qback in, \<not> QHas s a (sI8_Q_Qback_Sync physicalconsistency) *)
    have "\<not> QHas s a"
    proof
      assume "QHas s a"
      then obtain k where "Q_arr s k = a" unfolding QHas_def by blast
      have "a \<noteq> BOT" using `a \<in> SetB s` unfolding SetB_def Val_def BOT_def by auto
      with `Q_arr s k = a` have "Q_arr s k \<noteq> BOT" by simp
      have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" using INV unfolding system_invariant_def by auto
      with `Q_arr s k \<noteq> BOT` have "Qback_arr s k = a" unfolding sI8_Q_Qback_Sync_def
        by (metis \<open>Model.Q_arr s k = a\<close>)
      then have "InQBack s a" unfolding InQBack_def by blast
      with `\<not> InQBack s a` show False by contradiction
    qed

    (* A must E2 process has *)
    from TypeB_a `\<not> QHas s a` obtain p where p_E2: "program_counter s p = ''E2''" and v_p: "v_var s p = a"
      unfolding TypeB_def by auto

    (* HI1_E_Phase_Pending_Enq HasPendingEnq s p a *)
    have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by auto
    with p_E2 v_p have pending: "HasPendingEnq s p a"
      unfolding hI1_E_Phase_Pending_Enq_def by blast

    (* Extractwhen before Pending in of SSN and corresponds to of Call *)
    let ?cur_sn = "s_var s p"
    have call_in_his: "EnqCallInHis s p a ?cur_sn"
      using pending unfolding HasPendingEnq_def Let_def by blast

    (* LI1_Op_Sets_Equivalence and OP_B_enq, in one value as a of enq operation in, and ssn equal to?cur_sn *)
    let ?act_B = "mk_op enq a p ?cur_sn"
    have "?act_B \<in> OP_B_enq s"
      unfolding OP_B_enq_def using `a \<in> SetB s` call_in_his by auto
    with lI1_Op_Sets_Equivalence_s have act_B_in_lin: "?act_B \<in> OPLin s"
      unfolding lI1_Op_Sets_Equivalence_def by blast

    then obtain k_B where k_B: "k_B < length (lin_seq s)" "lin_seq s ! k_B = ?act_B"
      unfolding OPLin_def by (meson in_set_conv_nth)

    (* Data: since is one value a,?act_a and?act_B is one operation *)
    have di: "data_independent (lin_seq s)" using INV unfolding system_invariant_def by auto
    have "?act_a = ?act_B"
    proof (rule ccontr)
      assume "?act_a \<noteq> ?act_B"

      let ?S = "{i. i < length (lin_seq s) \<and> op_name (lin_seq s ! i) = enq \<and> op_val (lin_seq s ! i) = a}"

      (* 1. extract this, and as val_props and oper_props *)
      have val_props: "op_val ?act_a = a" "op_val ?act_B = a"
        by (simp_all add: mk_op_def op_val_def)
      have oper_props: "op_name ?act_a = enq" "op_name ?act_B = enq"
        by (simp_all add: mk_op_def op_name_def)

      (* 2. prove: setelement 1 *)
      have card_le_1: "card ?S \<le> 1"
        using di unfolding data_independent_def by blast

      (* 3. prove: use before of derivation *)
      have subset_S: "?S \<supseteq> {k_lin, k_B}"
        using k_lin(1) k_lin(2) k_B(1) k_B(2) val_props oper_props by auto

      (* 4. prove equal *)
      have neq_idx: "k_lin \<noteq> k_B"
        using `?act_a \<noteq> ?act_B` k_lin(2) k_B(2) by auto

      (* 5. prove: since two of, setelement \<ge> 2 *)
      have card_ge_2: "card ?S \<ge> 2"
        using subset_S neq_idx
        using di unique_enq_value by fastforce

      (* 6. contradiction: \<le> 1 and \<ge> 2 *)
      show False
        using card_le_1 card_ge_2 by linarith
    qed

    (* Corecontradiction: two is one operation, thereforeprocess PID and SSN complete one *)
    hence pid_eq: "p1 = p" and ssn_eq: "sn1 = ?cur_sn"
      unfolding mk_op_def by auto

    (* We in step2extract of k1, is one for process p and?cur_sn of ret event! *)
    have "act_pid (his_seq s ! k1) = p"
      and "act_ssn (his_seq s ! k1) = ?cur_sn"
      and "act_cr (his_seq s ! k1) = ret"
      using k_props(2) pid_eq ssn_eq unfolding match_ret_def Let_def
            mk_op_def op_pid_def op_ssn_def by auto

    (* But pending pid and ssn of ret event *)
    have "\<forall>e \<in> set (his_seq s). \<not> (act_pid e = p \<and> act_ssn e = ?cur_sn \<and> act_cr e = ret)"
      using pending unfolding HasPendingEnq_def Let_def by auto
    moreover have "his_seq s ! k1 \<in> set (his_seq s)"
      using k_props(2) unfolding match_ret_def by simp

    ultimately show False
      using `act_pid (his_seq s ! k1) = p` `act_ssn (his_seq s ! k1) = ?cur_sn` `act_cr (his_seq s ! k1) = ret`
      by blast
  qed
qed

(* ----------------------------------------------------------------- *)
(* Helper lemma: in historyrecord of *)
(* ----------------------------------------------------------------- *)

lemma prefix_wf:
  assumes wf_full: "\<forall>k < length (xs @ [x]). let e_ret = (xs @ [x]) ! k in
             act_cr e_ret = ret \<longrightarrow>
             (\<exists>j < k. act_pid ((xs @ [x]) ! j) = act_pid e_ret \<and>
                      act_name ((xs @ [x]) ! j) = act_name e_ret \<and>
                      act_cr ((xs @ [x]) ! j) = call \<and>
                      (\<forall>m. j < m \<and> m < k \<longrightarrow> act_pid ((xs @ [x]) ! m) \<noteq> act_pid e_ret))"
  shows "\<forall>k < length xs. let e_ret = xs ! k in
             act_cr e_ret = ret \<longrightarrow>
             (\<exists>j < k. act_pid (xs ! j) = act_pid e_ret \<and>
                      act_name (xs ! j) = act_name e_ret \<and>
                      act_cr (xs ! j) = call \<and>
                      (\<forall>m. j < m \<and> m < k \<longrightarrow> act_pid (xs ! m) \<noteq> act_pid e_ret))"
  unfolding Let_def
proof (intro allI impI)
  fix k
  assume k_lt: "k < length xs" and k_ret: "act_cr (xs ! k) = ret"

  have k_full: "k < length (xs @ [x])" using k_lt by simp
  have k_ret_full: "act_cr ((xs @ [x]) ! k) = ret" using k_ret k_lt by (simp add: nth_append)

  (* Use directly we of wf_full, definitely does not! *)
  from wf_full [unfolded Let_def, rule_format, OF k_full k_ret_full]
  obtain j where j_props:
    "j < k"
    "act_pid ((xs @ [x]) ! j) = act_pid ((xs @ [x]) ! k)"
    "act_name ((xs @ [x]) ! j) = act_name ((xs @ [x]) ! k)"
    "act_cr ((xs @ [x]) ! j) = call"
    "\<forall>m. j < m \<and> m < k \<longrightarrow> act_pid ((xs @ [x]) ! m) \<noteq> act_pid ((xs @ [x]) ! k)"
    by blast

  have j_lt: "j < length xs" using j_props(1) k_lt by linarith

  show "\<exists>j<k. act_pid (xs ! j) = act_pid (xs ! k) \<and>
              act_name (xs ! j) = act_name (xs ! k) \<and>
              act_cr (xs ! j) = call \<and>
              (\<forall>m. j < m \<and> m < k \<longrightarrow> act_pid (xs ! m) \<noteq> act_pid (xs ! k))"
    apply (rule exI[where x=j])
    using j_props j_lt k_lt
    by (auto simp add: nth_append)
qed



lemma His_WF_Deq_Count_Logic:
  (* 1: ret previouslymust has match of call (hI7_His_WF) *)
  assumes wf: "\<forall>k < length L. let e_ret = L ! k in
                 act_cr e_ret = ret \<longrightarrow>
                 (\<exists>j < k. act_pid (L ! j) = act_pid e_ret \<and> act_name (L ! j) = act_name e_ret \<and>
                          act_cr (L ! j) = call \<and> (\<forall>m. j < m \<and> m < k \<longrightarrow> act_pid (L ! m) \<noteq> act_pid e_ret))"
assumes wf_call: "\<forall>k \<le> length L. let q_his = filter (\<lambda>e. act_pid e = q) (take k L) in
             length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
             length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
             length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
             length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
             (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
              length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
              length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
  (* Conclusion: value *)
  shows "let q_his = filter (\<lambda>e. act_pid e = q) L in
         if q_his = [] then
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) = 0
         else if act_cr (last q_his) = call then
           (if act_name (last q_his) = deq then
              length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
              length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) = 1
            else
              length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
              length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) = 0)
         else
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) = 0"
using wf wf_call
proof (induction L rule: rev_induct)
  case Nil
  (* Basiccase: empty list *)
  then show ?case by (simp add: Let_def)
next
  case (snoc x xs)
  (* 1. when before of *)
  note wf_full = snoc.prems(1)
  note wf_call_full = snoc.prems(2)

  (* 2. prove xs wf (useprecondition) *)
  have wf_xs: "\<forall>k < length xs. let e_ret = xs ! k in act_cr e_ret = ret \<longrightarrow>
               (\<exists>j < k. act_pid (xs ! j) = act_pid e_ret \<and> act_name (xs ! j) = act_name e_ret \<and>
                        act_cr (xs ! j) = call \<and> (\<forall>m. j < m \<and> m < k \<longrightarrow> act_pid (xs ! m) \<noteq> act_pid e_ret))"
    using prefix_wf[OF wf_full] .

  (* 3. prove xs wf_call (prefixclosureproperty) *)
  (* Only xs @ [x] of allprefix all valid, then xs of allprefix also valid *)
  have wf_call_xs: "\<forall>k \<le> length xs. let q_his = filter (\<lambda>e. act_pid e = q) (take k xs) in
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
                      (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
  proof (intro allI impI)
    fix k assume "k \<le> length xs"
    hence "k \<le> length (xs @ [x])" by simp
    moreover have "take k xs = take k (xs @ [x])" using `k \<le> length xs` by simp
    ultimately show "let q_his = filter (\<lambda>e. act_pid e = q) (take k xs) in
                     length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
                     length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
                     length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
                     length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1\<and>
                      (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
                      length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
      using wf_call_full[rule_format, of k] by (simp add: Let_def)
  qed

  (* 4. *)
  note IH = snoc.IH[OF wf_xs wf_call_xs]

  (* 5. core prove *)
  show ?case
  proof (cases "act_pid x = q")
    (* Case False: x is process q of event, q_his, IH *)
    case False
    then show ?thesis
      using IH False by (auto simp add: Let_def)
  next
    (* Case True: x is process q of event *)
    case True
    note pid_x = True
    let ?q_his = "filter (\<lambda>e. act_pid e = q) xs"
    (* Fact: now of q_his equal to old of q_his x *)
    have q_his_full_eq: "filter (\<lambda>e. act_pid e = q) (xs @ [x]) = ?q_his @ [x]"
      using True by simp

    show ?thesis
    proof (cases "act_cr x = ret")
      (* === branch A: x is Ret event === *)
      case True
      (* Step A1: use wf_full to ret corresponds to of call *)
      have idx_x: "length xs < length (xs @ [x])" by simp
      have x_at_idx: "(xs @ [x]) ! length xs = x" by simp

      from wf_full[unfolded Let_def, rule_format, OF idx_x]
      obtain j where j_props:
        "j < length xs"
        "act_pid (xs ! j) = q"
        "act_cr (xs ! j) = call"
        "act_name (xs ! j) = act_name x"  (* <--- new: its key!operation mustmatch *)
        "\<forall>m. j < m \<and> m < length xs \<longrightarrow> act_pid (xs ! m) \<noteq> q"
        using True x_at_idx pid_x by (auto simp add: nth_append)

      (* Step A2: prove xs! j is q_his of last one element *)
      have "xs = take j xs @ [xs ! j] @ drop (Suc j) xs"
        using j_props(1) by (metis append_Cons append_Nil id_take_nth_drop)
      moreover have "filter (\<lambda>e. act_pid e = q) (drop (Suc j) xs) = []"
        unfolding filter_empty_conv
      proof (intro ballI)
        (* Filter empty in: in drop list in of one element e, it of pid all is q *)
        fix e
        assume "e \<in> set (drop (Suc j) xs)"

        (* 1. since e in drop list in, it necessarilycorresponds to one inside k *)
        then obtain k where k_lt: "k < length (drop (Suc j) xs)"
                        and e_val: "e = drop (Suc j) xs ! k"
          by (auto simp: in_set_conv_nth)

        (* 2. drop list of k, original into original list xs in of real (Suc j + k) *)
        hence e_eq: "e = xs ! (Suc j + k)" by simp

        (* 3. prove real in j and length xs *)
        have bound1: "j < Suc j + k" by simp
        have bound2: "Suc j + k < length xs"
          using k_lt by simp

        (* 4. guards: use j_props(4), inside of allelement all in q *)
        have "act_pid (xs ! (Suc j + k)) \<noteq> q"
          using j_props(5) bound1 bound2 by blast

        (* 5.: therefore e of pid impossible is q *)
        thus "act_pid e \<noteq> q"
          using e_eq by simp
      qed
      ultimately have q_his_structure: "?q_his = filter (\<lambda>e. act_pid e = q) (take j xs) @ [xs ! j]"
        using j_props(2)
        by (smt (verit) append.right_neutral filter.simps(1,2)
            filter_append)

      have last_is_call: "last ?q_his = xs ! j"
        using q_his_structure by simp
      have last_cr_call: "act_cr (last ?q_his) = call"
        using last_is_call j_props(3) by simp

      have last_oper_eq: "act_name (last ?q_his) = act_name x" (* <--- newderivation *)
        using last_is_call j_props(4) by simp

      (* Step A3: IH prove. IH if last is call, value is 1. now ret, value 1 0. *)
      show ?thesis
        using IH pid_x True last_cr_call last_oper_eq
        by (smt (verit, ccfv_SIG) add_le_same_cancel1 add_left_cancel
            append_is_Nil_conv count_invariant last_snoc le_add_diff_inverse
            le_eq_less_or_eq length_filter_append_singleton less_numeral_extra(1)
            linordered_semidom_class.add_diff_inverse not_one_le_zero
            q_his_full_eq q_his_structure zero_less_diff)

    next
      (* === branch B: x is Ret (necessarily is Call) === *)
      case False
      note x_not_ret = False

      show ?thesis
      proof (cases "act_name x = deq")
        case True
        (* B1: x is deq call. use derivation diff = 1 *)

        (* Of length definition as of C (Call) and R (Ret) *)
        define C where "C = length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) ?q_his)"
        define R where "R = length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) ?q_his)"

        have new_C: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (?q_his @ [x])) = Suc C"
          using True x_not_ret
          using C_def cr_type.exhaust by auto
        have new_R: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (?q_his @ [x])) = R"
          using True x_not_ret by (simp add: R_def)

        (* From xs @ [x] of guards in extractconclusion: (C + 1) - R \<le> 1 *)
        have bound: "Suc C - R \<le> 1"
          using wf_call_full[rule_format, of "length (xs @ [x])"] pid_x
          using new_C new_R by fastforce

        (* From xs of guards in extractconclusion: R \<le> C (is of key!) *)
        have prev_bound: "R \<le> C"
          using wf_call_full[rule_format, of "length xs"] pid_x
          by (simp add: Let_def R_def C_def)

        (* Of: R \<le> C and (C+1) - R \<le> 1 \<Longrightarrow> C necessarilyequal to R *)
        have "C = R" using bound prev_bound by simp

        (* Prove!sinceold state in C = R, then value from 0 into 1 *)
        show ?thesis
          using IH pid_x True x_not_ret `C = R`
          by (auto simp add: Let_def q_his_full_eq C_def R_def)
      next
        case False
        (* B2: x is enq call (act_name!= deq) *)

        (* Use guards: sinceappend x after last one element is enq call, then of deq necessarily is of! *)
        have deq_balanced: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (?q_his @ [x])) =
                            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (?q_his @ [x]))"
          using wf_call_full[rule_format, of "length (xs @ [x])"] pid_x x_not_ret False
          using cr_type.exhaust by auto

        (* Since deq, value as 0, precise goal else branch of value 0!! *)
        show ?thesis
          using pid_x x_not_ret False deq_balanced
          by (auto simp add: Let_def q_his_full_eq)
      qed
    qed
  qed
qed

(* Guard: HB of (Irreflexivity) *)
(* Physical: one enqueueoperation of Call definitelyimpossible in it of Ret afterwards *)
lemma HB_irrefl:
  assumes INV: "system_invariant s"
  shows "\<not> HB_EnqRetCall s a a"
proof
  assume "HB_EnqRetCall s a a"

  (* In of hI5_SSN_Unique change! *)
  have wf: "hI7_His_WF s" and uniq: "hI8_Val_Unique s"
    using INV unfolding system_invariant_def by auto

  (* 2. unfold HB of definition, two contradiction of event k1 and k2 *)
  (* Since a is val, it in mk_op of No. two. inside generate p1, p2 and sn1, sn2 *)
  from `HB_EnqRetCall s a a`
  obtain p1 p2 sn1 sn2 where "HB_Act s (mk_op enq a p1 sn1) (mk_op enq a p2 sn2)"
    unfolding HB_EnqRetCall_def by blast

  then obtain k1 k2 where hb_props:
    "k1 < k2"
    "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
    "match_call (his_seq s) k2 (mk_op enq a p2 sn2)"
    unfolding HB_Act_def HB_def by blast

  (* Analyze k1 (Ret) of, extractgoal: act_val = a *)
  have k1_props: "k1 < length (his_seq s)"
    "act_name (his_seq s ! k1) = enq"
    "act_cr (his_seq s ! k1) = ret"
    "act_val (his_seq s ! k1) = a"
    using hb_props(2) unfolding match_ret_def Let_def mk_op_def op_name_def op_val_def by auto

  (* Analyze k2 (Call) of, extractgoal: act_val = a *)
  have k2_props: "k2 < length (his_seq s)"
    "act_name (his_seq s ! k2) = enq"
    "act_cr (his_seq s ! k2) = call"
    "act_val (his_seq s ! k2) = a"
    using hb_props(3) unfolding match_call_def Let_def mk_op_def op_name_def op_val_def by auto

  (* 3. use hI7_His_WF guards: for in k1 of ret, history in necessarily in one early of call (as k0) *)
  have "let e_ret = his_seq s ! k1 in
        act_cr e_ret = ret \<longrightarrow>
        (\<exists>j < k1. act_pid (his_seq s ! j) = act_pid e_ret \<and>
                  act_ssn (his_seq s ! j) = act_ssn e_ret \<and>
                  act_name (his_seq s ! j) = act_name e_ret \<and>
                  act_cr (his_seq s ! j) = call \<and>
                  (if act_name e_ret = enq then act_val (his_seq s ! j) = act_val e_ret else act_val (his_seq s ! j) = BOT))"
    using wf unfolding hI7_His_WF_def using k1_props(1)
    by meson

  then obtain k0 where k0_props:
    "k0 < k1"
    "act_name (his_seq s ! k0) = enq"
    "act_cr (his_seq s ! k0) = call"
    "act_val (his_seq s ! k0) = a"  (* Precise k1 of val *)
    using k1_props by (auto simp: Let_def)

  (* 4. use hI8_Val_Unique guards: history in, value as a of enq call only has one one! *)
  (* Early of k0 and late of k2 must is one physicalevent *)
  have k0_lt_len: "k0 < length (his_seq s)" using k0_props(1) k1_props(1) by simp

  have "k0 = k2"
    using uniq unfolding hI8_Val_Unique_def
    using k0_lt_len k2_props(1) k0_props(2,3,4) k2_props(2,3,4)
    by blast

  (* 5. final step: of *)
  (* Since k0 = k2, then k1 < k2 then in k1 < k0. but before already prove k0 < k1! *)
  moreover have "k0 < k2" using `k0 < k1` hb_props(1) by simp
  ultimately show False by simp
qed



lemma no_bt_val_deq_in_L:
  assumes sys_inv: "system_invariant s"
  assumes L_def: "L = lin_seq s"
  assumes bt_type: "TypeBT s bt_val"
  assumes bt_in_val: "bt_val \<in> Val"
  shows "\<forall>x \<in> set L. op_name x = deq \<longrightarrow> op_val x \<noteq> bt_val"
proof -
  (* ========================================================== *)
  (* No. one phase: usephysicalhistory, prove bt_val necessarily is validvalue Val *)
  (* ========================================================== *)

  (* 1. TypeBT this element in Qback array in *)
  have "InQBack s bt_val"
    using bt_type unfolding TypeBT_def by auto
  hence "\<exists>k. Qback_arr s k = bt_val"
    unfolding InQBack_def by auto
  then obtain k where "Qback_arr s k = bt_val" by blast

  (* 2. use hI10_Enq_Call_Existence: only in Qback in, then necessarily in history in has sn of EnqCall record *)
  have "hI10_Enq_Call_Existence s" using sys_inv unfolding system_invariant_def by simp
  (* Fix point: hI10_Enq_Call_Existence extract to pid(q) and ssn(sn) *)
  hence "\<exists>q sn. EnqCallInHis s q bt_val sn"
    using bt_in_val `Qback_arr s k = bt_val`
    unfolding hI10_Enq_Call_Existence_def by blast
  then obtain q sn where "EnqCallInHis s q bt_val sn" by blast

  (* 3. unfoldhistoryrecord, extract this of enqueueevent e *)
  then obtain e where e_props:
    "e \<in> set (his_seq s)"
    "act_name e = enq"
    "act_val e = bt_val"
    unfolding EnqCallInHis_def by blast

  (* 4. use hI20_Enq_Val_Valid: physicalhistory in all of enq operation, its valuenecessarily in Val *)
  have "hI20_Enq_Val_Valid s" using sys_inv unfolding system_invariant_def by simp
  hence "\<forall>ev \<in> set (his_seq s). act_name ev = enq \<longrightarrow> act_val ev \<in> Val"
    unfolding hI20_Enq_Val_Valid_def by (metis in_set_conv_nth)
  hence "act_val e \<in> Val" using e_props(1) e_props(2) by blast

  (* 5. conclusion: bt_val necessarily is validvalue *)
  hence "bt_val \<in> Val" using e_props(3) by simp


  (* ========================================================== *)
  (* No. two phase: for of prove (use lI2_Op_Cardinality inside) *)
  (* ========================================================== *)

  have "bt_val \<in> SetB s"
    using bt_type bt_in_val unfolding TypeBT_def SetB_def by auto

  (* 6. simplification step: use lI2_Op_Cardinality out DeqIdxs as 0 *)
  have "lI2_Op_Cardinality s" using sys_inv unfolding system_invariant_def by simp
  hence "card (DeqIdxs s bt_val) = 0"
    using `bt_val \<in> SetB s` unfolding lI2_Op_Cardinality_def by blast

  (* Because DeqIdxs be in k < length, therefore it is has *)
  moreover have "finite (DeqIdxs s bt_val)"
    unfolding DeqIdxs_def by simp

  (* Has of card = 0 in empty *)
  ultimately have "DeqIdxs s bt_val = {}"
    by auto

  hence "\<forall>k < length L. op_name (L ! k) = deq \<longrightarrow> op_val (L ! k) \<noteq> bt_val"
    unfolding DeqIdxs_def L_def by auto

  thus ?thesis
    by (metis in_set_conv_nth)
qed


(* ========================================================================= *)
(* Derivation: use modify_lin_preserves_orders complete into deq prove *)
(* ========================================================================= *)
lemma modify_preserves_deq_filter:
  assumes sys_inv: "system_invariant s"
    and L_def: "L = lin_seq s"
    and type_bt: "TypeBT s bt_val"
    and bt_in_val: "bt_val \<in> Val"
  shows "filter (\<lambda>a. op_name a = deq \<and> op_pid a = p) (modify_lin L H bt_val) =
         filter (\<lambda>a. op_name a = deq \<and> op_pid a = p) L"
proof -
  have deq_order: "filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) (modify_lin L H bt_val) =
                   filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) L"
    using modify_lin_preserves_orders by blast

  have no_bt_val_deq: "\<forall>x \<in> set L. op_name x = deq \<longrightarrow> op_val x \<noteq> bt_val"
    using no_bt_val_deq_in_L[OF sys_inv L_def type_bt bt_in_val] by simp

  hence L_eq: "filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) L =
               filter (\<lambda>x. op_name x = deq) L"
    by (induction L) auto

  have mset_eq: "mset (modify_lin L H bt_val) = mset L"
    using modify_preserves_mset by simp
  hence "\<forall>x \<in> set (modify_lin L H bt_val). op_name x = deq \<longrightarrow> op_val x \<noteq> bt_val"
    using no_bt_val_deq by (metis mset_eq_setD)
  hence mod_eq: "filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) (modify_lin L H bt_val) =
                 filter (\<lambda>x. op_name x = deq) (modify_lin L H bt_val)"
    by (metis (mono_tags, lifting) filter_cong)

  have pure_deq: "filter (\<lambda>x. op_name x = deq) (modify_lin L H bt_val) =
                  filter (\<lambda>x. op_name x = deq) L"
    using deq_order L_eq mod_eq
    by metis

  then show ?thesis
    by (metis filter_filter)
qed


lemma modify_lin_preserves_enq_count:
  "length (filter (\<lambda>a. op_name a = enq) (modify_lin L H v)) = length (filter (\<lambda>a. op_name a = enq) L)"
proof -
  have "mset (modify_lin L H v) = mset L" by (rule modify_preserves_mset)
  then have "mset (filter (\<lambda>a. op_name a = enq) (modify_lin L H v)) = mset (filter (\<lambda>a. op_name a = enq) L)"
    by simp
  then show ?thesis by (metis mset_eq_length)
qed

lemma x_var_not_in_old_deq_ret:
  assumes INV: "system_invariant s"
    and pc: "program_counter s p = ''D4'' "
    and idx: "idx < length (his_seq s)"
    and deq_ret: "act_name (his_seq s ! idx) = deq \<and> act_cr (his_seq s ! idx) = ret"
  shows "act_val (his_seq s ! idx) \<noteq> x_var s p"
proof
  (* : history in idx of value equal towhen before p has of x_var *)
  assume val_eq: "act_val (his_seq s ! idx) = x_var s p"
  let ?a = "x_var s p"
  let ?q = "act_pid (his_seq s ! idx)"

  (* Extracthistoryrecord in of sn *)
  define sn_q where "sn_q = act_ssn (his_seq s ! idx)"

  (* ?a is one valid of, BOT of value *)
  have x_val: "?a \<in> Val" "?a \<noteq> BOT"
    using INV pc unfolding system_invariant_def sI7_D4_Deq_Result_def TypeOK_def Val_def by auto

  (* Process?q already in history complete into one for?a of dequeue *)
  have q_ret: "DeqRetInHis s ?q ?a sn_q"
    using idx deq_ret val_eq sn_q_def unfolding DeqRetInHis_def by auto

  consider (p_neq_q) "?q \<noteq> p" | (p_eq_q) "?q = p" by blast
  thus False
  proof cases
    case p_neq_q
    (* Return?hI15_Deq_Result_Exclusivity (all)!
       HI15_Deq_Result_Exclusivity: for in one value?a, has two of process " has " it (no is in history in is in) *)
    have "?q = p"
      using INV x_val(1) q_ret pc p_neq_q
      unfolding system_invariant_def hI15_Deq_Result_Exclusivity_def by blast
    thus False using p_neq_q by contradiction
  next
    case p_eq_q
    (* We with before return?hI26_DeqRet_D4_Mutex ()! *)
    have "\<not> (DeqRetInHis s p ?a sn_q \<and> program_counter s p = ''D4'' \<and> x_var s p = ?a)"
      using INV x_val(1) unfolding system_invariant_def hI26_DeqRet_D4_Mutex_def by blast
    thus False using q_ret p_eq_q pc by auto
  qed
qed


(* ========================================================================= *)

lemma HB_enq_stable_deq_append:
  fixes H :: "ActRec list" and a b :: nat
  assumes h_eq: "H' = H @ [mk_act deq v p sn ret]"
  (* Fill in sn1, sn2, and after of mk_op align *)
  shows "(\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)) \<longleftrightarrow>
         (\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2))"
proof
  (* One: H' \<longrightarrow> H () *)
  assume "\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  then obtain p1 sn1 p2 sn2 k1 k2 where k:
    "k1 < k2" "k1 < length H'" "k2 < length H'"
    "act_name (H' ! k1) = enq" "act_pid (H' ! k1) = p1" "act_val (H' ! k1) = a"
    "act_ssn (H' ! k1) = sn1" "act_cr (H' ! k1) = ret"
    "act_name (H' ! k2) = enq" "act_pid (H' ! k2) = p2" "act_val (H' ! k2) = b"
    "act_ssn (H' ! k2) = sn2" "act_cr (H' ! k2) = call"
    unfolding HB_def Let_def mk_op_def
    using op_name_def op_val_def match_call_def match_ret_def
    by fastforce

  (* Keycontradiction: H' last one is deq, and k2 is enq, therefore k2 in old history H inside *)
  have k2_old: "k2 < length H"
  proof (rule ccontr)
    assume "\<not> k2 < length H"
    hence "k2 = length H" using k(3) h_eq by simp
    hence "act_name (H' ! k2) = deq"
      using h_eq by (simp add: nth_append act_name_def mk_act_def)
    thus False using k(9) by simp
  qed
  hence k1_old: "k1 < length H" using k(1) by linarith

  (* Since all in old inside, and H'! k = H! k, old history in necessarily in HB *)
  show "\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  proof -
    (* 1.: p1, sn1, p2, sn2 with inside k1, k2 *)
    show ?thesis
      unfolding HB_def
    proof (intro exI conjI)
      show "k1 < k2" by (rule k(1))

      (* 2. core: prove in H in of match_ret *)
      show "match_ret H k1 (mk_op enq a p1 sn1)"
        unfolding match_ret_def mk_op_def
        using k(4,5,6,7,8) k1_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                      op_name_def op_val_def op_pid_def op_ssn_def)

      (* 3. core: prove in H in of match_call *)
      show "match_call H k2 (mk_op enq b p2 sn2)"
        unfolding match_call_def mk_op_def
        using k(9,10,11,12,13) k2_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                      op_name_def op_val_def op_pid_def op_ssn_def)
    qed
  qed

  next
  (* Two: H \<longrightarrow> H' (monotonicity) *)
  assume "\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  then obtain p1 sn1 p2 sn2 k1 k2 where k_old:
    "k1 < k2" "k1 < length H" "k2 < length H"
    "act_name (H ! k1) = enq" "act_pid (H ! k1) = p1" "act_val (H ! k1) = a"
    "act_ssn (H ! k1) = sn1" "act_cr (H ! k1) = ret"
    "act_name (H ! k2) = enq" "act_pid (H ! k2) = p2" "act_val (H ! k2) = b"
    "act_ssn (H ! k2) = sn2" "act_cr (H ! k2) = call"
    unfolding HB_def Let_def mk_op_def
    using op_name_def op_val_def match_call_def match_ret_def
    by fastforce

  (* In append one element, original has enq of HB preserve *)
  show "\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  proof -
    (* As from old stateextract out of p1, sn1, p2, sn2 with k1, k2 *)
    show ?thesis
      unfolding HB_def
    proof (intro exI conjI)
      show "k1 < k2" by (rule k_old(1))

      (* Prove in H' in match_ret into *)
      show "match_ret H' k1 (mk_op enq a p1 sn1)"
        unfolding match_ret_def mk_op_def
        using k_old(2,4,5,6,7,8) h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                      op_name_def op_val_def op_pid_def op_ssn_def)

      (* Prove in H' in match_call into *)
      show "match_call H' k2 (mk_op enq b p2 sn2)"
        unfolding match_call_def mk_op_def
        using k_old(1,3,9,10,11,12,13) h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                      op_name_def op_val_def op_pid_def op_ssn_def)
    qed
  qed
qed

(* As hI23_Deq_Call_Ret_Balanced of prefixmapping *)
lemma filter_butlast_take:
  "filter P xs \<noteq> [] \<Longrightarrow> \<exists>k\<le>length xs. filter P (take k xs) = butlast (filter P xs)"
proof (induction xs rule: rev_induct)
  case Nil then show ?case by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "P x")
    case True
    let ?k = "length xs"
    have "?k \<le> length (xs @ [x])" by simp
    moreover have "filter P (take ?k (xs @ [x])) = filter P xs" by simp
    moreover have "butlast (filter P (xs @ [x])) = filter P xs" using True by simp
    ultimately show ?thesis
      by metis
  next
    case False
    then have eq1: "filter P (xs @ [x]) = filter P xs" by simp
    then have eq2: "butlast (filter P (xs @ [x])) = butlast (filter P xs)" by simp
    from snoc.prems eq1 have "filter P xs \<noteq> []" by simp
    with snoc.IH obtain k where k_props: "k \<le> length xs" "filter P (take k xs) = butlast (filter P xs)" by blast
    have "k \<le> length (xs @ [x])" using k_props(1) by simp
    moreover have "take k (xs @ [x]) = take k xs" using k_props(1) by simp
    ultimately show ?thesis using k_props(2) eq2
      by metis
  qed
qed

(* ========================================================================= *)
(* Basiclist: list in as last of element, its in originallist in of necessarilyless than last *)
(* ========================================================================= *)
lemma filter_last_index_order:
  assumes "c \<in> set (filter P xs)"
    and "c \<noteq> last (filter P xs)"
  shows "\<exists>i j. i < j \<and> j < length xs \<and> xs ! i = c \<and> xs ! j = last (filter P xs)"
using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    let ?fxs = "filter P xs"
    have f_Cons: "filter P (x # xs) = x # ?fxs" using True by simp

    show ?thesis
    proof (cases "c = x")
      case True_c: True
      (* If c then is element, then it in originallist as 0 *)
      have "?fxs \<noteq> []" using Cons.prems(2) f_Cons True_c by auto
      hence last_eq: "last (filter P (x # xs)) = last ?fxs" using f_Cons by simp

      have "last ?fxs \<in> set ?fxs" using `?fxs \<noteq> []`
        using last_in_set by blast
      then obtain k where "k < length xs" "xs ! k = last ?fxs"
        unfolding in_set_conv_nth
        by (metis filter_is_subset in_set_conv_nth subset_iff)

      hence "0 < Suc k" "Suc k < length (x # xs)"
            "(x # xs) ! 0 = c" "(x # xs) ! Suc k = last (filter P (x # xs))"
        using True_c last_eq by auto
      thus ?thesis by blast
    next
      case False_c: False
      (* If c is, then it in after list in *)
      have c_in: "c \<in> set ?fxs" using Cons.prems(1) f_Cons False_c by auto
      have "?fxs \<noteq> []" using c_in
        by force
      hence last_eq: "last (filter P (x # xs)) = last ?fxs" using f_Cons by simp
      have c_neq: "c \<noteq> last ?fxs" using Cons.prems(2) last_eq by simp

      (* Use *)
      from Cons.IH[OF c_in c_neq] obtain i j where
        "i < j" "j < length xs" "xs ! i = c" "xs ! j = last ?fxs" by blast

      hence "Suc i < Suc j" "Suc j < length (x # xs)"
            "(x # xs) ! Suc i = c" "(x # xs) ! Suc j = last (filter P (x # xs))"
        using last_eq by auto
      thus ?thesis by blast
    qed
  next
    case False
    (* If be, use and translate *)
    have f_Cons: "filter P (x # xs) = filter P xs" using False by simp
    have c_in: "c \<in> set (filter P xs)" using Cons.prems(1) f_Cons by simp
    have c_neq: "c \<noteq> last (filter P xs)" using Cons.prems(2) f_Cons by simp

    from Cons.IH[OF c_in c_neq] obtain i j where
      "i < j" "j < length xs" "xs ! i = c" "xs ! j = last (filter P xs)" by blast

    hence "Suc i < Suc j" "Suc j < length (x # xs)"
          "(x # xs) ! Suc i = c" "(x # xs) ! Suc j = last (filter P (x # xs))"
      using f_Cons by auto
    thus ?thesis by blast
  qed
qed

(* ========================================================================= *)
(* Helper lemma: Pending Call is this processhistory in of last one event *)
(* : HasPendingDeq, hI2_SSN_Bounds (SSN), hI6_SSN_Order (SSN monotonicity) *)
(* ========================================================================= *)
lemma pending_call_is_last:
  assumes pending: "HasPendingDeq s p"
    and ai11: "hI2_SSN_Bounds s"
    and ssn_order: "hI6_SSN_Order s"
  shows "last (filter (\<lambda>e. act_pid e = p) (his_seq s)) = mk_act deq BOT p (s_var s p) call"
proof -
  let ?p_his = "filter (\<lambda>e. act_pid e = p) (his_seq s)"

  (* 1. Pending element c of in *)
  (* Unfold definition, make Isabelle to physical of consistency *)
  have "mk_act deq BOT p (s_var s p) call \<in> set (his_seq s)"
    using pending
    unfolding HasPendingDeq_def DeqCallInHis_def Let_def
              mk_act_def act_pid_def act_name_def act_cr_def act_val_def act_ssn_def
    by force

  then obtain c where c_in: "c \<in> set (his_seq s)"
    and c_def: "c = mk_act deq BOT p (s_var s p) call"
    by blast

  have c_mem: "c \<in> set ?p_his"
    using c_in c_def by (auto simp: mk_act_def act_pid_def)

  have p_his_not_empty: "?p_his \<noteq> []"
    using c_mem by (auto simp: filter_empty_conv)

  (* 2. hI2_SSN_Bounds: c of sequence number is *)
  have ssn_bound: "\<forall>e \<in> set ?p_his. act_ssn e \<le> s_var s p"
    using ai11 unfolding hI2_SSN_Bounds_def Let_def by auto

  (* 3. extract Pending nomatch Ret of fact *)
  have no_ret: "\<not> (\<exists>e \<in> set ?p_his. act_ssn e = s_var s p \<and> act_cr e = ret)"
    using pending unfolding HasPendingDeq_def DeqCallInHis_def Let_def by auto

  (* 4. use hI6_SSN_Order *)
  show ?thesis
  proof (rule ccontr)
    assume not_last: "last ?p_his \<noteq> mk_act deq BOT p (s_var s p) call"

    have last_is_mem: "last ?p_his \<in> set ?p_his"
      using p_his_not_empty
      using last_in_set by blast

      (* C and last mapping original his_seq s of i and j *)
          (* Prove of list: *)
          have c_neq_last: "c \<noteq> last ?p_his" using not_last c_def by simp

          from filter_last_index_order[OF c_mem c_neq_last]
          obtain i j where idx_props:
            "i < j" "j < length (his_seq s)"
            "his_seq s ! i = c"
            "his_seq s ! j = last ?p_his"
            by blast

    have pid_eq: "act_pid (his_seq s ! i) = act_pid (his_seq s ! j)"
      using idx_props(3,4) c_mem last_is_mem by auto

    (* HI6_SSN_Order of *)
    from ssn_order[unfolded hI6_SSN_Order_def, rule_format, OF _ idx_props(2)] idx_props(1) pid_eq
    have "act_ssn c < act_ssn (last ?p_his) \<or>
          (act_ssn c = act_ssn (last ?p_his) \<and> act_cr c = call \<and> act_cr (last ?p_his) = ret)"
      using idx_props(3,4)
      using idx_props(2) by auto

    (* Branch A: sequence number large?impossible, be hI2_SSN_Bounds *)
    moreover have "\<not> (act_ssn c < act_ssn (last ?p_his))"
    proof -
      (* 1. use blast set, to of *)
      have "act_ssn (last ?p_his) \<le> s_var s p"
        using ssn_bound last_is_mem by blast

      (* 2. use simp, out c of precisesequence number *)
      moreover have "act_ssn c = s_var s p"
        using c_def by (simp add: mk_act_def act_ssn_def)

      (* 3. two, contradiction out *)
      ultimately show ?thesis by simp
    qed

    (* Branch B: is one sequence number of Ret?impossible, Pending return *)
    moreover have "\<not> (act_ssn c = act_ssn (last ?p_his) \<and> act_cr c = call \<and> act_cr (last ?p_his) = ret)"
    proof -
      (* 1. c of *)
      have c_props: "act_ssn c = s_var s p" "act_cr c = call"
        using c_def by (simp_all add: mk_act_def act_ssn_def act_cr_def)

      (* 2. use blast no_ret of setderivation, last one elementimpossible is invariant of ret *)
      moreover have "\<not> (act_ssn (last ?p_his) = s_var s p \<and> act_cr (last ?p_his) = ret)"
        using no_ret last_is_mem by blast

      (* 3. precise *)
      ultimately show ?thesis using c_props by simp
    qed

    (* , success *)
    ultimately show False by blast
  qed
qed


lemma modify_lin_HB_stable:
  assumes HB_EQ: "\<And>a b. happens_before a b H' = happens_before a b H"
  shows "modify_lin L H' v = modify_lin L H v"
  using HB_EQ
proof (induction L H' v arbitrary: H rule: modify_lin.induct)
  case step: (1 L H' v)

  have HB_EQ': "\<And>a b. happens_before a b H' = happens_before a b H"
    using step.prems .

  have sm_eq: "should_modify L H' v = should_modify L H v"
    unfolding should_modify_def
    by simp

  show ?case
  proof (cases "should_modify L H' v")
    case False

    have FalseH: "\<not> should_modify L H v"
      using False sm_eq
      by simp

    have lhs: "modify_lin L H' v = L"
      using False
      by (subst modify_lin.simps) simp

    have rhs: "modify_lin L H v = L"
      using FalseH
      by (subst modify_lin.simps) simp

    show ?thesis
      using lhs rhs
      by simp

  next
    case True
    note do_modify_H' = True

    have do_modify_H: "should_modify L H v"
      using do_modify_H' sm_eq
      by simp

    define last_sa_pos where
      "last_sa_pos = find_last_SA L"

    define l1 where
      "l1 = take (nat (last_sa_pos + 1)) L"

    define remaining where
      "remaining = drop (nat (last_sa_pos + 1)) L"

    have idx_exists:
      "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) remaining \<noteq> None"
    proof
      assume none:
        "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) remaining = None"
      have False
        using do_modify_H' none
        unfolding should_modify_def last_sa_pos_def remaining_def
        by simp
      thus False .
    qed

    obtain bt_idx where bt_idx_def:
      "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) remaining = Some bt_idx"
      using idx_exists
      by (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) remaining") auto

    define bt_act where
      "bt_act = remaining ! bt_idx"

    define l2 where
      "l2 = take bt_idx remaining"

    define l3 where
      "l3 = drop (bt_idx + 1) remaining"

    have l2_not_nil: "l2 \<noteq> []"
    proof
      assume nil: "l2 = []"
      have False
        using do_modify_H' bt_idx_def nil
        unfolding should_modify_def last_sa_pos_def remaining_def l2_def
        by simp
      thus False .
    qed

    define l2_last where
      "l2_last = last l2"

    show ?thesis
    proof (cases "op_name l2_last = enq")
      case True
      note l2_last_enq = True

      define new_L where
        "new_L = l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3"

      have lhs:
        "modify_lin L H' v = modify_lin new_L H' v"
        using do_modify_H' bt_idx_def l2_last_enq
        unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                  l2_def l3_def l2_last_def new_L_def
        apply (subst (1) modify_lin.simps)
        by (simp del: modify_lin.simps add: Let_def)

      have rhs:
        "modify_lin L H v = modify_lin new_L H v"
        using do_modify_H bt_idx_def l2_last_enq
        unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                  l2_def l3_def l2_last_def new_L_def
        apply (subst (1) modify_lin.simps)
        by (simp del: modify_lin.simps add: Let_def)

      have the_bt_idx:
        "the (find_unique_index
                (\<lambda>a. op_name a = enq \<and> op_val a = v)
                (drop (nat (find_last_SA L + 1)) L)) = bt_idx"
        using bt_idx_def
        unfolding remaining_def last_sa_pos_def
        by simp

      have rec:
        "modify_lin new_L H' v = modify_lin new_L H v"
        apply
          (rule step.IH(1)
            [where H = H
               and x  = "Distance L v"
               and xa = last_sa_pos
               and xb = l1
               and xc = remaining
               and xd = bt_idx
               and xe = bt_act
               and xf = l2
               and xg = l3
               and xh = l2_last
               and xi = "butlast l2"
               and xj = new_L])
        subgoal
          using do_modify_H'
          by simp
        subgoal
          by simp
        subgoal
          unfolding last_sa_pos_def
          by simp
        subgoal
          unfolding l1_def
          by simp
        subgoal
          unfolding remaining_def
          by simp
        subgoal
          using bt_idx_def
          by simp
        subgoal
          unfolding bt_act_def
          by simp
        subgoal
          unfolding l2_def
          by simp
        subgoal
          unfolding l3_def
          by simp
        subgoal
          unfolding l2_last_def
          by simp
        subgoal
          using l2_last_enq
          by simp
        subgoal
          by simp
        subgoal
          unfolding new_L_def
          by simp
        subgoal
          using step.prems
          by simp
        done

      show ?thesis
        using lhs rhs rec
        by simp

    next
      case False
      note l2_last_not_enq = False

      have fle_not_none:
        "find_last_enq l2 \<noteq> None"
      proof
        assume none: "find_last_enq l2 = None"
        have False
          using do_modify_H' bt_idx_def l2_last_not_enq none
          unfolding should_modify_def last_sa_pos_def remaining_def
                    l2_def l2_last_def
          by simp
        thus False .
      qed

      obtain l21 b_act l22 where fle:
        "find_last_enq l2 = Some (l21, b_act, l22)"
        using fle_not_none
        by (cases "find_last_enq l2") auto

      have l22_not_nil: "l22 \<noteq> []"
      proof
        assume nil: "l22 = []"
        have False
          using do_modify_H' bt_idx_def l2_last_not_enq fle nil
          unfolding should_modify_def last_sa_pos_def remaining_def
                    l2_def l2_last_def
          by simp
        thus False .
      qed

      define o1 where
        "o1 = hd l22"

      define ou where
        "ou = last l22"

      have hb1_eq:
        "happens_before o1 bt_act H' = happens_before o1 bt_act H"
        using HB_EQ' by simp

      have hb2_eq:
        "happens_before b_act o1 H' = happens_before b_act o1 H"
        using HB_EQ' by simp

      show ?thesis
      proof (cases "happens_before o1 bt_act H'")
        case True
        note hb1_H' = True

        have hb1_H: "happens_before o1 bt_act H"
          using hb1_H' hb1_eq
          by simp

        define new_L where
          "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        have lhs:
          "modify_lin L H' v = modify_lin new_L H' v"
          using do_modify_H' bt_idx_def l2_last_not_enq fle hb1_H'
          unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                    l2_def l3_def l2_last_def o1_def ou_def new_L_def
          apply (subst (1) modify_lin.simps)
          by (simp del: modify_lin.simps add: Let_def)

        have rhs:
          "modify_lin L H v = modify_lin new_L H v"
          using do_modify_H bt_idx_def l2_last_not_enq fle hb1_H
          unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                    l2_def l3_def l2_last_def o1_def ou_def new_L_def
          apply (subst (1) modify_lin.simps)
          by (simp del: modify_lin.simps add: Let_def)

        have rec:
          "modify_lin new_L H' v = modify_lin new_L H v"
          apply (rule step.IH(2))

          apply (tactic \<open>ALLGOALS (simp_tac (put_simpset HOL_basic_ss @{context}
            addsimps @{thms last_sa_pos_def remaining_def l1_def l2_def l3_def
                            bt_act_def l2_last_def o1_def ou_def new_L_def} ))\<close>)

          subgoal
            using do_modify_H'
            by simp

          subgoal
            using bt_idx_def
            unfolding remaining_def last_sa_pos_def
            by simp

          subgoal
            using l2_last_not_enq
            unfolding l2_last_def l2_def remaining_def last_sa_pos_def
            by simp

          subgoal
            using fle
            unfolding l2_def remaining_def last_sa_pos_def
            by simp

          subgoal
            using hb1_H'
            unfolding o1_def bt_act_def remaining_def last_sa_pos_def
            by simp

          subgoal
            using step.prems
            by simp
          done

        show ?thesis
          using lhs rhs rec
          by simp

      next
        case False
        note hb1_false_H' = False

        have hb1_false_H: "\<not> happens_before o1 bt_act H"
          using hb1_false_H' hb1_eq
          by simp

        show ?thesis
        proof (cases "happens_before b_act o1 H'")
          case True
          note hb2_H' = True

          have hb2_H: "happens_before b_act o1 H"
            using hb2_H' hb2_eq
            by simp

          define new_L where
            "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"

          have lhs:
            "modify_lin L H' v = modify_lin new_L H' v"
            using do_modify_H' bt_idx_def l2_last_not_enq fle
                  hb1_false_H' hb2_H'
            unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                      l2_def l3_def l2_last_def o1_def ou_def new_L_def
            apply (subst (1) modify_lin.simps)
            by (simp del: modify_lin.simps add: Let_def)

          have rhs:
            "modify_lin L H v = modify_lin new_L H v"
            using do_modify_H bt_idx_def l2_last_not_enq fle
                  hb1_false_H hb2_H
            unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                      l2_def l3_def l2_last_def o1_def ou_def new_L_def
            apply (subst (1) modify_lin.simps)
            by (simp del: modify_lin.simps add: Let_def)

          have rec:
            "modify_lin new_L H' v = modify_lin new_L H v"
            apply (rule step.IH(3))

            apply (tactic \<open>ALLGOALS (simp_tac (put_simpset HOL_basic_ss @{context}
              addsimps @{thms last_sa_pos_def remaining_def l1_def l2_def l3_def
                              bt_act_def l2_last_def o1_def ou_def new_L_def} ))\<close>)

            subgoal
              using do_modify_H'
              by simp

            subgoal
              using bt_idx_def
              unfolding remaining_def last_sa_pos_def
              by simp

            subgoal
              using l2_last_not_enq
              unfolding l2_last_def l2_def remaining_def last_sa_pos_def
              by simp

            subgoal
              using fle
              unfolding l2_def remaining_def last_sa_pos_def
              by simp

            subgoal
              using hb1_false_H'
              unfolding o1_def bt_act_def remaining_def last_sa_pos_def
              by simp

            subgoal
              using hb2_H'
              unfolding o1_def
              by simp

            subgoal
              using step.prems
              by simp

            done

          show ?thesis
            using lhs rhs rec
            by simp

        next
          case False
          note hb2_false_H' = False

          have hb2_false_H: "\<not> happens_before b_act o1 H"
            using hb2_false_H' hb2_eq
            by simp

          define new_L where
            "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

          have lhs:
            "modify_lin L H' v = modify_lin new_L H' v"
            using do_modify_H' bt_idx_def l2_last_not_enq fle
                  hb1_false_H' hb2_false_H'
            unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                      l2_def l3_def l2_last_def o1_def ou_def new_L_def
            apply (subst (1) modify_lin.simps)
            by (simp del: modify_lin.simps add: Let_def)

          have rhs:
            "modify_lin L H v = modify_lin new_L H v"
            using do_modify_H bt_idx_def l2_last_not_enq fle
                  hb1_false_H hb2_false_H
            unfolding last_sa_pos_def l1_def remaining_def bt_act_def
                      l2_def l3_def l2_last_def o1_def ou_def new_L_def
            apply (subst (1) modify_lin.simps)
            by (simp del: modify_lin.simps add: Let_def)

          have rec:
            "modify_lin new_L H' v = modify_lin new_L H v"
            apply (rule step.IH(4))

            apply (tactic \<open>ALLGOALS (simp_tac (put_simpset HOL_basic_ss @{context}
              addsimps @{thms last_sa_pos_def remaining_def l1_def l2_def l3_def
                              bt_act_def l2_last_def o1_def ou_def new_L_def} ))\<close>)

            subgoal
              using do_modify_H'
              by simp

            subgoal
              using bt_idx_def
              unfolding remaining_def last_sa_pos_def
              by simp

            subgoal
              using l2_last_not_enq
              unfolding l2_last_def l2_def remaining_def last_sa_pos_def
              by simp

            subgoal
              using fle
              unfolding l2_def remaining_def last_sa_pos_def
              by simp

            subgoal
              using hb1_false_H'
              unfolding o1_def bt_act_def remaining_def last_sa_pos_def
              by simp

            subgoal
              using hb2_false_H'
              unfolding o1_def
              by simp

            subgoal
              using step.prems
              by simp

            done

          show ?thesis
            using lhs rhs rec
            by simp
        qed
      qed
    qed
  qed
qed




end
