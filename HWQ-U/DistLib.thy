theory DistLib
  imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
begin

(* : value and its of is 0 *)
lemma distance_self_zero:
  assumes "data_independent L"
  shows "distance_func v v L = 0"
proof -
  have "distance_func v v L = (
    if in_SA v L then 0
    else
      (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L of
         None \<Rightarrow> 0
       | Some pos_x \<Rightarrow>
           (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L of
              None \<Rightarrow> 0
            | Some pos_bt \<Rightarrow>
                if pos_x < pos_bt then pos_bt - pos_x else 0))
  )"
    by (simp add: distance_func_def)

  (* Now two case: in_SA v L as real or *)
  show ?thesis
  proof (cases "in_SA v L")
    case True
    then show ?thesis by (simp add: distance_func_def)
  next
    case False
    (* When in SA in, we need find_unique_index *)
    let ?idx = "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L"
    show ?thesis
    proof (cases ?idx)
      case None
      then show ?thesis using False by (simp add: distance_func_def)
    next
      case (Some pos_x)
      (* Key: No. two find_unique_index use and No. one, therefore also returnSome pos_x *)
      have same_idx: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some pos_x"
        by (simp add: Some)

      (* Pos_bt = pos_x, thereforepos_x < pos_bt as *)
      show ?thesis using False Some
        by (simp add: distance_func_def same_idx)
    qed
  qed
qed

(* Prove Distance is of, use in prove *)
lemma Distance_nonneg: "Distance L bt_val \<ge> 0"
  unfolding Distance_def
  by (simp add: sum_list_nonneg)


(* Use: for in preserve of prefix l1, its in enqueue value of does not *)
lemma l1_distance_non_increasing:
  assumes di_L: "data_independent L"
      and di_new_L: "data_independent new_L"
      and L_decomp: "L = l1 @ rest_L"
      and new_L_decomp: "new_L = l1 @ rest_new"
      and bt_unique_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some pos_bt_L"
      and bt_unique_new_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = Some pos_bt_new"
      and pos_bt_new_le: "pos_bt_new \<le> pos_bt_L"
      and same_SA: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L"
    shows "\<forall>v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l1)).
           distance_func v bt_val new_L \<le> distance_func v bt_val L"
proof
  fix v
  assume v_in: "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l1))"

  (* V in l1 in of enqueue operation *)
  from v_in obtain a where
    a_def: "a \<in> set (filter (\<lambda>a. op_name a = enq) l1)" "op_val a = v"
    by auto

  from a_def(1) have a_in_l1: "a \<in> set l1" and a_enq: "op_name a = enq"
    by auto

  (* To a in l1 in of *)
  obtain k where
    k_lt: "k < length l1" and l1_at_k: "l1 ! k = a"
    using a_in_l1 by (auto simp: in_set_conv_nth)

  (* In L and new_L in, k of operation all is a *)
  have L_at_k: "L ! k = a"
    using L_decomp k_lt
    by (simp add: l1_at_k nth_append_left)

  have new_L_at_k: "new_L ! k = a"
    using new_L_decomp k_lt
    by (simp add: l1_at_k nth_append_left)

  (* Sincedata, v of enqueue operation in L and new_L in all is one of, and as k *)
  have v_unique_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some k"
  proof -
    from di_L L_at_k a_enq a_def(2) k_lt
    have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L = [k]"
      using unique_enq_index L_decomp length_append nth_append
      by force
    then show ?thesis
      by (simp add: find_unique_index_def)
  qed

  have v_unique_new_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some k"
  proof -
    from di_new_L new_L_at_k a_enq a_def(2) k_lt
    have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = [k]"
      using unique_enq_index  new_L_decomp length_append nth_append
      by force
    then show ?thesis
      by (simp add: find_unique_index_def)
  qed

  (* Use same_SA *)
  have same_SA_v: "in_SA v new_L \<longleftrightarrow> in_SA v L"
    by (simp add: same_SA)

  (* Proof note *)
  show "distance_func v bt_val new_L \<le> distance_func v bt_val L"
  proof (cases "in_SA v L")
    case True
    (* V in SA in, new old all as 0 *)
    then have "in_SA v new_L"
      using same_SA_v by simp
    then show ?thesis
      by (simp add: True distance_func_def)
  next
    case False
    (* V in SA in *)
    then have not_in_SA: "\<not> in_SA v L" "\<not> in_SA v new_L"
      using same_SA_v by auto

    (* Unfold *)
    have dist_L: "distance_func v bt_val L =
                 (if k < pos_bt_L then pos_bt_L - k else 0)"
      by (simp add: distance_func_def v_unique_L bt_unique_L False)

    have dist_new_L: "distance_func v bt_val new_L =
                     (if k < pos_bt_new then pos_bt_new - k else 0)"
      by (simp add: distance_func_def v_unique_new_L bt_unique_new_L not_in_SA(2))

    (* K and pos_bt_new, pos_bt_L of case *)
    show ?thesis
    proof (cases "k < pos_bt_new")
      case True
      (* k < pos_bt_new \<le> pos_bt_L *)
      then have "k < pos_bt_L"
        using pos_bt_new_le by linarith
      with True show ?thesis
        by (simp add: diff_le_mono dist_L dist_new_L pos_bt_new_le)
    next
      case False
      (* k \<ge> pos_bt_new *)
      then show ?thesis
      proof (cases "k < pos_bt_L")
        case True
        (* pos_bt_new \<le> k < pos_bt_L *)
        with False show ?thesis
          by (simp add: dist_L dist_new_L)
      next
        case False2: False
        (* k \<ge> pos_bt_L *)
        then show ?thesis
          by (simp add: False dist_new_L)
    qed
  qed
qed
qed

(* : for in preserve of enqueue valueset, if bt_val of before or, then does not *)
lemma same_position_set_distance_non_increasing:
  assumes di_L: "data_independent L"
      and di_new_L: "data_independent new_L"
      and same_positions: "\<forall>v \<in> values.
            find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L =
            find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L"
      and bt_unique_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some pos_bt_L"
      and bt_unique_new_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = Some pos_bt_new"
      and pos_bt_new_le: "pos_bt_new \<le> pos_bt_L"
      and same_SA: "\<forall>v \<in> values. in_SA v new_L \<longleftrightarrow> in_SA v L"
    shows "\<forall>v \<in> values. distance_func v bt_val new_L \<le> distance_func v bt_val L"
proof
  fix v
  assume v_in: "v \<in> values"

  (* V in two in of *)
  from same_positions v_in have
    pos_eq: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L =
            find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L"
    by simp

  (* Need find_unique_index may as None of case *)
  show "distance_func v bt_val new_L \<le> distance_func v bt_val L"
  proof (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L")
    case None
    then have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = None"
      using pos_eq by simp

    (* If in enqueue operation, as 0 *)
    have dist_L: "distance_func v bt_val L = 0"
      by (simp add: distance_func_def None)

    have dist_new: "distance_func v bt_val new_L = 0"
      by (simp add: distance_func_def `find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = None`)

    then show ?thesis by (simp add: dist_L)

  next
    case (Some pos_v)
    then have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some pos_v"
      using pos_eq by simp

    (* Use same_SA *)
    have same_SA_v: "in_SA v new_L \<longleftrightarrow> in_SA v L"
      using same_SA v_in by simp

    (* Proof note *)
    show ?thesis
    proof (cases "in_SA v L")
      case True
      then have "in_SA v new_L"
        using same_SA_v by simp
      then show ?thesis
        by (simp add: True distance_func_def)
    next
      case False
      then have not_in_SA: "\<not> in_SA v L" "\<not> in_SA v new_L"
        using same_SA_v by auto

      (* Unfold *)
      have dist_L: "distance_func v bt_val L =
                   (if pos_v < pos_bt_L then pos_bt_L - pos_v else 0)"
        by (simp add: distance_func_def Some bt_unique_L False)

      have dist_new: "distance_func v bt_val new_L =
                     (if pos_v < pos_bt_new then pos_bt_new - pos_v else 0)"
        by (simp add: distance_func_def `find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some pos_v`
                      bt_unique_new_L not_in_SA(2))

      (* Pos_v and pos_bt_new, pos_bt_L of case *)
      show ?thesis
      proof (cases "pos_v < pos_bt_new")
        case True
        (* pos_v < pos_bt_new \<le> pos_bt_L *)
        then have "pos_v < pos_bt_L"
          using pos_bt_new_le by linarith
        with True show ?thesis
          by (simp add: diff_le_mono dist_L dist_new pos_bt_new_le)
      next
        case False
        (* pos_v \<ge> pos_bt_new *)
        then show ?thesis
        proof (cases "pos_v < pos_bt_L")
          case True
          (* pos_bt_new \<le> pos_v < pos_bt_L *)
          with False show ?thesis
            by (simp add: dist_L dist_new)
        next
          case False2: False
          (* pos_v \<ge> pos_bt_L *)
          then show ?thesis
            by (simp add: False dist_new)
        qed
      qed
    qed
  qed
qed

(* New: l3 in enqueue operationvalue of as 0, use l1_contains_all_SA_in_L of *)
lemma l3_distance_zero_observational:
  assumes "data_independent L"
  assumes "L = l1 @ middle @ l3"
  assumes "bt_act \<in> set middle"
  assumes "op_name bt_act = enq"
  assumes "op_val bt_act = bt_val"
  assumes "l1 = take (nat (last_sa_pos + 1)) L"
  assumes "last_sa_pos = find_last_SA L"
  assumes "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
  shows "distance_func v bt_val L = 0"
proof -
  (* Middle @ l3 as l2 *)
  define l2 where "l2 = middle @ l3"
  have L_decomp: "L = l1 @ l2" and l2_nonempty: "l2 \<noteq> []"
    using assms(2,3) unfolding l2_def by auto

  (* Use l1_contains_all_SA_in_L obtain SA property *)
  have l1_contains: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow>
    \<not> in_SA (op_val (L ! i)) L"
    using l1_contains_all_SA_in_L[OF assms(1) L_decomp l2_nonempty assms(6,7)] .

  (* From l3 in v of enqueue operation *)
  from assms(8) obtain a where
    a_def: "a \<in> set (filter (\<lambda>a. op_name a = enq) l3)" "op_val a = v"
    by auto
  then have a_in_l3: "a \<in> set l3" and a_enq: "op_name a = enq"
    by auto

  (* To a in l3 in of *)
  from a_in_l3 obtain i where
    i_lt: "i < length l3" and l3_at_i: "l3 ! i = a"
    by (auto simp: in_set_conv_nth)

  (* A in L in of definitely *)
  let ?pos_v = "length l1 + length middle + i"
  have pos_v_bounds: "?pos_v < length L"
    using assms(2) i_lt by auto
  have L_at_pos_v: "L ! ?pos_v = a"
    by (simp add: assms(2) i_lt l3_at_i nth_append)

  (* Prove v in SA in *)
  have v_not_in_SA: "\<not> in_SA v L"
  proof -
    have "?pos_v \<ge> length l1" by simp
    with pos_v_bounds a_enq L_at_pos_v a_def(2)
    show ?thesis using l1_contains by metis
  qed

  (* To bt_act in middle in of *)
  from assms(3) obtain j where
    j_lt: "j < length middle" and middle_at_j: "middle ! j = bt_act"
    by (auto simp: in_set_conv_nth)

  (* Bt_act in L in of definitely *)
  let ?pos_bt = "length l1 + j"
  have pos_bt_bounds: "?pos_bt < length L"
    using assms(2) j_lt by auto
  have L_at_pos_bt: "L ! ?pos_bt = bt_act"
    by (simp add: assms(2) j_lt middle_at_j nth_append)

  (* Prove bt_val of enqueue operation in L in one *)
  have bt_unique: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some ?pos_bt"
  proof -
    from assms(1) L_at_pos_bt assms(4,5) pos_bt_bounds
    have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = [?pos_bt]"
      by (simp add: unique_enq_index)
    then show ?thesis
      by (simp add: find_unique_index_def)
  qed

  (* Prove v of enqueue operation in L in one *)
  have v_unique: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some ?pos_v"
  proof -
    from assms(1) L_at_pos_v a_enq a_def(2) pos_v_bounds
    have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L = [?pos_v]"
      by (simp add: unique_enq_index)
    then show ?thesis
      by (simp add: find_unique_index_def)
  qed

  (* Prove v of in bt_val afterwards *)
  have "?pos_v > ?pos_bt"
  proof -
    from j_lt have "j < length middle" .
    then have "?pos_bt < length l1 + length middle" by simp
    also have "... \<le> ?pos_v" by simp
    finally show ?thesis .
  qed

  (* Definition, v in SA in and in bt_val afterwards, as 0 *)
  show ?thesis
    unfolding distance_func_def
    using v_not_in_SA v_unique bt_unique `?pos_v > ?pos_bt`
    by simp
qed



lemma distance_func_observational:
  assumes "data_independent L"
  assumes "L = pre @ [x_act] @ middle @ [bt_act] @ suf"
  assumes "op_name x_act = enq" "op_val x_act = x_val"
  assumes "op_name bt_act = enq" "op_val bt_act = bt_val"
  assumes "\<not> in_SA x_val L"  (* assms(5) *)
  shows "distance_func x_val bt_val L = length middle + 1"
proof -
  (* 1. x_act of *)
  let ?pos_x = "length pre"
  have x_at_idx: "L ! ?pos_x = x_act"
    using assms(2) by (simp add: nth_append)

  (* 2. bt_act of *)
  let ?pos_bt = "length pre + 1 + length middle"
  have bt_at_idx: "L ! ?pos_bt = bt_act"
    using assms(2) by (simp add: nth_append)

  (* 3. usedata prove uniqueness *)
  have unique_x: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L = Some ?pos_x"
  proof -
    let ?P = "\<lambda>a. op_name a = enq \<and> op_val a = x_val"
    let ?S = "{i. i < length L \<and> ?P (L ! i)}"

    (* Step A: Existence *)
    have pos_x_matches: "?pos_x < length L \<and> ?P (L ! ?pos_x)"
      using x_at_idx assms(3) assms(2)
      by (simp add: assms(4))

    (* Step B: Uniqueness *)
    have card_le_1: "card ?S \<le> 1"
      using assms(1) unfolding data_independent_def by simp

    have set_is_singleton: "?S = {?pos_x}"
    proof -
      have "?pos_x \<in> ?S" using pos_x_matches by simp
      have "\<forall>y \<in> ?S. y = ?pos_x"
      proof (rule ccontr)
        assume "\<not> (\<forall>y \<in> ?S. y = ?pos_x)"
        then obtain y where "y \<in> ?S" "y \<noteq> ?pos_x" by blast
        then have "{?pos_x, y} \<subseteq> ?S" using `?pos_x \<in> ?S` by simp
        then have "card {?pos_x, y} \<le> card ?S"
          using card_mono[of ?S "{?pos_x, y}"] by simp
        moreover have "card {?pos_x, y} = 2"
          using `y \<noteq> ?pos_x` by simp
        ultimately have "2 \<le> card ?S" by simp
        then show False using card_le_1 by simp
      qed
      then show ?thesis using `?pos_x \<in> ?S` by fastforce
    qed

    (* Step C: List Construction *)
    have indices_eq: "find_indices ?P L = [?pos_x]"
    proof -
      let ?k = "?pos_x"
      let ?n = "length L"

      have pointwise_equiv: "\<forall>i \<in> set [0..<length L]. ?P (L ! i) \<longleftrightarrow> i = ?k"
      proof
        fix i assume "i \<in> set [0..<length L]"
        then have i_bound: "i < length L" by simp
        show "?P (L ! i) \<longleftrightarrow> i = ?k"
        proof
          assume "?P (L ! i)" then have "i \<in> ?S" using i_bound by simp
          then show "i = ?k" using set_is_singleton by simp
        next
          assume "i = ?k" show "?P (L ! i)" using pos_x_matches `i = ?k` by simp
        qed
      qed

      have "filter (\<lambda>i. ?P (L ! i)) [0..<?n] = filter (\<lambda>i. i = ?k) [0..<?n]"
        apply (rule filter_cong) apply (rule refl) using pointwise_equiv by simp

      also have "... = [?k]"
      proof -
        have k_bound: "?k < ?n" using pos_x_matches by simp
        have split_interval: "[0..<?n] = [0..<?k] @ [?k] @ [Suc ?k..<?n]"
          using k_bound upt_add_eq_append[of 0 ?k "?n - ?k"] upt_conv_Cons by simp
        have "filter (\<lambda>i. i = ?k) [0..<?n] = filter (\<lambda>i. i = ?k) ([0..<?k] @ [?k] @ [Suc ?k..<?n])"
          using split_interval by simp
        also have "... = [] @ [?k] @ []"
        proof -
          have "filter (\<lambda>i. i = ?k) [0..<?k] = []"
            using filter_empty_conv by (auto)
          moreover have "filter (\<lambda>i. i = ?k) [?k] = [?k]" by simp
          moreover have "filter (\<lambda>i. i = ?k) [Suc ?k..<?n] = []"
            using filter_empty_conv by (auto)
          ultimately show ?thesis by simp
        qed
        finally show ?thesis by simp
      qed
      finally show ?thesis unfolding find_indices_def by simp
    qed

    show ?thesis unfolding find_unique_index_def using indices_eq by simp
  qed

  (* 4. prove is one of bt_val Enqueue *)
  have unique_bt: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some ?pos_bt"
  proof -
    let ?P = "\<lambda>a. op_name a = enq \<and> op_val a = bt_val"
    let ?S = "{i. i < length L \<and> ?P (L ! i)}"

    have pos_bt_matches: "?pos_bt < length L \<and> ?P (L ! ?pos_bt)"
      using assms(2,5,6) bt_at_idx by force

    have card_le_1: "card ?S \<le> 1" using assms(1) unfolding data_independent_def by simp

    have set_is_singleton: "?S = {?pos_bt}"
    proof -
      have "?pos_bt \<in> ?S" using pos_bt_matches by simp
      have "\<forall>y \<in> ?S. y = ?pos_bt"
      proof (rule ccontr)
        assume "\<not> (\<forall>y \<in> ?S. y = ?pos_bt)"
        then obtain y where "y \<in> ?S" "y \<noteq> ?pos_bt" by blast
        then have "{?pos_bt, y} \<subseteq> ?S" using `?pos_bt \<in> ?S` by simp
        then have "card {?pos_bt, y} \<le> card ?S"
          using card_mono[of ?S "{?pos_bt, y}"] by simp
        moreover have "card {?pos_bt, y} = 2"
          using `y \<noteq> ?pos_bt` by simp
        ultimately have "2 \<le> card ?S" by simp
        then show False using card_le_1 by simp
      qed
      then show ?thesis using `?pos_bt \<in> ?S` by blast
    qed

    have indices_eq: "find_indices ?P L = [?pos_bt]"
    proof -
      let ?k = "?pos_bt"
      let ?n = "length L"

      have pointwise_equiv: "\<forall>i \<in> set [0..<length L]. ?P (L ! i) \<longleftrightarrow> i = ?k"
      proof
        fix i assume "i \<in> set [0..<length L]"
        then have i_bound: "i < length L" by simp
        show "?P (L ! i) \<longleftrightarrow> i = ?k"
        proof
          assume "?P (L ! i)" then have "i \<in> ?S" using i_bound by simp
          then show "i = ?k" using set_is_singleton by simp
        next
          assume "i = ?k" show "?P (L ! i)" using pos_bt_matches `i = ?k` by simp
        qed
      qed

      have "filter (\<lambda>i. ?P (L ! i)) [0..<?n] = filter (\<lambda>i. i = ?k) [0..<?n]"
        apply (rule filter_cong) apply (rule refl) using pointwise_equiv by simp

      also have "... = [?k]"
      proof -
        have k_bound: "?k < ?n" using pos_bt_matches by simp
        have split_interval: "[0..<?n] = [0..<?k] @ [?k] @ [Suc ?k..<?n]"
          using k_bound upt_add_eq_append[of 0 ?k "?n - ?k"] upt_conv_Cons
          by (metis append_Cons append_Nil
              canonically_ordered_monoid_add_class.lessE upt_add_eq_append
              zero_le)
        have "filter (\<lambda>i. i = ?k) [0..<?n] = filter (\<lambda>i. i = ?k) ([0..<?k] @ [?k] @ [Suc ?k..<?n])"
          using split_interval by simp
        also have "... = [] @ [?k] @ []"
        proof -
          have "filter (\<lambda>i. i = ?k) [0..<?k] = []"
            using filter_empty_conv by (auto)
          moreover have "filter (\<lambda>i. i = ?k) [?k] = [?k]" by simp
          moreover have "filter (\<lambda>i. i = ?k) [Suc ?k..<?n] = []"
            using filter_empty_conv by (auto)
          ultimately show ?thesis by simp
        qed
        finally show ?thesis by simp
      qed
      finally show ?thesis unfolding find_indices_def by simp
    qed

    show ?thesis unfolding find_unique_index_def using indices_eq by simp
  qed

(* 5. *)
  show ?thesis
  proof -
    (* 1. unfolddefinition *)
    have "distance_func x_val bt_val L =
          (if in_SA x_val L then 0 else
           (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L of
              None \<Rightarrow> 0
            | Some px \<Rightarrow>
                (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                   None \<Rightarrow> 0
                 | Some pbt \<Rightarrow> if px < pbt then pbt - px else 0)))"
      unfolding distance_func_def by simp

    (* 2. use not_in_sa (assms(5)) No. one if *)
    also have "... = (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L of
                        None \<Rightarrow> 0
                      | Some px \<Rightarrow>
                          (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                             None \<Rightarrow> 0
                           | Some pbt \<Rightarrow> if px < pbt then pbt - px else 0))"
      by (simp add: assms(7))

    (* 3. use unique_x No. one case *)
    also have "... = (case Some ?pos_x of
                        None \<Rightarrow> 0
                      | Some px \<Rightarrow>
                          (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                             None \<Rightarrow> 0
                           | Some pbt \<Rightarrow> if px < pbt then pbt - px else 0))"
      using unique_x by simp

    (* 4. simplify case Some *)
    also have "... = (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                        None \<Rightarrow> 0
                      | Some pbt \<Rightarrow> if ?pos_x < pbt then pbt - ?pos_x else 0)"
      by simp

    (* 5. use unique_bt No. two case *)
    also have "... = (if ?pos_x < ?pos_bt then ?pos_bt - ?pos_x else 0)"
      using unique_bt by simp

    (* 6. simplify *)
    (* At this pointonly: (len_pre < len_pre + 1 + len_mid)... *)
    also have "... = length middle + 1"
      by simp

    (* 7. conclusion *)
    finally show ?thesis .
  qed
qed

(* Use list:
  Iflist xs x, andmapping f return (),
  Thenmapping after of and sum_list (map f xs) necessarilygreater thanequal to f x.
*)
lemma sum_list_map_ge_element:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "x \<in> set xs"
  shows "sum_list (map f xs) \<ge> f x"
proof -
  (* Use split_list xs split as: prefix @ [x] @ suffix *)
  from assms obtain ys zs where "xs = ys @ x # zs"
    by (meson split_list)

  (* Mapping after of *)
  hence "map f xs = map f ys @ (f x) # map f zs"
    by simp

  (* And unfold *)
  hence "sum_list (map f xs) = sum_list (map f ys) + f x + sum_list (map f zs)"
    by simp

  (* Because is nat, a + b + c \<ge> b into *)
  thus ?thesis by simp
qed

end