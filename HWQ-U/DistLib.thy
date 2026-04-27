theory DistLib
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
    PureLib
begin

(* ========================================================== *)
(* Distance lemmas for linearization rearrangement proofs      *)
(* ========================================================== *)

(* ========== Basic facts about the distance measure ========== *)
(* Any value has distance zero from itself. *)
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
  
  (* Split on whether v already belongs to the SetA portion of the linearization. *)
  show ?thesis
  proof (cases "in_SA v L")
    case True
    then show ?thesis by (simp add: distance_func_def)
  next
    case False
    (* Otherwise we inspect the unique enqueue position returned by find_unique_index. *)
    let ?idx = "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L"
    show ?thesis
    proof (cases ?idx)
      case None
      then show ?thesis using False by (simp add: distance_func_def)
    next
      case (Some pos_x)
      (* The two index lookups are syntactically identical, so the second one yields the same position. *)
      have same_idx: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some pos_x"
        by (simp add: Some)
      
      (* Hence pos_bt = pos_x, and the strict inequality branch is impossible. *)
      show ?thesis using False Some
        by (simp add: distance_func_def same_idx)
    qed
  qed
qed

(* The global distance measure is nonnegative, which is useful for well-founded arguments. *)
lemma Distance_nonneg: "Distance L bt_val \<ge> 0"
  unfolding Distance_def
  by (simp add: sum_list_nonneg)


(* ========== Distance monotonicity under prefix preservation ========== *)
(* If the common prefix l1 is preserved and bt_val does not move to the right,
   then the distance of each enqueue value in l1 cannot increase. *)
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
  
  (* Pick the enqueue action of v from the preserved prefix l1. *)
  from v_in obtain a where 
    a_def: "a \<in> set (filter (\<lambda>a. op_name a = enq) l1)" "op_val a = v"
    by auto
  
  from a_def(1) have a_in_l1: "a \<in> set l1" and a_enq: "op_name a = enq"
    by auto
  
  (* Recover the position of that enqueue action inside l1. *)
  obtain k where 
    k_lt: "k < length l1" and l1_at_k: "l1 ! k = a"
    using a_in_l1 by (auto simp: in_set_conv_nth)
  
  (* The same action remains at position k in both L and new_L. *)
  have L_at_k: "L ! k = a"
    using L_decomp k_lt
    by (simp add: l1_at_k nth_append_left)
  
  have new_L_at_k: "new_L ! k = a"
    using new_L_decomp k_lt
    by (simp add: l1_at_k nth_append_left)
  
  (* By data independence, the enqueue of v is unique in both sequences and occurs at position k. *)
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
  
  (* Transfer SetA membership information between the two sequences. *)
  have same_SA_v: "in_SA v new_L \<longleftrightarrow> in_SA v L"
    by (simp add: same_SA)
  
  (* Now compare the two distance values. *)
  show "distance_func v bt_val new_L \<le> distance_func v bt_val L"
  proof (cases "in_SA v L")
    case True
    (* If v is in SetA, both distances are zero by definition. *)
    then have "in_SA v new_L"
      using same_SA_v by simp
    then show ?thesis
      by (simp add: True distance_func_def)
  next
    case False
    (* Otherwise v is outside SetA in both sequences. *)
    then have not_in_SA: "\<not> in_SA v L" "\<not> in_SA v new_L"
      using same_SA_v by auto
    
    (* Unfold distance_func on both sides. *)
    have dist_L: "distance_func v bt_val L = 
                 (if k < pos_bt_L then pos_bt_L - k else 0)"
      by (simp add: distance_func_def v_unique_L bt_unique_L False)
    
    have dist_new_L: "distance_func v bt_val new_L = 
                     (if k < pos_bt_new then pos_bt_new - k else 0)"
      by (simp add: distance_func_def v_unique_new_L bt_unique_new_L not_in_SA(2))
    
    (* Split on the relative position of k with respect to the two bt indices. *)
    show ?thesis
    proof (cases "k < pos_bt_new")
      case True
      (* Case: k is before both versions of bt_val. *)
      then have "k < pos_bt_L"
        using pos_bt_new_le by linarith
      with True show ?thesis
        by (simp add: diff_le_mono dist_L dist_new_L pos_bt_new_le)
    next
      case False
      (* Case: k is not before the new position of bt_val. *)
      then show ?thesis
      proof (cases "k < pos_bt_L")
        case True
        (* Subcase: bt_val moved left past k, but k was still before the old position. *)
        with False show ?thesis
          by (simp add: dist_L dist_new_L)
      next
        case False2: False
        (* Subcase: k is not before the old position either. *)
        then show ?thesis
          by (simp add: False dist_new_L)
    qed
  qed
qed
qed

(* The same argument can be abstracted from a concrete prefix to any preserved value set. *)
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
  
  (* Compare the enqueue position of v in the two sequences. *)
  from same_positions v_in have 
    pos_eq: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L =
            find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L"
    by simp
  
  (* We first split on whether v has any enqueue occurrence at all. *)
  show "distance_func v bt_val new_L \<le> distance_func v bt_val L"
  proof (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L")
    case None
    then have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = None"
      using pos_eq by simp
    
    (* If v never appears as an enqueue, the distance is zero on both sides. *)
    have dist_L: "distance_func v bt_val L = 0"
      by (simp add: distance_func_def None)
    
    have dist_new: "distance_func v bt_val new_L = 0"
      by (simp add: distance_func_def `find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = None`)
    
    then show ?thesis by (simp add: dist_L)
    
  next
    case (Some pos_v)
    then have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some pos_v"
      using pos_eq by simp
    
    (* Transfer SetA membership information between the two sequences. *)
    have same_SA_v: "in_SA v new_L \<longleftrightarrow> in_SA v L"
      using same_SA v_in by simp
    
    (* Now compare the two distance values. *)
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
      
      (* Unfold distance_func on both sides. *)
      have dist_L: "distance_func v bt_val L = 
                   (if pos_v < pos_bt_L then pos_bt_L - pos_v else 0)"
        by (simp add: distance_func_def Some bt_unique_L False)
      
      have dist_new: "distance_func v bt_val new_L = 
                     (if pos_v < pos_bt_new then pos_bt_new - pos_v else 0)"
        by (simp add: distance_func_def `find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some pos_v`
                      bt_unique_new_L not_in_SA(2))
      
      (* Again split on the relative position of pos_v and the two bt indices. *)
      show ?thesis
      proof (cases "pos_v < pos_bt_new")
        case True
        (* Case: pos_v lies before both bt positions. *)
        then have "pos_v < pos_bt_L"
          using pos_bt_new_le by linarith
        with True show ?thesis
          by (simp add: diff_le_mono dist_L dist_new pos_bt_new_le)
      next
        case False
        (* Case: pos_v is not before the new bt position. *)
        then show ?thesis
        proof (cases "pos_v < pos_bt_L")
          case True
          (* Subcase: the new bt position moved left across pos_v. *)
          with False show ?thesis
            by (simp add: dist_L dist_new)
        next
          case False2: False
          (* Subcase: pos_v is not before the old bt position either. *)
          then show ?thesis
            by (simp add: False dist_new)
        qed
      qed
    qed
  qed
qed

(* ========== Observational lemmas for list decompositions ========== *)
(* Values introduced in the suffix l3 have distance zero from bt_val,
   because all SetA enqueues have already been exhausted in the prefix l1. *)
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
  (* Treat middle @ l3 as the residual suffix after l1. *)
  define l2 where "l2 = middle @ l3"
  have L_decomp: "L = l1 @ l2" and l2_nonempty: "l2 \<noteq> []"
    using assms(2,3) unfolding l2_def by auto

  (* Use l1_contains_all_SA_in_L to show that no enqueue in the suffix belongs to SetA. *)
  have l1_contains: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> 
    \<not> in_SA (op_val (L ! i)) L"
    using l1_contains_all_SA_in_L[OF assms(1) L_decomp l2_nonempty assms(6,7)] .

  (* Pick the enqueue action of v from l3. *)
  from assms(8) obtain a where
    a_def: "a \<in> set (filter (\<lambda>a. op_name a = enq) l3)" "op_val a = v"
    by auto
  then have a_in_l3: "a \<in> set l3" and a_enq: "op_name a = enq"
    by auto

  (* Recover its position inside l3. *)
  from a_in_l3 obtain i where
    i_lt: "i < length l3" and l3_at_i: "l3 ! i = a"
    by (auto simp: in_set_conv_nth)

  (* Translate that local position into the absolute index in L. *)
  let ?pos_v = "length l1 + length middle + i"
  have pos_v_bounds: "?pos_v < length L"
    using assms(2) i_lt by auto
  have L_at_pos_v: "L ! ?pos_v = a"
    by (simp add: assms(2) i_lt l3_at_i nth_append)

  (* Hence v cannot belong to SetA. *)
  have v_not_in_SA: "\<not> in_SA v L"
  proof -
    have "?pos_v \<ge> length l1" by simp
    with pos_v_bounds a_enq L_at_pos_v a_def(2)
    show ?thesis using l1_contains by metis
  qed

  (* Recover the position of bt_act inside middle. *)
  from assms(3) obtain j where
    j_lt: "j < length middle" and middle_at_j: "middle ! j = bt_act"
    by (auto simp: in_set_conv_nth)

  (* Translate the bt position into its absolute index in L. *)
  let ?pos_bt = "length l1 + j"
  have pos_bt_bounds: "?pos_bt < length L"
    using assms(2) j_lt by auto
  have L_at_pos_bt: "L ! ?pos_bt = bt_act"
    by (simp add: assms(2) j_lt middle_at_j nth_append)

  (* Uniqueness of the enqueue action for bt_val follows from data independence. *)
  have bt_unique: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some ?pos_bt"
  proof -
    from assms(1) L_at_pos_bt assms(4,5) pos_bt_bounds
    have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = [?pos_bt]"
      by (simp add: unique_enq_index)
    then show ?thesis
      by (simp add: find_unique_index_def)
  qed

  (* The enqueue action for v is unique for the same reason. *)
  have v_unique: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some ?pos_v"
  proof -
    from assms(1) L_at_pos_v a_enq a_def(2) pos_v_bounds
    have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L = [?pos_v]"
      by (simp add: unique_enq_index)
    then show ?thesis
      by (simp add: find_unique_index_def)
  qed

  (* The enqueue of v occurs strictly after bt_val. *)
  have "?pos_v > ?pos_bt"
  proof -
    from j_lt have "j < length middle" .
    then have "?pos_bt < length l1 + length middle" by simp
    also have "... \<le> ?pos_v" by simp
    finally show ?thesis .
  qed

  (* Therefore distance_func returns zero: v is outside SetA and does not occur before bt_val. *)
  show ?thesis
    unfolding distance_func_def
    using v_not_in_SA v_unique bt_unique `?pos_v > ?pos_bt`
    by simp
qed




(* This specialized decomposition computes the exact distance when x_act occurs before bt_act. *)
lemma distance_func_observational:
  assumes "data_independent L"
  assumes "L = pre @ [x_act] @ middle @ [bt_act] @ suf"
  assumes "op_name x_act = enq" "op_val x_act = x_val"
  assumes "op_name bt_act = enq" "op_val bt_act = bt_val"
  assumes "\<not> in_SA x_val L"
  shows "distance_func x_val bt_val L = length middle + 1"
proof -
  (* Step 1: identify the index of x_act. *)
  let ?pos_x = "length pre"
  have x_at_idx: "L ! ?pos_x = x_act"
    using assms(2) by (simp add: nth_append)
  
  (* Step 2: identify the index of bt_act. *)
  let ?pos_bt = "length pre + 1 + length middle"
  have bt_at_idx: "L ! ?pos_bt = bt_act"
    using assms(2) by (simp add: nth_append)

  (* Step 3: use data independence to recover unique enqueue indices. *)
  have unique_x: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L = Some ?pos_x"
  proof -
    let ?P = "\<lambda>a. op_name a = enq \<and> op_val a = x_val"
    let ?S = "{i. i < length L \<and> ?P (L ! i)}"
    
    (* Step 3a: establish existence of the target index. *)
    have pos_x_matches: "?pos_x < length L \<and> ?P (L ! ?pos_x)"
      using x_at_idx assms(3) assms(2)
      by (simp add: assms(4))
      
    (* Step 3b: prove uniqueness of that index. *)
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

    (* Step 3c: reconstruct the singleton index list. *)
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

  (* Step 4: repeat the same uniqueness argument for bt_val. *)
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

(* Step 5: compute distance_func by unfolding the two unique indices. *)
  show ?thesis
  proof -
    (* Step 5.1: unfold distance_func. *)
    have "distance_func x_val bt_val L = 
          (if in_SA x_val L then 0 else 
           (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L of
              None \<Rightarrow> 0 
            | Some px \<Rightarrow> 
                (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                   None \<Rightarrow> 0 
                 | Some pbt \<Rightarrow> if px < pbt then pbt - px else 0)))"
      unfolding distance_func_def by simp

    (* Step 5.2: eliminate the SetA branch using the assumption \<not> in_SA x_val L. *)
    also have "... = (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L of
                        None \<Rightarrow> 0 
                      | Some px \<Rightarrow> 
                          (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                             None \<Rightarrow> 0 
                           | Some pbt \<Rightarrow> if px < pbt then pbt - px else 0))"
      by (simp add: assms(7)) 

    (* Step 5.3: rewrite the first case analysis with unique_x. *)
    also have "... = (case Some ?pos_x of
                        None \<Rightarrow> 0 
                      | Some px \<Rightarrow> 
                          (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                             None \<Rightarrow> 0 
                           | Some pbt \<Rightarrow> if px < pbt then pbt - px else 0))"
      using unique_x by simp

    (* Step 5.4: simplify the resulting Some-case. *)
    also have "... = (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                        None \<Rightarrow> 0 
                      | Some pbt \<Rightarrow> if ?pos_x < pbt then pbt - ?pos_x else 0)"
      by simp

    (* Step 5.5: rewrite the second case analysis with unique_bt. *)
    also have "... = (if ?pos_x < ?pos_bt then ?pos_bt - ?pos_x else 0)"
      using unique_bt by simp

    (* Step 5.6: finish with a pure arithmetic simplification. *)
    (* At this point only the positional arithmetic remains. *)
    also have "... = length middle + 1"
      by simp
      
    (* Step 5.7: conclude the desired equality. *)
    finally show ?thesis .
  qed
qed

(* ========== A generic lower bound for sums over mapped lists ========== *)
(* If x occurs in xs and f returns natural numbers, then the total sum
   over map f xs is at least f x. *)
lemma sum_list_map_ge_element:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "x \<in> set xs"
  shows "sum_list (map f xs) \<ge> f x"
proof -
  (* Decompose xs around one occurrence of x. *)
  from assms obtain ys zs where "xs = ys @ x # zs" 
    by (meson split_list)
  
  (* Apply map f to the decomposition. *)
  hence "map f xs = map f ys @ (f x) # map f zs" 
    by simp
    
  (* Expand sum_list over the concatenated list. *)
  hence "sum_list (map f xs) = sum_list (map f ys) + f x + sum_list (map f zs)" 
    by simp
    
  (* Over nat, the surrounding summands are nonnegative, so the target term is bounded by the total sum. *)
  thus ?thesis by simp
qed

end