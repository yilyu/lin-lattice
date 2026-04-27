theory Termination
  imports 
    Main 
    "HOL-Library.Multiset"
    PureLib
    DistLib
begin


(* Case 2.2. *)
lemma moving_bt_act_forward_over_l2_last_case2:
  assumes "data_independent L"
  assumes "L = l1 @ l2 @ [bt_act] @ l3"                    (* Comment. *)
  assumes "l1 = take (nat (last_sa_pos + 1)) L"             (* l1 SA *)
  assumes "last_sa_pos = find_last_SA L"  
  assumes "l2 \<noteq> []"                                        (* l2 non-empty *)
  assumes "l2_last = last l2"                              (* l2 *)
  assumes "op_name l2_last = enq"                         (* l2_last enq *)
  assumes "ll2 = butlast l2"                               (* l2 *)
  assumes "op_name bt_act = enq" "op_val bt_act = bt_val" (* bt_act *)
  assumes "new_L = l1 @ ll2 @ [bt_act] @ [l2_last] @ l3"  (* position *)
  shows "Distance new_L bt_val < Distance L bt_val"
proof -
  (* Step 1. *)
  have l2_decomp: "l2 = ll2 @ [l2_last]"
    by (simp add: assms(5,6,8))
    
  have L_decomp: "L = l1 @ ll2 @ [l2_last] @ [bt_act] @ l3"
    using assms(2) l2_decomp by simp

  (* Step 2. *)
  have mset_eq: "mset new_L = mset L"
  proof -
    show ?thesis
      using L_decomp assms(10) mset_append add.commute add.left_commute
      by (simp add: assms(11))
  qed

  (* Step 3. *)
  have di_new_L: "data_independent new_L"
    using assms(1) mset_eq new_L_is_data_independent by blast

(* Step 4. *)
  have same_SA: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L"
  proof
    fix v
    (* Final: filter_empty_conv all_set_conv_all_nth, *)
    have filter_to_set: "\<And>xs P. (find_indices P xs = []) \<longleftrightarrow> (\<forall>x \<in> set xs. \<not> P x)"
      unfolding find_indices_def 
      by (auto simp add: filter_empty_conv all_set_conv_all_nth)
      
    (* extract *)
    have set_eq: "set new_L = set L" 
      using mset_eq by (metis set_mset_mset)

    (* Comment. *)
    have enq_eq: "(find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = []) \<longleftrightarrow> 
                  (find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L = [])"
      using filter_to_set[of "\<lambda>a. op_name a = enq \<and> op_val a = v"] set_eq by simp
      
    have deq_eq: "(find_indices (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L = []) \<longleftrightarrow> 
                  (find_indices (\<lambda>a. op_name a = deq \<and> op_val a = v) L = [])"
      using filter_to_set[of "\<lambda>a. op_name a = deq \<and> op_val a = v"] set_eq by simp
      
    show "in_SA v new_L \<longleftrightarrow> in_SA v L"
      unfolding in_SA_def find_unique_index_def Let_def
      using enq_eq deq_eq by simp
  qed

  (* Step 5.1.2. *)
  have prefix_part_unchanged: "\<forall>v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ ll2))).
    distance_func v bt_val new_L \<le> distance_func v bt_val L"
  proof -
    have bt_pos_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = 
                    Some (length (l1 @ ll2 @ [l2_last]))"
    proof -
      let ?bt_pos = "length (l1 @ ll2 @ [l2_last])"
      have "L ! ?bt_pos = bt_act" by (simp add: L_decomp nth_append)
      have "?bt_pos < length L" by (simp add: L_decomp)
      from assms(1) `?bt_pos < length L` `L ! ?bt_pos = bt_act` assms(9)
      show ?thesis
        using find_unique_index_def unique_enq_index assms(10) by force 
    qed
    
    have bt_pos_new: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = 
                      Some (length (l1 @ ll2))"
    proof -
      let ?bt_pos = "length (l1 @ ll2)"
      have "new_L ! ?bt_pos = bt_act" by (simp add: assms(11))
      have "?bt_pos < length new_L" by (simp add: assms(11))
      from di_new_L `?bt_pos < length new_L` `new_L ! ?bt_pos = bt_act` assms(9)
      show ?thesis
        using find_unique_index_def unique_enq_index assms(10) by force
    qed
    
    have pos_le: "length (l1 @ ll2) \<le> length (l1 @ ll2 @ [l2_last])" by simp
    
    define rest_L where "rest_L = [l2_last] @ [bt_act] @ l3"
    define rest_new where "rest_new = [bt_act] @ [l2_last] @ l3"
    
    have L_form: "L = (l1 @ ll2) @ rest_L" using L_decomp rest_L_def by simp
    have new_L_form: "new_L = (l1 @ ll2) @ rest_new" using assms(10) rest_new_def by (simp add: assms(11))
      
    show ?thesis
      using l1_distance_non_increasing[OF assms(1) di_new_L L_form new_L_form bt_pos_L bt_pos_new pos_le same_SA]
      by auto
  qed

  (* Step6: analysis l2_last *)
  have l2_last_strict_decrease: "distance_func (op_val l2_last) bt_val new_L < distance_func (op_val l2_last) bt_val L"
  proof -
    have l2_last_not_in_SA: "\<not> in_SA (op_val l2_last) L"
    proof -
      define k where "k = length (l1 @ ll2)"
      have "k < length L" and "k \<ge> length l1" unfolding k_def using L_decomp by simp_all
      have L_k_eq: "L ! k = l2_last" unfolding k_def using L_decomp by (simp add: nth_append)
      have oper_eq: "op_name (L ! k) = enq" using L_k_eq assms(7) by simp
      have target_not_in_SA: "\<not> in_SA (op_val (L ! k)) L"
        using l1_contains_all_SA_in_L assms(1-4) `k < length L` `k \<ge> length l1` oper_eq by blast
      show ?thesis using target_not_in_SA L_k_eq by simp
    qed
    
    have dist_old: "distance_func (op_val l2_last) bt_val L = 1"
    proof -
      let ?pos_v = "length (l1 @ ll2)"
      let ?pos_bt = "length (l1 @ ll2) + 1"
      have pos_v_bound: "?pos_v < length L" using L_decomp by simp
      have val_at_pos_v: "L ! ?pos_v = l2_last" using L_decomp by (simp add: nth_append)
      have oper_v: "op_name (L ! ?pos_v) = enq" "op_val (L ! ?pos_v) = op_val l2_last"
        using val_at_pos_v assms(7) by auto
      have idx_v: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = op_val l2_last) L = Some ?pos_v"
        unfolding find_unique_index_def using unique_enq_index[OF assms(1) oper_v(1) oper_v(2) pos_v_bound] by simp
        
      have pos_bt_bound: "?pos_bt < length L" using L_decomp by simp
      have val_at_pos_bt: "L ! ?pos_bt = bt_act" using L_decomp by (simp add: nth_append)
      have oper_bt: "op_name (L ! ?pos_bt) = enq" "op_val (L ! ?pos_bt) = bt_val"
        using val_at_pos_bt assms(9,10) by auto 
      have idx_bt: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some ?pos_bt"
        unfolding find_unique_index_def using assms(1) pos_bt_bound unique_enq_index oper_bt by auto
      show ?thesis using distance_func_def l2_last_not_in_SA idx_v idx_bt by simp
    qed
    
    have dist_new: "distance_func (op_val l2_last) bt_val new_L = 0"
    proof -
      let ?pos_v = "length (l1 @ ll2) + 1"
      let ?pos_bt = "length (l1 @ ll2)"
      have not_in_sa_new: "\<not> in_SA (op_val l2_last) new_L" using same_SA l2_last_not_in_SA by simp
      
      have pos_v_bound: "?pos_v < length new_L" by (simp add: assms(11)) 
      (* Fix. *)
      have val_at_pos_v: "new_L ! ?pos_v = l2_last" by (simp add: assms(11) nth_append)
      have oper_v: "op_name (new_L ! ?pos_v) = enq" "op_val (new_L ! ?pos_v) = op_val l2_last"
        using val_at_pos_v assms(7) by auto
      have idx_v: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = op_val l2_last) new_L = Some ?pos_v"
        unfolding find_unique_index_def using assms(7) di_new_L pos_v_bound unique_enq_index oper_v by auto
        
      have pos_bt_bound: "?pos_bt < length new_L" by (simp add: assms(11)) 
      have val_at_pos_bt: "new_L ! ?pos_bt = bt_act" using assms(11) by (simp add: nth_append) 
      have oper_bt: "op_name (new_L ! ?pos_bt) = enq" "op_val (new_L ! ?pos_bt) = bt_val"
        using assms(9,10) val_at_pos_bt by auto
      have idx_bt: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = Some ?pos_bt"
        unfolding find_unique_index_def using di_new_L pos_bt_bound unique_enq_index oper_bt by auto 
        
      show ?thesis using distance_func_def not_in_sa_new idx_v idx_bt by simp
    qed
    
    show ?thesis using dist_old dist_new by simp
  qed
  
  (* Step 7.0.0. *)
  have bt_act_unchanged: "distance_func bt_val bt_val new_L = distance_func bt_val bt_val L"
    using distance_self_zero[OF di_new_L] distance_self_zero[OF assms(1)] by simp
    
  (* Step8: analysis l3 (distance 0 = 0) *)
  have l3_part_unchanged: "\<forall>v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3)). 
    distance_func v bt_val new_L = 0 \<and> distance_func v bt_val L = 0"
  proof
    fix v assume v_in: "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
    
    have dist_L_zero: "distance_func v bt_val L = 0"
      using l3_distance_zero_observational[OF assms(1) _ _ assms(9,10,3,4) v_in] assms(2) by fastforce
      
    have sa_pos_eq: "find_last_SA new_L = last_sa_pos"
    proof -
      let ?P_L = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L"
      let ?P_new = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) new_L"
      have len_eq: "length new_L = length L" using mset_eq by (metis size_mset)
      
      have P_eq: "\<forall>a. ?P_L a \<longleftrightarrow> ?P_new a" using same_SA by auto
      
      (* Fix. *)
      have indices_eq: "find_indices ?P_new new_L = find_indices ?P_L L"
      proof -
        have split_list: "[0..<length L] = [0..<length l1] @ [length l1..<length L]" 
          using assms(2) by (metis length_append upt_add_eq_append zero_le)
          
        (* explicit L, *)
        have L_indices_scope: "\<forall>i < length L. ?P_L (L ! i) \<longrightarrow> i < length l1"
        proof (intro allI impI)
          fix i assume "i < length L" and "?P_L (L ! i)"
          then show "i < length l1"
            using l1_contains_all_SA_in_L[OF assms(1,2) _ assms(3,4)] assms(5)
            by (metis append_is_Nil_conv leI)
        qed

        (* : l1, extract *)
        have part1: "filter (\<lambda>i. ?P_new (new_L ! i)) [0..<length l1] = filter (\<lambda>i. ?P_L (L ! i)) [0..<length l1]"
        proof (rule filter_cong[OF refl])
          fix i assume "i \<in> set [0..<length l1]"
          then have "i < length l1" by simp
          have "new_L ! i = L ! i" 
            using `i < length l1` assms(2,11) by (metis nth_append)
          thus "?P_new (new_L ! i) = ?P_L (L ! i)" using P_eq
            by presburger
        qed

        (* L SA *)
        have part2_L: "filter (\<lambda>i. ?P_L (L ! i)) [length l1..<length L] = []"
        proof -
          have "\<forall>i \<in> set [length l1..<length L]. \<not> ?P_L (L ! i)"
            using L_indices_scope by auto
          thus ?thesis by (simp add: filter_empty_conv)
        qed

        (* new_L SA () *)
        have part2_new: "filter (\<lambda>i. ?P_new (new_L ! i)) [length l1..<length L] = []"
        proof -
          have "\<forall>i \<in> set [length l1..<length L]. \<not> ?P_new (new_L ! i)"
          proof (intro ballI notI)
            fix i assume "i \<in> set [length l1..<length L]" and "?P_new (new_L ! i)"
            hence i_bounds: "length l1 \<le> i" "i < length L" by auto
            hence i_len_new: "i < length new_L" using len_eq by simp
            
            have is_enq: "op_name (new_L ! i) = enq" and in_sa: "in_SA (op_val (new_L ! i)) new_L" 
              using `?P_new (new_L ! i)` by auto
            
            define val_i where "val_i = op_val (new_L ! i)"
            have "in_SA val_i L" using in_sa same_SA val_i_def by simp
            
            (* val_i SA, L l1 *)
            obtain j where j_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = val_i) L = Some j"
              using `in_SA val_i L` unfolding in_SA_def Let_def 
              by (auto split: option.splits)
              
            have j_props: "op_name (L ! j) = enq" "op_val (L ! j) = val_i" "j < length L"
              using find_unique_index_enq[OF assms(1) j_def] by auto
              
            have "j < length l1" 
              using L_indices_scope `in_SA val_i L` j_props(1,2) j_props(3) by auto
              
            (* prefix, new_L L j *)
            have "new_L ! j = L ! j" 
              using `j < length l1` assms(2,11) by (metis nth_append)
              
            have "op_name (new_L ! j) = enq" "op_val (new_L ! j) = val_i"
              using j_props `new_L ! j = L ! j` by auto
              
            (* ,, i j *)
            have "i = j"
              using unique_enq_value[OF di_new_L i_len_new] `j < length l1` len_eq
              is_enq val_i_def `op_name (new_L ! j) = enq` `op_val (new_L ! j) = val_i`
              by (metis j_props(3)) 
              
            (* i, j, ！ *)
            thus False using i_bounds `j < length l1` by simp
          qed
          thus ?thesis by (simp add: filter_empty_conv)
        qed

        show ?thesis
          unfolding find_indices_def len_eq split_list filter_append part1 part2_L part2_new by simp
      qed
      show ?thesis unfolding find_last_SA_def indices_eq using assms(4) find_last_SA_def by simp
    qed
    
    (* distance_zero_observational *)
    have dist_new_zero: "distance_func v bt_val new_L = 0"
    proof (rule l3_distance_zero_observational)
      show "data_independent new_L" by (fact di_new_L)
      show "new_L = l1 @ (ll2 @ [bt_act] @ [l2_last]) @ l3" by (simp add: assms(11))
      show "bt_act \<in> set (ll2 @ [bt_act] @ [l2_last])" by simp
      show "op_name bt_act = enq" by (fact assms(9))
      show "op_val bt_act = bt_val" by (fact assms(10))
      show "find_last_SA new_L = find_last_SA new_L" by simp
      show "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))" by (fact v_in)
      show "l1 = take (nat (find_last_SA new_L + 1)) new_L"
      proof -
        have "take (nat (find_last_SA new_L + 1)) new_L = take (nat (last_sa_pos + 1)) new_L"
          using sa_pos_eq by simp
        
        (* Fix. *)
        also have "... = take (length l1) new_L"
        proof -
          (* Step 1.1. *)
          have "length l1 = min (nat (last_sa_pos + 1)) (length L)"
            using assms(3) by simp
          (* Step 2.2.1. *)
          moreover have "length l1 < length L"
            using assms(2) assms(5) by simp
          (* Step 3.1. *)
          ultimately have "nat (last_sa_pos + 1) = length l1"
            by linarith
          (* Step 4. *)
          thus ?thesis by simp
        qed
        
        also have "... = l1"
          using assms(11) by simp
        finally show ?thesis by simp
      qed
    qed
    
    show "distance_func v bt_val new_L = 0 \<and> distance_func v bt_val L = 0" 
      using dist_new_zero dist_L_zero by simp
  qed

  (* Step 9. *)
  show ?thesis
  proof -
    let ?S_prefix = "set (map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ ll2)))"
    let ?S_l2_last = "{op_val l2_last}"
    let ?S_bt = "{bt_val}"
    let ?S_l3 = "set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
    let ?all_enqueues_L = "filter (\<lambda>a. op_name a = enq) L"
    let ?enqueued_values_L = "set (map op_val ?all_enqueues_L)"
    
    (* structure *)
    have list_structure: "?all_enqueues_L = filter (\<lambda>a. op_name a = enq) (l1 @ ll2) @ [l2_last] @ [bt_act] @ filter (\<lambda>a. op_name a = enq) l3"
      using L_decomp assms(7,9) by auto
      
    have values_decomposition: "?enqueued_values_L = ?S_prefix \<union> ?S_l2_last \<union> ?S_bt \<union> ?S_l3"
      unfolding list_structure by (simp add: assms(10) ac_simps)
      
    have distinct_all: "distinct (map op_val ?all_enqueues_L)"
    proof -
      (* Proof step. *)
      have list_equiv: "map op_val ?all_enqueues_L = 
                        map (\<lambda>i. op_val (L ! i)) (filter (\<lambda>i. op_name (L ! i) = enq) [0..<length L])"
      proof -
        (* Step 1. *)
        have "L = map (\<lambda>i. L ! i) [0..<length L]" 
          by (simp add: map_nth)
        (* Step 2. *)
        hence "filter (\<lambda>a. op_name a = enq) L = 
               filter (\<lambda>a. op_name a = enq) (map (\<lambda>i. L ! i) [0..<length L])" 
          by simp
        (* Step 3. *)
        also have "... = map (\<lambda>i. L ! i) (filter (\<lambda>i. op_name (L ! i) = enq) [0..<length L])"
          by (simp add: filter_map o_def)
        (* Step 4. *)
        finally show ?thesis 
          by simp
      qed
      
      (* Auxiliary lemma. *)
      thus ?thesis 
        using enq_values_distinct[OF assms(1)] by simp
    qed
      
    have disjoints: "?S_prefix \<inter> (?S_l2_last \<union> ?S_bt \<union> ?S_l3) = {}"
                    "?S_l2_last \<inter> (?S_bt \<union> ?S_l3) = {}"
                    "?S_bt \<inter> ?S_l3 = {}"
    proof -
      (* map, preserve structure *)
      have mapped_list_eq: "map op_val ?all_enqueues_L = 
        map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ ll2)) @ 
        [op_val l2_last] @ [bt_val] @ 
        map op_val (filter (\<lambda>a. op_name a = enq) l3)"
        using list_structure assms(10) by simp

      (* , unfold 4,, auto automatic distinct_append *)
      have "distinct (map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ ll2)) @ 
                      [op_val l2_last] @ [bt_val] @ 
                      map op_val (filter (\<lambda>a. op_name a = enq) l3))"
        using distinct_all mapped_list_eq by simp
        
      thus "?S_prefix \<inter> (?S_l2_last \<union> ?S_bt \<union> ?S_l3) = {}"
           "?S_l2_last \<inter> (?S_bt \<union> ?S_l3) = {}"
           "?S_bt \<inter> ?S_l3 = {}"
        by auto
    qed
      
    have sum_L: "(\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val L) = 
      (\<Sum>v\<in>?S_prefix. distance_func v bt_val L) + (\<Sum>v\<in>?S_l2_last. distance_func v bt_val L) +
      (\<Sum>v\<in>?S_bt. distance_func v bt_val L) + (\<Sum>v\<in>?S_l3. distance_func v bt_val L)"
    proof -
      have 1: "(\<Sum>v\<in>?S_prefix \<union> (?S_l2_last \<union> ?S_bt \<union> ?S_l3). distance_func v bt_val L) = 
               (\<Sum>v\<in>?S_prefix. distance_func v bt_val L) + (\<Sum>v\<in>?S_l2_last \<union> ?S_bt \<union> ?S_l3. distance_func v bt_val L)"
      proof (rule sum.union_disjoint)
        show "finite ?S_prefix" by simp
        show "finite (?S_l2_last \<union> ?S_bt \<union> ?S_l3)" by simp
        show "?S_prefix \<inter> (?S_l2_last \<union> ?S_bt \<union> ?S_l3) = {}" by (fact disjoints(1))
      qed

      have 2: "(\<Sum>v\<in>?S_l2_last \<union> (?S_bt \<union> ?S_l3). distance_func v bt_val L) = 
               (\<Sum>v\<in>?S_l2_last. distance_func v bt_val L) + (\<Sum>v\<in>?S_bt \<union> ?S_l3. distance_func v bt_val L)"
      proof (rule sum.union_disjoint)
        show "finite ?S_l2_last" by simp
        show "finite (?S_bt \<union> ?S_l3)" by simp
        show "?S_l2_last \<inter> (?S_bt \<union> ?S_l3) = {}" by (fact disjoints(2))
      qed

      have 3: "(\<Sum>v\<in>?S_bt \<union> ?S_l3. distance_func v bt_val L) = 
               (\<Sum>v\<in>?S_bt. distance_func v bt_val L) + (\<Sum>v\<in>?S_l3. distance_func v bt_val L)"
      proof (rule sum.union_disjoint)
        show "finite ?S_bt" by simp
        show "finite ?S_l3" by simp
        show "?S_bt \<inter> ?S_l3 = {}" by (fact disjoints(3))
      qed
      
      show ?thesis unfolding values_decomposition 1 2 3
        using "1" "2" "3" by auto 
    qed
    
    have sum_new: "(\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val new_L) = 
      (\<Sum>v\<in>?S_prefix. distance_func v bt_val new_L) + (\<Sum>v\<in>?S_l2_last. distance_func v bt_val new_L) +
      (\<Sum>v\<in>?S_bt. distance_func v bt_val new_L) + (\<Sum>v\<in>?S_l3. distance_func v bt_val new_L)"
    proof -
      have 1: "(\<Sum>v\<in>?S_prefix \<union> (?S_l2_last \<union> ?S_bt \<union> ?S_l3). distance_func v bt_val new_L) = 
               (\<Sum>v\<in>?S_prefix. distance_func v bt_val new_L) + (\<Sum>v\<in>?S_l2_last \<union> ?S_bt \<union> ?S_l3. distance_func v bt_val new_L)"
      proof (rule sum.union_disjoint)
        show "finite ?S_prefix" by simp
        show "finite (?S_l2_last \<union> ?S_bt \<union> ?S_l3)" by simp
        show "?S_prefix \<inter> (?S_l2_last \<union> ?S_bt \<union> ?S_l3) = {}" by (fact disjoints(1))
      qed

      have 2: "(\<Sum>v\<in>?S_l2_last \<union> (?S_bt \<union> ?S_l3). distance_func v bt_val new_L) = 
               (\<Sum>v\<in>?S_l2_last. distance_func v bt_val new_L) + (\<Sum>v\<in>?S_bt \<union> ?S_l3. distance_func v bt_val new_L)"
      proof (rule sum.union_disjoint)
        show "finite ?S_l2_last" by simp
        show "finite (?S_bt \<union> ?S_l3)" by simp
        show "?S_l2_last \<inter> (?S_bt \<union> ?S_l3) = {}" by (fact disjoints(2))
      qed

      have 3: "(\<Sum>v\<in>?S_bt \<union> ?S_l3. distance_func v bt_val new_L) = 
               (\<Sum>v\<in>?S_bt. distance_func v bt_val new_L) + (\<Sum>v\<in>?S_l3. distance_func v bt_val new_L)"
      proof (rule sum.union_disjoint)
        show "finite ?S_bt" by simp
        show "finite ?S_l3" by simp
        show "?S_bt \<inter> ?S_l3 = {}" by (fact disjoints(3))
      qed
      
      show ?thesis unfolding values_decomposition 1 2 3
        using "1" "2" "3" by auto 
    qed

    (* : 4 conclusion *)
    have "(\<Sum>v\<in>?S_prefix. distance_func v bt_val new_L) \<le> (\<Sum>v\<in>?S_prefix. distance_func v bt_val L)"
      using prefix_part_unchanged by (meson sum_mono)
    moreover have "(\<Sum>v\<in>?S_l2_last. distance_func v bt_val new_L) < (\<Sum>v\<in>?S_l2_last. distance_func v bt_val L)"
      using l2_last_strict_decrease by simp
    moreover have "(\<Sum>v\<in>?S_bt. distance_func v bt_val new_L) = (\<Sum>v\<in>?S_bt. distance_func v bt_val L)"
      using bt_act_unchanged by simp
    moreover have "(\<Sum>v\<in>?S_l3. distance_func v bt_val new_L) = (\<Sum>v\<in>?S_l3. distance_func v bt_val L)"
      using l3_part_unchanged by (metis sum.not_neutral_contains_not_neutral)
      
    (* Core *)
    ultimately have strict_ineq: "(\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val new_L) < (\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val L)"
      unfolding sum_L sum_new by linarith

    (* sorry 4: Distance definition *)
    
    (* Step 1. *)
    have dist_L: "Distance L bt_val = (\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val L)"
    proof -
      have "Distance L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val L) (sorted_list_of_set ?enqueued_values_L))"
        unfolding Distance_def Let_def by simp
      also have "... = (\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val L)"
        using sum_list_distinct_conv_sum_set distinct_sorted_list_of_set by (metis List.finite_set sorted_list_of_set.set_sorted_key_list_of_set)
      finally show ?thesis .
    qed

    (* Step 2. *)
    have enq_vals_new_eq: "set (map op_val (filter (\<lambda>a. op_name a = enq) new_L)) = ?enqueued_values_L"
    proof -
      have "set new_L = set L" using mset_eq by (metis set_mset_mset)
      hence "set (filter (\<lambda>a. op_name a = enq) new_L) = set ?all_enqueues_L" by auto
      thus ?thesis
        by simp 
    qed

    (* Step 3. *)
    have dist_new: "Distance new_L bt_val = (\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val new_L)"
    proof -
      let ?enqueued_values_new = "set (map op_val (filter (\<lambda>a. op_name a = enq) new_L))"
      have "Distance new_L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val new_L) (sorted_list_of_set ?enqueued_values_new))"
        unfolding Distance_def Let_def by simp
      also have "... = (\<Sum>v\<in>?enqueued_values_new. distance_func v bt_val new_L)"
        using sum_list_distinct_conv_sum_set distinct_sorted_list_of_set by (metis List.finite_set sorted_list_of_set.set_sorted_key_list_of_set)
      also have "... = (\<Sum>v\<in>?enqueued_values_L. distance_func v bt_val new_L)"
        using enq_vals_new_eq by simp
      finally show ?thesis .
    qed

    (* Step 4. *)
    show ?thesis
      using dist_L dist_new strict_ineq by simp
  qed
qed

(* 3 (Case 3): 
    find_last_enq  o1 (l22) happens_before bt_act ，
    o1  b_act 。
   : ... [b_act] @ [o1] @ new_l22 ... -> ... [o1] @ [b_act] @ new_l22 ...
    b_act  bt_act 。
*)
lemma moving_b_act_forward_over_o1_case3:
  assumes "data_independent L"
  assumes "L = l1 @ l2 @ [bt_act] @ l3"                    (* Comment. *)
  assumes "l1 = take (nat (last_sa_pos + 1)) L"             (* l1 SA *)
  assumes "last_sa_pos = find_last_SA L"
  assumes "find_last_enq l2 = Some (l21, b_act, l22)"     (* l2 *)
  assumes "l22 \<noteq> []"                                      (* l22 non-empty *)
  assumes "o1 = hd l22"                                   (* o1 l22 *)
  assumes "new_l22 = tl l22"                              (* new_l22 *)
  assumes "op_name b_act = enq" "op_name bt_act = enq"  (* b_act bt_act enq *)
  assumes "op_val bt_act = bt_val"
  assumes "new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3" (* Comment. *)
  shows "Distance new_L bt_val < Distance L bt_val"
proof -
  (* Step 1. *)
  (* l2 = l21 @ [b_act] @ l22 *)
  from assms(5) have l2_decomp_raw: "l2 = l21 @ [b_act] @ l22"
    unfolding find_last_enq_def
    by (smt (verit, ccfv_threshold) Cons_eq_appendI add.commute add_lessD1 append_self_conv2 assms(6) drop_eq_Nil2 id_take_nth_drop old.prod.inject option.distinct(1) option.inject plus_1_eq_Suc verit_comp_simplify1(3))

  (* l22 = o1 # new_l22 *)
  have l22_decomp: "l22 = [o1] @ new_l22"
    using assms(6,7,8)
    by simp

  (* L *)
  have L_decomp: "L = l1 @ l21 @ [b_act] @ [o1] @ new_l22 @ [bt_act] @ l3"
    using assms(2) l2_decomp_raw l22_decomp by simp

  (* Step 2.22.1. *)
  have l22_all_deq: "\<forall>a \<in> set l22. op_name a = deq"
    using assms(5,6) l22_are_all_deq by blast
  
  have o1_is_deq: "op_name o1 = deq"
    using l22_all_deq l22_decomp by simp

(* Step 3. *)
  have mset_eq: "mset new_L = mset L"
  proof -
    (* : assumes, new_L definition assms(12) *)
    (* explicit unfold L_decomp new_L definition *)
    show ?thesis
      using L_decomp assms(12) 
      by (simp add: ac_simps) 
  qed

  (* Step 4. *)
  have di_new_L: "data_independent new_L"
    using assms(1) mset_eq new_L_is_data_independent by blast

  (* Step5: SA stateunchanged *)
  have same_SA: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L"
    using assms(1,3,4,12) di_new_L mset_eq L_and_new_L_have_same_SA
    by (metis append_is_Nil_conv assms(2) list.distinct(1))

  (* Step 6.1. *)
  have l1_contains_all_SA: "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> 
    \<not> in_SA (op_val (L ! i)) L"
    using assms(1,2,3,4) l1_contains_all_SA_in_L by blast

(* Step 7. *)
  
  (* Step 7.1.1.21. *)
  have prefix_unchanged: "\<forall>v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ l21))).
      distance_func v bt_val new_L \<le> distance_func v bt_val L"
  proof
    fix v assume v_in: "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ l21)))"
    
    (* Proof step. *)
    
    (* A. analysis L structure *)
    let ?pre_L = "l1 @ l21 @ [b_act] @ [o1] @ new_l22"
    have L_struct: "L = ?pre_L @ [bt_act] @ l3" using L_decomp by simp

    (* A1. bt_act L uniqueindex *)
    have idx_bt_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some (length ?pre_L)"
    proof -
      have val_at_idx: "L ! (length ?pre_L) = bt_act" using L_struct by (simp add: nth_append)
      have valid_idx: "length ?pre_L < length L" using L_struct by simp
      have cond_holds: "op_name bt_act = enq \<and> op_val bt_act = bt_val" using assms(10,11) by simp
      show ?thesis
        unfolding find_unique_index_def
        using assms(1) valid_idx unique_enq_index val_at_idx cond_holds by fastforce
    qed

    (* B. analysis new_L structure *)
    let ?pre_new = "l1 @ l21 @ [o1] @ [b_act] @ new_l22"
    have new_L_struct: "new_L = ?pre_new @ [bt_act] @ l3" by (simp add: assms(12)) 
      
    (* B1. bt_act new_L uniqueindex *)
    have idx_bt_new: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = Some (length ?pre_new)"
    proof -
      have val_at_idx: "new_L ! (length ?pre_new) = bt_act" using new_L_struct by (simp add: nth_append)
      have valid_idx: "length ?pre_new < length new_L" using new_L_struct by simp
      have cond_holds: "op_name bt_act = enq \<and> op_val bt_act = bt_val" using assms(10,11) by simp
      show ?thesis
        unfolding find_unique_index_def
        using di_new_L valid_idx unique_enq_index val_at_idx cond_holds by fastforce
    qed

    (* C. index *)
    have len_eq: "length ?pre_L = length ?pre_new" by simp
    have idx_bt_eq: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = 
                     find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L"
      using idx_bt_L idx_bt_new len_eq by simp

    (* Proof step. *)
    have idx_v_eq: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = 
                    find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L"
    proof -
      (* Final: x auto, structure *)
      obtain i where i_bounds: "i < length (l1 @ l21)" 
                 and i_act: "op_name ((l1 @ l21) ! i) = enq" 
                 and i_val: "op_val ((l1 @ l21) ! i) = v"
      proof -
        (* :,, extractconcrete x *)
        obtain x where x_in: "x \<in> set (l1 @ l21)" 
                   and x_act: "op_name x = enq" 
                   and x_val: "op_val x = v"
          using v_in by auto
          
        (* : x directmap idx *)
        obtain idx where "idx < length (l1 @ l21)" "(l1 @ l21) ! idx = x"
          using x_in by (metis in_set_conv_nth)
          
        (* : assembleconclusion *)
        thus ?thesis 
          using that x_act x_val by blast
      qed

      (* Step 2. *)
      have i_valid_L: "i < length L" using i_bounds L_struct by simp
      have L_at_i: "L ! i = (l1 @ l21) ! i" using L_struct i_bounds
        by (metis append.assoc nth_append_left) 
      have cond_L: "op_name (L ! i) = enq \<and> op_val (L ! i) = v" using L_at_i i_act i_val by simp
      have idx_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some i"
        unfolding find_unique_index_def using assms(1) cond_L i_valid_L unique_enq_index by force

      (* Step 3. *)
      have i_valid_new: "i < length new_L" using i_bounds new_L_struct by simp
      have new_L_at_i: "new_L ! i = (l1 @ l21) ! i" using new_L_struct i_bounds
        by (metis append.assoc nth_append_left) 
      have cond_new: "op_name (new_L ! i) = enq \<and> op_val (new_L ! i) = v" using new_L_at_i i_act i_val by simp
      have idx_new: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some i"
        unfolding find_unique_index_def using cond_new di_new_L i_valid_new unique_enq_index by fastforce
        
      (* Step 4. *)
      show ?thesis using idx_L idx_new by simp
    qed

    (* E. conclusion *)
    show "distance_func v bt_val new_L \<le> distance_func v bt_val L"
      unfolding distance_func_def
      using idx_bt_eq idx_v_eq less_eq_nat.simps(1) same_SA by presburger
  qed


(* Step 7.2. *)
  have b_act_strict_decrease: "distance_func (op_val b_act) bt_val new_L < distance_func (op_val b_act) bt_val L"
  proof -
    (* Proof step. *)
    have b_not_in_SA: "\<not> in_SA (op_val b_act) L"
    proof -
      let ?idx = "length l1 + length l21"
      have "L ! ?idx = b_act" using L_decomp by (simp add: nth_append)
      moreover have "?idx < length L" using L_decomp by simp
      moreover have "?idx \<ge> length l1" by simp
      ultimately show ?thesis
        using l1_contains_all_SA assms(9) by blast
    qed
    
    have b_not_in_SA_new: "\<not> in_SA (op_val b_act) new_L"
      using b_not_in_SA same_SA by simp

    (* B. L distance *)
    have dist_L: "distance_func (op_val b_act) bt_val L = 2 + length new_l22"
    proof -
      let ?idx_b = "length l1 + length l21"
      let ?idx_bt = "length l1 + length l21 + 2 + length new_l22"
      
      (* --- 1. b_act position --- *)
      have idx_b_valid: "?idx_b < length L" using L_decomp by simp
      have val_b: "L ! ?idx_b = b_act" using L_decomp by (simp add: nth_append)
      
      have cond_b: "op_name (L ! ?idx_b) = enq \<and> op_val (L ! ?idx_b) = op_val b_act"
        using val_b assms(9) by simp
        
      have pos_b: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = op_val b_act) L = Some ?idx_b"
        unfolding find_unique_index_def
        using assms(1,9) idx_b_valid unique_enq_index val_b
        by auto

      (* --- 2. bt_act position --- *)
      (* constructionprefix index *)
      let ?prefix_bt = "l1 @ l21 @ [b_act] @ [o1] @ new_l22"
      have L_struct_bt: "L = ?prefix_bt @ [bt_act] @ l3" using L_decomp by simp
      
      have idx_bt_calc: "?idx_bt = length ?prefix_bt" by simp
      have idx_bt_valid: "?idx_bt < length L" using L_struct_bt idx_bt_calc by simp
      have val_bt: "L ! ?idx_bt = bt_act" using L_struct_bt idx_bt_calc by (simp add: nth_append)
        
      have cond_bt: "op_name (L ! ?idx_bt) = enq \<and> op_val (L ! ?idx_bt) = bt_val"
        using val_bt assms(10,11) by simp
        
      have pos_bt: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some ?idx_bt"
        unfolding find_unique_index_def
        using assms(1,10,11) idx_bt_valid unique_enq_index val_bt
        by force

      (* Comment. *)
      show ?thesis 
        using distance_func_def b_not_in_SA pos_b pos_bt by simp
    qed

(* C. new_L distance *)
    have dist_new: "distance_func (op_val b_act) bt_val new_L = 1 + length new_l22"
    proof -
      let ?idx_b = "length l1 + length l21 + 1"
      let ?idx_bt = "length l1 + length l21 + 2 + length new_l22"
      
      (* --- 1. b_act position --- *)
      (* assms(12) replace new_L_def *)
      have idx_b_valid: "?idx_b < length new_L" using assms(12) by simp
      
      (* new_L, b_act l1 @ l21 @ [o1] *)
      have val_b: "new_L ! ?idx_b = b_act" using assms(12) by (simp add: nth_append)

      have cond_b: "op_name (new_L ! ?idx_b) = enq \<and> op_val (new_L ! ?idx_b) = op_val b_act"
        using val_b assms(9) by simp

      (* : di_new_L *)
      have pos_b: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = op_val b_act) new_L = Some ?idx_b"
        unfolding find_unique_index_def
        using assms(9) di_new_L idx_b_valid unique_enq_index val_b
        by fastforce
      
      (* --- 2. bt_act position --- *)
      let ?prefix_bt = "l1 @ l21 @ [o1] @ [b_act] @ new_l22"
      have new_L_struct_bt: "new_L = ?prefix_bt @ [bt_act] @ l3" using assms(12) by simp
      
      have idx_bt_calc: "?idx_bt = length ?prefix_bt" by simp
      have idx_bt_valid: "?idx_bt < length new_L" using new_L_struct_bt idx_bt_calc by simp
      have val_bt: "new_L ! ?idx_bt = bt_act" using new_L_struct_bt idx_bt_calc by (simp add: nth_append)
      
      have cond_bt: "op_name (new_L ! ?idx_bt) = enq \<and> op_val (new_L ! ?idx_bt) = bt_val"
        using val_bt assms(10,11) by simp
        
      have pos_bt: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = Some ?idx_bt"
        unfolding find_unique_index_def
        using cond_bt di_new_L idx_bt_valid unique_enq_index
        by force
        
      (* Comment. *)
      show ?thesis 
        using distance_func_def b_not_in_SA_new pos_b pos_bt by simp
    qed

    (* D. *)
    show ?thesis using dist_L dist_new by simp
  qed


(* Step 7.3.3.0. *)
  have l3_unchanged: "\<forall>v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3)). 
      distance_func v bt_val new_L = 0 \<and> distance_func v bt_val L = 0"
  proof (rule ballI)
    fix v assume v_in: "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
    
    (* Proof step. *)
    have dist_L: "distance_func v bt_val L = 0"
    proof -
      let ?middle = "l21 @ [b_act] @ [o1] @ new_l22 @ [bt_act]"
      have L_decomp_middle: "L = l1 @ ?middle @ l3" by (simp add: L_decomp)
      have bt_in_middle: "bt_act \<in> set ?middle" by auto
      
      show "distance_func v bt_val L = 0"
        apply (rule l3_distance_zero_observational[where middle="?middle"])
        apply (rule assms(1))
        apply (rule L_decomp_middle)
        apply (rule bt_in_middle)
        apply (rule assms(10))
        apply (rule assms(11))
        apply (rule assms(3))
        apply (rule assms(4))
        apply (rule v_in)
        done
    qed

    (* Proof step. *)
    
    (* Step 1. *)
    have prefix_L: "take (length l1) L = l1"
      using assms(2) assms(3) by (metis append_eq_conv_conj)
    have prefix_new: "take (length l1) new_L = l1"
      using assms(12) by simp

    (* 2. Proof find_last_SA new_L = find_last_SA L *)
    have same_find_last_SA: "find_last_SA new_L = last_sa_pos"
    proof -
      let ?idxs_L = "find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L"
      let ?idxs_new = "find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) new_L) new_L"
      let ?S_L = "set ?idxs_L"
      let ?S_new = "set ?idxs_new"

      (* Proof step. *)
      have sets_eq: "?S_L = ?S_new"
      proof -
        (* A1. i < length l1 *)
        have part_prefix: "{i \<in> ?S_L. i < length l1} = {i \<in> ?S_new. i < length l1}"
        proof -
          have val_eq: "\<forall>i < length l1. L!i = new_L!i"
            using prefix_L prefix_new by (metis nth_take)

          have "\<forall>i. i < length l1 \<longrightarrow> (i \<in> ?S_L \<longleftrightarrow> i \<in> ?S_new)"
          proof (intro allI impI)
            fix i assume "i < length l1"
            have bounds: "i < length L" "i < length new_L"
              using `i < length l1` prefix_L prefix_new
              apply (metis dual_order.strict_trans linorder_le_less_linear
                  take_all_iff)
              apply (metis \<open>i < length l1\<close> dual_order.strict_trans not_le_imp_less
                  prefix_new take_all_iff)
              done
            have in_L: "i \<in> ?S_L \<longleftrightarrow> op_name (L!i) = enq \<and> in_SA (op_val (L!i)) L"
              using bounds(1) unfolding find_indices_def by auto
            have in_new: "i \<in> ?S_new \<longleftrightarrow> op_name (new_L!i) = enq \<and> in_SA (op_val (new_L!i)) new_L"
              using bounds(2) unfolding find_indices_def by auto
            show "i \<in> ?S_L \<longleftrightarrow> i \<in> ?S_new"
              using in_L in_new val_eq `i < length l1` same_SA by simp
          qed
          then show ?thesis by auto
        qed

        (* A2. i >= length l1, L *)
        have part_suffix_L: "{i \<in> ?S_L. i \<ge> length l1} = {}"
        proof (rule equals0I)
          fix i assume asm: "i \<in> {i \<in> ?S_L. i \<ge> length l1}"
          have i_valid: "i < length L" using asm unfolding find_indices_def by auto
          have i_prop: "op_name (L!i) = enq" "in_SA (op_val (L!i)) L"
            using asm unfolding find_indices_def by auto
          have i_ge: "i \<ge> length l1" using asm by simp
          have "\<not> in_SA (op_val (L!i)) L"
            by (simp add: i_ge i_prop(1) i_valid l1_contains_all_SA)
          show False using i_prop(2) `\<not> in_SA (op_val (L!i)) L` by simp
        qed

        (* A3. i >= length l1, new_L *)
        have part_suffix_new: "{i \<in> ?S_new. i \<ge> length l1} = {}"
        proof (rule ccontr)
          assume "{i \<in> ?S_new. i \<ge> length l1} \<noteq> {}"
          then obtain i where i_bad: "i \<in> ?S_new" "i \<ge> length l1" by auto
          have "i < length new_L" using i_bad unfolding find_indices_def by auto
          let ?elem = "new_L ! i"
          let ?v = "op_val ?elem"
          have elem_prop: "op_name ?elem = enq" "in_SA ?v new_L"
            using i_bad unfolding find_indices_def by auto

          have "?elem \<in> set L" 
            using mset_eq `i < length new_L` by (metis nth_mem set_mset_mset)
          then obtain j where j_def: "j < length L" "L!j = ?elem"
            by (auto simp: in_set_conv_nth)
          
          have "in_SA ?v L" using elem_prop same_SA by simp
          have "j < length l1"
            using l1_contains_all_SA_in_L j_def elem_prop `in_SA ?v L`
            by (metis l1_contains_all_SA leI) 
          
          have "i = j"
          proof -
            have "new_L ! j = L ! j" 
              using `j < length l1` prefix_new prefix_L by (metis nth_take)
            then have val_j: "op_name (new_L!j) = enq \<and> op_val (new_L!j) = ?v"
              using j_def elem_prop by simp
            have val_i: "op_name (new_L!i) = enq \<and> op_val (new_L!i) = ?v"
              using elem_prop by simp
            let ?S_match = "{k. k < length new_L \<and> op_name (new_L!k) = enq \<and> op_val (new_L!k) = ?v}"
            have "i \<in> ?S_match" using `i < length new_L` val_i by simp
            have "j \<in> ?S_match" using `j < length l1` prefix_new val_j 
              using mem_Collect_eq j_def(1) mset_eq mset_eq_length by fastforce
            have "card ?S_match \<le> 1" 
              using di_new_L unfolding data_independent_def by simp
            show ?thesis using `i \<in> ?S_match` `j \<in> ?S_match` `card ?S_match \<le> 1`
              using di_new_L same_enq_value_same_index by blast
          qed
          show False using `i = j` `i \<ge> length l1` `j < length l1` by simp
        qed
        
        show ?thesis
        proof (rule set_eqI)
          fix x show "x \<in> ?S_L \<longleftrightarrow> x \<in> ?S_new"
            using part_prefix part_suffix_L part_suffix_new
            using leI by blast
        qed
      qed

      (* Proof step. *)
      have props_L: "sorted ?idxs_L \<and> distinct ?idxs_L"
        unfolding find_indices_def by (simp add: sorted_wrt_filter)
      have props_new: "sorted ?idxs_new \<and> distinct ?idxs_new"
        unfolding find_indices_def by (simp add: sorted_wrt_filter)
      have idxs_eq: "?idxs_L = ?idxs_new"
        using sets_eq props_L props_new by (metis sorted_distinct_set_unique)

      (* C. conclusion *)
      show ?thesis
        unfolding find_last_SA_def
        using idxs_eq assms(4)
        by (simp add: find_last_SA_def)
    qed

    (* Step 3.1. *)
    have l1_new: "l1 = take (nat (last_sa_pos + 1)) new_L"
      using same_find_last_SA assms(3) prefix_new
      using length_take min_def nat_le_iff_add plus_1_eq_Suc assms(4)
      by (metis mset_eq prefix_L size_mset take_all_iff)

    (* Proof step. *)
    have dist_new: "distance_func v bt_val new_L = 0"
    proof -
      let ?middle_new = "l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act]"
      have new_L_decomp_middle: "new_L = l1 @ ?middle_new @ l3"
        by (simp add: assms(12))
      have bt_in_middle_new: "bt_act \<in> set ?middle_new" by auto

      show "distance_func v bt_val new_L = 0"
        apply (rule l3_distance_zero_observational[where middle="?middle_new"])
        apply (rule di_new_L)
        apply (rule new_L_decomp_middle)
        apply (rule bt_in_middle_new)
        apply (rule assms(10))
        apply (rule assms(11))
        apply (rule l1_new)
        apply (simp add: same_find_last_SA) 
        apply (rule v_in)
        done
    qed
    
    show "distance_func v bt_val new_L = 0 \<and> distance_func v bt_val L = 0"
      using dist_L dist_new by simp
  qed

(* Step 8. *)
  show ?thesis
  proof -
    (* definition *)
    let ?S_prefix = "set (map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ l21)))"
    let ?S_b = "{op_val b_act}"
    let ?S_bt = "{bt_val}"
    let ?S_l3 = "set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
    
    (* Step 1. *)
    have sum_prefix: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix \<le> sum (\<lambda>v. distance_func v bt_val L) ?S_prefix"
      using prefix_unchanged by (meson sum_mono)
    have sum_b: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_b < sum (\<lambda>v. distance_func v bt_val L) ?S_b"
      using b_act_strict_decrease by simp
    have sum_bt: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_bt = sum (\<lambda>v. distance_func v bt_val L) ?S_bt"
      using distance_self_zero[OF assms(1)] distance_self_zero[OF di_new_L] by simp
    have sum_l3: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_l3 = sum (\<lambda>v. distance_func v bt_val L) ?S_l3"
      using l3_unchanged by (auto simp: sum.neutral)

    (* Proof step. *)
    (* Proof step. *)
    have enq_list_L: "map op_val (filter (\<lambda>a. op_name a = enq) L) = 
          map op_val (filter (\<lambda>a. op_name a = enq) (l1 @ l21)) @ 
          [op_val b_act] @ 
          [bt_val] @ 
          map op_val (filter (\<lambda>a. op_name a = enq) l3)"
    proof -
      (* Proof step. *)
      have part_b: "map op_val (filter (\<lambda>a. op_name a = enq) [b_act]) = [op_val b_act]"
        using assms(9) by simp
      
      have part_o1: "map op_val (filter (\<lambda>a. op_name a = enq) [o1]) = []"
        using o1_is_deq by simp
        
      have part_new_l22: "map op_val (filter (\<lambda>a. op_name a = enq) new_l22) = []"
      proof -
        have "set new_l22 \<subseteq> set l22" using l22_decomp by auto
        then have "\<forall>x \<in> set new_l22. op_name x \<noteq> enq" 
          using l22_all_deq by auto
        then show ?thesis by (simp add: filter_empty_conv)
      qed

      have part_bt: "map op_val (filter (\<lambda>a. op_name a = enq) [bt_act]) = [bt_val]"
        using assms(10,11) by simp

      (* combine *)
      show ?thesis
        unfolding L_decomp
        by (smt (verit, del_insts) append_assoc filter_append map_append
            part_b part_bt part_new_l22 part_o1 self_append_conv2)
    qed

    (* Proof step. *)
    (* Proof step. *)
    
    (* Step 3.1. *)
    have distinct_enqs: "distinct (map op_val (filter (\<lambda>a. op_name a = enq) L))"
    proof -
      (* distinct *)
      have "\<forall>v. count (mset (map op_val (filter (\<lambda>a. op_name a = enq) L))) v \<le> 1"
      proof
        fix v
        (* map+filter filter *)
        have "count (mset (map op_val (filter (\<lambda>a. op_name a = enq) L))) v = 
              length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L)"
          by (induction L) auto
        (* index *)
        also have "... = card {i. i < length L \<and> op_name (L!i) = enq \<and> op_val (L!i) = v}"
          using length_filter_conv_card by fastforce
        (* apply definition *)
        finally show "count (mset (map op_val (filter (\<lambda>a. op_name a = enq) L))) v \<le> 1"
          using assms(1) unfolding data_independent_def by simp
      qed
      thus ?thesis using distinct_count_atmost_1 
        by (metis count_mset_0_iff less_one nless_le)
    qed
      
    (* Step 3.2. *)
    (* distinct, set *)
    (* Proof step. *)
    have disjoints: 
      "?S_prefix \<inter> ?S_b = {}" "?S_prefix \<inter> ?S_bt = {}" "?S_prefix \<inter> ?S_l3 = {}"
      "?S_b \<inter> ?S_bt = {}" "?S_b \<inter> ?S_l3 = {}" "?S_bt \<inter> ?S_l3 = {}"
      using distinct_enqs unfolding enq_list_L
      by auto

    (* Step 4. *)
    let ?S_all = "set (map op_val (filter (\<lambda>a. op_name a = enq) L))"
    have S_union: "?S_all = ?S_prefix \<union> ?S_b \<union> ?S_bt \<union> ?S_l3"
      unfolding enq_list_L
      by auto

    have dist_L: "Distance L bt_val = sum (\<lambda>v. distance_func v bt_val L) ?S_prefix + 
                                      sum (\<lambda>v. distance_func v bt_val L) ?S_b + 
                                      sum (\<lambda>v. distance_func v bt_val L) ?S_bt + 
                                      sum (\<lambda>v. distance_func v bt_val L) ?S_l3"
    proof -
      (* A. unfold Distance definition (strict) *)
      
      (* definition all_enqueues *)
      let ?all_enqueues = "filter (\<lambda>a. op_name a = enq) L"
      
      (* definition enqueued_values *)
      let ?enqueued_values = "set (map op_val ?all_enqueues)"
      
      (* Proof step. *)
      have "?enqueued_values = ?S_all" by simp
      
      (* Distance L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val L) (sorted_list_of_set ?S_all)) *)
      have "Distance L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val L) (sorted_list_of_set ?S_all))"
        unfolding Distance_def
        by (simp add: `?enqueued_values = ?S_all`)
      
      (* Proof step. *)
      (* distinct_enqs, map op_val (filter (\<lambda>a. op_name a = enq) L) distinct *)
      (* ?S_all *)
      have "card ?S_all = length (map op_val (filter (\<lambda>a. op_name a = enq) L))"
        using distinct_enqs distinct_card by blast
        
      (* sum_list sum *)
      (* : distinct xs, sum_list (map f xs) = sum f (set xs) *)
      have "sum_list (map (\<lambda>v. distance_func v bt_val L) (sorted_list_of_set ?S_all)) = 
            sum (\<lambda>v. distance_func v bt_val L) ?S_all"
      proof -
        (* Auxiliary lemma. *)
        (* direct sum_list_distinct_conv_sum_set *)
        (* Proof step. *)
        have "distinct (sorted_list_of_set ?S_all)"
          by simp
        
        (* Proof step. *)
        have "set (sorted_list_of_set ?S_all) = ?S_all"
          by simp
        
        (* apply sum_list_distinct_conv_sum_set *)
        show ?thesis
          using `distinct (sorted_list_of_set ?S_all)`
          by (simp add: sum_list_distinct_conv_sum_set)
      qed
      
      (* C. Distance L bt_val = sum (\<lambda>v. distance_func v bt_val L) ?S_all *)
      then have "Distance L bt_val = sum (\<lambda>v. distance_func v bt_val L) ?S_all"
        using `Distance L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val L) (sorted_list_of_set ?S_all))`
        by simp
        
      (* D. unfold *)
      also have "... = sum (\<lambda>v. distance_func v bt_val L) (?S_prefix \<union> ?S_b \<union> ?S_bt \<union> ?S_l3)"
        using S_union by simp
        
      (* Step. *)
      also have "... = sum (\<lambda>v. distance_func v bt_val L) ?S_prefix + 
                       sum (\<lambda>v. distance_func v bt_val L) (?S_b \<union> ?S_bt \<union> ?S_l3)"
      proof -
        have "finite ?S_prefix" by simp
        have "finite (?S_b \<union> ?S_bt \<union> ?S_l3)" by simp
        have "?S_prefix \<inter> (?S_b \<union> ?S_bt \<union> ?S_l3) = {}" using disjoints by auto
        show ?thesis 
          using sum.union_disjoint[OF `finite ?S_prefix` `finite (?S_b \<union> ?S_bt \<union> ?S_l3)` `?S_prefix \<inter> (?S_b \<union> ?S_bt \<union> ?S_l3) = {}`] 
          by simp
      qed
      
      also have "... = sum (\<lambda>v. distance_func v bt_val L) ?S_prefix + 
                       (sum (\<lambda>v. distance_func v bt_val L) ?S_b + 
                        sum (\<lambda>v. distance_func v bt_val L) (?S_bt \<union> ?S_l3))"
      proof -
        have "finite ?S_b" by simp
        have "finite (?S_bt \<union> ?S_l3)" by simp
        have "?S_b \<inter> (?S_bt \<union> ?S_l3) = {}" using disjoints by auto
        show ?thesis 
          using sum.union_disjoint[OF `finite ?S_b` `finite (?S_bt \<union> ?S_l3)` `?S_b \<inter> (?S_bt \<union> ?S_l3) = {}`] 
          by simp
      qed
      
      also have "... = sum (\<lambda>v. distance_func v bt_val L) ?S_prefix + 
                       sum (\<lambda>v. distance_func v bt_val L) ?S_b + 
                       (sum (\<lambda>v. distance_func v bt_val L) ?S_bt + 
                        sum (\<lambda>v. distance_func v bt_val L) ?S_l3)"
      proof -
        have "finite ?S_bt" by simp
        have "finite ?S_l3" by simp
        have "?S_bt \<inter> ?S_l3 = {}" using disjoints by auto
        show ?thesis 
          using sum.union_disjoint[OF `finite ?S_bt` `finite ?S_l3` `?S_bt \<inter> ?S_l3 = {}`] 
          by simp
      qed
      
      finally show ?thesis by simp
    qed

    (* Step 5. *)
    have dist_new: "Distance new_L bt_val = sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix + 
                                            sum (\<lambda>v. distance_func v bt_val new_L) ?S_b + 
                                            sum (\<lambda>v. distance_func v bt_val new_L) ?S_bt + 
                                            sum (\<lambda>v. distance_func v bt_val new_L) ?S_l3"
    proof -
      (* A. unfold Distance definition () *)
      let ?all_enqueues_new = "filter (\<lambda>a. op_name a = enq) new_L"
      let ?enqueued_values_new = "set (map op_val ?all_enqueues_new)"
      
      have "?enqueued_values_new = ?S_all"
      proof -
        have "mset (map op_val ?all_enqueues_new) = mset (map op_val (filter (\<lambda>a. op_name a = enq) L))"
          using mset_eq mset_filter mset_map by simp

        then show ?thesis
          by (metis set_mset_mset)
      qed
      
      have "Distance new_L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val new_L) (sorted_list_of_set ?S_all))"
        unfolding Distance_def
        by (metis `?enqueued_values_new = ?S_all`)
      
      (* B. sum_list sum () *)
      have "distinct (sorted_list_of_set ?S_all)" by simp
      
      have "sum_list (map (\<lambda>v. distance_func v bt_val new_L) (sorted_list_of_set ?S_all)) = 
            sum (\<lambda>v. distance_func v bt_val new_L) ?S_all"
      proof -
        have "set (sorted_list_of_set ?S_all) = ?S_all" by simp
        show ?thesis
          using `distinct (sorted_list_of_set ?S_all)`
          by (simp add: sum_list_distinct_conv_sum_set)
      qed
      
      (* C. Distance new_L bt_val = sum... () *)
      then have "Distance new_L bt_val = sum (\<lambda>v. distance_func v bt_val new_L) ?S_all"
        using `Distance new_L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val new_L) (sorted_list_of_set ?S_all))`
        by simp
        
      (* D. unfold apply sum.union_disjoint () *)
      also have "... = sum (\<lambda>v. distance_func v bt_val new_L) (?S_prefix \<union> ?S_b \<union> ?S_bt \<union> ?S_l3)"
        using S_union by simp
        
      (* Proof step. *)
      also have "... = sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix + 
                       sum (\<lambda>v. distance_func v bt_val new_L) (?S_b \<union> ?S_bt \<union> ?S_l3)"
      proof -
        have "finite ?S_prefix" by simp
        have "finite (?S_b \<union> ?S_bt \<union> ?S_l3)" by simp
        have "?S_prefix \<inter> (?S_b \<union> ?S_bt \<union> ?S_l3) = {}" using disjoints by auto
        show ?thesis 
          using sum.union_disjoint[OF `finite ?S_prefix` `finite (?S_b \<union> ?S_bt \<union> ?S_l3)` `?S_prefix \<inter> (?S_b \<union> ?S_bt \<union> ?S_l3) = {}`] 
          by simp
      qed

      also have "... = sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix + 
                       (sum (\<lambda>v. distance_func v bt_val new_L) ?S_b + 
                        sum (\<lambda>v. distance_func v bt_val new_L) (?S_bt \<union> ?S_l3))"
      proof -
        have "finite ?S_b" by simp
        have "finite (?S_bt \<union> ?S_l3)" by simp
        have "?S_b \<inter> (?S_bt \<union> ?S_l3) = {}" using disjoints by auto
        show ?thesis 
          using sum.union_disjoint[OF `finite ?S_b` `finite (?S_bt \<union> ?S_l3)` `?S_b \<inter> (?S_bt \<union> ?S_l3) = {}`] 
          by simp
      qed

      also have "... = sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix + 
                       sum (\<lambda>v. distance_func v bt_val new_L) ?S_b + 
                       (sum (\<lambda>v. distance_func v bt_val new_L) ?S_bt + 
                        sum (\<lambda>v. distance_func v bt_val new_L) ?S_l3)"
      proof -
        have "finite ?S_bt" by simp
        have "finite ?S_l3" by simp
        have "?S_bt \<inter> ?S_l3 = {}" using disjoints by auto
        show ?thesis 
          using sum.union_disjoint[OF `finite ?S_bt` `finite ?S_l3` `?S_bt \<inter> ?S_l3 = {}`] 
          by simp
      qed

      finally show ?thesis by simp
    qed

    (* --- 6. final --- *)
    show ?thesis
      unfolding dist_L dist_new
      using sum_prefix sum_b sum_bt sum_l3
      by linarith
  qed
qed


lemma moving_bt_act_before_b_act_case4:
  assumes "data_independent L"
  assumes "L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3"
  assumes "op_name b_act = enq" 
  assumes "op_name bt_act = enq"
  assumes "op_val bt_act = bt_val"
  assumes "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"
  assumes "l1 = take (nat (find_last_SA L + 1)) L" 
  shows "Distance new_L bt_val < Distance L bt_val"
proof -
  (* 1. basicstructurepreparation *)
  have mset_eq: "mset new_L = mset L"
    using assms(2,6) by (simp add: ac_simps)
  have di_new_L: "data_independent new_L"
    using assms(1) mset_eq new_L_is_data_independent by blast
  have same_SA: "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L"
    by (metis (no_types, lifting) L_and_new_L_have_same_SA
        Nil_is_append_conv assms(1,2,6,7) mset_eq)

  (* --- preparationpositionLemma --- *)
  
  let ?prefix_list = "l1 @ l21"
  let ?jumped_list = "[b_act] @ l22"
  let ?rest_list = "[bt_act] @ l3"

  let ?pos_bt_L = "length ?prefix_list + length ?jumped_list"
  let ?pos_bt_new = "length ?prefix_list"

  (* Step 1. *)
  have pos_bt_L_val: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some ?pos_bt_L"
  proof -
   have L_expanded: "L = ?prefix_list @ ?jumped_list @ [bt_act] @ l3"
      by (subst assms(2), simp)
    
    have val_at_pos: "L ! ?pos_bt_L = bt_act"
      using L_expanded by (simp add: nth_append)
    have idx_bound: "?pos_bt_L < length L"
        using L_expanded by simp
    
    show ?thesis
      unfolding find_unique_index_def
      using val_at_pos idx_bound assms(4,5)
      using unique_enq_value[OF assms(1)]
      using L_expanded
      using assms(1) unique_enq_index by force 
  qed

  (* Step 2. *)
  have pos_bt_new_val: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = Some ?pos_bt_new"
  proof -
    have new_L_expanded: "new_L = ?prefix_list @ [bt_act] @ (?jumped_list @ l3)"
      using assms(6)
      by simp
      
    have val_at_pos: "new_L ! ?pos_bt_new = bt_act"
      using new_L_expanded by (simp add: nth_append)
    have idx_bound: "?pos_bt_new < length new_L"
      using new_L_expanded
      by force
      
    show ?thesis
      unfolding find_unique_index_def
      using val_at_pos idx_bound assms(4,5)
      using unique_enq_value[OF di_new_L]
      using new_L_expanded
      using di_new_L unique_enq_index by force 
  qed

  (* : positionstrict *)
  have pos_decrease: "?pos_bt_new < ?pos_bt_L"
    by simp 

  (* --- distanceanalysis --- *)
  
  (* A. definition *)
  let ?S_prefix = "set (map op_val (filter (\<lambda>a. op_name a = enq) ?prefix_list))"
  let ?S_jumped = "set (map op_val (filter (\<lambda>a. op_name a = enq) ?jumped_list))"
  let ?S_rest = "set (map op_val (filter (\<lambda>a. op_name a = enq) ?rest_list))"
  let ?S_total = "set (map op_val (filter (\<lambda>a. op_name a = enq) L))"

  (* Proof step. *)
  have set_decomp: "?S_total = ?S_prefix \<union> ?S_jumped \<union> ?S_rest"
  proof -
    have "filter (\<lambda>a. op_name a = enq) L = 
          filter (\<lambda>a. op_name a = enq) ?prefix_list @ 
          filter (\<lambda>a. op_name a = enq) ?jumped_list @ 
          filter (\<lambda>a. op_name a = enq) ?rest_list"
      using assms(2)
      by simp
    then show ?thesis by auto
  qed

  have finite_sets: "finite ?S_prefix" "finite ?S_jumped" "finite ?S_rest" by auto

  (* Proof step. *)
  
  (* C.1 Prefix Jumped *)
  have disjoint_1: "?S_prefix \<inter> ?S_jumped = {}"
  proof (rule ccontr)
     assume "\<not> ?thesis"
     then obtain v where "v \<in> ?S_prefix" "v \<in> ?S_jumped" by blast
     
     (* Prefix index *)
     obtain x where x_in: "x \<in> set ?prefix_list" "op_name x = enq" "op_val x = v"
       using `v \<in> ?S_prefix` unfolding set_map set_filter image_iff by blast
     obtain i where i_bound: "i < length ?prefix_list" and l1_at_i: "?prefix_list ! i = x"
       using x_in(1) by (metis in_set_conv_nth)
     have L_at_i: "L ! i = x" using assms(2) i_bound l1_at_i
       by (metis append.assoc nth_append_left)

     (* Jumped index *)
     obtain y where y_in: "y \<in> set ?jumped_list" "op_name y = enq" "op_val y = v"
       using `v \<in> ?S_jumped` unfolding set_map set_filter image_iff by blast
     obtain k where k_bound: "k < length ?jumped_list" and j_at_k: "?jumped_list ! k = y"
       using y_in(1) by (metis in_set_conv_nth)
     
     let ?global_k = "length ?prefix_list + k"
     have global_k_bound: "?global_k < length L" using assms(2) k_bound by simp
     have L_at_k: "L ! ?global_k = y" 
       using assms(2) k_bound j_at_k by (metis append_assoc nth_append_left nth_append_length_plus)
     
     have "i < ?global_k" using i_bound by simp
     show False 
       using unique_enq_value[OF assms(1), of i ?global_k]
       using L_at_i L_at_k x_in(2,3) y_in(2,3) `i < ?global_k`
       using i_bound global_k_bound by simp 
  qed

  (* C.2 Prefix Rest *)
  have disjoint_2: "?S_prefix \<inter> ?S_rest = {}"
  proof (rule ccontr)
     assume "\<not> ?thesis"
     then obtain v where "v \<in> ?S_prefix" "v \<in> ?S_rest" by blast
     
     (* Prefix *)
     obtain x where x_in: "x \<in> set ?prefix_list" "op_name x = enq" "op_val x = v"
       using `v \<in> ?S_prefix` unfolding set_map set_filter image_iff by blast
     obtain i where i_bound: "i < length ?prefix_list" and l1_at_i: "?prefix_list ! i = x"
       using x_in(1) by (metis in_set_conv_nth)
     have L_at_i: "L ! i = x" using assms(2) i_bound l1_at_i
       by (metis append.assoc nth_append_left)
     
     (* Rest *)
     obtain z where z_in: "z \<in> set ?rest_list" "op_name z = enq" "op_val z = v"
       using `v \<in> ?S_rest` unfolding set_map set_filter image_iff by blast
     obtain k where k_bound: "k < length ?rest_list" and r_at_k: "?rest_list ! k = z"
       using z_in(1) by (metis in_set_conv_nth)
     
     let ?offset = "length ?prefix_list + length ?jumped_list"
     let ?global_k = "?offset + k"
     
     have global_k_bound: "?global_k < length L" using assms(2) k_bound by simp
     have L_at_k: "L ! ?global_k = z" using assms(2) k_bound r_at_k by (simp add: nth_append)

     have "i < ?global_k" using i_bound by simp
     show False
       using unique_enq_value[OF assms(1), of i ?global_k]
       using L_at_i L_at_k x_in(2,3) z_in(2,3) `i < ?global_k`
       using i_bound global_k_bound by simp
   qed

  (* C.3 Jumped Rest *)
  have disjoint_3: "?S_jumped \<inter> ?S_rest = {}"
  proof (rule ccontr)
     assume "\<not> ?thesis"
     then obtain v where "v \<in> ?S_jumped" "v \<in> ?S_rest" by blast

     (* Jumped *)
     obtain y where y_in: "y \<in> set ?jumped_list" "op_name y = enq" "op_val y = v"
       using `v \<in> ?S_jumped` unfolding set_map set_filter image_iff by blast
     obtain j where j_bound: "j < length ?jumped_list" and j_at_j: "?jumped_list ! j = y"
       using y_in(1) by (metis in_set_conv_nth)
     
     let ?global_j = "length ?prefix_list + j"
     have L_at_j: "L ! ?global_j = y" using assms(2) j_bound j_at_j by (metis append_assoc nth_append_left nth_append_length_plus)
     have global_j_bound: "?global_j < length L" using assms(2) j_bound by simp

     (* Rest *)
     obtain z where z_in: "z \<in> set ?rest_list" "op_name z = enq" "op_val z = v"
       using `v \<in> ?S_rest` unfolding set_map set_filter image_iff by blast
     obtain k where k_bound: "k < length ?rest_list" and r_at_k: "?rest_list ! k = z"
       using z_in(1) by (metis in_set_conv_nth)

     let ?offset = "length ?prefix_list + length ?jumped_list"
     let ?global_k = "?offset + k"
     
     have L_at_k: "L ! ?global_k = z" using assms(2) k_bound r_at_k by (simp add: nth_append) 
     have global_k_bound: "?global_k < length L" using assms(2) k_bound by simp

     have "?global_j < ?global_k" using j_bound by simp
     show False
       using unique_enq_value[OF assms(1), of ?global_j ?global_k]
       using L_at_j L_at_k y_in(2,3) z_in(2,3) `?global_j < ?global_k`
       using global_j_bound global_k_bound by auto
  qed

  (* Proof step. *)

  (* D.1 Prefix (l1 + l21): distance *)
  have sum_prefix_le: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix \<le> sum (\<lambda>v. distance_func v bt_val L) ?S_prefix"
  proof -
    have "\<forall>v \<in> ?S_prefix. distance_func v bt_val new_L \<le> distance_func v bt_val L"
    proof
      fix v assume v_in: "v \<in> ?S_prefix"
      
      (* Step 1. *)
      obtain e where e_in: "e \<in> set ?prefix_list" "op_name e = enq" "op_val e = v"
        using v_in unfolding set_map set_filter image_iff by blast
      obtain k where k_bound: "k < length ?prefix_list" and act_at_k: "?prefix_list ! k = e"
        using e_in by (metis in_set_conv_nth)

      (* Step 2. *)
      show "distance_func v bt_val new_L \<le> distance_func v bt_val L"
      proof (cases "in_SA v L")
        case True
        (* Case 0. *)
        then have sa_new: "in_SA v new_L" using same_SA by simp
        have "distance_func v bt_val L = 0" 
          using True unfolding distance_func_def by simp
        moreover have "distance_func v bt_val new_L = 0" 
          using sa_new unfolding distance_func_def by simp
        ultimately show ?thesis by simp
      next
        case False
        (* Case. *)
        note not_sa_L = False
        have not_sa_new: "\<not> in_SA v new_L" using same_SA False by simp

        (* v L position *)
        have L_at_k: "L ! k = e" using assms(2) k_bound act_at_k
          by (metis append.assoc nth_append_left)
        have k_less_bt_L: "k < ?pos_bt_L" using k_bound by simp
        
        have idx_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some k"
          unfolding find_unique_index_def
          using L_at_k assms(2) k_bound e_in(2,3) unique_enq_value[OF assms(1)]
          using assms(1) unique_enq_index by simp fastforce

        (* v new_L position *)
        have new_L_at_k: "new_L ! k = e" using assms(6) k_bound act_at_k
          by (metis append_eq_appendI nth_append_left)
        have k_less_bt_new: "k < ?pos_bt_new" using k_bound by simp

        have idx_new: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some k"
          unfolding find_unique_index_def
          using new_L_at_k assms(6) k_bound e_in(2,3) unique_enq_value[OF di_new_L]
          using di_new_L unique_enq_index by simp fastforce

        (* distance *)
        have dL: "distance_func v bt_val L = ?pos_bt_L - k"
          unfolding distance_func_def
          using idx_L pos_bt_L_val not_sa_L k_less_bt_L by auto
        
        have dNew: "distance_func v bt_val new_L = ?pos_bt_new - k"
          unfolding distance_func_def
          using idx_new pos_bt_new_val not_sa_new k_less_bt_new by auto

        (* : pos_bt, k unchanged, distance *)
        show ?thesis using dL dNew pos_decrease by simp
      qed
    qed
    then show ?thesis using sum_mono
      by metis
  qed

  (* D.2 Jumped (b_act + l22): distancestrict () *)
  (* Core: L bt_act, new_L bt_act *)
  have sum_jumped_strict: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_jumped < sum (\<lambda>v. distance_func v bt_val L) ?S_jumped"
  proof -
    (* non-empty (b_act) *)
    have "b_act \<in> set ?jumped_list" by simp
    then have "op_val b_act \<in> ?S_jumped" using assms(3) unfolding set_map set_filter image_iff by blast
    then have not_empty: "?S_jumped \<noteq> {}" by auto

    have "\<forall>v \<in> ?S_jumped. distance_func v bt_val new_L < distance_func v bt_val L"
    proof
      fix v assume v_in: "v \<in> ?S_jumped"
      
      (* Step 1. *)
      obtain e where e_in: "e \<in> set ?jumped_list" "op_name e = enq" "op_val e = v"
        using v_in unfolding set_map set_filter image_iff by blast
      obtain k where k_bound: "k < length ?jumped_list" and act_at_k: "?jumped_list ! k = e"
        using e_in by (metis in_set_conv_nth)

      (* Step 2.4. *)
      (* l1 SA. Jumped (b_act+l22) l1, SA *)
      have "\<not> in_SA v L"
      proof -
        (* A. v L position *)
        let ?pos_v_L = "length ?prefix_list + k"
        have L_at_pos: "L ! ?pos_v_L = e" 
          using assms(2) k_bound act_at_k 
          by (metis append_assoc nth_append_left nth_append_length_plus)
          
        (* B. position *)
        have pos_bound: "?pos_v_L < length L" 
          using assms(2) k_bound by simp

        show ?thesis
          using L_at_pos pos_bound e_in(2,3)
          using assms(1,2,7) l1_contains_all_SA_in_L
          by force
      qed

      (* Step 3.0. *)
      let ?pos_v_L = "length ?prefix_list + k"
      
      (* Proof step. *)
      have L_at_pos: "L ! ?pos_v_L = e" 
        using assms(2) k_bound act_at_k 
        by (metis append_assoc nth_append_left nth_append_length_plus)
      
      (* Proof step. *)
      have pos_bound: "?pos_v_L < length L" 
        using assms(2) k_bound by simp

      (* Proof step. *)
      have idx_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some ?pos_v_L"
        unfolding find_unique_index_def
        using L_at_pos pos_bound e_in(2,3) (* e_in oper=enq, val=v *)
        using unique_enq_value[OF assms(1)] (* unique *)
        using assms(1) unique_enq_index 
        by fastforce

      have pos_rel: "?pos_v_L < ?pos_bt_L" using k_bound by simp
      
      have dist_L_pos: "distance_func v bt_val L > 0"
        unfolding distance_func_def
        using idx_L pos_bt_L_val `\<not> in_SA v L` pos_rel by simp

     (* Step 4.0. *)
      (* new_L = prefix @ [bt] @ jumped @ ... *)
      let ?pos_v_new = "length ?prefix_list + 1 + k"
      
      have new_L_at_new: "new_L ! ?pos_v_new = e" 
      proof -
        (* Step 1. *)
        have struct: "new_L = ?prefix_list @ ([bt_act] @ ?jumped_list @ l3)"
          using assms(6) by simp
          
        (* Step 2. *)
        (* index len(prefix) + (1 + k) *)
        have "new_L ! ?pos_v_new = (?prefix_list @ ([bt_act] @ ?jumped_list @ l3)) ! (length ?prefix_list + (1 + k))"
          using struct by simp
        also have "... = ([bt_act] @ ?jumped_list @ l3) ! (1 + k)"
          by (rule nth_append_length_plus)
          
        (* Step 3. *)
        (* [bt_act] 1, index 1 + k *)
        also have "... = ([bt_act] @ (?jumped_list @ l3)) ! (length [bt_act] + k)"
          by simp
        also have "... = (?jumped_list @ l3) ! k"
          by (rule nth_append_length_plus)
          
        (* Step 4. *)
        also have "... = ?jumped_list ! k"
          using k_bound
          using nth_append_left by blast
          
        (* 5. conclusion *)
        finally show ?thesis using act_at_k by simp
      qed
        
      have idx_new: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some ?pos_v_new"
        unfolding find_unique_index_def
        using new_L_at_new assms(6) k_bound e_in(2,3) unique_enq_value[OF di_new_L]
        using di_new_L unique_enq_index by simp fastforce

      have pos_rel_new: "?pos_v_new > ?pos_bt_new" by simp

      have dist_new_zero: "distance_func v bt_val new_L = 0"
        unfolding distance_func_def
        using idx_new pos_bt_new_val pos_rel_new by simp

      (* conclusion *)
      show "distance_func v bt_val new_L < distance_func v bt_val L"
        using dist_L_pos dist_new_zero by simp
    qed
    then show ?thesis
      using not_empty sum_strict_mono
      by (metis (lifting) finite_sets(2)) 
  qed

(* D.3 Rest (bt_act + l3): distanceunchanged (0) *)
  have rest_unchanged: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_rest = sum (\<lambda>v. distance_func v bt_val L) ?S_rest"
  proof -
    (* Step 1.3.0. *)
    have l3_zeros_L: "\<forall>v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3)). distance_func v bt_val L = 0"
    proof
      fix v assume v_in_l3: "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
      obtain z where z_in: "z \<in> set l3" "op_name z = enq" "op_val z = v"
        using v_in_l3 unfolding set_map set_filter image_iff by blast
      obtain k where k_bound: "k < length l3" and l3_at_k: "l3 ! k = z"
        using z_in(1) by (metis in_set_conv_nth)

      let ?pre_bt = "l1 @ l21 @ [b_act] @ l22"
      let ?pos_bt = "length ?pre_bt"
      let ?pos_v = "?pos_bt + 1 + k" 
      
      have L_bt: "L ! ?pos_bt = bt_act" using assms(2) by (simp add: nth_append)
      have L_v: "L ! ?pos_v = z" using assms(2) l3_at_k k_bound by (simp add: nth_append)
      have len_L: "length L = ?pos_bt + 1 + length l3" using assms(2) by simp
      have bound_bt: "?pos_bt < length L" using len_L by simp
      have bound_v: "?pos_v < length L" using len_L k_bound by simp

      have idx_bt: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L = Some ?pos_bt"
        unfolding find_unique_index_def
        using L_bt bound_bt assms(4,5) unique_enq_value[OF assms(1)]
        using find_unique_index_def pos_bt_L_val by auto  

      have idx_v: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some ?pos_v"
        unfolding find_unique_index_def
        using L_v bound_v z_in(2,3) unique_enq_value[OF assms(1)]
        using assms(1) unique_enq_index by auto

      have "?pos_v > ?pos_bt" by simp
      show "distance_func v bt_val L = 0"
        unfolding distance_func_def
        using idx_bt idx_v `?pos_v > ?pos_bt` by simp
    qed

    (* Step 2.3.0. *)
    have l3_zeros_new: "\<forall>v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3)). distance_func v bt_val new_L = 0"
    proof
      fix v assume v_in_l3: "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
      obtain z where z_in: "z \<in> set l3" "op_name z = enq" "op_val z = v"
        using v_in_l3 unfolding set_map set_filter image_iff by blast
      obtain k where k_bound: "k < length l3" and l3_at_k: "l3 ! k = z"
        using z_in(1) by (metis in_set_conv_nth)

      let ?pre_bt_new = "l1 @ l21"
      let ?pos_bt_new = "length ?pre_bt_new"
      (* new_L = prefix @ [bt] @ (jumped @ l3) *)
      (* pos_v = len(prefix) + 1 + len(jumped) + k *)
      let ?pos_v_new = "?pos_bt_new + 1 + length ([b_act] @ l22) + k" 
      
      have new_L_bt: "new_L ! ?pos_bt_new = bt_act" 
        using assms(6) by (simp add: nth_append)
        
      have new_L_v: "new_L ! ?pos_v_new = z" 
        using assms(6) l3_at_k k_bound by (simp add: nth_append)
        
      have len_new: "length new_L = ?pos_bt_new + 1 + length ([b_act] @ l22) + length l3"
        using assms(6) by simp
        
      have bound_bt: "?pos_bt_new < length new_L" using len_new by simp
      have bound_v: "?pos_v_new < length new_L" using len_new k_bound by simp

      have idx_bt: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) new_L = Some ?pos_bt_new"
        unfolding find_unique_index_def
        using new_L_bt bound_bt assms(4,5) unique_enq_value[OF di_new_L]
        using find_unique_index_def pos_bt_new_val by auto

      have idx_v: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some ?pos_v_new"
      proof -
        let ?P = "\<lambda>a. op_name a = enq \<and> op_val a = v"
        have P_holds: "?P (new_L ! ?pos_v_new)" using new_L_v z_in(2,3) by simp
        have unique: "\<forall>j < length new_L. ?P (new_L ! j) \<longrightarrow> j = ?pos_v_new"
          using P_holds bound_v di_new_L same_enq_value_same_index by blast
        have exists_unique: "\<exists>!i. i < length new_L \<and> ?P (new_L ! i)"
          using assms(1,2) di_new_L unique_enq_value P_holds bound_v by blast 
        have the_is_idx: "(THE i. i < length new_L \<and> ?P (new_L ! i)) = ?pos_v_new"
          apply (rule the_equality)
          apply (simp add: bound_v P_holds)
          using unique bound_v new_L_v z_in(2,3) apply force
          using unique by auto
        show ?thesis
          unfolding find_unique_index_def
          using unique P_holds bound_v di_new_L exists_unique list.distinct(1)
            list.sel(1) the_is_idx unique_enq_index
        proof -
          obtain nn :: nat where
            "nn < length new_L \<and> op_name (new_L ! nn) = enq \<and> op_val (new_L ! nn) = v"
            by (metis exists_unique)
          then show "(let ns = find_indices (\<lambda>p. op_name p = enq \<and> op_val p = v) new_L in if ns = [] then None else Some (hd ns)) = Some ?pos_v_new"
            using di_new_L unique unique_enq_index the_is_idx by force
        qed
      qed

      have "?pos_v_new > ?pos_bt_new" by simp
      show "distance_func v bt_val new_L = 0"
        unfolding distance_func_def
        using idx_bt idx_v `?pos_v_new > ?pos_bt_new` by simp
    qed

    (* Step 3.0. *)
    have d_bt_L: "distance_func bt_val bt_val L = 0" using distance_self_zero[OF assms(1)] .
    have d_bt_new: "distance_func bt_val bt_val new_L = 0" using distance_self_zero[OF di_new_L] .

    have all_L_0: "\<forall>v \<in> ?S_rest. distance_func v bt_val L = 0"
    proof
      fix v assume "v \<in> ?S_rest"
      have "v = bt_val \<or> v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
        using `v \<in> ?S_rest` assms(4,5) by auto
      then show "distance_func v bt_val L = 0"
        using d_bt_L l3_zeros_L by auto
    qed

    have all_new_0: "\<forall>v \<in> ?S_rest. distance_func v bt_val new_L = 0"
    proof
      fix v assume "v \<in> ?S_rest"
      have "v = bt_val \<or> v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
        using `v \<in> ?S_rest` assms(4,5) by auto
      then show "distance_func v bt_val new_L = 0"
        using d_bt_new l3_zeros_new by auto
    qed

    show ?thesis
      using all_L_0 all_new_0 by (simp add: sum.neutral)
  qed

  (* --- F. combineconclusion --- *)
  
  have finite_S: "finite ?S_total" by simp
  have union_disjoint_rest: "(?S_prefix \<union> ?S_jumped) \<inter> ?S_rest = {}"
    using disjoint_2 disjoint_3
    by blast 
  
  (* 2. Distance L unfold *)
  have dist_L_sum: "Distance L bt_val = sum (\<lambda>v. distance_func v bt_val L) ?S_total"
  proof -
    have "Distance L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val L) (sorted_list_of_set ?S_total))"
      unfolding Distance_def Let_def by simp
    then show ?thesis using sum_list_distinct_conv_sum_set finite_S
      by (metis sorted_list_of_set.distinct_sorted_key_list_of_set
          sorted_list_of_set.set_sorted_key_list_of_set)
  qed

  (* 3. Distance new_L unfold *)
  have dist_new_sum: "Distance new_L bt_val = sum (\<lambda>v. distance_func v bt_val new_L) ?S_total"
  proof -
    let ?S_new = "set (map op_val (filter (\<lambda>a. op_name a = enq) new_L))"
    have S_eq: "?S_new = ?S_total"
    proof -
      have "mset (filter (\<lambda>a. op_name a = enq) new_L) = mset (filter (\<lambda>a. op_name a = enq) L)"
        using mset_eq by simp
      then have "set (filter (\<lambda>a. op_name a = enq) new_L) = set (filter (\<lambda>a. op_name a = enq) L)"
        by (metis set_mset_mset)
      then show ?thesis unfolding set_map by simp
    qed
    
    have "Distance new_L bt_val = sum_list (map (\<lambda>v. distance_func v bt_val new_L) (sorted_list_of_set ?S_new))"
      unfolding Distance_def Let_def by simp
    also have "... = sum (\<lambda>v. distance_func v bt_val new_L) ?S_new"
      using sum_list_distinct_conv_sum_set finite_S S_eq
      by (metis sorted_list_of_set.distinct_sorted_key_list_of_set
          sorted_list_of_set.set_sorted_key_list_of_set)
    finally show ?thesis using S_eq by simp
  qed

  (* Step 4. *)
  (* unfold new_L Sum *)
  have "Distance new_L bt_val = sum (\<lambda>v. distance_func v bt_val new_L) ?S_total"
    using dist_new_sum by simp
  
  also have "... = sum (\<lambda>v. distance_func v bt_val new_L) (?S_prefix \<union> ?S_jumped \<union> ?S_rest)"
    using set_decomp by simp
    
  also have "... = sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix + sum (\<lambda>v. distance_func v bt_val new_L) ?S_jumped + sum (\<lambda>v. distance_func v bt_val new_L) ?S_rest"
    using finite_sets disjoint_1 disjoint_2 disjoint_3 union_disjoint_rest
    by (simp add: finite_UnI sum.union_disjoint)
    
  (* Comment. *)
  also have "... < sum (\<lambda>v. distance_func v bt_val L) ?S_prefix + sum (\<lambda>v. distance_func v bt_val L) ?S_jumped + sum (\<lambda>v. distance_func v bt_val L) ?S_rest"
  proof -
    have le1: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_prefix \<le> sum (\<lambda>v. distance_func v bt_val L) ?S_prefix"
      using sum_prefix_le by simp
    have less2: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_jumped < sum (\<lambda>v. distance_func v bt_val L) ?S_jumped"
      using sum_jumped_strict by simp
    have eq3: "sum (\<lambda>v. distance_func v bt_val new_L) ?S_rest = sum (\<lambda>v. distance_func v bt_val L) ?S_rest"
      using rest_unchanged by simp
    show ?thesis using le1 less2 eq3 by linarith
  qed
  
  (* L Sum *)
  also have "... = sum (\<lambda>v. distance_func v bt_val L) (?S_prefix \<union> ?S_jumped \<union> ?S_rest)"
    using finite_sets disjoint_1 disjoint_2 disjoint_3 union_disjoint_rest
    by (simp add: sum.union_disjoint)
    
  also have "... = sum (\<lambda>v. distance_func v bt_val L) ?S_total"
    using set_decomp by simp
    
  also have "... = Distance L bt_val"
    using dist_L_sum by simp
    
  finally show ?thesis .
qed




(* Proof step. *)
termination modify_lin
proof (relation "measure (\<lambda>(L, H, bt_val). Distance L bt_val)")
  (* Subgoal 1. *)
  show "wf (measure (\<lambda>(L, H, bt_val). Distance L bt_val))"
    using Distance_nonneg
    by simp
  
next
(* Case 2.2.2. *)
  show "\<And>L H bt_val x xa xb xc xd xe xf xg xh xi xj.
        \<not> \<not> should_modify L H bt_val \<Longrightarrow>
        x = Distance L bt_val \<Longrightarrow>
        xa = find_last_SA L \<Longrightarrow>
        xb = take (nat (xa + 1)) L \<Longrightarrow>
        xc = drop (nat (xa + 1)) L \<Longrightarrow>
        xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc) \<Longrightarrow>
        xe = xc ! xd \<Longrightarrow>
        xf = take xd xc \<Longrightarrow>
        xg = drop (xd + 1) xc \<Longrightarrow>
        xh = last xf \<Longrightarrow>
        op_name xh = enq \<Longrightarrow>
        xi = butlast xf \<Longrightarrow> xj = xb @ xi @ [xe] @ [xh] @ xg \<Longrightarrow> ((xj, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, bt_val). Distance L bt_val)"
  proof -
    (* Step 1. *)
    fix L H bt_val x xa xb xc xd xe xf xg xh xi xj
    assume prems:
      "\<not> \<not> should_modify L H bt_val"
      "x = Distance L bt_val"
      "xa = find_last_SA L"
      "xb = take (nat (xa + 1)) L"   (* 1:, show strictalignment *)
      "xc = drop (nat (xa + 1)) L"   (* 1:, show strictalignment *)
      "xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc)"
      "xe = xc ! xd"
      "xf = take xd xc"
      "xg = drop (xd + 1) xc"
      "xh = last xf"
      "op_name xh = enq"
      "xi = butlast xf"
      "xj = xb @ xi @ [xe] @ [xh] @ xg"

    (* should_modify extract *)
    from prems(1) have should_mod: "should_modify L H bt_val" by simp
    from should_mod have di_L: "data_independent L" 
      unfolding should_modify_def by simp

    (* map *)
    define last_sa_pos where "last_sa_pos = xa"
    define l1 where "l1 = xb"
    define remaining where "remaining = xc"
    define bt_idx where "bt_idx = xd"
    define bt_act where "bt_act = xe"
    define l2 where "l2 = xf"
    define l3 where "l3 = xg"
    define l2_last where "l2_last = xh"
    define ll2 where "ll2 = xi"
    define new_L where "new_L = xj"

    (* Proof step. *)
    (* Branch 2. *)
    have bt_in_remaining: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      thus False
        using should_mod prems(3) prems(5)
        unfolding should_modify_def Let_def remaining_def
        by (auto split: option.splits)
    qed
      
    then have bt_idx_some: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      unfolding bt_idx_def using option.collapse by (simp add: prems(6) remaining_def)

    have bt_act_props: "op_name bt_act = enq" "op_val bt_act = bt_val"
      using find_unique_index_prop[OF bt_idx_some]
      unfolding bt_act_def using prems(7) remaining_def bt_idx_def
      apply simp
      using \<open>bt_idx < length remaining \<and> op_name (remaining ! bt_idx) = enq \<and> op_val (remaining ! bt_idx) = bt_val\<close>
        bt_idx_def prems(7) remaining_def by auto 

    have remaining_split: "remaining = l2 @ [bt_act] @ l3"
    proof -
      have "bt_idx < length remaining"
        using find_unique_index_prop[OF bt_idx_some] by simp
      then show ?thesis
        unfolding l2_def l3_def bt_act_def
        using append_take_drop_id Cons_nth_drop_Suc
        by (metis Suc_eq_plus1 append_Cons append_self_conv2 bt_idx_def prems(7,8,9) remaining_def)
    qed

    have L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
      unfolding l1_def remaining_def
      using prems(4,5) append_take_drop_id remaining_split
      by (metis remaining_def)

    (* Proof l2 non-empty *)
    have l2_not_empty: "l2 \<noteq> []"
      using should_mod unfolding should_modify_def Let_def
      unfolding l2_def[symmetric] remaining_def[symmetric] bt_idx_def[symmetric]
      unfolding last_sa_pos_def[symmetric] l1_def[symmetric]
      using prems(6) 
      by (smt (z3) l2_def option.case_eq_if prems(10,3,5,8))

    (* construction new_L structure *)
    have new_L_struct: "new_L = l1 @ ll2 @ [bt_act] @ [l2_last] @ l3"
      unfolding new_L_def l1_def ll2_def bt_act_def l2_last_def l3_def
      using prems(13) by simp


    (* applyLemma *)
    have "Distance new_L bt_val < Distance L bt_val"
      apply (rule moving_bt_act_forward_over_l2_last_case2)
      apply (rule di_L)                         (* 1 *)
      apply (rule L_decomp)                     (* 2 *)
      unfolding l1_def last_sa_pos_def apply (rule prems(4)) (* 3 *)
      unfolding last_sa_pos_def apply (rule prems(3))        (* 4 *)
      apply (rule l2_not_empty)                 (* 5 *)
      unfolding l2_last_def l2_def apply (rule prems(10))   (* 6 *)
      unfolding l2_last_def apply (rule prems(11))           (* 7 *)
      unfolding ll2_def l2_def apply (rule prems(12))        (* 8 *)
      apply (rule bt_act_props(1))              (* 9 *)
      apply (rule bt_act_props(2))               (* 10 *)
      by (simp add: bt_act_def l3_def new_L_def prems(13))             

    thus "((xj, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, bt_val). Distance L bt_val)"
      unfolding new_L_def[symmetric] by simp
  qed

next
  (* Subgoal3: happens_before o1 bt_act H Branch (Case 3) *)
  show "\<And>L H bt_val x xa xb xc xd xe xf xg xh xi xj y xk ya xl xm xn xo.
       \<not> \<not> should_modify L H bt_val \<Longrightarrow>
       x = Distance L bt_val \<Longrightarrow>
       xa = find_last_SA L \<Longrightarrow>
       xb = take (nat (xa + 1)) L \<Longrightarrow>
       xc = drop (nat (xa + 1)) L \<Longrightarrow>
       xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc) \<Longrightarrow>
       xe = xc ! xd \<Longrightarrow>
       xf = take xd xc \<Longrightarrow>
       xg = drop (xd + 1) xc \<Longrightarrow>
       xh = last xf \<Longrightarrow>
       op_name xh \<noteq> enq \<Longrightarrow>
       xi = the (find_last_enq xf) \<Longrightarrow>
       (xj, y) = xi \<Longrightarrow>
       (xk, ya) = y \<Longrightarrow>
       xl = hd ya \<Longrightarrow>
       xm = last ya \<Longrightarrow>
       happens_before xl xe H \<Longrightarrow>
       xn = tl ya \<Longrightarrow>
       xo = xb @ xj @ [xl] @ [xk] @ xn @ [xe] @ xg \<Longrightarrow> ((xo, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, bt_val). Distance L bt_val)"
  proof -
    (* Step 1. *)
    fix L H bt_val x xa xb xc xd xe xf xg xh xi xj y xk ya xl xm xn xo
    assume prems:
      "\<not> \<not> should_modify L H bt_val"
      "x = Distance L bt_val"
      "xa = find_last_SA L"
      "xb = take (nat (xa + 1)) L"
      "xc = drop (nat (xa + 1)) L"
      "xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc)"
      "xe = xc ! xd"
      "xf = take xd xc"
      "xg = drop (xd + 1) xc"
      "xh = last xf"
      "op_name xh \<noteq> enq"
      "xi = the (find_last_enq xf)"
      "(xj, y) = xi"
      "(xk, ya) = y"
      "xl = hd ya"
      "xm = last ya"
      "happens_before xl xe H"
      "xn = tl ya"
      "xo = xb @ xj @ [xl] @ [xk] @ xn @ [xe] @ xg"

    (* should_modify extract *)
    from prems(1) have should_mod: "should_modify L H bt_val" by simp
    from should_mod have di_L: "data_independent L" 
      unfolding should_modify_def by simp

    (* Auxiliary lemma. *)
    define last_sa_pos where "last_sa_pos = xa"
    define l1 where "l1 = xb"
    define remaining where "remaining = xc"
    define bt_idx where "bt_idx = xd"
    define bt_act where "bt_act = xe"
    define l2 where "l2 = xf"
    define l3 where "l3 = xg"
    define l21 where "l21 = xj"
    define b_act where "b_act = xk"
    define l22 where "l22 = ya"
    define o1 where "o1 = xl"
    define new_l22 where "new_l22 = xn"
    define new_L where "new_L = xo"

    (* Step 2. *)
    have bt_in_remaining: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      thus False
        using should_mod prems(3) prems(5)
        unfolding should_modify_def Let_def remaining_def
        by (auto split: option.splits)
    qed    
    
    then have bt_idx_some: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      unfolding bt_idx_def using option.collapse
      by (simp add: prems(6) remaining_def)

    (* Proof step. *)
    have bt_act_props: "op_name bt_act = enq" "op_val bt_act = bt_val"
      using find_unique_index_prop[OF bt_idx_some]
      unfolding bt_act_def 
      using bt_idx_def prems(7) remaining_def
      apply meson
      using \<open>bt_idx < length remaining \<and> op_name (remaining ! bt_idx) = enq \<and> op_val (remaining ! bt_idx) = bt_val\<close> bt_idx_def prems(7) remaining_def by auto 

    (* combineProof L = l1 @ l2 @ [bt_act] @ l3 *)
    have L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
    proof -
      (* : L = l1 @ remaining *)
      have step1: "L = l1 @ remaining"
        unfolding l1_def remaining_def using append_take_drop_id
        by (simp add: prems(4,5))
      
      (* : remaining = l2 @ [bt_act] @ l3 *)
      have step2: "remaining = l2 @ [bt_act] @ l3"
      proof -
        have "bt_idx < length remaining"
          using find_unique_index_prop[OF bt_idx_some] by simp
        then show ?thesis
          unfolding l2_def l3_def bt_act_def
          using append_take_drop_id Cons_nth_drop_Suc
          by (metis Suc_eq_plus1 append_Cons append_self_conv2 bt_idx_def prems(7,8,9) remaining_def) 
      qed
      
      (* Comment. *)
      from step1 step2 show ?thesis by simp
    qed

    (* Step 3.2. *)
    
    (* l2 enq (should_modify execution path) *)
    have find_last_enq_not_none: "find_last_enq l2 \<noteq> None"
      using should_mod unfolding should_modify_def Let_def 
      l2_def[symmetric] remaining_def[symmetric] bt_idx_def[symmetric]
      last_sa_pos_def[symmetric] l1_def[symmetric]
      using prems(6) 
      by (smt (z3) l2_def option.case_eq_if prems(10,11,3,5,8)) 

    then have find_last_enq_eq: "find_last_enq l2 = Some (l21, b_act, l22)"
      using prems(12-14) unfolding l2_def l21_def b_act_def l22_def
      using option.collapse by fastforce

    (* Proof step. *)
    have b_act_enq: "op_name b_act = enq"
      using find_last_enq_props[OF find_last_enq_eq] by simp

    (* Step 4.22.1. *)

    (* l22 non-empty *)
    have l22_not_empty: "l22 \<noteq> []"
      using should_mod unfolding should_modify_def Let_def
      unfolding l2_def[symmetric] remaining_def[symmetric] bt_idx_def[symmetric]
      unfolding last_sa_pos_def[symmetric] l1_def[symmetric]
      using prems(6) find_last_enq_eq
      using b_act_enq find_last_enq_props(1) l2_def prems(10,11)
      by fastforce

    (* o1 l22 (hd) *)
    have o1_is_hd: "o1 = hd l22"
      using prems(15) unfolding o1_def l22_def by simp

    (* new_l22 l22 (tl) *)
    have new_l22_is_tl: "new_l22 = tl l22"
      using prems(18) unfolding new_l22_def l22_def by simp

    (* Case 1.5. *)
    have o1_is_deq: "op_name o1 = deq"
    proof -
      have all_deq: "\<forall>a \<in> set l22. op_name a = deq"
        using find_last_enq_eq l22_are_all_deq l22_not_empty by auto
      have "o1 \<in> set l22"
        using o1_is_hd l22_not_empty by (simp add: list.set_sel(1))
      with all_deq show ?thesis by auto
    qed

    (* Step 5. *)
    (* new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3 *)
    have new_L_struct: "new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3"
      unfolding new_L_def prems(19)
      unfolding l1_def l21_def o1_def b_act_def new_l22_def bt_act_def l3_def
      by simp

    (* Case 3.1.3. *)
    have "Distance new_L bt_val < Distance L bt_val"
      apply (rule moving_b_act_forward_over_o1_case3)
      apply (rule di_L)                              (* 1: data_independent L *)
      apply (rule L_decomp)                          (* 2: L = ... *)
      
      (* 3: l1 = take ... *)
      unfolding l1_def last_sa_pos_def 
      apply (rule prems(4)) 
      
      (* 4: last_sa_pos = find_last_SA L *)
      unfolding last_sa_pos_def 
      apply (rule prems(3))
      
      apply (rule find_last_enq_eq)                  (* 5: find_last_enq l2 = Some ... *)
      apply (rule l22_not_empty)                     (* 6: l22 \<noteq> [] *)
      apply (rule o1_is_hd)                          (* 7: o1 = hd l22 *)
      apply (rule new_l22_is_tl)                     (* 8: new_l22 = tl l22 *)
      apply (rule b_act_enq)                         (* 9: op_name b_act = enq *)
      apply (rule bt_act_props(1))                   (* 10: op_name bt_act = enq *)
      apply (rule bt_act_props(2))                   (* 11: op_val bt_act = bt_val *)
      by (simp add: l1_def new_L_struct)             (* 12: new_L definition *)

    (* 6. conclusion *)
    thus "((xo, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, bt_val). Distance L bt_val)"
      unfolding new_L_def[symmetric]
      by simp
  qed

next
  (* Subgoal4: happens_before b_act o1 H Branch (Case 4) *)
  (* logical: bt_act b_act *)
  show "\<And>L H bt_val x xa xb xc xd xe xf xg xh xi xj y xk ya xl xm xn.
       \<not> \<not> should_modify L H bt_val \<Longrightarrow>
       x = Distance L bt_val \<Longrightarrow>
       xa = find_last_SA L \<Longrightarrow>
       xb = take (nat (xa + 1)) L \<Longrightarrow>
       xc = drop (nat (xa + 1)) L \<Longrightarrow>
       xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc) \<Longrightarrow>
       xe = xc ! xd \<Longrightarrow>
       xf = take xd xc \<Longrightarrow>
       xg = drop (xd + 1) xc \<Longrightarrow>
       xh = last xf \<Longrightarrow>
       op_name xh \<noteq> enq \<Longrightarrow>
       xi = the (find_last_enq xf) \<Longrightarrow>
       (xj, y) = xi \<Longrightarrow>
       (xk, ya) = y \<Longrightarrow>
       xl = hd ya \<Longrightarrow>
       xm = last ya \<Longrightarrow>
       \<not> happens_before xl xe H \<Longrightarrow>
       happens_before xk xl H \<Longrightarrow>
       xn = xb @ xj @ [xe] @ [xk] @ ya @ xg \<Longrightarrow> ((xn, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, bt_val). Distance L bt_val)"
  proof -
    (* Step 1. *)
    fix L H bt_val x xa xb xc xd xe xf xg xh xi xj y xk ya xl xm xn
    assume prems:
      "\<not> \<not> should_modify L H bt_val"
      "x = Distance L bt_val"
      "xa = find_last_SA L"
      "xb = take (nat (xa + 1)) L"
      "xc = drop (nat (xa + 1)) L"
      "xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc)"
      "xe = xc ! xd"
      "xf = take xd xc"
      "xg = drop (xd + 1) xc"
      "xh = last xf"
      "op_name xh \<noteq> enq"
      "xi = the (find_last_enq xf)"
      "(xj, y) = xi"
      "(xk, ya) = y"
      "xl = hd ya"
      "xm = last ya"
      "\<not> happens_before xl xe H"
      "happens_before xk xl H"
      "xn = xb @ xj @ [xe] @ [xk] @ ya @ xg"

    (* should_modify extract *)
    from prems(1) have should_mod: "should_modify L H bt_val" by simp
    from should_mod have di_L: "data_independent L" 
      unfolding should_modify_def by simp

    (* Auxiliary lemma. *)
    define last_sa_pos where "last_sa_pos = xa"
    define l1 where "l1 = xb"
    define remaining where "remaining = xc"
    define bt_idx where "bt_idx = xd"
    define bt_act where "bt_act = xe"
    define l2 where "l2 = xf"
    define l3 where "l3 = xg"
    define l21 where "l21 = xj"
    define b_act where "b_act = xk"
    define l22 where "l22 = ya"
    define new_L where "new_L = xn"

    (* Step 2. *)
    
    (* Proof step. *)
    have bt_in_remaining: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
      using should_mod unfolding should_modify_def Let_def remaining_def last_sa_pos_def
      using option.simps(4) prems(3,5) by fastforce
    
    then have bt_idx_some: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      unfolding bt_idx_def using option.collapse
      by (simp add: prems(6) remaining_def)

    (* Proof step. *)
    have bt_act_props: "op_name bt_act = enq" "op_val bt_act = bt_val"
      using find_unique_index_prop[OF bt_idx_some]
      unfolding bt_act_def 
      using bt_idx_def prems(7) remaining_def
      apply meson
      using \<open>bt_idx < length remaining \<and> op_name (remaining ! bt_idx) = enq \<and> op_val (remaining ! bt_idx) = bt_val\<close> bt_idx_def prems(7) remaining_def by auto 

    (* combineProof L = l1 @ l2 @ [bt_act] @ l3 *)
    have L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
    proof -
      (* : L = l1 @ remaining *)
      have step1: "L = l1 @ remaining"
        unfolding l1_def remaining_def using append_take_drop_id
        by (simp add: prems(4,5))
      
      (* : remaining = l2 @ [bt_act] @ l3 *)
      have step2: "remaining = l2 @ [bt_act] @ l3"
      proof -
        have "bt_idx < length remaining"
          using find_unique_index_prop[OF bt_idx_some] by simp
        then show ?thesis
          unfolding l2_def l3_def bt_act_def
          using append_take_drop_id Cons_nth_drop_Suc
          by (metis Suc_eq_plus1 append_Cons append_self_conv2 bt_idx_def prems(7,8,9) remaining_def) 
      qed
      
      (* Comment. *)
      from step1 step2 show ?thesis by simp
    qed

    (* Step 3.2. *)
    
    (* l2 enq (should_modify execution path) *)
    have find_last_enq_not_none: "find_last_enq l2 \<noteq> None"
      using should_mod unfolding should_modify_def Let_def 
      l2_def[symmetric] remaining_def[symmetric] bt_idx_def[symmetric]
      last_sa_pos_def[symmetric] l1_def[symmetric]
      using prems(6) 
      by (smt (z3) l2_def option.case_eq_if prems(10,11,3,5,8)) 

    then have find_last_enq_eq: "find_last_enq l2 = Some (l21, b_act, l22)"
      using prems(12-14) unfolding l2_def l21_def b_act_def l22_def
      using option.collapse by fastforce

    (* Proof step. *)
    have b_act_enq: "op_name b_act = enq"
      using find_last_enq_props[OF find_last_enq_eq] by simp

    (* Step 4. *)
    (* new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3 *)
    (* : premise xn = xb @ xj @ [xe] @ [xk] @ ya @ xg *)
    (* corresponding: l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3 *)
    have new_L_struct: "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"
      unfolding new_L_def prems(19)
      unfolding l1_def l21_def bt_act_def b_act_def l22_def l3_def
      by simp

    (* Case 4.4. *)
    have "Distance new_L bt_val < Distance L bt_val"
      apply (rule moving_bt_act_before_b_act_case4)
      apply (rule di_L)                              (* 1: data_independent L *)
      apply (simp add: L_decomp find_last_enq_props(1)[OF find_last_enq_eq]) (* 2: L = l1 @ l21 @ [b_act] @ l22 @ [bt_act] @ l3 *)
      apply (rule b_act_enq)                         (* 3: op_name b_act = enq *)
      apply (rule bt_act_props(1))                   (* 4: op_name bt_act = enq *)
      apply (rule bt_act_props(2))
      apply (simp add: new_L_struct)
      by (simp add: l1_def prems(3,4))   


    (* 5. conclusion *)
    thus "((xn, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, bt_val). Distance L bt_val)"
      unfolding new_L_def[symmetric]
      by simp
  qed

next
  (* Case 5.1.5. *)
  show "\<And>L H bt_val x xa xb xc xd xe xf xg xh xi xj y xk ya xl xm xn xo.
       \<not> \<not> should_modify L H bt_val \<Longrightarrow>
       x = Distance L bt_val \<Longrightarrow>
       xa = find_last_SA L \<Longrightarrow>
       xb = take (nat (xa + 1)) L \<Longrightarrow>
       xc = drop (nat (xa + 1)) L \<Longrightarrow>
       xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc) \<Longrightarrow>
       xe = xc ! xd \<Longrightarrow>
       xf = take xd xc \<Longrightarrow>
       xg = drop (xd + 1) xc \<Longrightarrow>
       xh = last xf \<Longrightarrow>
       op_name xh \<noteq> enq \<Longrightarrow>
       xi = the (find_last_enq xf) \<Longrightarrow>
       (xj, y) = xi \<Longrightarrow>
       (xk, ya) = y \<Longrightarrow>
       xl = hd ya \<Longrightarrow>
       xm = last ya \<Longrightarrow>
       \<not> happens_before xl xe H \<Longrightarrow>
       \<not> happens_before xk xl H \<Longrightarrow>
       \<not> happens_before xk xl H \<Longrightarrow>
       xn = tl ya \<Longrightarrow> xo = xb @ xj @ [xl] @ [xk] @ xn @ [xe] @ xg \<Longrightarrow> ((xo, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, v). Distance L v)"
  proof -
    (* Step 1. *)
    fix L H bt_val x xa xb xc xd xe xf xg xh xi xj y xk ya xl xm xn xo
    assume prems: 
      "\<not> \<not> should_modify L H bt_val"
      "x = Distance L bt_val" 
      "xa = find_last_SA L"
      "xb = take (nat (xa + 1)) L"
      "xc = drop (nat (xa + 1)) L"
      "xd = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) xc)"
      "xe = xc ! xd"
      "xf = take xd xc"
      "xg = drop (xd + 1) xc"
      "xh = last xf"
      "op_name xh \<noteq> enq"
      "xi = the (find_last_enq xf)"
      "(xj, y) = xi"
      "(xk, ya) = y"
      "xl = hd ya"
      "xm = last ya"
      "\<not> happens_before xl xe H"
      "\<not> happens_before xk xl H"
      "\<not> happens_before xk xl H"
      "xn = tl ya"
      "xo = xb @ xj @ [xl] @ [xk] @ xn @ [xe] @ xg"

    (* should_modify extract *)
    from prems(1) have should_mod: "should_modify L H bt_val" by simp
    from should_mod have di_L: "data_independent L" 
      unfolding should_modify_def by simp

    (* Auxiliary lemma. *)
    define last_sa_pos where "last_sa_pos = xa"
    define l1 where "l1 = xb"
    define remaining where "remaining = xc"
    define bt_idx where "bt_idx = xd"
    define bt_act where "bt_act = xe"
    define l2 where "l2 = xf"
    define l3 where "l3 = xg"
    define l21 where "l21 = xj"
    define b_act where "b_act = xk"
    define l22 where "l22 = ya"
    define o1 where "o1 = xl"
    define new_l22 where "new_l22 = xn"
    define new_L where "new_L = xo"

    (* Step 2. *)
    have bt_in_remaining: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      thus False
        using should_mod prems(3) prems(5)
        unfolding should_modify_def Let_def remaining_def
        by (auto split: option.splits)
    qed    
    
    then have bt_idx_some: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      unfolding bt_idx_def using option.collapse
      by (simp add: prems(6) remaining_def)

    (* Proof step. *)
    have bt_act_props: "op_name bt_act = enq" "op_val bt_act = bt_val"
      using find_unique_index_prop[OF bt_idx_some]
      unfolding bt_act_def 
      using bt_idx_def prems(7) remaining_def
      apply meson
      using \<open>bt_idx < length remaining \<and> op_name (remaining ! bt_idx) = enq \<and> op_val (remaining ! bt_idx) = bt_val\<close> bt_idx_def prems(7) remaining_def by auto 

    (* combineProof L = l1 @ l2 @ [bt_act] @ l3 *)
    have L_decomp: "L = l1 @ l2 @ [bt_act] @ l3"
    proof -
      (* : L = l1 @ remaining *)
      have step1: "L = l1 @ remaining"
        unfolding l1_def remaining_def using append_take_drop_id
        by (simp add: prems(4,5))
      
      (* : remaining = l2 @ [bt_act] @ l3 *)
      have step2: "remaining = l2 @ [bt_act] @ l3"
      proof -
        have "bt_idx < length remaining"
          using find_unique_index_prop[OF bt_idx_some] by simp
        then show ?thesis
          unfolding l2_def l3_def bt_act_def
          using append_take_drop_id Cons_nth_drop_Suc
          by (metis Suc_eq_plus1 append_Cons append_self_conv2 bt_idx_def prems(7,8,9) remaining_def) 
      qed
      
      (* Comment. *)
      from step1 step2 show ?thesis by simp
    qed

    (* Step 3.2. *)
    
    (* l2 enq (should_modify execution path) *)
    have find_last_enq_not_none: "find_last_enq l2 \<noteq> None"
      using should_mod unfolding should_modify_def Let_def 
      l2_def[symmetric] remaining_def[symmetric] bt_idx_def[symmetric]
      last_sa_pos_def[symmetric] l1_def[symmetric]
      using prems(6) 
      by (smt (z3) l2_def option.case_eq_if prems(10,11,3,5,8)) 

    then have find_last_enq_eq: "find_last_enq l2 = Some (l21, b_act, l22)"
      using prems(12-14) unfolding l2_def l21_def b_act_def l22_def
      using option.collapse by fastforce

    (* Proof step. *)
    have b_act_enq: "op_name b_act = enq"
      using find_last_enq_props[OF find_last_enq_eq] by simp

    (* Step 4.22.1. *)

    (* l22 non-empty *)
    have l22_not_empty: "l22 \<noteq> []"
      using should_mod unfolding should_modify_def Let_def
      unfolding l2_def[symmetric] remaining_def[symmetric] bt_idx_def[symmetric]
      unfolding last_sa_pos_def[symmetric] l1_def[symmetric]
      using prems(6) find_last_enq_eq
      using b_act_enq find_last_enq_props(1) l2_def prems(10,11)
      by fastforce

    (* o1 l22 (hd) *)
    have o1_is_hd: "o1 = hd l22"
      using prems(15) unfolding o1_def l22_def by simp

    (* new_l22 l22 (tl) *)
    have new_l22_is_tl: "new_l22 = tl l22"
      using prems(18) unfolding new_l22_def l22_def
      by (simp add: prems(20)) 

    (* Case 1.5. *)
    have o1_is_deq: "op_name o1 = deq"
    proof -
      have all_deq: "\<forall>a \<in> set l22. op_name a = deq"
        using find_last_enq_eq l22_are_all_deq l22_not_empty by auto
      have "o1 \<in> set l22"
        using o1_is_hd l22_not_empty by (simp add: list.set_sel(1))
      with all_deq show ?thesis by auto
    qed

    (* Step 5. *)
    (* new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3 *)
    have new_L_struct: "new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3"
      unfolding new_L_def prems(19)
      unfolding l1_def l21_def o1_def b_act_def new_l22_def bt_act_def l3_def
      by (simp add: prems(21))

    (* Case 3.1.3. *)
    have "Distance new_L bt_val < Distance L bt_val"
      apply (rule moving_b_act_forward_over_o1_case3)
      apply (rule di_L)                              (* 1: data_independent L *)
      apply (rule L_decomp)                          (* 2: L = ... *)
      
      (* 3: l1 = take ... *)
      unfolding l1_def last_sa_pos_def 
      apply (rule prems(4)) 
      
      (* 4: last_sa_pos = find_last_SA L *)
      unfolding last_sa_pos_def 
      apply (rule prems(3))
      
      apply (rule find_last_enq_eq)                  (* 5: find_last_enq l2 = Some ... *)
      apply (rule l22_not_empty)                     (* 6: l22 \<noteq> [] *)
      apply (rule o1_is_hd)                          (* 7: o1 = hd l22 *)
      apply (rule new_l22_is_tl)                     (* 8: new_l22 = tl l22 *)
      apply (rule b_act_enq)                         (* 9: op_name b_act = enq *)
      apply (rule bt_act_props(1))                   (* 10: op_name bt_act = enq *)
      apply (rule bt_act_props(2))                   (* 11: op_val bt_act = bt_val *)
      by (simp add: l1_def new_L_struct)             (* 12: new_L definition *)

    (* 6. conclusion *)
    thus "((xo, H, bt_val), L, H, bt_val) \<in> measure (\<lambda>(L, H, bt_val). Distance L bt_val)"
      unfolding new_L_def[symmetric]
      by simp
  qed
qed



end
