theory PureLib
  imports 
    Main 
    "HOL-Library.Multiset"
    Model
begin

(* ========================================================== *)
(* Basic list lemmas used throughout the proof development    *)
(* ========================================================== *)

(* ========== Append and indexing facts ========== *)
(* Appending to the right does not affect the first n elements when n stays within the prefix. *)
lemma take_append_le [simp]: 
  "n \<le> length xs \<Longrightarrow> take n (xs @ ys) = take n xs"
  by simp

(* The appended singleton is stored exactly at the old length position. *)
lemma nth_append_length [simp]: 
  "(xs @ [x]) ! (length xs) = x"
  by simp

(* Appending one element increases the length by one. *)
lemma length_append_singleton [simp]: 
  "length (xs @ [x]) = Suc (length xs)"
  by simp

(* Standard case split for reading from an appended list. *)
lemma nth_append_cases:
  "k < length xs \<Longrightarrow> (xs @ ys) ! k = xs ! k"
  "k \<ge> length xs \<Longrightarrow> (xs @ ys) ! k = ys ! (k - length xs)"
  by (auto simp: nth_append)

(* Filtering count is unchanged when the appended element does not satisfy the predicate. *)
lemma count_invariant [simp]:
  assumes "\<not> P x"
  shows "length (filter P (xs @ [x])) = length (filter P xs)"
  using assms by auto

(* Filtering count increases by one when the appended element satisfies the predicate. *)
lemma count_increment [simp]:
  assumes "P x"
  shows "length (filter P (xs @ [x])) = length (filter P xs) + 1"
  using assms by auto

(* Uniform counting formula for appending one element. *)
lemma length_filter_append_singleton:
  "length (filter P (xs @ [x])) =
     length (filter P xs) + (if P x then 1 else 0)"
  by simp


(* ========================================================== *)
(* Multiset characterization of data independence             *)
(* ========================================================== *)

(* ========== Counting via filtered multisets ========== *)
(* Convert index-based counting over a list into multiset counting. *)
lemma card_indices_eq_count_mset:
  "card {i. i < length L \<and> P (L ! i)} = size {# x \<in># mset L. P x #}"
proof -
  have "{i. i < length L \<and> P (L ! i)} = {i. i < length L \<and> L ! i \<in> {x. P x}}"
    by blast
  also have "card ... = size (filter (\<lambda>x. P x) L)"
    by (metis calculation length_filter_conv_card)
  also have "... = size {# x \<in># mset L. P x #}"
    by (metis mset_filter size_mset)
  finally show ?thesis .
qed

(* Data independence depends only on the multiset of operations, not on their concrete order. *)
lemma data_independent_cong:
  assumes "mset L1 = mset L2"
  shows "data_independent L1 \<longleftrightarrow> data_independent L2"
proof -
  
  
  
  have di1_eq: "data_independent L1 \<longleftrightarrow> 
        (\<forall>v. size {# x \<in># mset L1. op_name x = enq \<and> op_val x = v #} \<le> 1) \<and>
        (\<forall>v. size {# x \<in># mset L1. op_name x = deq \<and> op_val x = v #} \<le> 1)"
    unfolding data_independent_def
    apply (subst card_indices_eq_count_mset)+ 
    by simp

  
  have di2_eq: "data_independent L2 \<longleftrightarrow> 
        (\<forall>v. size {# x \<in># mset L2. op_name x = enq \<and> op_val x = v #} \<le> 1) \<and>
        (\<forall>v. size {# x \<in># mset L2. op_name x = deq \<and> op_val x = v #} \<le> 1)"
    unfolding data_independent_def
    apply (subst card_indices_eq_count_mset)+ 
    by simp

  
  show ?thesis
    using di1_eq di2_eq assms by simp
qed


(* ========================================================== *)
(* Uniqueness of enqueue/dequeue indices under data independence *)
(* ========================================================== *)

(* ========== Singleton-index arguments ========== *)
(* Under data independence, a witnessed enqueue value occurs at exactly one index. *)
lemma card_enq_set_eq_1:
  assumes "data_independent L"
  assumes "op_name (L ! i) = enq" "op_val (L ! i) = v" "i < length L"
  shows "card {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = v} = 1"
proof -
  let ?S = "{j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = v}"
  
  
  have "i \<in> ?S" using assms(2-4) by simp
  hence "?S \<noteq> {}" by blast
  
  
  have "finite ?S"
  proof -
    have "?S \<subseteq> {..<length L}" by auto
    thus ?thesis using finite_subset by blast
  qed
  
  
  have "card ?S \<le> 1"
    using assms(1) unfolding data_independent_def by blast
  
  
  show "card ?S = 1"
  proof (rule ccontr)
    assume "card ?S \<noteq> 1"
    with `card ?S \<le> 1` have "card ?S = 0" by linarith
    
    with `finite ?S` have "?S = {}" by simp
    with `?S \<noteq> {}` show False by blast
  qed
qed

(* Recover the unique enqueue position of a given value. *)
lemma unique_enq_index:
  assumes "data_independent L"
  assumes "op_name (L ! i) = enq" "op_val (L ! i) = v" "i < length L"
  shows "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L = [i]"
proof -
  let ?S = "{j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = v}"
  
  
  from card_enq_set_eq_1[OF assms] have "card ?S = 1" .
  
  
  have "i \<in> ?S" using assms(2-4) by auto
  
  
  have "?S = {i}"
  proof
    show "?S \<subseteq> {i}"
    proof
      fix j
      assume "j \<in> ?S"
      then have "j < length L" "op_name (L ! j) = enq" "op_val (L ! j) = v" by auto
      
      
      from `card ?S = 1` obtain k where "?S = {k}"
        using card_1_singletonE by auto
      
      
      from `i \<in> ?S` and `?S = {k}` have "i = k" by simp
      from `j \<in> ?S` and `?S = {k}` have "j = k" by simp
      
      
      from `j = k` and `i = k` show "j \<in> {i}" by simp
    qed
    
    show "{i} \<subseteq> ?S"
      using `i \<in> ?S` by auto
  qed
  
  
  show ?thesis
    unfolding find_indices_def
  proof -
    
    have "set [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = enq \<and> op_val a = v) (L ! i)] = ?S"
      by auto
    with `?S = {i}` have "set [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = enq \<and> op_val a = v) (L ! i)] = {i}"
      by simp
    
    
    have "sorted [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = enq \<and> op_val a = v) (L ! i)]"
      by (simp add: sorted_wrt_filter)
    have "distinct [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = enq \<and> op_val a = v) (L ! i)]"
      by simp
    
    
    from `set [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = enq \<and> op_val a = v) (L ! i)] = {i}`
         `distinct [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = enq \<and> op_val a = v) (L ! i)]`
    show "[i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = enq \<and> op_val a = v) (L ! i)] = [i]"
      by (simp add: \<open>sorted (filter (\<lambda>i. op_name (L ! i) = enq \<and> op_val (L ! i) = v) [0..<length L])\<close> sorted_distinct_set_unique)
  qed
qed

(* Recover the unique dequeue position of a given value. *)
lemma unique_deq_index:
  assumes "data_independent L"
  assumes "op_name (L ! i) = deq" "op_val (L ! i) = v" "i < length L"
  shows "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = v) L = [i]"
proof -
  let ?S = "{j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = v}"
  
  from assms(1) have di_deq: "\<forall>v. card {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = v} \<le> 1"
    by (simp add: data_independent_def)
  
  
  have "i \<in> ?S" using assms(2-4) by auto
  then have "?S \<noteq> {}" by auto
  have "finite ?S" by auto
  from di_deq have "card ?S \<le> 1" by auto
  
  have "card ?S = 1"
  proof (rule ccontr)
    assume "card ?S \<noteq> 1"
    with `card ?S \<le> 1` and `?S \<noteq> {}` have "card ?S = 0"
      by linarith    
    with `?S \<noteq> {}` show False
      by force
  qed
  
  
  have "?S = {i}"
  proof
    show "?S \<subseteq> {i}"
    proof
      fix j
      assume "j \<in> ?S"
      
      from `card ?S = 1` obtain x where "?S = {x}"
        using card_1_singletonE by auto
      with `i \<in> ?S` and `j \<in> ?S` show "j \<in> {i}"
        by auto
    qed
    show "{i} \<subseteq> ?S" using `i \<in> ?S` by auto
  qed
  
  
  show ?thesis
    unfolding find_indices_def
  proof -
    
    have "set [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = deq \<and> op_val a = v) (L ! i)] = ?S"
      by auto
    with `?S = {i}` have "set [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = deq \<and> op_val a = v) (L ! i)] = {i}"
      by simp
    
    
    have "sorted [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = deq \<and> op_val a = v) (L ! i)]"
      by (simp add: sorted_wrt_filter)
    have "distinct [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = deq \<and> op_val a = v) (L ! i)]"
      by simp
    
    
    from `set [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = deq \<and> op_val a = v) (L ! i)] = {i}`
         `distinct [i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = deq \<and> op_val a = v) (L ! i)]`
    show "[i\<leftarrow>[0..<length L]. (\<lambda>a. op_name a = deq \<and> op_val a = v) (L ! i)] = [i]"
      using \<open>sorted (filter (\<lambda>i. op_name (L ! i) = deq \<and> op_val (L ! i) = v) [0..<length L])\<close> sorted_list_of_set.idem_if_sorted_distinct by fastforce
  qed
qed


(* ========== Reading back witnesses from find_unique_index ========== *)

(* ========== Reading witnesses returned by find_unique_index ========== *)
(* Read back the witness index from find_unique_index for dequeue operations. *)
lemma find_unique_index_deq:
  assumes "data_independent L"
  assumes "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x_val) L = Some k"
  shows "op_name (L ! k) = deq \<and> op_val (L ! k) = x_val \<and> k < length L"
proof -
  
  from assms(2) have 
    "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = x_val) L = Some k"
    by simp
  
  
  have "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x_val) L = [k]"
  proof -
    from assms(2) have 
      "let indices = find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x_val) L in
       indices \<noteq> [] \<and> hd indices = k"
      by (smt (verit, best) find_unique_index_def not_None_eq option.inject)
    
    then obtain indices where 
      indices_def: "indices = find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x_val) L"
      and "indices \<noteq> []" 
      and "hd indices = k"
      by meson
    
    
    have "distinct indices"
      unfolding indices_def find_indices_def
      by auto
    
    
    from assms(1) have card_le1: 
      "card {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val} \<le> 1"
      by (simp add: data_independent_def)
    
    
    have "set indices = {k}"
    proof
      show "set indices \<subseteq> {k}"
      proof
        fix m
        assume "m \<in> set indices"
        then have "m < length L \<and> op_name (L ! m) = deq \<and> op_val (L ! m) = x_val"
          unfolding indices_def find_indices_def by auto
        
        
        from `hd indices = k` and `indices \<noteq> []` have "k \<in> set indices"
          by auto
        then have "k < length L \<and> op_name (L ! k) = deq \<and> op_val (L ! k) = x_val"
          unfolding indices_def find_indices_def by auto
        
        
        have "{j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val} = {k}"
        proof
          show "{j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val} \<subseteq> {k}"
          proof
            fix j
            assume "j \<in> {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val}"
            then have "j < length L" "op_name (L ! j) = deq" "op_val (L ! j) = x_val" by auto
            
            
            from card_le1 have 
              "card {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val} \<le> 1"
              by simp
            
            from `k \<in> set indices` have 
              "k \<in> {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val}"
              unfolding indices_def find_indices_def by auto
            
            show "j \<in> {k}"
            proof (rule ccontr)
              assume "j \<notin> {k}"
              then have "j \<noteq> k" by simp
              
              
              have "{j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val} \<supseteq> {j, k}"
                using `j \<in> {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val}`
                      `k \<in> {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val}`
                by auto
              
              then have "card {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val} \<ge> 2"
                using \<open>hd indices = k\<close> \<open>j \<noteq> k\<close> assms(1) indices_def unique_deq_index by fastforce
              
              
              with card_le1 show False by linarith
            qed
          qed
        next
          show "{k} \<subseteq> {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val}"
            using `k \<in> set indices` unfolding indices_def find_indices_def by auto
        qed
        
        
        from `m \<in> set indices` have 
          "m \<in> {j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val}"
          unfolding indices_def find_indices_def by auto
        with `{j. j < length L \<and> op_name (L ! j) = deq \<and> op_val (L ! j) = x_val} = {k}`
        show "m \<in> {k}" by simp
      qed
      
      show "{k} \<subseteq> set indices"
        using `hd indices = k` `indices \<noteq> []`
        by (metis \<open>set indices \<subseteq> {k}\<close> set_empty subset_singleton_iff) 
    qed
    
    
    have "indices = [k]"
    proof -
      from `set indices = {k}` and `distinct indices` 
      have "length indices = 1"
        by (metis One_nat_def Suc_lessI \<open>indices \<noteq> []\<close> length_greater_0_conv nth_eq_iff_index_eq nth_mem singleton_iff zero_neq_one)
      
      with `indices \<noteq> []` and `hd indices = k`
      show ?thesis
        by (metis One_nat_def Zero_not_Suc hd_Cons_tl length_Cons old.nat.inject)
    qed
    
    then show ?thesis
      by (simp add: indices_def)
  qed
  
  
  have "k \<in> set (find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x_val) L)"
    using `find_indices (\<lambda>a. op_name a = deq \<and> op_val a = x_val) L = [k]`
    by simp
  
  
  then have "k < length L \<and> (\<lambda>a. op_name a = deq \<and> op_val a = x_val) (L ! k)"
    unfolding find_indices_def by auto
  
  then show ?thesis
    by auto
qed

(* Read back the witness index from find_unique_index for enqueue operations. *)
lemma find_unique_index_enq:
  assumes "data_independent L"
  assumes "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L = Some k"
  shows "op_name (L ! k) = enq \<and> op_val (L ! k) = x_val \<and> k < length L"
proof -
  
  from assms(2) have 
    "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L = Some k"
    by simp
  
  
  have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L = [k]"
  proof -
    from assms(2) have 
      "let indices = find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L in
       indices \<noteq> [] \<and> hd indices = k"
      by (smt (verit) find_unique_index_def option.distinct(1) option.inject)
    
    then obtain indices where 
      indices_def: "indices = find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L"
      and "indices \<noteq> []" 
      and "hd indices = k"
      by meson
    
    
    have "distinct indices"
      unfolding indices_def find_indices_def
      by simp
    
    
    from assms(1) have card_le1: 
      "card {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val} \<le> 1"
      by (simp add: data_independent_def)
    
    
    have "set indices = {k}"
    proof
      show "set indices \<subseteq> {k}"
      proof
        fix m
        assume "m \<in> set indices"
        then have "m < length L \<and> op_name (L ! m) = enq \<and> op_val (L ! m) = x_val"
          unfolding indices_def find_indices_def by auto
        
        
        from `hd indices = k` and `indices \<noteq> []` have "k \<in> set indices"
          by auto
        then have "k < length L \<and> op_name (L ! k) = enq \<and> op_val (L ! k) = x_val"
          unfolding indices_def find_indices_def by auto
        
        
        have "{j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val} = {k}"
        proof
          show "{j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val} \<subseteq> {k}"
          proof
            fix j
            assume "j \<in> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val}"
            then have "j < length L" "op_name (L ! j) = enq" "op_val (L ! j) = x_val" by auto
            
            
            from card_le1 have 
              "card {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val} \<le> 1"
              by simp
            
            from `k \<in> set indices` have 
              "k \<in> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val}"
              unfolding indices_def find_indices_def by auto
            
            show "j \<in> {k}"
            proof (rule ccontr)
              assume "j \<notin> {k}"
              then have "j \<noteq> k" by simp
              
              
              have "{j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val} \<supseteq> {j, k}"
                using `j \<in> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val}`
                      `k \<in> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val}`
                by auto
              
              then have "card {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val} \<ge> 2"
                using \<open>hd indices = k\<close> \<open>j \<noteq> k\<close> assms(1) indices_def
                  unique_enq_index by auto
              
              
              with card_le1 show False by linarith
            qed
          qed
        next
          show "{k} \<subseteq> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val}"
            using `k \<in> set indices` unfolding indices_def find_indices_def by auto
        qed
        
        
        from `m \<in> set indices` have 
          "m \<in> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val}"
          unfolding indices_def find_indices_def by auto
        with `{j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = x_val} = {k}`
        show "m \<in> {k}" by simp
      qed
      
      show "{k} \<subseteq> set indices"
        using `hd indices = k` `indices \<noteq> []`
        by fastforce 
    qed
    
    
    have "indices = [k]"
    proof -
      from `set indices = {k}` and `distinct indices` 
      have "length indices = 1"
        by (metis One_nat_def \<open>hd indices = k\<close> \<open>indices \<noteq> []\<close> distinct.simps(2) empty_iff insert_iff last_in_set last_tl length_Cons list.exhaust_sel list.size(3))
      
      with `indices \<noteq> []` and `hd indices = k`
      show ?thesis
        by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    qed
    
    then show ?thesis
      by (simp add: indices_def)
  qed
  
  
  have "k \<in> set (find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L)"
    using `find_indices (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L = [k]`
    by simp
  
  
  then have "k < length L \<and> (\<lambda>a. op_name a = enq \<and> op_val a = x_val) (L ! k)"
    unfolding find_indices_def by auto
  
  then show ?thesis
    by auto
qed


(* ========== Uniqueness of values induced by data independence ========== *)

(* ========== Uniqueness of values induced by unique indices ========== *)
(* Two enqueue actions at the same index must carry the same value. *)
lemma unique_enq_value:
  assumes "data_independent L"
  assumes "i < length L" "j < length L" "i \<noteq> j"
  assumes "op_name (L ! i) = enq" "op_name (L ! j) = enq"
  shows "op_val (L ! i) \<noteq> op_val (L ! j)"
proof (rule ccontr)
  assume "\<not> op_val (L ! i) \<noteq> op_val (L ! j)"
  then have same_val: "op_val (L ! i) = op_val (L ! j)" by simp
  
  
  let ?v = "op_val (L ! i)"
  let ?S = "{k. k < length L \<and> op_name (L ! k) = enq \<and> op_val (L ! k) = ?v}"
  
  
  have i_in_S: "i \<in> ?S"
    using assms(2,5) same_val by auto
  have j_in_S: "j \<in> ?S"  
    using assms(3,6) same_val by auto
  
  
  have "i \<noteq> j" by (rule assms(4))
  then have "card ?S \<ge> 2"
  proof -
    have "{i, j} \<subseteq> ?S" using i_in_S j_in_S by auto
    moreover have "i \<noteq> j" by fact
    moreover have "finite ?S" by auto
    ultimately show ?thesis
      by (metis (lifting) card_2_iff card_mono)
  qed
  
  
  from assms(1) have "\<forall>v. card {k. k < length L \<and> op_name (L ! k) = enq \<and> op_val (L ! k) = v} \<le> 1"
    by (simp add: data_independent_def)
  
  
  then have "card ?S \<le> 1" by auto
  
  
  with `card ?S \<ge> 2` show False by linarith
qed

(* Two dequeue actions at the same index must carry the same value. *)
lemma unique_deq_value:
  assumes "data_independent L"
  assumes "i < length L" "j < length L" "i \<noteq> j"
  assumes "op_name (L ! i) = deq" "op_name (L ! j) = deq"
  shows "op_val (L ! i) \<noteq> op_val (L ! j)"
proof (rule ccontr)
  assume "\<not> op_val (L ! i) \<noteq> op_val (L ! j)"
  then have same_val: "op_val (L ! i) = op_val (L ! j)" by simp
  
  let ?v = "op_val (L ! i)"
  let ?S = "{k. k < length L \<and> op_name (L ! k) = deq \<and> op_val (L ! k) = ?v}"
  
  have i_in_S: "i \<in> ?S" using assms(2,5) same_val by auto
  have j_in_S: "j \<in> ?S" using assms(3,6) same_val by auto
  
  have "i \<noteq> j" by (rule assms(4))
  then have "card ?S \<ge> 2"
  proof -
    have "{i, j} \<subseteq> ?S" using i_in_S j_in_S by auto
    moreover have "i \<noteq> j" by fact
    moreover have "finite ?S" by auto
    ultimately show ?thesis
      by (metis (lifting) card_2_iff card_mono)
  qed
  
  from assms(1) have "\<forall>v. card {k. k < length L \<and> op_name (L ! k) = deq \<and> op_val (L ! k) = v} \<le> 1"
    by (simp add: data_independent_def)
  
  then have "card ?S \<le> 1" by auto
  with `card ?S \<ge> 2` show False by linarith
qed


(* ========================================================== *)
(* Preservation of data independence under fresh extensions   *)
(* ========================================================== *)

(* ========== Appending a fresh enqueue/dequeue action ========== *)

(* ========================================================== *)
(* Preservation of data independence under fresh extensions   *)
(* ========================================================== *)

(* ========== Appending fresh enqueue/dequeue operations ========== *)
(* Appending a fresh enqueue value preserves data independence. *)
lemma data_independent_append_enq_fresh:
  fixes L :: "OpRec list" and v p sn  
  assumes DI: "data_independent L"
  assumes FRESH: "\<forall>i < length L. op_name (L ! i) = enq \<longrightarrow> op_val (L ! i) \<noteq> v"
  shows "data_independent (L @ [mk_op enq v p sn])" 
  (* Step 3: transfer data independence through the multiset characterization. *)
  unfolding data_independent_def
proof (intro conjI allI)
  
  fix u
  let ?L' = "L @ [mk_op enq v p sn]"
  let ?S_enq = "{i. i < length ?L' \<and> op_name (?L' ! i) = enq \<and> op_val (?L' ! i) = u}"
  let ?S_orig = "{i. i < length L \<and> op_name (L ! i) = enq \<and> op_val (L ! i) = u}"

  show "card ?S_enq \<le> 1"
  proof (cases "u = v")
    case True
    
    have "?S_enq = {length L}" 
    proof (rule set_eqI)
      fix i
      show "i \<in> ?S_enq \<longleftrightarrow> i \<in> {length L}"
        using True FRESH 
        by (auto simp: nth_append mk_op_def op_name_def op_val_def less_Suc_eq)
    qed
    thus ?thesis by simp
  next
    case False
    
    have "?S_enq = ?S_orig"
    proof (rule set_eqI)
      fix i
      show "i \<in> ?S_enq \<longleftrightarrow> i \<in> ?S_orig"
        using False 
        by (auto simp: nth_append mk_op_def op_name_def op_val_def less_Suc_eq)
    qed
    moreover have "card ?S_orig \<le> 1" 
      using DI unfolding data_independent_def by blast
    ultimately show ?thesis by simp
  qed

next
  
  fix u
  let ?L' = "L @ [mk_op enq v p sn]"
  let ?S_deq = "{i. i < length ?L' \<and> op_name (?L' ! i) = deq \<and> op_val (?L' ! i) = u}"
  let ?S_orig = "{i. i < length L \<and> op_name (L ! i) = deq \<and> op_val (L ! i) = u}"

  
  have "?S_deq = ?S_orig"
  proof (rule set_eqI)
    fix i
    show "i \<in> ?S_deq \<longleftrightarrow> i \<in> ?S_orig"
      by (auto simp: nth_append mk_op_def op_name_def op_val_def less_Suc_eq)
  qed
  moreover have "card ?S_orig \<le> 1" 
    using DI unfolding data_independent_def by blast
  ultimately show "card ?S_deq \<le> 1" by simp
qed

(* Appending a fresh dequeue value preserves data independence. *)
lemma data_independent_append_deq_fresh:
  fixes L :: "OpRec list" and v p sn  
  assumes DI: "data_independent L"
  assumes FRESH: "\<forall>i < length L. op_name (L ! i) = deq \<longrightarrow> op_val (L ! i) \<noteq> v"
  shows "data_independent (L @ [mk_op deq v p sn])" 
  (* Step 3: transfer data independence through the multiset characterization. *)
  unfolding data_independent_def
proof (intro conjI allI)
  
  fix u
  let ?L' = "L @ [mk_op deq v p sn]"
  let ?S_enq = "{i. i < length ?L' \<and> op_name (?L' ! i) = enq \<and> op_val (?L' ! i) = u}"
  let ?S_orig = "{i. i < length L \<and> op_name (L ! i) = enq \<and> op_val (L ! i) = u}"

  
  have "?S_enq = ?S_orig"
  proof (rule set_eqI)
    fix i
    show "i \<in> ?S_enq \<longleftrightarrow> i \<in> ?S_orig"
      by (auto simp: nth_append mk_op_def op_name_def op_val_def less_Suc_eq)
  qed
  moreover have "card ?S_orig \<le> 1" 
    using DI unfolding data_independent_def by blast
  ultimately show "card ?S_enq \<le> 1" by simp

next
  
  fix u
  let ?L' = "L @ [mk_op deq v p sn]"
  let ?S_deq = "{i. i < length ?L' \<and> op_name (?L' ! i) = deq \<and> op_val (?L' ! i) = u}"
  let ?S_orig = "{i. i < length L \<and> op_name (L ! i) = deq \<and> op_val (L ! i) = u}"

  show "card ?S_deq \<le> 1"
  proof (cases "u = v")
    case True
    
    have "?S_deq = {length L}" 
    proof (rule set_eqI)
      fix i
      show "i \<in> ?S_deq \<longleftrightarrow> i \<in> {length L}"
        using True FRESH 
        by (auto simp: nth_append mk_op_def op_name_def op_val_def less_Suc_eq)
    qed
    thus ?thesis by simp
  next
    case False
    
    have "?S_deq = ?S_orig"
    proof (rule set_eqI)
      fix i
      show "i \<in> ?S_deq \<longleftrightarrow> i \<in> ?S_orig"
        using False 
        by (auto simp: nth_append mk_op_def op_name_def op_val_def less_Suc_eq)
    qed
    moreover have "card ?S_orig \<le> 1" 
      using DI unfolding data_independent_def by blast
    ultimately show ?thesis by simp
  qed
qed


(* ========== Immediate corollaries ========== *)

(* ========== Index/value correspondences under data independence ========== *)
(* Equal enqueue values imply equal enqueue indices under data independence. *)
lemma same_enq_value_same_index:
  assumes "data_independent L"
  assumes "i < length L" "j < length L"
  assumes "op_name (L ! i) = enq" "op_name (L ! j) = enq"
  assumes "op_val (L ! i) = op_val (L ! j)"
  shows "i = j"
proof (rule ccontr)
  assume "i \<noteq> j"
  with assms(1-5) have "op_val (L ! i) \<noteq> op_val (L ! j)"
    using unique_enq_value by auto
  with assms(6) show False by simp
qed

(* Distinct enqueue indices induce distinct enqueue values. *)
lemma enq_values_distinct:
  assumes "data_independent L"
  shows "distinct (map (\<lambda>i. op_val (L ! i)) 
                      (filter (\<lambda>i. op_name (L ! i) = enq) [0..<length L]))"
proof -
  let ?enq_indices = "filter (\<lambda>i. op_name (L ! i) = enq) [0..<length L]"
  
  
  have "inj_on (\<lambda>i. op_val (L ! i)) (set ?enq_indices)"
  proof (rule inj_onI)
    fix i j
    assume i_in: "i \<in> set ?enq_indices"
       and j_in: "j \<in> set ?enq_indices"
       and val_eq: "op_val (L ! i) = op_val (L ! j)"
    
    
    from i_in have enq_i: "op_name (L ! i) = enq" by auto
    from j_in have enq_j: "op_name (L ! j) = enq" by auto
    
    
    from i_in have i_bound: "i < length L" by auto
    from j_in have j_bound: "j < length L" by auto
    
    
    from same_enq_value_same_index[OF assms i_bound j_bound enq_i enq_j val_eq]
    show "i = j" .
  qed
  
  
  have "distinct ?enq_indices"
    by auto
  
  
  show ?thesis
    by (metis \<open>distinct (filter (\<lambda>i. op_name (L ! i) = enq) [0..<length L])\<close>
        \<open>inj_on (\<lambda>i. op_val (L ! i)) (set (filter (\<lambda>i. op_name (L ! i) = enq) [0..<length L]))\<close> distinct_map)
qed

(* Distinct dequeue indices induce distinct dequeue values. *)
lemma deq_values_distinct:
  assumes "data_independent L"
  shows "distinct (map (\<lambda>i. op_val (L ! i)) 
                      (filter (\<lambda>i. op_name (L ! i) = deq) [0..<length L]))"
proof -
  let ?deq_indices = "filter (\<lambda>i. op_name (L ! i) = deq) [0..<length L]"
  
  
  have "inj_on (\<lambda>i. op_val (L ! i)) (set ?deq_indices)"
  proof (rule inj_onI)
    fix i j
    assume i_in: "i \<in> set ?deq_indices"
       and j_in: "j \<in> set ?deq_indices"
       and val_eq: "op_val (L ! i) = op_val (L ! j)"
    
    
    from i_in have deq_i: "op_name (L ! i) = deq" by auto
    from j_in have deq_j: "op_name (L ! j) = deq" by auto
    
    
    from i_in have i_bound: "i < length L" by auto
    from j_in have j_bound: "j < length L" by auto
    
    
    
    have "i = j"
    proof (rule ccontr)
      assume "i \<noteq> j"
      with unique_deq_value[OF assms i_bound j_bound `i \<noteq> j` deq_i deq_j]
      have "op_val (L ! i) \<noteq> op_val (L ! j)" by simp
      with val_eq show False by simp
    qed
    thus "i = j" .
  qed
  
  
  have "distinct ?deq_indices"
    using distinct_filter distinct_upt by blast
  
  
  show ?thesis
    using \<open>distinct (filter (\<lambda>i. op_name (L ! i) = deq) [0..<length L])\<close>
      \<open>inj_on (\<lambda>i. op_val (L ! i)) (set (filter (\<lambda>i. op_name (L ! i) = deq) [0..<length L]))\<close> distinct_map
    by blast
qed


(* ========================================================== *)
(* Preservation of data independence under list rearrangements *)
(* ========================================================== *)

(* ========== Swap and multiset-preserving rewrites ========== *)

(* ========================================================== *)
(* Data independence preservation for modify_lin-style updates *)
(* ========================================================== *)
(* The local swap/reordering step used in modify_lin preserves data independence. *)
lemma new_L_is_data_independent_after_swap:
  assumes "data_independent L"
  assumes "i < length L" "j < length L" "i < j"
  assumes "op_name (L ! i) = enq" "op_name (L ! j) = enq"
  assumes "op_val (L ! i) = x_val" "op_val (L ! j) = bt_val"
  assumes "new_L = (take i L) @ [L ! j] @ (take (j - i - 1) (drop (i + 1) L)) @ [L ! i] @ (drop (j + 1) L)"
  shows "data_independent new_L"
proof -
  
  have mset_eq: "mset new_L = mset L"
  proof -
    
    have L_decomp: "L = take i L @ [L ! i] @ take (j - i - 1) (drop (i + 1) L) @ [L ! j] @ drop (j + 1) L"
    proof -
      have "L = take i L @ drop i L" by simp
      also have "drop i L = [L ! i] @ drop (i + 1) L"
        using assms(2)
        using Cons_nth_drop_Suc by force 
      also have "drop (i + 1) L = take (j - i - 1) (drop (i + 1) L) @ drop (j - i - 1) (drop (i + 1) L)"
        by (metis append_take_drop_id)
      also have "drop (j - i - 1) (drop (i + 1) L) = drop j L"
        using assms(4) by auto
      also have "drop j L = [L ! j] @ drop (j + 1) L"
        using assms(3)
        using Cons_nth_drop_Suc by fastforce 
      finally show ?thesis by simp
    qed
    
     
    have new_L_decomp: "new_L = take i L @ [L ! j] @ take (j - i - 1) (drop (i + 1) L) @ [L ! i] @ drop (j + 1) L"
      by (simp add: assms(9))
  
    
    let ?A = "mset (take i L)"
    let ?B = "mset [L ! i]"
    let ?C = "mset (take (j - i - 1) (drop (i + 1) L))"
    let ?D = "mset [L ! j]"
    let ?E = "mset (drop (j + 1) L)"
  
    
    have mset_L: "mset L = ?A + ?B + ?C + ?D + ?E"
      by (metis (no_types, lifting) L_decomp add.assoc mset_append)
  
    
    have mset_new_L: "mset new_L = ?A + ?D + ?C + ?B + ?E"
      by (simp add: new_L_decomp)
  
    
    show ?thesis
      by (simp add: mset_L mset_new_L add.commute add.left_commute)
  qed
  
  
  have len_eq: "length new_L = length L"
    using mset_eq mset_eq_length by auto
  
  
  show ?thesis
    unfolding data_independent_def
  proof (intro conjI allI)
    fix v
    
    show "card {k. k < length new_L \<and> op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = v} \<le> 1"
    proof -
      
      
      let ?P = "\<lambda>a. op_name a = enq \<and> op_val a = v"
      
      
      let ?count_L = "card {k. k < length L \<and> ?P (L ! k)}"
      
      
      let ?count_new = "card {k. k < length new_L \<and> ?P (new_L ! k)}"
      
      
      have count_eq: "?count_new = ?count_L"
      proof -
        
        let ?filtered_L = "filter ?P L"
        let ?filtered_new_L = "filter ?P new_L"
        
        
        have "mset ?filtered_new_L = mset ?filtered_L"
          using mset_eq by simp
        
        
        have "length ?filtered_new_L = length ?filtered_L"
          using \<open>mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L) = mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L)\<close> mset_eq_length by blast
        
        
        have "length ?filtered_L = ?count_L"
          by (simp add: length_filter_conv_card)
        
        have "length ?filtered_new_L = ?count_new"
          by (simp add: length_filter_conv_card)
        
        then show ?thesis
          using \<open>length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L) = length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L)\<close> 
                \<open>length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L) = card {k. k < length L \<and> op_name (L ! k) = enq \<and> op_val (L ! k) = v}\<close> 
                \<open>length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L) = card {k. k < length new_L \<and> op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = v}\<close> 
          by presburger
      qed
      
      
      from assms(1) have "?count_L \<le> 1"
        by (simp add: data_independent_def)
      
      then show ?thesis by (simp add: count_eq)
    qed
    
    
    fix v
    show "card {k. k < length new_L \<and> op_name (new_L ! k) = deq \<and> op_val (new_L ! k) = v} \<le> 1"
    proof -
      
      let ?P = "\<lambda>a. op_name a = deq \<and> op_val a = v"
      
      
      let ?count_L = "card {k. k < length L \<and> ?P (L ! k)}"
      
      
      let ?count_new = "card {k. k < length new_L \<and> ?P (new_L ! k)}"
      
      
      have count_eq: "?count_new = ?count_L"
      proof -
        
        let ?filtered_L = "filter ?P L"
        let ?filtered_new_L = "filter ?P new_L"
        
        
        have "mset ?filtered_new_L = mset ?filtered_L"
          by (simp add: mset_eq)
        
        
        have "length ?filtered_new_L = length ?filtered_L"
          by (metis (lifting) \<open>mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L) = mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L)\<close> size_mset)
        
        
        have "length ?filtered_L = ?count_L"
          by (simp add: length_filter_conv_card)
        
        have "length ?filtered_new_L = ?count_new"
          by (simp add: length_filter_conv_card)
        
        then show ?thesis
          using \<open>length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L) = length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L)\<close> 
                \<open>length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L) = card {k. k < length L \<and> op_name (L ! k) = deq \<and> op_val (L ! k) = v}\<close> 
                \<open>length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L) = card {k. k < length new_L \<and> op_name (new_L ! k) = deq \<and> op_val (new_L ! k) = v}\<close> 
          by presburger
      qed
      
      
      from assms(1) have "?count_L \<le> 1"
        by (simp add: data_independent_def)
      
      then show ?thesis by (simp add: count_eq)
    qed
  qed
qed

(* The reconstructed linearization remains data independent after the full update. *)
lemma new_L_is_data_independent:
  assumes "data_independent L"
  assumes "mset new_L = mset L"
  shows "data_independent new_L"
proof -
  
  have len_eq: "length new_L = length L"
    using assms(2) by (metis size_mset)

  
  show ?thesis
    unfolding data_independent_def
  proof (intro conjI allI)
    fix v
    
    show "card {k. k < length new_L \<and> op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = v} \<le> 1"
    proof -
      
      
      let ?P = "\<lambda>a. op_name a = enq \<and> op_val a = v"
      
      
      let ?count_L = "card {k. k < length L \<and> ?P (L ! k)}"
      
      
      let ?count_new = "card {k. k < length new_L \<and> ?P (new_L ! k)}"
      
      
      have count_eq: "?count_new = ?count_L"
      proof -
        
        let ?filtered_L = "filter ?P L"
        let ?filtered_new_L = "filter ?P new_L"
        
        
        have "mset ?filtered_new_L = mset ?filtered_L"
          using assms(2) by simp
        
        
        have "length ?filtered_new_L = length ?filtered_L"
          using assms(2) mset_eq_length
          using \<open>mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L) = mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L)\<close> by blast 
        
        
        have "length ?filtered_L = ?count_L"
          by (simp add: length_filter_conv_card)
        
        have "length ?filtered_new_L = ?count_new"
          by (simp add: length_filter_conv_card)
        
        then show ?thesis
          using \<open>length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L) = length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L)\<close> 
                \<open>length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L) = card {k. k < length L \<and> op_name (L ! k) = enq \<and> op_val (L ! k) = v}\<close> 
                \<open>length (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L) = card {k. k < length new_L \<and> op_name (new_L ! k) = enq \<and> op_val (new_L ! k) = v}\<close> 
          by presburger
      qed
      
      
      from assms(1) have "?count_L \<le> 1"
        by (simp add: data_independent_def)
      
      then show ?thesis by (simp add: count_eq)
    qed
    
  next
    fix v
    
    show "card {k. k < length new_L \<and> op_name (new_L ! k) = deq \<and> op_val (new_L ! k) = v} \<le> 1"
    proof -
      
      let ?P = "\<lambda>a. op_name a = deq \<and> op_val a = v"
      
      
      let ?count_L = "card {k. k < length L \<and> ?P (L ! k)}"
      
      
      let ?count_new = "card {k. k < length new_L \<and> ?P (new_L ! k)}"
      
      
      have count_eq: "?count_new = ?count_L"
      proof -
        
        let ?filtered_L = "filter ?P L"
        let ?filtered_new_L = "filter ?P new_L"
        
        
        have "mset ?filtered_new_L = mset ?filtered_L"
          by (simp add: assms(2))
        
        
        have "length ?filtered_new_L = length ?filtered_L"
          by (metis (lifting) \<open>mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L) = mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L)\<close> size_mset)
        
        
        have "length ?filtered_L = ?count_L"
          by (simp add: length_filter_conv_card)
        
        have "length ?filtered_new_L = ?count_new"
          by (simp add: length_filter_conv_card)
        
        then show ?thesis
          using \<open>length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L) = length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L)\<close> 
                \<open>length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L) = card {k. k < length L \<and> op_name (L ! k) = deq \<and> op_val (L ! k) = v}\<close> 
                \<open>length (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L) = card {k. k < length new_L \<and> op_name (new_L ! k) = deq \<and> op_val (new_L ! k) = v}\<close> 
          by presburger
      qed
      
      
      from assms(1) have "?count_L \<le> 1"
        by (simp add: data_independent_def)
      
      then show ?thesis by (simp add: count_eq)
    qed
  qed
qed


(* ========================================================== *)
(* SA decomposition lemmas for modify_lin-style arguments     *)
(* ========================================================== *)

(* ========== Structure after the last enqueue ========== *)

(* ========================================================== *)
(* Structural lemmas for SetA-based list decompositions        *)
(* ========================================================== *)
(* The suffix block l22 consists entirely of dequeue operations. *)
lemma l22_are_all_deq:
  assumes "find_last_enq l2 = Some (l21, b_act, l22)"
  assumes "l22 \<noteq> []"
  shows "\<forall>a \<in> set l22. op_name a = deq"
proof
  fix a
  assume a_in_l22: "a \<in> set l22"
  
  
  from assms(1) have find_last_enq_expanded:
    "let enq_indices = find_indices (\<lambda>a. op_name a = enq) l2 in
     enq_indices \<noteq> [] \<and>
     l21 = take (last enq_indices) l2 \<and>
     b_act = l2 ! (last enq_indices) \<and>
     l22 = drop (last enq_indices + 1) l2"
    unfolding find_last_enq_def
    by (smt (verit, best) Pair_inject option.discI option.inject) 
  
  
  obtain enq_indices where
    enq_indices_def: "enq_indices = find_indices (\<lambda>a. op_name a = enq) l2" and
    enq_indices_nonempty: "enq_indices \<noteq> []" and
    l21_equals: "l21 = take (last enq_indices) l2" and
    b_act_equals: "b_act = l2 ! (last enq_indices)" and
    l22_equals: "l22 = drop (last enq_indices + 1) l2"
    by (metis find_last_enq_expanded)
  
  
  have b_act_is_enq: "op_name b_act = enq"
  proof -
    from enq_indices_nonempty have "last enq_indices \<in> set enq_indices"
      by simp
    then have "last enq_indices \<in> set (find_indices (\<lambda>a. op_name a = enq) l2)"
      by (simp add: enq_indices_def)
    then have "last enq_indices < length l2" 
      and "op_name (l2 ! (last enq_indices)) = enq"
      unfolding find_indices_def by auto
    with b_act_equals show ?thesis by simp
  qed
  
  
  show "op_name a = deq"
  proof (rule ccontr)
    assume "\<not> op_name a = deq"
    then have a_is_enq: "op_name a = enq" 
      by (metis mname.exhaust)
    
    
    from a_in_l22 and l22_equals have "a \<in> set (drop (last enq_indices + 1) l2)"
      by simp
    
    
    then obtain k where
      k_gt: "k \<ge> last enq_indices + 1" and
      k_lt: "k < length l2" and
      l2_at_k: "l2 ! k = a"
      by (smt (verit, best) add.commute assms(2) drop_drop drop_eq_Nil2 in_set_conv_nth l22_equals leD
          le_add2 nat_le_linear nat_less_le nth_drop)
    
    
    from a_is_enq and k_lt and l2_at_k have 
      "k \<in> set (find_indices (\<lambda>a. op_name a = enq) l2)"
      unfolding find_indices_def by auto
    
    then have k_in_enq_indices: "k \<in> set enq_indices"
      by (simp add: enq_indices_def)
    
    
    
    have sorted_enq_indices: "sorted enq_indices"
      unfolding enq_indices_def find_indices_def
      using sorted_upt sorted_wrt_filter by blast 
    
    
    have "enq_indices \<noteq> []" by fact
    
    
    have last_ge: "\<forall>x \<in> set enq_indices. x \<le> last enq_indices"
    proof -
      from sorted_enq_indices and `enq_indices \<noteq> []`
      have "\<forall>i<length enq_indices. enq_indices ! i \<le> last enq_indices"
        by (simp add: last_conv_nth sorted_nth_mono)

      then show ?thesis
        by (metis in_set_conv_nth)
    qed
    
    
    from last_ge and k_in_enq_indices have "k \<le> last enq_indices"
      by simp
    
    
    with k_gt show False
      by linarith
  qed
qed

(* The prefix l1 already contains every completed SetA element from the original linearization. *)
lemma l1_contains_all_SA_in_L:
  assumes "data_independent L"
  assumes "L = l1 @ l2"
  assumes "l2 \<noteq> []"
  assumes "l1 = take (nat (last_sa_pos + 1)) L"
  assumes "last_sa_pos = find_last_SA L"
  shows "\<forall>i. i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq \<longrightarrow> 
    \<not> in_SA (op_val (L ! i)) L"
proof (intro allI impI)
  fix i
  assume prems: "i \<ge> length l1 \<and> i < length L \<and> op_name (L ! i) = enq"
  then have i_ge: "i \<ge> length l1" 
    and i_lt: "i < length L" 
    and enq_at_i: "op_name (L ! i) = enq"
    by auto
  
  show "\<not> in_SA (op_val (L ! i)) L"
  proof (rule ccontr)
    assume "\<not> \<not> in_SA (op_val (L ! i)) L"
    then have v_in_SA: "in_SA (op_val (L ! i)) L" by simp
    
    
    from v_in_SA obtain enq_idx where
      enq_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = op_val (L ! i)) L = Some enq_idx"
      unfolding in_SA_def by (auto split: option.splits)
    
    
    from assms(1) enq_idx_def have 
      enq_props: "op_name (L ! enq_idx) = enq \<and> op_val (L ! enq_idx) = op_val (L ! i) \<and> enq_idx < length L"
      using find_unique_index_enq by blast
    
    
    
    
    
    
    have enq_idx_in_SA: "enq_idx \<in> {j. j < length L \<and> 
      op_name (L ! j) = enq \<and> in_SA (op_val (L ! j)) L}"
      using enq_props v_in_SA by auto
    
    
    
    
    have find_last_SA_spec: "find_last_SA L = (
      let sa_indices = find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L in
      if sa_indices = [] then -1 else int (last sa_indices))"
      unfolding find_last_SA_def by simp
    
    
    have sa_indices_nonempty: "find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L \<noteq> []"
    proof -
      
      from enq_idx_in_SA have 
        enq_idx_props: "enq_idx < length L" 
        "op_name (L ! enq_idx) = enq" 
        "in_SA (op_val (L ! enq_idx)) L"
        by auto
      
      
      have "find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L = 
            [i \<leftarrow> [0..<length L]. (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) (L ! i)]"
        unfolding find_indices_def by simp
      
      
      have "enq_idx \<in> set [i \<leftarrow> [0..<length L]. (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) (L ! i)]"
      proof -
        
        from enq_idx_props(1) have "enq_idx \<in> set [0..<length L]"
          by (simp add: in_set_conv_nth)
        
        
        from enq_idx_props(2,3) have 
          "(\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) (L ! enq_idx)"
          by simp
        
        
        show ?thesis
          using `enq_idx \<in> set [0..<length L]` 
                `(\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) (L ! enq_idx)`
          by auto
      qed
      
      
      then show ?thesis 
        by (metis \<open>find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L = filter (\<lambda>i. op_name (L ! i) = enq \<and> 
        in_SA (op_val (L ! i)) L) [0..<length L]\<close> length_pos_if_in_set less_nat_zero_code
          list.size(3)) 

    qed
    
    
    from find_last_SA_spec sa_indices_nonempty have
      find_last_SA_eq: "find_last_SA L = int (last (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L))"
      by simp
    
    
    have sa_indices_sorted: "sorted (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L)"
      unfolding find_indices_def
      by (simp add: sorted_wrt_filter)
    
    have sa_indices_distinct: "distinct (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L)"
      unfolding find_indices_def
      by simp
    
    from enq_idx_in_SA have enq_idx_in_sa_indices: 
      "enq_idx \<in> set (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L)"
      unfolding find_indices_def by auto
    
    with sa_indices_sorted sa_indices_distinct sa_indices_nonempty have
      enq_idx_le_last: "enq_idx \<le> last (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L)"
      by (metis (no_types, lifting) last.simps last_appendR last_in_set list.distinct(1) order_le_less sorted_append sorted_simps(2) split_list_last)
    
    
    from assms(5) have last_sa_pos_eq: "last_sa_pos = find_last_SA L" by simp
    
    
    have "enq_idx \<le> nat last_sa_pos"
    proof -
      from find_last_SA_eq have 
        "last_sa_pos = int (last (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L))"
        by (simp add: last_sa_pos_eq)
      
      
      have "last (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L) \<ge> 0"
        using sa_indices_nonempty by auto
      
      from enq_idx_le_last and this show ?thesis
        by (metis \<open>last_sa_pos = int (last (find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L))\<close> 
                  nat_int)
    qed
    
    
    from assms(4) have "length l1 = (nat (last_sa_pos + 1))"
          using length_take min.absorb2
          by (metis i_ge i_lt min.absorb3 verit_comp_simplify1(3))
    
    have "enq_idx < length l1"
      using `enq_idx \<le> nat last_sa_pos` `length l1 = (nat (last_sa_pos + 1))`
      using find_last_SA_eq last_sa_pos_eq by linarith
    
    
    
    from assms(1) have unique_enq: "\<forall>v. card {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = v} \<le> 1"
      by (simp add: data_independent_def)
    
    
    let ?v = "op_val (L ! i)"
    have enq_idx_in_set: "enq_idx \<in> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = ?v}"
      using enq_props by auto
    
    
    have i_in_set: "i \<in> {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = ?v}"
      using i_lt enq_at_i by auto
    
    
    from unique_enq have "card {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = ?v} \<le> 1"
      by auto
    
    
    have i_eq_enq_idx: "i = enq_idx"
    proof -
      from enq_idx_in_set and i_in_set and `card {j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = ?v} \<le> 1`
      have "{j. j < length L \<and> op_name (L ! j) = enq \<and> op_val (L ! j) = ?v} = {enq_idx}"
        using assms(1) same_enq_value_same_index by auto
      
      with i_in_set show ?thesis by auto
    qed
    
    
    with `enq_idx < length l1` and i_ge show False
      by linarith
  qed
qed

(* The transformation preserves the SetA classification. *)
lemma L_and_new_L_have_same_SA:
  assumes "data_independent L"
  assumes "L = l1 @ l2"                    
  assumes "new_L = l1 @ l3"
  assumes "l2 \<noteq> []" 
  assumes "mset L = mset new_L"       
  assumes "l1 = take (nat (last_sa_pos + 1)) L"             
  assumes "last_sa_pos = find_last_SA L"                  
 shows "\<forall>v. in_SA v new_L \<longleftrightarrow> in_SA v L"
proof (intro allI iffI)
  fix v
  show "in_SA v L \<Longrightarrow> in_SA v new_L"
  proof -
    assume "in_SA v L"
    then obtain enq_idx deq_idx where
      enq_idx_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some enq_idx" and
      deq_idx_L: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) L = Some deq_idx"
      unfolding in_SA_def by (auto split: option.splits)
    
    
    from assms(1) enq_idx_L have 
      enq_props: "op_name (L ! enq_idx) = enq \<and> op_val (L ! enq_idx) = v \<and> enq_idx < length L"
      using find_unique_index_enq by blast
    
    from assms(1) deq_idx_L have 
      deq_props: "op_name (L ! deq_idx) = deq \<and> op_val (L ! deq_idx) = v \<and> deq_idx < length L"
      using find_unique_index_deq by blast

    have same_mset: "mset new_L = mset L"
      using assms(5)
      by simp
    
    
    have di_new_L: "data_independent new_L"
      using assms(1,5) same_mset new_L_is_data_independent by blast
    
    
    
    have enq_exists_new: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = None"
        by simp
      
      
      
      have "mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L) = 
            mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L)"
        using assms(5) by simp
      
      
      from enq_props have "filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L \<noteq> []"
        by (metis (mono_tags, lifting) filter_empty_conv in_set_conv_nth)
      
      
      then have "filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L \<noteq> []"
        using \<open>mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L) = mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L)\<close> mset_zero_iff by fastforce
      
      
      then have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L \<noteq> []"
        unfolding find_indices_def
        using filter_empty_conv in_set_conv_nth find_unique_index_def option.distinct(1) di_new_L filter_eq_Cons_iff find_indices_def in_set_conv_decomp unique_enq_index
        by (smt (verit, ccfv_threshold))
      
      
      then show False
        using \<open>find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = None\<close> find_unique_index_def
        by auto 
    qed
    
    
    have deq_exists_new: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L = None"
        by simp
      
      
      
      have "mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L) = 
            mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L)"
        using assms(5) by simp
      
      
      from deq_props have "filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L \<noteq> []"
        by (metis (mono_tags, lifting) filter_empty_conv in_set_conv_nth)
      
      
      then have "filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L \<noteq> []"
        using \<open>mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L) = mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L)\<close> mset_zero_iff_right by fastforce
      
      
      then have "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L \<noteq> []"
      proof -
        
        from `filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L \<noteq> []`
        obtain a where "a \<in> set (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L)"
          using hd_in_set by blast
        
        
        then have "a \<in> set new_L" and "op_name a = deq" and "op_val a = v"
          by auto
        
        
        then obtain i where "i < length new_L" and "new_L ! i = a"
          by (auto simp: in_set_conv_nth)
        
        
        with `op_name a = deq` and `op_val a = v`
        have "op_name (new_L ! i) = deq \<and> op_val (new_L ! i) = v"
          by simp
        
        
        then have "i \<in> set (find_indices (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L)"
          unfolding find_indices_def
          using `i < length new_L` by auto
        
        
        then show ?thesis by auto
      qed
      
      
      then show False
        using \<open>\<not> find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L \<noteq> None\<close> find_unique_index_def by auto
    qed
    
    
    show "in_SA v new_L"
      using deq_exists_new enq_exists_new in_SA_def by auto
  qed
  
  show "in_SA v new_L \<Longrightarrow> in_SA v L"
  proof -
    assume "in_SA v new_L"
    then obtain enq_idx deq_idx where
      enq_idx_new: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L = Some enq_idx" and
      deq_idx_new: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L = Some deq_idx"
      unfolding in_SA_def by (auto split: option.splits)
    
    
    have di_new_L: "data_independent new_L"
      using assms(1,5) new_L_is_data_independent
      by auto
    
    from di_new_L enq_idx_new have 
      enq_props_new: "op_name (new_L ! enq_idx) = enq \<and> op_val (new_L ! enq_idx) = v \<and> enq_idx < length new_L"
      using find_unique_index_enq by blast
    
    from di_new_L deq_idx_new have 
      deq_props_new: "op_name (new_L ! deq_idx) = deq \<and> op_val (new_L ! deq_idx) = v \<and> deq_idx < length new_L"
      using find_unique_index_deq by blast
    
    
    
    have enq_exists_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = None"
        by simp
      
      
      
      have "mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L) = 
            mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L)"
        using assms(5) by simp
      
      
      from enq_props_new have "filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L \<noteq> []"
        by (metis (mono_tags, lifting) filter_empty_conv in_set_conv_nth)
      
      
      then have "filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L \<noteq> []"
        using \<open>mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L) = mset (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) new_L)\<close> mset_eq_setD set_empty
        by (metis (lifting)) 
      
      
      then have "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L \<noteq> []"
      proof -
        
        from `filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L \<noteq> []`
        obtain a where "a \<in> set (filter (\<lambda>a. op_name a = enq \<and> op_val a = v) L)"
          by (meson hd_in_set)
        
        
        then have "a \<in> set L" and "op_name a = enq" and "op_val a = v"
          by auto
        
        
        then obtain i where "i < length L" and "L ! i = a"
          by (auto simp: in_set_conv_nth)
        
        
        with `op_name a = enq` and `op_val a = v`
        have "op_name (L ! i) = enq \<and> op_val (L ! i) = v"
          by simp
        
        
        then have "i \<in> set (find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L)"
          unfolding find_indices_def
          using `i < length L` by auto
        
        
        then show ?thesis by auto
      qed
      
      
      then show False
        using \<open>\<not> find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L \<noteq> None\<close> find_unique_index_def by auto
    qed
    
    
    have deq_exists_L: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) L \<noteq> None"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) L = None"
        by simp
      
      
      
      have "mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L) = 
            mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L)"
        using assms(5) by simp
      
      
      from deq_props_new have "filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L \<noteq> []"
        by (metis (mono_tags, lifting) filter_empty_conv in_set_conv_nth)
      
      
      then have "filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L \<noteq> []"
        using \<open>mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) L) = mset (filter (\<lambda>a. op_name a = deq \<and> op_val a = v) new_L)\<close> mset_eq_setD set_empty
        by (metis (lifting)) 
      
      
      then have "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = v) L \<noteq> []"
        unfolding find_indices_def
        using filter_empty_conv in_set_conv_nth enq_exists_L find_unique_index_def assms(1) filter_eq_Cons_iff find_indices_def in_set_conv_decomp unique_deq_index
        by (smt (verit, ccfv_threshold))
      
      
      then show False
        using \<open>\<not> find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) L \<noteq> None\<close> find_unique_index_def by auto
    qed
    
    
    show "in_SA v L"
      using deq_exists_L enq_exists_L in_SA_def by auto
  qed
qed


(* ========== Stability properties of the SA partition ========== *)
(* Elements in the trailing suffix are outside SetA. *)
lemma l3_elements_not_in_SA:
  assumes "data_independent L"
  assumes "L = l1 @ l2 @ [bt_act] @ l3"
  assumes "l1 = take (nat (last_sa_pos + 1)) L"
  assumes "last_sa_pos = find_last_SA L"
  assumes "v \<in> set (map op_val (filter (\<lambda>a. op_name a = enq) l3))"
  shows "\<not> in_SA v L"
proof -
  
  from assms(5) obtain a where 
    a_def: "a \<in> set (filter (\<lambda>a. op_name a = enq) l3)" "op_val a = v"
    by auto
  
  from a_def(1) have a_in_l3: "a \<in> set l3" and a_enq: "op_name a = enq"
    by auto
  
  
  obtain i where 
    i_def: "i < length l3" "l3 ! i = a"
    using a_in_l3 by (auto simp: in_set_conv_nth)
  
  
  let ?abs_pos = "length (l1 @ l2 @ [bt_act]) + i"
  
  
  have abs_pos_in_bounds: "?abs_pos < length L"
    by (simp add: assms(2) i_def(1))
  
  
  have "L ! ?abs_pos = a"
    by (simp add: assms(2) i_def(2) nth_append)
  
  
  have "?abs_pos \<ge> length l1"
    by (simp add: assms(2))
  
  from l1_contains_all_SA_in_L[OF assms(1) assms(2) _ assms(3) assms(4)] 
       abs_pos_in_bounds a_enq `?abs_pos \<ge> length l1`
  show ?thesis
    using a_def(2)
    using \<open>L ! (length (l1 @ l2 @ [bt_act]) + i) = a\<close> by blast 
qed

(* The prefix ending at the last SetA enqueue is stable across the transformation. *)
lemma find_last_SA_stable_prefix:
  assumes "length L1 = length L2"
  assumes "take n L1 = take n L2"
  assumes "\<forall>i \<in> {n..<length L1}. \<not> (op_name (L1 ! i) = enq \<and> in_SA (op_val (L1 ! i)) L1)"
  assumes "\<forall>i \<in> {n..<length L2}. \<not> (op_name (L2 ! i) = enq \<and> in_SA (op_val (L2 ! i)) L2)"
  assumes "\<forall>v. in_SA v L1 \<longleftrightarrow> in_SA v L2" 
  shows "find_last_SA L1 = find_last_SA L2"
proof -
  
  let ?P1 = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L1"
  let ?P2 = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L2"

  
  have indices_eq: "find_indices ?P1 L1 = find_indices ?P2 L2"
  proof -
    
    have "find_indices ?P1 L1 = find_indices ?P2 L1"
      using assms(5) by simp
    also have "... = find_indices ?P2 L2"
      unfolding find_indices_def
    proof (rule filter_cong) 
      
      show "[0..<length L1] = [0..<length L2]" 
        using assms(1) by simp
    next
      
      fix i assume "i \<in> set [0..<length L2]"
      then have i_valid: "i < length L1" 
        using assms(1) by simp
      
      show "?P2 (L1 ! i) \<longleftrightarrow> ?P2 (L2 ! i)"
      proof (cases "i < n")
        case True 
        
        have "L1 ! i = L2 ! i" 
          using assms(2) True i_valid by (metis nth_take)
        then show ?thesis by simp
      next
        case False 
        
        have i_ge: "i \<ge> n" using False by simp
        
        
        have "\<not> ?P1 (L1 ! i)"
          using assms(3) i_valid i_ge by auto
        then have lhs_false: "\<not> ?P2 (L1 ! i)" 
          using assms(5) by simp
          
        
        have rhs_false: "\<not> ?P2 (L2 ! i)"
          using assms(4) i_valid i_ge assms(1) by auto
          
        show ?thesis using lhs_false rhs_false
          by auto 
      qed
    qed
    finally show ?thesis .
  qed

  
  
  show ?thesis
    unfolding find_last_SA_def
    using indices_eq by simp
qed


(* ========== Consequences of data independence for SetA witnesses ========== *)
(* Data independence yields uniqueness of dequeue occurrences directly. *)
lemma data_independent_implies_unique_deq:
  assumes "data_independent L"
  assumes "i < length L" "j < length L"
  assumes "op_name (L ! i) = deq" "op_val (L ! i) = v"
  assumes "op_name (L ! j) = deq" "op_val (L ! j) = v"
  shows "i = j"
proof -
  
  have deq_prop: "\<forall>v. card {k. k < length L \<and> op_name (L ! k) = deq \<and> op_val (L ! k) = v} \<le> 1"
    using assms(1) unfolding data_independent_def by simp
    
  
  let ?S = "{k. k < length L \<and> op_name (L ! k) = deq \<and> op_val (L ! k) = v}"
  
  
  have "i \<in> ?S" using assms(2,4,5) by simp
  have "j \<in> ?S" using assms(3,6,7) by simp
  
  
  have "card ?S \<le> 1" using deq_prop by simp
  
  
  show "i = j"
    using `i \<in> ?S` `j \<in> ?S` `card ?S \<le> 1`
    using assms(1) unique_deq_value by auto
qed

(* Membership in SetA can be transferred between equivalent linearizations. *)
lemma SetA_equivalent_in_SA:
  assumes "lI1_Op_Sets_Equivalence s" 
  assumes "lI2_Op_Cardinality s"
  shows "op_val x \<in> SetA s \<longleftrightarrow> in_SA (op_val x) (lin_seq s)"
proof
  let ?v = "op_val x"
  let ?L = "lin_seq s" 
  
  
  show "?v \<in> SetA s \<Longrightarrow> in_SA ?v ?L"
  proof -
    assume "?v \<in> SetA s"
    
    have "card (EnqIdxs s ?v) = 1" and "card (DeqIdxs s ?v) = 1"
      using assms(2) `?v \<in> SetA s` unfolding lI2_Op_Cardinality_def by auto
    
    
    have enq_exists: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = ?v) ?L \<noteq> None"
    proof -
      
      obtain k where k_def: "EnqIdxs s ?v = {k}"
        using `card (EnqIdxs s ?v) = 1`
        using card_1_singletonE by auto 
      
      
      have k_prop: "k < length ?L" 
               and k_is_enq: "op_name (?L ! k) = enq" 
               and k_val: "op_val (?L ! k) = ?v"
        using k_def unfolding EnqIdxs_def by auto

      
      have k_unique: "\<forall>j < length ?L. op_name (?L ! j) = enq \<and> op_val (?L ! j) = ?v \<longrightarrow> j = k"
        using k_def unfolding EnqIdxs_def by auto

      
      
      
      have "\<exists>!i. i < length ?L \<and> op_name (?L ! i) = enq \<and> op_val (?L ! i) = ?v"
        using k_prop k_is_enq k_val k_unique
        by blast

      
      
      have k_in_list: "k \<in> set (find_indices (\<lambda>a. op_name a = enq \<and> op_val a = ?v) ?L)"
        using k_prop k_is_enq k_val
        
        unfolding find_indices_def 
        by auto 

      
      have list_not_empty: "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = ?v) ?L \<noteq> []"
        using k_in_list by auto

      
      then show ?thesis
        
        
        unfolding find_unique_index_def Let_def 
        by auto 
    qed

    have deq_exists: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = ?v) ?L \<noteq> None"
    proof -
      
      obtain k where k_def: "DeqIdxs s ?v = {k}"
        using `card (DeqIdxs s ?v) = 1` using card_1_singletonE by auto
      
      
      have k_prop: "k < length ?L" 
               and k_is_deq: "op_name (?L ! k) = deq" 
               and k_val: "op_val (?L ! k) = ?v"
        using k_def unfolding DeqIdxs_def by auto

      
      
      have k_in_list: "k \<in> set (find_indices (\<lambda>a. op_name a = deq \<and> op_val a = ?v) ?L)"
        using k_prop k_is_deq k_val
        
        unfolding find_indices_def 
        by auto 

      
      have list_not_empty: "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = ?v) ?L \<noteq> []"
        using k_in_list by auto

      
      then show ?thesis
        
        unfolding find_unique_index_def Let_def 
        by auto 
    qed

    
    show "in_SA ?v ?L"
      unfolding in_SA_def
      using enq_exists deq_exists by (auto split: option.split)
  qed

next
  
  
  show "in_SA (op_val x) (lin_seq s) \<Longrightarrow> op_val x \<in> SetA s"
  proof -
    
    assume asm: "in_SA (op_val x) (lin_seq s)"
    
    
    let ?v = "op_val x"
    let ?L = "lin_seq s"
    
    
    
    
    have deq_exists: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = ?v) ?L \<noteq> None"
      using asm unfolding in_SA_def 
      by (auto split: option.splits if_splits)
      
    
    obtain deq_act where deq_in_L: "deq_act \<in> set ?L" 
      and is_deq: "op_name deq_act = deq" 
      and val_is_v: "op_val deq_act = ?v"
    proof -
      
      have indices_not_empty: "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = ?v) ?L \<noteq> []"
        using deq_exists unfolding find_unique_index_def Let_def by (auto split: if_splits)
      
      
      obtain idx where idx_in_list: "idx \<in> set (find_indices (\<lambda>a. op_name a = deq \<and> op_val a = ?v) ?L)"
        using indices_not_empty by (meson list.set_sel(1))
      
      
      
      have idx_valid: "idx < length ?L" 
                   and idx_prop_oper: "op_name (?L ! idx) = deq"
                   and idx_prop_val: "op_val (?L ! idx) = ?v"
        using idx_in_list 
        unfolding find_indices_def 
        by auto 
      
      
      let ?witness = "?L ! idx"
      
      
      have witness_in_L: "?witness \<in> set ?L" 
        using idx_valid by simp
        
      
      show ?thesis
        apply (rule that[of ?witness]) 
        using witness_in_L idx_prop_oper idx_prop_val by auto
    qed

    
    
    have "deq_act \<in> OPLin s" 
      using deq_in_L unfolding OPLin_def by simp
    
    
    have "deq_act \<in> OP_A_deq s"
    proof -
      
      have "OPLin s = OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
        using assms(1) unfolding lI1_Op_Sets_Equivalence_def by simp
      
      
      moreover have "\<forall>x \<in> OP_A_enq s. op_name x = enq" 
        unfolding OP_A_enq_def
        
        by (auto simp add: mk_op_def op_name_def)
        
      
      moreover have "\<forall>x \<in> OP_B_enq s. op_name x = enq" 
        unfolding OP_B_enq_def
        by (auto simp add: mk_op_def op_name_def)
      
      
      ultimately show ?thesis 
        using `deq_act \<in> OPLin s` is_deq
        by auto 
    qed

    
    
    show "?v \<in> SetA s"
      using `deq_act \<in> OP_A_deq s` val_is_v
      unfolding OP_A_deq_def
      
      by (auto simp add: op_val_def mk_op_def)
  qed
qed


(* ========================================================== *)
(* SetA/SetB auxiliary facts                                  *)
(* ========================================================== *)
(* Enqueues outside SetA correspond to still-active values. *)
lemma non_SA_enqs_are_active:
  assumes "lI1_Op_Sets_Equivalence s"
  assumes "lI2_Op_Cardinality s"
  shows "\<forall>x \<in> set (lin_seq s).
         op_name x = enq \<and> \<not> in_SA (op_val x) (lin_seq s) \<longrightarrow>
         x \<in> active_enqs s"
proof (intro ballI impI)
  
  fix x
  assume x_in_L: "x \<in> set (lin_seq s)"
  assume prem: "op_name x = enq \<and> \<not> in_SA (op_val x) (lin_seq s)"

  let ?v = "op_val x"
  let ?L = "lin_seq s"

  
  have "x \<in> OPLin s" using x_in_L unfolding OPLin_def by simp
  
  
  then have x_union: "x \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using assms(1) unfolding lI1_Op_Sets_Equivalence_def by simp

  
  have not_A_deq: "x \<notin> OP_A_deq s"
  proof
    assume "x \<in> OP_A_deq s"
    
    then have "op_name x = deq" unfolding OP_A_deq_def by blast
    then show False using prem by simp
  qed

  
  have not_A_enq: "x \<notin> OP_A_enq s"
  proof
    assume "x \<in> OP_A_enq s"
    
    then obtain p a sn where "x = mk_op enq a p sn" "a \<in> SetA s"
      unfolding OP_A_enq_def by blast
    then have val_is_a: "?v = a"
      unfolding op_val_def mk_op_def by simp
    then have "?v \<in> SetA s" using `a \<in> SetA s` by simp

    
    
    have "in_SA ?v ?L"
      using SetA_equivalent_in_SA[OF assms(1) assms(2)] `?v \<in> SetA s` by simp

    
    then show False using prem by simp
  qed

  
  from x_union not_A_deq not_A_enq have "x \<in> OP_B_enq s" by blast

  
  then show "x \<in> active_enqs s"
    unfolding active_enqs_def by simp
qed


(* ========================================================== *)
(* SetB classifications and counting arguments                 *)
(* ========================================================== *)
(* TypeBT is a refinement of TypeB. *)
lemma TypeBT_implies_TypeB:
  "TypeBT s a \<Longrightarrow> TypeB s a"
  unfolding TypeBT_def by simp

(* SetB is partitioned into the disjoint subsets SetBO and SetBT. *)
lemma SetB_partition:
  shows "SetB s = SetBO s \<union> SetBT s"
proof -
  
  have "SetBO s \<union> SetBT s = {a \<in> Val. TypeBO s a} \<union> {a \<in> Val. TypeBT s a}"
    unfolding SetBO_def SetBT_def by simp
  also have "... = {a \<in> Val. TypeB s a \<and> \<not> TypeBT s a} \<union> {a \<in> Val. TypeBT s a}"
    unfolding TypeBO_def by simp
  also have "... = {a \<in> Val. (TypeB s a \<and> \<not> TypeBT s a) \<or> TypeBT s a}"
    by auto
  also have "... = {a \<in> Val. TypeB s a}"
    using TypeBT_implies_TypeB
    by blast 
  also have "... = SetB s"
    unfolding SetB_def by simp
  finally show ?thesis by simp
qed


(* ========================================================== *)
(* Counting lemmas for filtered enqueue/dequeue index sets    *)
(* ========================================================== *)
(* Reexpress the cardinality of enqueue-index sets as multiset counts. *)
lemma card_EnqIdxs_mset_eq:
  assumes mset_eq: "mset (lin_seq s') = mset (lin_seq s) + {# act #}"
  assumes not_enq: "op_name act \<noteq> enq"
  shows "card (EnqIdxs s' v) = card (EnqIdxs s v)"
proof -
  
  have "card (EnqIdxs s' v) = length (filter (\<lambda>x. op_name x = enq \<and> op_val x = v) (lin_seq s'))"
    unfolding EnqIdxs_def 
    using length_filter_conv_card by (metis (no_types, lifting) Collect_cong)
  
  
  also have "... = size (mset (filter (\<lambda>x. op_name x = enq \<and> op_val x = v) (lin_seq s')))"
    by (metis size_mset)
  also have "... = size (filter_mset (\<lambda>x. op_name x = enq \<and> op_val x = v) (mset (lin_seq s')))"
    by simp

  
  also have "... = size (filter_mset (\<lambda>x. op_name x = enq \<and> op_val x = v) (mset (lin_seq s) + {# act #}))"
    using mset_eq by simp
    
  
  also have "... = size (filter_mset (\<lambda>x. op_name x = enq \<and> op_val x = v) (mset (lin_seq s)))"
    using not_enq by simp
    
  
  also have "... = length (filter (\<lambda>x. op_name x = enq \<and> op_val x = v) (lin_seq s))"
    by (metis (lifting) mset_filter size_mset)
  also have "... = card (EnqIdxs s v)"
    unfolding EnqIdxs_def 
    using length_filter_conv_card by (metis (no_types, lifting) Collect_cong)
    
  finally show ?thesis .
qed

(* Appending a matching dequeue increments the corresponding multiset count. *)
lemma card_DeqIdxs_mset_incr:
  assumes mset_eq: "mset (lin_seq s') = mset (lin_seq s) + {# act #}"
  assumes is_deq: "op_name act = deq"
  assumes val_eq: "op_val act = v"
  shows "card (DeqIdxs s' v) = card (DeqIdxs s v) + 1"
proof -
  
  have "card (DeqIdxs s' v) = size (filter_mset (\<lambda>x. op_name x = deq \<and> op_val x = v) (mset (lin_seq s')))"
    unfolding DeqIdxs_def 
    using length_filter_conv_card
    using card_indices_eq_count_mset by force 

  
  also have "... = size (filter_mset (\<lambda>x. op_name x = deq \<and> op_val x = v) (mset (lin_seq s) + {# act #}))"
    using mset_eq by simp

  
  also have "... = size (filter_mset (\<lambda>x. op_name x = deq \<and> op_val x = v) (mset (lin_seq s))) + 1"
    using is_deq val_eq by simp

  
  also have "... = card (DeqIdxs s v) + 1"
    unfolding DeqIdxs_def 
    by (metis (no_types, lifting) Collect_cong
        card_indices_eq_count_mset)
    
  finally show ?thesis .
qed

(* Appending an unrelated dequeue leaves the multiset count unchanged. *)
lemma card_DeqIdxs_mset_unchanged:
  assumes mset_eq: "mset (lin_seq s') = mset (lin_seq s) + {# act #}"
  assumes diff_val: "op_val act \<noteq> a" 
  shows "card (DeqIdxs s' a) = card (DeqIdxs s a)"
proof -
  
  have "card (DeqIdxs s' a) = size (filter_mset (\<lambda>x. op_name x = deq \<and> op_val x = a) (mset (lin_seq s')))"
    unfolding DeqIdxs_def 
    using length_filter_conv_card
    using card_indices_eq_count_mset by force 

  
  also have "... = size (filter_mset (\<lambda>x. op_name x = deq \<and> op_val x = a) (mset (lin_seq s) + {# act #}))"
    using mset_eq by simp

  
  also have "... = size (filter_mset (\<lambda>x. op_name x = deq \<and> op_val x = a) (mset (lin_seq s)))"
    using diff_val by simp

  
  also have "... = card (DeqIdxs s a)"
    unfolding DeqIdxs_def 
    by (metis (no_types, lifting) Collect_cong
        card_indices_eq_count_mset) 
    
  finally show ?thesis .
qed


(* ========================================================== *)
(* Order preservation through filtering                       *)
(* ========================================================== *)

(* ========== Rank-based correspondence between filtered lists ========== *)

(* ========================================================== *)
(* Order-preservation facts for filtered lists                *)
(* ========================================================== *)
(* Filtering preserves the relative order inherited from the source list. *)
lemma filter_order_preserved:
  fixes L1 L2 :: "'a list"
  assumes eq: "filter P L1 = filter P L2"
  assumes idx1: "i1 < j1" "j1 < length L1"
  assumes P1: "P (L1 ! i1)" "P (L1 ! j1)"
  assumes map: "L2 ! i2 = L1 ! i1" "L2 ! j2 = L1 ! j1"
  assumes idx2: "i2 < length L2" "j2 < length L2"
  assumes P2: "P (L2 ! i2)" "P (L2 ! j2)"
  assumes dist: "distinct (filter P L2)"
  shows "i2 < j2"
proof -
  
  let ?rank = "\<lambda>L i. length (filter P (take i L))"
  
  define r1 where "r1 = ?rank L1 i1"
  define r2 where "r2 = ?rank L1 j1"

  
  
  
  have "r1 < r2"
  proof -
    
    have "Suc i1 \<le> j1" using idx1(1) by simp
    then obtain k where k_def: "j1 = Suc i1 + k" 
      using le_Suc_ex by blast
      
    
    
    have "take j1 L1 = take (Suc i1) L1 @ take k (drop (Suc i1) L1)"
      unfolding k_def using idx1 take_add by metis
    
    
    then have filter_j1: "filter P (take j1 L1) = filter P (take (Suc i1) L1) @ filter P (take k (drop (Suc i1) L1))"
      by simp
      
    
    
    have "take (Suc i1) L1 = take i1 L1 @ [L1 ! i1]"
      using idx1 by (simp add: take_Suc_conv_app_nth)
    then have filter_Suc: "filter P (take (Suc i1) L1) = filter P (take i1 L1) @ [L1 ! i1]"
      using P1(1) by simp
      
    
    have "length (filter P (take j1 L1)) = length (filter P (take (Suc i1) L1)) + length (filter P (take k (drop (Suc i1) L1)))"
      using filter_j1 by simp
    also have "... = (r1 + 1) + length (filter P (take k (drop (Suc i1) L1)))"
      using filter_Suc r1_def by simp
    finally have "r2 \<ge> r1 + 1" 
      unfolding r2_def by simp
    then show ?thesis by simp
  qed

  
  
  
  have nth_rank_L1_i1: "filter P L1 ! r1 = L1 ! i1"
  proof -
    
    
    
    have split_L1: "filter P L1 = filter P (take (Suc i1) L1) @ filter P (drop (Suc i1) L1)"
      by (metis append_take_drop_id filter_append)

    
    have take_Suc: "take (Suc i1) L1 = take i1 L1 @ [L1 ! i1]"
      using idx1 by (simp add: take_Suc_conv_app_nth)

    
    have filter_take_Suc: "filter P (take (Suc i1) L1) = filter P (take i1 L1) @ [L1 ! i1]"
      using take_Suc P1(1) by simp

    
    have local_nth: "filter P (take (Suc i1) L1) ! r1 = L1 ! i1"
      using filter_take_Suc r1_def by (simp add: nth_append)

    
    
    have "r1 < length (filter P (take (Suc i1) L1))"
      using filter_take_Suc r1_def by simp
    
    
    show ?thesis
      using split_L1 local_nth `r1 < length (filter P (take (Suc i1) L1))`
      by (simp add: nth_append)
  qed

  
  have nth_rank_L1_j1: "filter P L1 ! r2 = L1 ! j1"
  proof -
    have split_L1: "filter P L1 = filter P (take (Suc j1) L1) @ filter P (drop (Suc j1) L1)"
      by (metis append_take_drop_id filter_append)
      
    have take_Suc: "take (Suc j1) L1 = take j1 L1 @ [L1 ! j1]"
      using idx1 by (simp add: take_Suc_conv_app_nth)
      
    have filter_take_Suc: "filter P (take (Suc j1) L1) = filter P (take j1 L1) @ [L1 ! j1]"
      using take_Suc P1(2) by simp

    have local_nth: "filter P (take (Suc j1) L1) ! r2 = L1 ! j1"
      using filter_take_Suc r2_def by (simp add: nth_append)
      
    have "r2 < length (filter P (take (Suc j1) L1))"
      using filter_take_Suc r2_def by simp
      
    show ?thesis
      using split_L1 local_nth `r2 < length (filter P (take (Suc j1) L1))`
      by (simp add: nth_append)
  qed

  
  
  
  
  
  have r1_L2: "?rank L2 i2 = r1"
  proof (rule ccontr)
    assume neq: "?rank L2 i2 \<noteq> r1"
    let ?r_i2 = "?rank L2 i2"
    
    
    have val_at_rank: "filter P L2 ! ?r_i2 = L2 ! i2"
    proof -
      
      have split_L2: "filter P L2 = filter P (take (Suc i2) L2) @ filter P (drop (Suc i2) L2)"
        by (metis append_take_drop_id filter_append)
      
      
      have take_Suc: "take (Suc i2) L2 = take i2 L2 @ [L2 ! i2]"
        using idx2(1) by (simp add: take_Suc_conv_app_nth)
        
      have filter_take_Suc: "filter P (take (Suc i2) L2) = filter P (take i2 L2) @ [L2 ! i2]"
        using take_Suc P2(1) by simp
        
      
      have local_nth: "filter P (take (Suc i2) L2) ! ?r_i2 = L2 ! i2"
        using filter_take_Suc by (simp add: nth_append)
      
      
      have rank_lt: "?r_i2 < length (filter P (take (Suc i2) L2))"
        using filter_take_Suc by simp
        
      
      
      show ?thesis
        using split_L2 local_nth rank_lt
        by (simp add: nth_append)
    qed
    
    
    have valid_ri2: "?r_i2 < length (filter P L2)"
    proof -
      have "take (Suc i2) L2 = take i2 L2 @ [L2 ! i2]"
        using idx2(1) by (simp add: take_Suc_conv_app_nth)
      then have "length (filter P (take (Suc i2) L2)) = ?r_i2 + 1"
        using P2(1) by simp
      
      have "length (filter P L2) = length (filter P (take (Suc i2) L2)) + length (filter P (drop (Suc i2) L2))"
        by (metis append_take_drop_id filter_append length_append)
        
      thus ?thesis 
        using `length (filter P (take (Suc i2) L2)) = ?r_i2 + 1` by arith
    qed

    
    have valid_r1: "r1 < length (filter P L2)"
    proof -
      
      
      
      have "take (Suc i1) L1 = take i1 L1 @ [L1 ! i1]"
        using idx1 by (simp add: take_Suc_conv_app_nth)
      then have "length (filter P (take (Suc i1) L1)) = r1 + 1"
        using r1_def P1(1) by simp
      
      have "length (filter P L1) = length (filter P (take (Suc i1) L1)) + length (filter P (drop (Suc i1) L1))"
        by (metis append_take_drop_id filter_append length_append)
      
      then have "r1 < length (filter P L1)" 
        using `length (filter P (take (Suc i1) L1)) = r1 + 1` by arith
      
      thus ?thesis using eq by simp
    qed

    
    have val_at_r1: "filter P L2 ! r1 = L2 ! i2"
      using eq nth_rank_L1_i1 map(1) by simp
      
    have "?r_i2 = r1"
      using dist valid_r1 valid_ri2 val_at_rank val_at_r1
      using nth_eq_iff_index_eq
      by metis
      
    thus False using neq by simp
  qed

  
  have r2_L2: "?rank L2 j2 = r2"
  proof -
    let ?r_j2 = "?rank L2 j2"

    
    
    
    have val_at_rank: "filter P L2 ! ?r_j2 = L2 ! j2"
    proof -
      
      
      have split_L2: "filter P L2 = filter P (take (Suc j2) L2) @ filter P (drop (Suc j2) L2)"
        by (metis append_take_drop_id filter_append)

      
      have take_Suc: "take (Suc j2) L2 = take j2 L2 @ [L2 ! j2]"
        using idx2(2) by (simp add: take_Suc_conv_app_nth)
      
      have filter_take_Suc: "filter P (take (Suc j2) L2) = filter P (take j2 L2) @ [L2 ! j2]"
        using take_Suc P2(2) by simp

      
      have local_nth: "filter P (take (Suc j2) L2) ! ?r_j2 = L2 ! j2"
        using filter_take_Suc by (simp add: nth_append)
      
      
      have rank_lt_prefix: "?r_j2 < length (filter P (take (Suc j2) L2))"
        using filter_take_Suc by simp

      
      show ?thesis
        using split_L2 local_nth rank_lt_prefix
        by (simp add: nth_append)
    qed

    
    
    
    have valid_r2: "r2 < length (filter P L2)"
    proof -
      
      have "filter P L1 = filter P (take (Suc j1) L1) @ filter P (drop (Suc j1) L1)"
        by (metis append_take_drop_id filter_append)
      then have len_L1_split: "length (filter P L1) = length (filter P (take (Suc j1) L1)) + length (filter P (drop (Suc j1) L1))"
        by simp
      
      
      have "take (Suc j1) L1 = take j1 L1 @ [L1 ! j1]"
        using idx1(2) by (simp add: take_Suc_conv_app_nth)
      then have len_prefix: "length (filter P (take (Suc j1) L1)) = r2 + 1"
        using P1(2) r2_def by simp
        
      
      
      have "r2 < length (filter P L1)"
        using len_L1_split len_prefix by arith
        
      
      thus ?thesis using eq by simp
    qed

    
    
    
    have valid_rj2: "?r_j2 < length (filter P L2)"
    proof -
      
      have "filter P L2 = filter P (take (Suc j2) L2) @ filter P (drop (Suc j2) L2)"
        by (metis append_take_drop_id filter_append)
      then have len_L2_split: "length (filter P L2) = length (filter P (take (Suc j2) L2)) + length (filter P (drop (Suc j2) L2))"
        by simp
        
      
      have "take (Suc j2) L2 = take j2 L2 @ [L2 ! j2]"
        using idx2(2) by (simp add: take_Suc_conv_app_nth)
      then have len_prefix: "length (filter P (take (Suc j2) L2)) = ?r_j2 + 1"
        using P2(2) by simp

      
      thus ?thesis 
        using len_L2_split len_prefix by arith
    qed

    
    
    
    have val_match: "filter P L2 ! r2 = L2 ! j2"
      using eq nth_rank_L1_j1 map(2) by simp
      
    show ?thesis
      using dist valid_r2 valid_rj2 
            val_at_rank val_match
      using nth_eq_iff_index_eq
      by metis 
  qed

  
  
  
  (* Step 4: conclude the order transfer in the original lists. *)
  show "i2 < j2"
  proof (rule ccontr)
    assume "\<not> i2 < j2"
    hence "j2 \<le> i2" by simp
    
    
    
    obtain k where "i2 = j2 + k" using `j2 \<le> i2` le_iff_add by blast
    then have "take i2 L2 = take j2 L2 @ take k (drop j2 L2)"
      using take_add by metis
    then have "length (filter P (take i2 L2)) = length (filter P (take j2 L2)) + length (filter P (take k (drop j2 L2)))"
      by simp
    then have "?rank L2 j2 \<le> ?rank L2 i2" by simp
    
    
    thus False using r2_L2 r1_L2 `r1 < r2` by simp
  qed
qed

(* Recover the source position of the nth filtered element together with its rank information. *)
lemma filter_nth_ex_rank:
  fixes L1 L2 :: "'a list"
  assumes eq: "filter P L1 = filter P L2"
  assumes i: "i < length L1"
  assumes P: "P (L1 ! i)"
  shows "\<exists>j < length L2. L2 ! j = L1 ! i \<and> 
         length (filter P (take j L2)) = length (filter P (take i L1))"
proof -
  
  let ?rank = "length (filter P (take i L1))"
  
  
  have "filter P L1 ! ?rank = L1 ! i"
    using i P
  proof (induct L1 arbitrary: i)
    case Nil then show ?case by simp
  next
    case (Cons x xs)
    show ?case
    proof (cases "P x")
      case True
      then show ?thesis using Cons by (cases i) auto
    next
      case False
      then show ?thesis using Cons by (cases i) auto
    qed
  qed

  
  have "?rank < length (filter P L1)"
    using i P
    apply (induct L1 arbitrary: i)
     apply simp
    apply (case_tac i, auto)
    done

  
  have "filter P L2 ! ?rank = L1 ! i" 
    using `filter P L1 ! ?rank = L1 ! i` eq by simp
  have rank_valid_L2: "?rank < length (filter P L2)"
    using `?rank < length (filter P L1)` eq by simp

  
  {
    fix k
    assume k_valid: "k < length (filter P L2)"
    have "\<exists>j < length L2. L2 ! j = filter P L2 ! k \<and> length (filter P (take j L2)) = k"
      using k_valid
    proof (induct L2 arbitrary: k)
      case Nil then show ?case by simp
    next
      case (Cons y ys)
      show ?case
      proof (cases "P y")
        case True note Py = True 
        show ?thesis
        proof (cases "k = 0")
          case True 
          
          
          show ?thesis 
            using Py True Cons.prems 
            by (rule_tac x=0 in exI, simp)
        next
          case False
          then obtain k' where k_def: "k = Suc k'" by (cases k) auto
          
          
          have "k' < length (filter P ys)"
            using Cons.prems Py k_def by simp
            
          
          then obtain j' where IH: 
            "j' < length ys" 
            "ys ! j' = filter P ys ! k'" 
            "length (filter P (take j' ys)) = k'"
            using Cons.hyps by blast
            
          
          show ?thesis
            apply (rule_tac x="Suc j'" in exI)
            using Py k_def IH by simp
        qed
      next
        case False note nPy = False 
        
        
        
        have "k < length (filter P ys)"
          using Cons.prems nPy by simp
          
        
        then obtain j' where IH: 
          "j' < length ys" 
          "ys ! j' = filter P ys ! k" 
          "length (filter P (take j' ys)) = k"
          using Cons.hyps by blast
          
        
        show ?thesis
          apply (rule_tac x="Suc j'" in exI)
          using nPy IH by simp
      qed
    qed
  }
  
  note ex_j_generic = this
  
  obtain j where "j < length L2" "L2 ! j = filter P L2 ! ?rank" "length (filter P (take j L2)) = ?rank"
    using ex_j_generic[OF rank_valid_L2] by blast
    
  
  then show ?thesis
    using `filter P L2 ! ?rank = L1 ! i` by auto
qed


(* ========================================================== *)
(* Further properties of find_last_SA and find_last_enq       *)
(* ========================================================== *)
(* Enqueues appearing after the last SetA enqueue are not in SetA. *)
lemma enqs_after_last_sa_are_not_in_sa:
  fixes L :: "OpRec list"
  assumes range: "k < length L"
  assumes idx_after: "int k > find_last_SA L"
  assumes is_enq: "op_name (L!k) = enq" 
  shows "\<not> in_SA (op_val (L!k)) L"
proof
  assume in_sa: "in_SA (op_val (L!k)) L"
  
  
  
  let ?P = "\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L"
  let ?indices = "find_indices ?P L"
  
  
  have "k \<in> set ?indices"
    unfolding find_indices_def
    using range is_enq in_sa
    by simp 

  
  then have not_empty: "?indices \<noteq> []" by auto
  
  
  
  have last_sa_eq: "find_last_SA L = int (last ?indices)"
    using not_empty unfolding find_last_SA_def Let_def
    by simp

  
  
  have "sorted ?indices"
    unfolding find_indices_def
    by (simp add: sorted_wrt_filter)
    
  
  
  have "k \<le> last ?indices"
    using `sorted ?indices` not_empty `k \<in> set ?indices`
  proof (induct ?indices rule: rev_induct)
    case Nil 
    then show ?case by simp
  next
    case (snoc x xs)
    
    
    
    
    show ?case
    proof (cases "k = x")
      case True then show ?thesis
        by (metis idx_after last_sa_eq last_snoc less_imp_neq
            snoc.hyps(2))
    next
      case False
      
      then have "k \<in> set xs" using snoc.prems(3)
        by (metis rotate1.simps(2) set_ConsD set_rotate1 snoc.hyps(2)) 
      
      
      have "\<forall>y \<in> set xs. y \<le> x"
        using snoc.prems(1)
        by (metis list.set_intros(1) snoc.hyps(2) sorted_wrt_append)
        
      then show ?thesis using `k \<in> set xs`
        by (metis last_snoc snoc.hyps(2)) 
    qed
  qed

  
  
  then have "int k \<le> find_last_SA L"
    using last_sa_eq by simp
  then show False 
    using idx_after by simp
qed


(* ========================================================== *)
(* Generic search and list-update lemmas                      *)
(* ========================================================== *)
(* Generic correctness property of find_unique_index under uniqueness assumptions. *)
lemma find_unique_index_prop:
  assumes "find_unique_index P L = Some k"
  shows "k < length L \<and> P (L ! k)"
proof -
  obtain indices where indices_def: "indices = find_indices P L"
    by simp
  from assms have "indices \<noteq> []" and "k = hd indices"
    unfolding find_unique_index_def indices_def Let_def
    by (metis (no_types, lifting) option.inject option.simps(3))+
  then have "k \<in> set indices"
    by (simp add: list.set_sel(1))
  then show ?thesis
    unfolding indices_def find_indices_def
    by (simp add: in_set_conv_nth)
qed

(* Structural facts about the final enqueue occurrence in a list decomposition. *)
lemma find_last_enq_props:
  assumes "find_last_enq L = Some (before, enq_act, after)"
  shows "L = before @ [enq_act] @ after" 
    and "op_name enq_act = enq"
    and "\<forall>a \<in> set after. op_name a \<noteq> enq"
proof -
  
  from assms have 
    "let enq_indices = find_indices (\<lambda>a. op_name a = enq) L in
     enq_indices \<noteq> [] \<and>
     before = take (last enq_indices) L \<and>
     enq_act = L ! (last enq_indices) \<and>
     after = drop (last enq_indices + 1) L"
    unfolding find_last_enq_def
    by (smt (verit, best) option.distinct(1) option.inject prod.inject)
  
  then obtain enq_indices where
    indices_def: "enq_indices = find_indices (\<lambda>a. op_name a = enq) L" and
    indices_nonempty: "enq_indices \<noteq> []" and
    before_def: "before = take (last enq_indices) L" and
    enq_act_def: "enq_act = L ! (last enq_indices)" and
    after_def: "after = drop (last enq_indices + 1) L"
    by meson
  
  
  have last_idx_in_set: "last enq_indices \<in> set enq_indices"
    using indices_nonempty
    by simp
  
  have all_indices_valid: "\<forall>i \<in> set enq_indices. i < length L"
    unfolding indices_def find_indices_def by auto
    
  have last_idx_lt_length: "last enq_indices < length L"
    using last_idx_in_set all_indices_valid by blast
  
  
  show "L = before @ [enq_act] @ after"
    using after_def before_def enq_act_def id_take_nth_drop last_idx_lt_length by auto
  
  
  show "op_name enq_act = enq"
  proof -
    from last_idx_in_set have 
      "last enq_indices \<in> set (find_indices (\<lambda>a. op_name a = enq) L)"
      by (simp add: indices_def)
    
    then have "op_name (L ! (last enq_indices)) = enq"
      unfolding find_indices_def by auto
    
    then show ?thesis by (simp add: enq_act_def)
  qed
  
  
  show "\<forall>a \<in> set after. op_name a \<noteq> enq"
  proof (rule ccontr)
    assume "\<not> (\<forall>a \<in> set after. op_name a \<noteq> enq)"
    then obtain a where 
      a_in_after: "a \<in> set after" and 
      a_is_enq: "op_name a = enq"
      by auto
    
    
    from a_in_after obtain k where
      k_lt: "k < length after" and
      after_at_k: "after ! k = a"
      by (auto simp: in_set_conv_nth)
    
    
    let ?abs_pos = "last enq_indices + 1 + k"
    
    
    have abs_pos_lt_length: "?abs_pos < length L"
    proof -
      have "length after = length L - (last enq_indices + 1)"
        using after_def by auto
      with k_lt show ?thesis by linarith
    qed
    
    
    have L_at_abs_pos: "L ! ?abs_pos = a"
      using after_def k_lt
      using after_at_k by auto
    
    
    
    have abs_pos_in_indices: "?abs_pos \<in> set enq_indices"
    proof -
      
      have enq_indices_def_expanded: 
        "enq_indices = [i \<leftarrow> [0..<length L]. op_name (L ! i) = enq]"
        by (simp add: indices_def find_indices_def)
      
      
      have condition_holds: "op_name (L ! ?abs_pos) = enq"
        using L_at_abs_pos a_is_enq by auto
      
      
      have in_range: "?abs_pos \<in> set [0..<length L]"
        using abs_pos_lt_length by auto
      
      
      show ?thesis
        unfolding enq_indices_def_expanded
        using in_range condition_holds
        by (simp add: enq_indices_def_expanded)
    qed
    
    
    have gt: "?abs_pos > last enq_indices"
      by simp
    
    
    have indices_sorted: "sorted enq_indices"
      unfolding indices_def find_indices_def
      by (meson sorted_upt sorted_wrt_filter)

    
    
    have last_is_max: "\<forall>x \<in> set enq_indices. x \<le> last enq_indices"
    proof -
      from indices_sorted indices_nonempty
      have "sorted enq_indices" and "enq_indices \<noteq> []" by auto
      
      show ?thesis
      proof (intro ballI)
        fix x
        assume "x \<in> set enq_indices"
        then obtain i where 
          i_lt: "i < length enq_indices" and
          enq_indices_at_i: "enq_indices ! i = x"
          by (auto simp: in_set_conv_nth)
        
        
        from indices_sorted have
          "\<forall>i j. i \<le> j \<and> j < length enq_indices \<longrightarrow> enq_indices ! i \<le> enq_indices ! j"
          by (simp add: sorted_iff_nth_mono)
        
        
        have last_index: "last enq_indices = enq_indices ! (length enq_indices - 1)"
          using indices_nonempty by (simp add: last_conv_nth)
        
        have "i \<le> length enq_indices - 1"
          using i_lt by linarith
          
        with indices_sorted i_lt have 
          "enq_indices ! i \<le> enq_indices ! (length enq_indices - 1)"
          using \<open>\<forall>i j. i \<le> j \<and> j < length enq_indices \<longrightarrow> enq_indices ! i \<le> enq_indices ! j\<close> by auto
        
        then show "x \<le> last enq_indices"
          by (simp add: enq_indices_at_i last_index)
      qed
    qed
    
    
    from last_is_max abs_pos_in_indices have 
      "?abs_pos \<le> last enq_indices"
      by blast
    
    
    with gt show False by linarith
  qed
qed

(* Cardinality-one sets yield a successful result for find_unique_index. *)
lemma find_unique_index_card_1:
  assumes "card {i. i < length L \<and> P (L ! i)} = 1"
  shows "\<exists>k. find_unique_index P L = Some k"
proof -
  
  let ?indices = "find_indices P L"
  
  
  
  have set_indices: "set ?indices = {i. i < length L \<and> P (L ! i)}"
    unfolding find_indices_def 
    using set_filter by auto 

  
  
  have distinct_indices: "distinct ?indices"
    unfolding find_indices_def 
    using distinct_upt distinct_filter by auto

  
  have "length ?indices = card (set ?indices)"
    using distinct_indices distinct_card
    by fastforce
  also have "... = 1"
    using set_indices assms by simp
  finally have len_1: "length ?indices = 1" .

  
  
  show ?thesis
    unfolding find_unique_index_def Let_def
    using len_1 by (auto)
qed


(* ========================================================== *)
(* Index-mapping lemmas for local list rewrites               *)
(* ========================================================== *)
(* Swapping adjacent positions only affects the two exchanged indices. *)
lemma swap_adjacent_nth:
  assumes "L = pre @ [a, b] @ post"
  assumes "new_L = pre @ [b, a] @ post"
  assumes "idx = length pre"
  shows "new_L ! k = L ! (if k = idx then idx + 1 else if k = idx + 1 then idx else k)"
proof -
  consider (before) "k < idx" | (at1) "k = idx" | (at2) "k = idx + 1" | (after) "k \<ge> idx + 2" by linarith
  then show ?thesis
  proof cases
    case before
    then have "new_L ! k = pre ! k" using assms by (simp add: nth_append)
    moreover have "L ! k = pre ! k" using before assms by (simp add: nth_append)
    ultimately show ?thesis using before by simp
  next
    case at1
    then have "new_L ! k = b" using assms by (simp add: nth_append)
    moreover have "L ! (idx + 1) = b" using assms by (simp add: nth_append)
    ultimately show ?thesis using at1 by simp
  next
    case at2
    then have "new_L ! k = a" using assms by (simp add: nth_append)
    moreover have "L ! idx = a" using assms by (simp add: nth_append)
    ultimately show ?thesis using at2 by simp
  next
    case after
    then have "new_L ! k = post ! (k - idx - 2)" using assms by (auto simp add: nth_append)
    moreover have "L ! k = post ! (k - idx - 2)" using assms after by (auto simp add: nth_append)
    ultimately show ?thesis using after by simp
  qed
qed

(* Moving one element backward preserves all unrelated nth observations. *)
lemma jump_back_nth:
  assumes "L = pre @ [mid_enq] @ mid_list @ [jump_enq] @ post"
  assumes "new_L = pre @ [jump_enq] @ [mid_enq] @ mid_list @ post"
  assumes "idx = length pre"
  assumes "m_len = length mid_list"
  shows "new_L ! k = L ! (
    if k < idx then k
    else if k = idx then idx + m_len + 1  
    else if k \<le> idx + m_len + 1 then k - 1 
    else k)"
proof -
  let ?map = "\<lambda>k. if k < idx then k 
                 else if k = idx then idx + m_len + 1 
                 else if k \<le> idx + m_len + 1 then k - 1 
                 else k"
  consider (before) "k < idx" 
         | (at_jump) "k = idx" 
         | (middle) "idx < k \<and> k \<le> idx + m_len + 1" 
         | (after) "k > idx + m_len + 1" 
    by linarith
  then show ?thesis
  proof cases
    case before
    then show ?thesis using assms by (simp add: nth_append)
  next
    case at_jump
    then have "new_L ! k = jump_enq" using assms by (simp add: nth_append)
    moreover have "L ! (idx + m_len + 1) = jump_enq" 
      using assms by (simp add: nth_append)
    ultimately show ?thesis using at_jump by simp
  next
    case middle
    
    have "new_L ! k = ([jump_enq] @ [mid_enq] @ mid_list @ post) ! (k - idx)"
      using middle assms by (simp add: nth_append)
    also have "... = ([mid_enq] @ mid_list @ post) ! (k - idx - 1)"
      using middle by (simp add: nth_append)
    finally have left: "new_L ! k = (mid_enq # mid_list @ post) ! (k - idx - 1)" by simp

    have "L ! (k - 1) = ([mid_enq] @ mid_list @ [jump_enq] @ post) ! (k - 1 - idx)"
      using middle assms
      using interval_class.less_imp_less_eq_dec nth_append_right
      by blast 
    hence right: "L ! (k - 1) = (mid_enq # mid_list @ [jump_enq] @ post) ! (k - idx - 1)" by simp

    
    have "k - idx - 1 < length (mid_enq # mid_list)"
      using middle assms
      by fastforce
    
    hence "(mid_enq # mid_list @ post) ! (k - idx - 1) = (mid_enq # mid_list) ! (k - idx - 1)"
      by (metis append_Cons nth_append_left)

    also have "... = (mid_enq # mid_list @ [jump_enq] @ post) ! (k - idx - 1)"
      using `k - idx - 1 < length (mid_enq # mid_list)`
      by (metis append_Cons nth_append_left) 
    finally show ?thesis using left right middle by simp
  next
    case after
    
    then have "new_L ! k = post ! (k - idx - m_len - 2)"
      using assms by (auto simp add: nth_append)
    moreover have "L ! k = post ! (k - idx - m_len - 2)"
      using after assms by (auto simp add: nth_append)
    ultimately show ?thesis using after by simp
  qed
qed

(* Moving one element forward preserves all unrelated nth observations. *)
lemma jump_forward_nth:
  assumes "L = pre @ [jump_enq] @ mid_list @ post"
  assumes "new_L = pre @ mid_list @ [jump_enq] @ post"
  assumes "idx = length pre"
  assumes "m_len = length mid_list"
  shows "new_L ! k = L ! (
    if k < idx then k 
    else if k < idx + m_len then k + 1 
    else if k = idx + m_len then idx 
    else k)"
proof -
  have len_pre: "length pre = idx" using assms by simp
  have len_mid: "length mid_list = m_len" using assms by simp
  
  show ?thesis
  proof (cases "k < idx")
    case True
    thus ?thesis using assms by (simp add: nth_append)
  next
    case False
    hence k_ge_idx: "k \<ge> idx" by simp
    show ?thesis
    proof (cases "k < idx + m_len")
      case True
      
      have "new_L ! k = (mid_list @ [jump_enq] @ post) ! (k - idx)" 
        using assms True k_ge_idx by (simp add: nth_append)
      also have "... = mid_list ! (k - idx)"
        using True k_ge_idx len_mid
        by (simp add: nth_append_left)
      finally have 1: "new_L ! k = mid_list ! (k - idx)" .
      
      have "L ! (k + 1) = ([jump_enq] @ mid_list @ post) ! (k + 1 - idx)"
        using assms True k_ge_idx by (simp add: nth_append)
      also have "... = (jump_enq # mid_list @ post) ! (Suc (k - idx))"
        using k_ge_idx by simp
      also have "... = (mid_list @ post) ! (k - idx)"
        by simp
      also have "... = mid_list ! (k - idx)"
        using True k_ge_idx len_mid
        by (metis le_add_diff_inverse nat_add_left_cancel_less
            nth_append_cases(1)) 
      finally have 2: "L ! (k + 1) = mid_list ! (k - idx)" .
      
      show ?thesis using `\<not> k < idx` True 1 2 by simp
    next
      case False
      hence k_ge_idx_m: "k \<ge> idx + m_len" by simp
      show ?thesis
      proof (cases "k = idx + m_len")
        case True
        
        have 1: "new_L ! k = jump_enq" 
          using assms True by (simp add: nth_append)
        have 2: "L ! idx = jump_enq"
          using assms by (simp add: nth_append)
        show ?thesis using `\<not> k < idx` `\<not> k < idx + m_len` True 1 2 by simp
      next
        case False
        
        hence k_gt: "k > idx + m_len" using k_ge_idx_m by simp
        have 1: "new_L ! k = post ! (k - idx - m_len - 1)"
          using assms k_gt
          by (simp add: nth_append_cases(2)) 
        have 2: "L ! k = post ! (k - idx - 1 - m_len)"
          using assms k_gt
          by (simp add: nth_append_right) 
        show ?thesis using `\<not> k < idx` `\<not> k < idx + m_len` `k \<noteq> idx + m_len` 1 2 by simp
      qed
    qed
  qed
qed


(* ========== Bridges from matched pairs to SA membership ========== *)

(* ========================================================== *)
(* Happens-before and counting consequences                    *)
(* ========================================================== *)
(* A matched enqueue/dequeue pair implies SetA membership. *)
lemma matched_pair_implies_in_SA:
  assumes indep: "data_independent L"
  assumes enq_valid: "k_enq < length L" "op_name (L ! k_enq) = enq" "op_val (L ! k_enq) = v"
  assumes deq_valid: "k_deq < length L" "op_name (L ! k_deq) = deq" "op_val (L ! k_deq) = v"
  shows "in_SA v L"
proof -
  
  have enq_idx_list: "find_indices (\<lambda>a. op_name a = enq \<and> op_val a = v) L = [k_enq]"
    using unique_enq_index[OF indep enq_valid(2) enq_valid(3) enq_valid(1)] .

  
  have find_enq: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some k_enq"
    unfolding find_unique_index_def Let_def enq_idx_list by simp

  
  have deq_idx_list: "find_indices (\<lambda>a. op_name a = deq \<and> op_val a = v) L = [k_deq]"
    using unique_deq_index[OF indep deq_valid(2) deq_valid(3) deq_valid(1)] .

  
  have find_deq: "find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) L = Some k_deq"
    unfolding find_unique_index_def Let_def deq_idx_list by simp

  
  show ?thesis
    unfolding in_SA_def
    using find_enq find_deq by simp
qed


(* ========================================================== *)
(* Happens-before auxiliary lemmas                            *)
(* ========================================================== *)
(* Consistency with happens-before excludes the reversed happens-before edge. *)
lemma HB_consistent_order_implies_not_HB_rev:
  assumes "HB_consistent L H"
  assumes "k1 < k2"
  assumes "k2 < length L"
  shows "\<not> happens_before (L ! k2) (L ! k1) H"
proof -
  
  have "happens_before (L ! k2) (L ! k1) H \<Longrightarrow> k2 < k1"
    using assms(1) unfolding HB_consistent_def
    by (metis assms(2) assms(3) less_trans) 
  
  thus ?thesis
    using assms(2) by auto
qed

(* Chain together timeline facts to derive a composite happens-before relation. *)
lemma HB_timeline_chain:
  assumes "happens_before a o1 H"           
  assumes "\<not> happens_before o2 o1 H"        
  assumes "happens_before o2 b H"           
  shows "happens_before a b H"              
proof -
  
  from assms(1) obtain k1_a k2_o1 where a_o1:
    "k1_a < k2_o1" 
    "match_ret H k1_a a" 
    "match_call H k2_o1 o1"
    unfolding HB_def by blast

  
  from assms(3) obtain k1_o2 k2_b where o2_b:
    "k1_o2 < k2_b" 
    "match_ret H k1_o2 o2" 
    "match_call H k2_b b"
    unfolding HB_def by blast

  
  have "k2_o1 \<le> k1_o2"
  proof (rule ccontr)
    assume "\<not> (k2_o1 \<le> k1_o2)"
    hence "k1_o2 < k2_o1" by simp
    
    
    have "happens_before o2 o1 H"
      unfolding HB_def
      using `k1_o2 < k2_o1` o2_b(2) a_o1(3) by blast
    
    
    with assms(2) show False by contradiction
  qed

  
  hence "k1_a < k2_b"
    using a_o1(1) o2_b(1) by linarith

  
  show ?thesis
    unfolding HB_def
    using `k1_a < k2_b` a_o1(2) o2_b(3) by blast
qed


(* ========================================================== *)
(* Monotonicity of enqueue counting over prefixes             *)
(* ========================================================== *)
(* Adding a fresh enqueue strictly increases the enqueue count. *)
lemma enq_count_strict_mono:
  assumes "kb < kv"
      and "kv < length L"
      and "op_name (L ! kb) = enq"
      and "op_name (L ! kv) = enq"
  shows "length (filter (\<lambda>x. op_name x = enq) (take (kb + 1) L)) < 
         length (filter (\<lambda>x. op_name x = enq) (take (kv + 1) L))"
proof -
  let ?P = "\<lambda>x. op_name x = enq"
  
  
  let ?R = "drop (kb + 1) (take (kv + 1) L)"
  

  
  
  have split_eq: "take (kv + 1) L = take (kb + 1) L @ ?R"
  proof -
    
    have "take (kv + 1) L = take (kb + 1) (take (kv + 1) L) @ drop (kb + 1) (take (kv + 1) L)"
      by (metis append_take_drop_id)
    moreover have "take (kb + 1) (take (kv + 1) L) = take (kb + 1) L"
      using \<open>kb < kv\<close> by simp
    ultimately show ?thesis by simp
  qed

  
  
  have len_split: "length (filter ?P (take (kv + 1) L)) = 
                   length (filter ?P (take (kb + 1) L)) + length (filter ?P ?R)"
    by (subst split_eq, simp)
  
  
  
  have "length (filter ?P ?R) > 0"
  proof -
    
    have "L ! kv \<in> set ?R"
    proof -
      have len_R: "length ?R = kv - kb" 
        using \<open>kb < kv\<close> \<open>kv < length L\<close> by simp
      have idx_valid: "kv - kb - 1 < length ?R" 
        using \<open>kb < kv\<close> len_R by simp
        
      
      have "?R ! (kv - kb - 1) = L ! kv" 
        using \<open>kb < kv\<close> \<open>kv < length L\<close> by simp
        
      
      moreover have "?R ! (kv - kb - 1) \<in> set ?R"
        using idx_valid by (rule nth_mem)
        
      ultimately show ?thesis by simp
    qed
    
    moreover have "?P (L ! kv)" 
      using \<open>op_name (L ! kv) = enq\<close> by simp
      
    
    ultimately have "filter ?P ?R \<noteq> []" 
      by (auto simp: filter_empty_conv)
      
    thus ?thesis by simp
  qed

  
  
  
  thus ?thesis 
    using len_split by simp
qed

end