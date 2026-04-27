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

(* ========================================================== *)
(* Dequeue-side helper lemmas and permutation arguments        *)
(* ========================================================== *)

(* ========== Basic index and queue-back facts ========== *)

(* Idx coincides with the witness given by AtIdx under the system invariant. *)
lemma Idx_implies_AtIdx:
  assumes "system_invariant s"
  assumes "InQBack s a"
  shows "AtIdx s a (Idx s a)"
proof -
  from assms(2) have "\<exists>k. AtIdx s a k" unfolding AtIdx_def InQBack_def by auto
  then show ?thesis unfolding Idx_def by (rule someI_ex)
qed

(* AtIdx directly exposes the corresponding Qback_arr entry. *)
lemma AtIdx_implies_Qback_eq:
  assumes "AtIdx s a k"
  shows "Qback_arr s k = a"
  using assms unfolding AtIdx_def by simp

(* A non-BOT value stored in Qback must belong to Val. *)
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

(* An E2 process always witnesses a pending enqueue. *)
lemma E2_implies_HasPendingEnq:
  assumes "system_invariant s"
  assumes "program_counter s p = ''E2''"
  shows "HasPendingEnq s p (v_var s p)"
proof -
  (* Step 1: extract hI1_E_Phase_Pending_Enq from the global invariant. *)
  from assms(1) have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" unfolding system_invariant_def by simp
  
  (* Step 2: observe that E2 is one of the enqueue-phase control states. *)
  from assms(2) have "program_counter s p \<in> {''E1'', ''E2'', ''E3''}" by simp
  
  (* Step 3: instantiate the pending-enqueue invariant. *)
  with hI1_E_Phase_Pending_Enq_s show ?thesis unfolding hI1_E_Phase_Pending_Enq_def by blast
qed

(* The slot addressed by j in phase D3 is synchronized with Qback or already empty. *)
lemma D3_Q_at_j:
  assumes "system_invariant s"
  assumes "program_counter s p = ''D3''"
  shows "Q_arr s (j_var s p) = Qback_arr s (j_var s p) \<or> Q_arr s (j_var s p) = BOT"
proof -
  from assms(1) have sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" unfolding system_invariant_def by simp
  show ?thesis using sI8_Q_Qback_Sync_s unfolding sI8_Q_Qback_Sync_def by simp
qed

(* ========================================================== *)
(* TypeB exclusion when the corresponding queue slot is empty  *)
(* ========================================================== *)

(* If the Qback index of a points to a BOT slot in Q, then a cannot be a TypeB value. *)
lemma Idx_eq_j_and_Q_BOT_implies_not_TypeB:
  assumes "system_invariant s"
  assumes "InQBack s a"
  assumes "Idx s a = j"
  assumes "Q_arr s j = BOT"   (* Critical assumption: the concrete queue slot Q[j] is empty. *)
  assumes "a \<noteq> BOT"
  shows "\<not> TypeB s a"
proof
  assume TypeB_a: "TypeB s a"
  
  (* Step 1: extract the invariants used in the contradiction argument. *)
  from assms(1) have 
    sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s" and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s"
    unfolding system_invariant_def by simp_all

  (* Step 2: obtain Qback_arr s j = a from the definition of Idx. *)
  have T_j_eq_a: "Qback_arr s j = a"
    using AtIdx_implies_Qback_eq Idx_implies_AtIdx assms(1,2,3) by blast

  (* Step 3: unfold TypeB and split according to whether a is still in Q. *)
  from TypeB_a show False
  proof (cases "QHas s a")
    case True
    (* Case A: a still occurs in the concrete queue. *)
    then obtain k where Q_k: "Q_arr s k = a" unfolding QHas_def by blast
    
    (* Use sI8_Q_Qback_Sync to lift the queue fact to Qback. *)
    have "Qback_arr s k = a"
    proof -
      have "Q_arr s k \<noteq> BOT" using Q_k assms(5) by simp
      with sI8_Q_Qback_Sync_s have "Q_arr s k = Qback_arr s k" unfolding sI8_Q_Qback_Sync_def by fastforce
      with Q_k show ?thesis by simp
    qed
    
    (* Uniqueness of Qback values forces k = j. *)
    have "k = j"
    proof (rule ccontr)
      assume "k \<noteq> j"
      (* Show that a is a valid queue value. *)
      have "a \<in> Val" using InQBack_non_BOT_implies_Val[OF assms(1) assms(2) assms(5)] .
      with sI10_Qback_Unique_Vals_s `Qback_arr s k = a` T_j_eq_a `k \<noteq> j` 
      show False unfolding sI10_Qback_Unique_Vals_def
        by (metis assms(5))
    qed
    
    (* Contradiction: Q[j] cannot be both a and BOT. *)
    have "Q_arr s j = a" using Q_k `k = j` by simp
    with assms(4) assms(5) show False by simp
    
  next
    case False
    (* Case B: a is not in Q, so TypeB places it in some E2 process. *)
    from TypeB_a False have E2_exists: "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = a"
      unfolding TypeB_def by simp
    
    then obtain q where q_props: "program_counter s q = ''E2''" "v_var s q = a" by blast
    
    (* Use sI3_E2_Slot_Exclusive to obtain Qback_arr s (i_var s q) = BOT. *)
    have T_i_bot: "Qback_arr s (i_var s q) = BOT"
      using sI3_E2_Slot_Exclusive_s q_props(1) unfolding sI3_E2_Slot_Exclusive_def by simp
    
    (* Since Qback_arr s j = a \<noteq> BOT, we get j \<noteq> i_var s q. *)
    have j_ne_i: "j \<noteq> i_var s q"
      using T_j_eq_a T_i_bot assms(5) by auto
    
    (* Reuse the pending-enqueue witness from the E2 control state. *)
    have "HasPendingEnq s q a"
      using E2_implies_HasPendingEnq[OF assms(1) q_props(1)] q_props(2) by simp
    
    (* Pending enqueues exclude the same value from all other Qback positions. *)
    have no_other_T: "\<not> (\<exists>k. Qback_arr s k = a \<and> k \<noteq> i_var s q)"
      using hI14_Pending_Enq_Qback_Exclusivity_s `HasPendingEnq s q a` q_props(1) unfolding hI14_Pending_Enq_Qback_Exclusivity_def by blast
    
    (* Contradiction: j carries a while being different from the unique pending-enqueue slot. *)
    then show False using T_j_eq_a j_ne_i by blast
  qed
qed

(* ========================================================== *)
(* Multiset preservation for modify_lin permutations           *)
(* ========================================================== *)


lemma mset_modify_eq_case:
  (* Shared assumption: all cases start from the same decomposition of L. *)
  assumes L_decomp: "mset L = mset (l1 @ l2 @ [bt_act] @ l3)"
  shows 
    (* Case 1: only the non-emptiness of l2 is needed. *)
    case1: "l2 \<noteq> [] \<Longrightarrow> mset (l1 @ butlast l2 @ [bt_act] @ [last l2] @ l3) = mset L"
    
    (* Case 2: use a decomposition of l2 together with a non-empty tail l22. *)
    and case2: "\<lbrakk> l2 = l21 @ [b_act] @ l22; l22 \<noteq> []; o1 = hd l22 \<rbrakk> \<Longrightarrow> 
                mset (l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3) = mset L"
    
    (* Case 3: only the decomposition of l2 is needed. *)
    and case3: "\<lbrakk> l2 = l21 @ [b_act] @ l22 \<rbrakk> \<Longrightarrow> 
                mset (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) = mset L"
    
    (* Case 4: use a decomposition of l2 together with a non-empty tail and ou = last l22. *)
    and case4: "\<lbrakk> l2 = l21 @ [b_act] @ l22; l22 \<noteq> []; ou = last l22 \<rbrakk> \<Longrightarrow> 
                mset (l1 @ l21 @ [b_act] @ butlast l22 @ [bt_act] @ [ou] @ l3) = mset L"
    
    (* Case 5: again only the decomposition of l2 is needed. *)
    and case5: "\<lbrakk> l2 = l21 @ [b_act] @ l22 \<rbrakk> \<Longrightarrow> 
                mset (l1 @ l21 @ l22 @ [bt_act] @ [b_act] @ l3) = mset L"
proof -
  (* Proof of Case 1. *)
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
  
  (* Proof of Case 2. *)
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
  
  (* Proof of Case 3. *)
  {
    assume "l2 = l21 @ [b_act] @ l22"
    have "mset (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) = mset L"
      using L_decomp `l2 = l21 @ [b_act] @ l22` by (simp add: ac_simps)
    then show "mset (l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3) = mset L" .
  }
  
  (* Proof of Case 4. *)
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
  
  (* Proof of Case 5. *)
  {
    assume "l2 = l21 @ [b_act] @ l22"
    have "mset (l1 @ l21 @ l22 @ [bt_act] @ [b_act] @ l3) = mset L"
      using L_decomp `l2 = l21 @ [b_act] @ l22` by (simp add: ac_simps)
    then show "mset (l1 @ l21 @ l22 @ [bt_act] @ [b_act] @ l3) = mset L" .
  }
qed

(* If find_unique_index returns Some idx, then idx is a valid list position. *)
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
  
  (* Step 1: check whether modify_lin actually enters the rewriting branch. *)
  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    (* Base case: no modification is performed, so the claim is immediate. *)
    then show ?thesis by (subst modify_lin.simps, simp)
  next
    case True
    (* Inductive step: analyze the branch that performs a reordering. *)
    note do_modify = True
    
    (* Step 2: introduce the local abbreviations used by modify_lin. *)
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define remaining where "remaining = drop (nat (last_sa_pos + 1)) L"
    
    (* Show that bt_idx exists, so that the later use of the definite choice is justified. *)
    have idx_exists: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining \<noteq> None"
      using True unfolding should_modify_def last_sa_pos_def remaining_def by (metis option.simps(4))
    
    obtain bt_idx where bt_idx_def: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining = Some bt_idx"
      using idx_exists by blast

    (* Prove that the computed index passes the bounds check. *)
    have bt_idx_valid: "bt_idx < length remaining"
      using bt_idx_def by (rule find_unique_index_Some_less_length)

    define l1 where "l1 = take (nat (last_sa_pos + 1)) L"
    define l2 where "l2 = take bt_idx remaining"
    define l3 where "l3 = drop (bt_idx + 1) remaining"
    define bt_act where "bt_act = remaining ! bt_idx"


    (* Step 3: prove that l2 is non-empty. *)
    have l2_not_nil: "l2 \<noteq> []"
    proof (cases "l2 = []")
      case True
      (* Step 3A: first show that the suffix remaining is non-empty. *)
      (* Include find_unique_index.simps so that the empty-list case reduces to None. *)
      have "remaining \<noteq> []"
        using bt_idx_def
        apply (cases remaining)
         apply (auto simp: find_unique_index_def)
        using bt_idx_def find_unique_index_Some_less_length by force

      (* Step 3B: use the library lemma take_eq_Nil. *)
      have "bt_idx = 0" 
        using True l2_def `remaining \<noteq> []`
        by (metis take_eq_Nil)
        
      (* Step 3C: derive the contradiction. *)
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

    (* Step 4: classify according to the last operation occurring in l2. *)
    show ?thesis
    proof (cases "op_name l2_last = enq")
      
      (* Case A: the last operation of l2 is an enqueue. *)
      case True
      
      (* Define the updated list produced by this branch. *)
      define new_L where "new_L = l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3"
      
      (* Step A.1: show that the recursive call has the expected argument. *)
      have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
      proof -
        have "modify_lin L H bt_val = modify_lin (l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3) H bt_val"
          (* Unfold modify_lin together with the local definitions. *)
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def do_modify True
          apply (subst modify_lin.simps) (* Unfold the recursive definition. *)
          apply (simp only: Let_def case_prod_unfold) (* Eliminate the Let-bound abbreviations. *)
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
      
      (* Step A.2: prove multiset preservation for the local permutation. *)
      have mset_eq: "mset new_L = mset L"
        unfolding new_L_def l2_last_def (* Unfold the abbreviations so that last l2 becomes explicit. *)
        apply (rule mset_modify_eq_case(1)[OF L_decomp])
        by (simp add: l2_not_nil)

      (* Combine the local equality with the induction hypothesis. *)
      show ?thesis 
        using mod_eq mset_eq 1(1) True do_modify 
        (* Expand new_L back to the primitive list expression to match the induction hypothesis. *)
        unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        using bt_idx_def 
        by (metis last_sa_pos_def option.sel remaining_def)

    next
      
      (* Case B: the last operation of l2 is not an enqueue. *)
      case False
      note not_enq = False
      
      (* Show that find_last_enq returns a non-empty list. *)
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


      (* Key strategy: split the nested conditionals with consider to avoid a large monolithic proof. *)
      (* This mirrors the structure of the current modify_lin definition and keeps the proof modular. *)
      consider 
          (c1) "happens_before o1 bt_act H" 
        | (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H"
        | (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast
          
      then show ?thesis
      proof cases
        (* Subcase 1. *)
        case c1 
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"

        (* Step 1: prove that l22 is non-empty. *)
        have l22_not_nil: "l22 \<noteq> []"
          using do_modify not_enq l2_last_def 
          using l2_split l2_not_nil
          unfolding find_last_enq_def
          using l2_def remaining_def
          by (metis find_last_enq_props(1,2) l2_split last_snoc self_append_conv)        


        (* Step 2: identify the recursive argument passed to modify_lin. *)
        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c1 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)

        (* Step 3: show multiset preservation for this permutation. *)
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

        (* Step 4: conclude by combining the local result with the induction hypothesis. *)
        show ?thesis 
          using mod_eq perm_eq      
          using 1                   
          using c1 False do_modify l2_split bt_idx_def 
          using l22_not_nil          
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (no_types, lifting) option.sel)

      next
        (* Subcase 2. *)
        case c2
        define new_L where "new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3"
        
        (* Step 1: show the equality of the recursive call. *)
        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c2 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)

        (* Step 2: show multiset preservation. *)
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

        (* Step 3: conclude the branch. *)
        show ?thesis 
          using perm_eq mod_eq
          using 1(3)            
          using c2 False do_modify l2_split bt_idx_def
          unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def o1_def ou_def
          by (metis (no_types, lifting) option.sel)

      next
        (* Subcase 3: the additional else-if branch for \<not> happens_before b_act o1 H. *)
        case c3
        (* This branch swaps o1 and b_act, just as in Subcase 1. *)
        define new_L where "new_L = l1 @ l21 @ [o1] @ [b_act] @ tl l22 @ [bt_act] @ l3"
        
        (* Step 1: prove that l22 is non-empty. *)
        have l22_not_nil: "l22 \<noteq> []"
          using do_modify not_enq l2_last_def 
          using l2_split l2_not_nil
          unfolding find_last_enq_def
          using l2_def remaining_def
          by (metis find_last_enq_props(1,2) l2_split last_snoc self_append_conv)

        (* Step 2: identify the recursive argument passed to modify_lin. *)
        have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
          unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
          using bt_idx_def l2_split c3 False do_modify o1_def ou_def
          apply (subst modify_lin.simps)
          apply (simp only: Let_def case_prod_unfold)
          apply (subst if_not_P, simp)
          by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
              last_sa_pos_def new_L_def remaining_def)

        (* Step 3: prove multiset preservation by reusing the Subcase 1 pattern. *)
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

        (* Step 4: conclude using the corresponding induction hypothesis. *)
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


(* ========================================================== *)
(* Data-independence preservation for modify_lin              *)
(* ========================================================== *)

lemma modify_preserves_data_independent:
  assumes "data_independent L"
  shows "data_independent (modify_lin  L H v)"
proof -
  have "mset (modify_lin  L H v) = mset L"
    by (rule modify_preserves_mset)
  then show ?thesis
    using data_independent_cong assms by blast
qed

(* ========================================================== *)
(* Excluding dequeue witnesses for values that still belong to SetB *)
(* ========================================================== *)

(* This lemma is a key ingredient for the uniqueness part of lI2_Op_Cardinality. *)
lemma SetB_implies_no_deq_in_lin:
  assumes "system_invariant s"
  assumes "x \<in> SetB s"
  shows "DeqIdxs s x = {}"
proof (rule ccontr)
  assume "DeqIdxs s x \<noteq> {}"
  then obtain k where k_in: "k \<in> DeqIdxs s x" by blast
  
  (* Step 1: extract the invariants used by the argument. *)
  have lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and typeOK_s: "TypeOK s"
    using assms(1) unfolding system_invariant_def by auto

  (* Step 2: unfold the meaning of membership in DeqIdxs. *)
  have k_bound: "k < length (lin_seq s)" 
   and act_deq: "op_name (lin_seq s ! k) = deq" 
   and op_val: "op_val (lin_seq s ! k) = x"
    using k_in unfolding DeqIdxs_def by auto

  let ?act = "lin_seq s ! k"
  have "?act \<in> OPLin s" 
    unfolding OPLin_def using k_bound by auto

  (* Step 3: classify ?act with lI1_Op_Sets_Equivalence. *)
  have "?act \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_Op_Sets_Equivalence_s `?act \<in> OPLin s` unfolding lI1_Op_Sets_Equivalence_def by blast
    
  (* Step 4: immediately exclude the enqueue classes, since ?act is a dequeue action. *)
  moreover have "?act \<notin> OP_A_enq s"
    unfolding OP_A_enq_def using act_deq
    using SetB_implies_no_deq_in_lin op_val assms(1,2) k_bound
    by auto
    
  moreover have "?act \<notin> OP_B_enq s"
    unfolding OP_B_enq_def using act_deq
    using SetB_implies_no_deq_in_lin op_val assms(1,2) k_bound
    by auto 
    
  (* Step 5: conclude that ?act must belong to OP_A_deq. *)
  ultimately have "?act \<in> OP_A_deq s" by blast

  (* Step 6: infer x \<in> SetA from the OP_A_deq classification. *)
  then obtain p a sn where "?act = mk_op deq a p sn" "a \<in> SetA s"
    unfolding OP_A_deq_def
    using OPLin_def SetB_implies_no_deq_in_lin op_val assms(1,2)
    by blast 
    
  have "a = x" 
    using `?act = mk_op deq a p sn` op_val unfolding mk_op_def op_val_def by simp
    
  hence "x \<in> SetA s" using `a \<in> SetA s` by simp

  (* Step 7: derive the contradiction from the disjointness of SetA and SetB. *)
  have "SetA s \<inter> SetB s = {}"
  proof -
    (* In the current encoding, disjointness of SetA and SetB follows from the QHas/InQBack split in TypeOK. *)
    (* We therefore finish by unfolding the relevant definitions directly. *)
    have "\<forall>v. v \<in> SetA s \<longrightarrow> \<not> QHas s v"
      unfolding SetA_def
      by (simp add: TypeA_def) 
    moreover have "\<forall>v. v \<in> SetB s \<longrightarrow> QHas s v \<or> (\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = v)"
      unfolding SetB_def
      by (simp add: TypeB_def) 
      
    show ?thesis 
    proof (rule equals0I)
      fix v assume "v \<in> SetA s \<inter> SetB s"
      hence "v \<in> SetA s" "v \<in> SetB s" by auto
      hence not_Q: "\<not> QHas s v" and B_cond: "QHas s v \<or> (\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = v)"
        using `\<forall>v. v \<in> SetA s \<longrightarrow> \<not> QHas s v` `\<forall>v. v \<in> SetB s \<longrightarrow> QHas s v \<or> (\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = v)`
        by auto
        
      (* If v is not in Q, then some E2 process must currently hold it. *)
      from B_cond not_Q obtain p where "program_counter s p = ''E2''" "v_var s p = v" by auto
      
      (* Use the E2 invariant stating that the designated Qback slot is still BOT. *)
      have sI2_X_var_Upper_Bound_2_s: "sI2_X_var_Upper_Bound_2 s" using assms(1) unfolding system_invariant_def
        using SetB_implies_no_deq_in_lin act_deq op_val assms(1,2) k_bound
          nth_mem by blast 
      have "Qback_arr s (i_var s p) = BOT" 
        using sI2_X_var_Upper_Bound_2_s `program_counter s p = ''E2''`
        using OPLin_def SetB_implies_no_deq_in_lin \<open>lin_seq s ! k \<in> OPLin s\<close>
          act_deq op_val assms(1,2) by blast 
        
      (* Use the pending-enqueue history invariant attached to E2. *)
      have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using assms(1) unfolding system_invariant_def by auto
      have "HasPendingEnq s p v" 
        using hI1_E_Phase_Pending_Enq_s `program_counter s p = ''E2''` `v_var s p = v` unfolding hI1_E_Phase_Pending_Enq_def by blast
        
      (* Pending-enqueue exclusivity prevents the same value from appearing at another Qback position. *)
      have hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" using assms(1) unfolding system_invariant_def by auto
      have no_other_v: "\<not> (\<exists>k. Qback_arr s k = v \<and> k \<noteq> i_var s p)"
        using hI14_Pending_Enq_Qback_Exclusivity_s `HasPendingEnq s p v` `program_counter s p = ''E2''` unfolding hI14_Pending_Enq_Qback_Exclusivity_def by simp
        
      (* But v \<in> SetA also places v in InQBack, i.e. at some valid Qback position. *)
      have "InQBack s v" using `v \<in> SetA s` unfolding SetA_def
        using OPLin_def SetB_implies_no_deq_in_lin \<open>lin_seq s ! k \<in> OPLin s\<close>
          act_deq op_val assms(1,2) by auto 
      then obtain k where "Qback_arr s k = v" unfolding InQBack_def by blast
      
      (* Contradiction: the only possible slot is forced to be BOT, while v occupies a valid Qback position. *)
      have "v \<in> Val" using `v \<in> SetA s` unfolding SetA_def by simp
      hence "v \<noteq> BOT" unfolding Val_def BOT_def by auto
      
      have "k \<noteq> i_var s p" using `Qback_arr s k = v` `Qback_arr s (i_var s p) = BOT` `v \<noteq> BOT` by auto
      
      thus False using `Qback_arr s k = v` no_other_v by blast
    qed
  qed

  (* Step 8: close the contradiction proof. *)
  thus False using `x \<in> SetA s` assms(2) by blast
qed


(* ========================================================== *)
(* HB consistency under an adjacent swap                       *)
(* ========================================================== *)
lemma HB_swap_adjacent:
  assumes consistent_L1: "HB_consistent (pre @ [a] @ [b] @ post) H"
  assumes not_HB_ab: "\<not> HB H a b"
  shows "HB_consistent (pre @ [b] @ [a] @ post) H"
proof -
  (* Step 1: introduce the local abbreviations. *)
  let ?L1 = "pre @ [a] @ [b] @ post"
  let ?L2 = "pre @ [b] @ [a] @ post"
  let ?k = "length pre"
  
  (* Step 2: define the index-mapping function. *)
  let ?f = "\<lambda>idx. if idx = ?k then ?k + 1 else if idx = ?k + 1 then ?k else idx"

  (* Step 3: prove the basic properties of the mapping. *)
  have eq_nth: "\<And>idx. idx < length ?L2 \<Longrightarrow> ?L2 ! idx = ?L1 ! (?f idx)"
  proof -
    fix idx assume "idx < length ?L2"
    consider "idx < ?k" | "idx = ?k" | "idx = ?k + 1" | "idx > ?k + 1" by linarith
    then show "?L2 ! idx = ?L1 ! (?f idx)" 
      by cases (simp_all add: nth_append)
  qed

  (* Step 4: unfold the consistency definition and start the main proof. *)
  show ?thesis
    unfolding HB_consistent_def
  proof (intro allI impI)
    (* Introduce the quantified indices and hypotheses. *)
    fix i j
    assume valid_and_hb: "i < length ?L2 \<and> j < length ?L2 \<and> HB H (?L2 ! i) (?L2 ! j)"
    
    (* Decompose the assumptions. *)
    have valid_i: "i < length ?L2" using valid_and_hb by simp
    have valid_j: "j < length ?L2" using valid_and_hb by simp
    have hb_ij: "HB H (?L2 ! i) (?L2 ! j)" using valid_and_hb by simp

    (* The remaining argument follows the core index-order reasoning. *)

    (* Step 4.1: transport the HB fact through the mapping. *)
    have hb_mapped: "HB H (?L1 ! (?f i)) (?L1 ! (?f j))"
      using hb_ij eq_nth[OF valid_i] eq_nth[OF valid_j] by simp

    (* Step 4.2: use the consistency of L1 to obtain the mapped index order. *)
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

    (* Step 4.3: prove i < j by contradiction. *)
    show "i < j"
    proof (rule ccontr)
      assume "\<not> i < j" 
      hence "j \<le> i" by simp
      
      (* Analyze the only conflicting arrangement. *)
      have "i \<noteq> ?k + 1 \<or> j \<noteq> ?k"
      proof (rule ccontr)
        (* Assume the bad configuration i = k + 1 and j = k. *)
        assume "\<not> (i \<noteq> ?k + 1 \<or> j \<noteq> ?k)"
        hence conflict_case: "i = ?k + 1 \<and> j = ?k" by simp
        
        (* Compute the corresponding entries of L2. *)
        (* At i = k + 1 we read a, and at j = k we read b. *)
        (* Recall that L2 has the local shape [..., b, a, ...]. *)
        have "HB H a b" 
          using conflict_case hb_ij 
          by (simp add: nth_append) (* The index arithmetic now yields L2 ! i = a and L2 ! j = b. *)

        (* This contradicts the assumption \<not> HB H a b. *)
        thus False using not_HB_ab by simp
      qed
      
      (* Alternatively, derive the contradiction from monotonicity of the mapping. *)
      have "?f j \<le> ?f i" 
        using `j \<le> i` `i \<noteq> ?k + 1 \<or> j \<noteq> ?k` 
        by (auto split: if_splits)
        
      thus False using f_i_less_f_j by simp
    qed
  qed
qed

(* ========================================================== *)
(* HB consistency under a left jump                            *)
(* ========================================================== *)
lemma HB_jump_left:
  assumes consistent_L1: "HB_consistent (pre @ middle @ [x] @ post) H"
  assumes not_HB_middle_x: "\<forall>m \<in> set middle. \<not> HB H m x" (* This side condition rules out forbidden HB edges into x. *)
  shows "HB_consistent (pre @ [x] @ middle @ post) H"
proof -
  (* Step 1: introduce the local abbreviations. *)
  let ?L1 = "pre @ middle @ [x] @ post"
  let ?L2 = "pre @ [x] @ middle @ post"
  let ?k = "length pre"
  let ?mid_len = "length middle"

  (* Step 2: define the index map f from L2 back to L1. *)
  (* L2 has the shape [pre][x][middle][post]. *)
  (* Index layout in L2. *)
  (* L1 has the shape [pre][middle][x][post]. *)
  (* Index layout in L1. *)
  
  let ?f = "\<lambda>idx. if idx < ?k then idx 
                  else if idx = ?k then ?k + ?mid_len 
                  else if idx \<le> ?k + ?mid_len then idx - 1 
                  else idx"

  (* Step 3: prove the basic properties of the mapping. *)
  have eq_nth: "\<And>idx. idx < length ?L2 \<Longrightarrow> ?L2 ! idx = ?L1 ! (?f idx)"
  proof -
    fix idx assume "idx < length ?L2"
    consider "idx < ?k" | "idx = ?k" | "idx > ?k \<and> idx \<le> ?k + ?mid_len" | "idx > ?k + ?mid_len" 
      by linarith
then show "?L2 ! idx = ?L1 ! (?f idx)"
    proof cases
      case 1 (* Case idx < k. *)
      then show ?thesis by (simp add: nth_append)
    next
      case 2 (* Case idx = k. *)
      then show ?thesis by (simp add: nth_append)
    next
      case 3 (* Case k < idx \<le> k + mid_len. *)
      (* This is the delicate range where explicit index calculations are needed. *)
      
      (* Step 3.1: compute ?L2 ! idx. *)
      (* Expand ?L2 into pre @ [x] @ middle @ post. *)
      (* Here idx skips pre and x, and falls into middle. *)
      (* Therefore ?L2 ! idx is read from middle. *)
      have "idx > length pre" using 3 by simp
      have idx_in_mid_L2: "idx - (length pre + 1) < length middle" 
        using 3 by arith
      
      have lhs: "?L2 ! idx = middle ! (idx - (length pre + 1))"
        using 3
        by (metis (mono_tags, lifting) Cons_eq_appendI append_self_conv2
            diff_diff_left idx_in_mid_L2 nat_less_le nth_Cons_pos nth_append_left
            nth_append_right zero_less_diff) 

      (* Step 3.2: compute ?L1 ! (?f idx). *)
      (* In this range, f idx = idx - 1. *)
      (* Expand ?L1 into pre @ middle @ [x] @ post. *)
      (* The shifted index is still beyond pre. *)
      (* And it still points inside middle. *)
      let ?idx' = "idx - 1"
      have "?idx' \<ge> length pre" using 3 by arith
      have idx_in_mid_L1: "?idx' - length pre < length middle" 
        using 3 by arith

      have rhs: "?L1 ! ?idx' = middle ! (?idx' - length pre)"
        using 3
        by (metis \<open>length pre \<le> idx - 1\<close> idx_in_mid_L1 nth_append_left
            nth_append_right)
      
      (* Step 3.3: show that the two local indices coincide. *)
      (* Compare idx - (k + 1) with idx - 1 - k. *)
      have "idx - (length pre + 1) = ?idx' - length pre"
        using 3 by arith
        
      show ?thesis 
        using lhs rhs 3 by simp
    next
      case 4 (* Case idx > k + mid_len. *)
      then show ?thesis by (simp add: nth_append)
    qed
  qed

  (* Step 4: prove HB consistency for the reordered list. *)
  show ?thesis
    unfolding HB_consistent_def
  proof (intro allI impI)
    fix i j
    assume valid_and_hb: "i < length ?L2 \<and> j < length ?L2 \<and> HB H (?L2 ! i) (?L2 ! j)"
    
    (* Decompose the assumptions. *)
    have valid_i: "i < length ?L2" using valid_and_hb by simp
    have valid_j: "j < length ?L2" using valid_and_hb by simp
    have hb_ij: "HB H (?L2 ! i) (?L2 ! j)" using valid_and_hb by simp

    (* Step 4.1: map the HB relation back to L1. *)
    have hb_mapped: "HB H (?L1 ! (?f i)) (?L1 ! (?f j))"
      using hb_ij eq_nth[OF valid_i] eq_nth[OF valid_j] by simp

    (* Step 4.2: derive f i < f j from the consistency of L1. *)
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

    (* Step 4.3: prove i < j by contradiction. *)
    show "i < j"
    proof (rule ccontr)
      assume "\<not> i < j" 
      hence "j \<le> i" by simp
      
      (* Analyze the only possible forbidden inversion. *)
      (* The only dangerous case is when j points to x and i points into middle. *)
      (* This is exactly the inversion created by moving x to the left. *)
      
      have "\<not> (j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len)"
      proof
        assume conflict: "j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len"
        (* In this situation, L2 ! j = x and L2 ! i comes from middle. *)
        let ?m = "?L2 ! i"
        
        (* Show that the selected element ?m indeed lies in middle. *)
        have "?m \<in> set middle"
        proof -
          (* Step 4.3.1: compute the local middle index explicitly. *)
          (* In L2, i lies after pre and the distinguished element x. *)
          (* Hence the middle block starts at index k + 1. *)
          let ?local_idx = "i - (?k + 1)"

          (* Step 4.3.2: prove that the local index is within bounds. *)
          (* This follows from the conflict assumptions. *)
          have in_bounds: "?local_idx < length middle"
            using conflict by arith

          (* Step 4.3.3: identify L2 ! i as middle ! local_idx. *)
          (* Since i > k, the lookup has passed both pre and x. *)
          have match: "?L2 ! i = middle ! ?local_idx"
            using conflict in_bounds 
            by (simp add: nth_append)

          (* Step 4.3.4: use nth_mem to place the element in set middle. *)
          show ?thesis
            unfolding match
            using in_bounds by (rule nth_mem)
        qed
          
        (* The HB assumption now yields HB H m x. *)
        (* And L2 ! j is exactly x. *)
        have "HB H ?m x" using hb_ij conflict by (simp add: nth_append)
        
        (* This contradicts not_HB_middle_x. *)
        thus False using not_HB_middle_x `?m \<in> set middle` by blast
      qed
      
      (* Outside the conflict case, f is weakly monotone. *)
      (* Concretely, j \<le> i implies f j \<le> f i. *)
      have "j \<le> i \<Longrightarrow> \<not> (j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len) \<Longrightarrow> ?f j \<le> ?f i"
        by (auto split: if_splits)
        
      (* Combined with f i < f j, this yields the contradiction. *)
      hence "?f j \<le> ?f i" using `j \<le> i` `\<not> (j = ?k \<and> i > ?k \<and> i \<le> ?k + ?mid_len)` by simp
      thus False using f_i_less_f_j by simp
    qed
  qed
qed


(* ========================================================== *)
(* HB consistency under a right jump                           *)
(* ========================================================== *)
lemma HB_jump_right:
  assumes consistent_L1: "HB_consistent (pre @ [x] @ middle @ post) H"
  assumes not_HB_x_middle: "\<forall>m \<in> set middle. \<not> HB H x m" (* This side condition rules out forbidden HB edges into x. *)
  shows "HB_consistent (pre @ middle @ [x] @ post) H"
proof -
  (* Step 1: introduce the local abbreviations. *)
  let ?L1 = "pre @ [x] @ middle @ post"
  let ?L2 = "pre @ middle @ [x] @ post"
  let ?k = "length pre"
  let ?mid_len = "length middle"

  (* Step 2: define the index map f from L2 back to L1. *)
  (* L2 has the shape [pre][middle][x][post]. *)
  (* Index layout in L2. *)
  (* L1 has the shape [pre][x][middle][post]. *)
  (* Index layout in L2. *)
  
  let ?f = "\<lambda>idx. if idx < ?k then idx 
                  else if idx = ?k + ?mid_len then ?k 
                  else if idx < ?k + ?mid_len then idx + 1 
                  else idx"

  (* Step 3: prove the basic properties of the mapping. *)
  have eq_nth: "\<And>idx. idx < length ?L2 \<Longrightarrow> ?L2 ! idx = ?L1 ! (?f idx)"
  proof -
    fix idx assume "idx < length ?L2"
    consider "idx < ?k" | "idx \<ge> ?k \<and> idx < ?k + ?mid_len" | "idx = ?k + ?mid_len" | "idx > ?k + ?mid_len" 
      by linarith
    then show "?L2 ! idx = ?L1 ! (?f idx)"
    proof cases
      case 1 then show ?thesis by (simp add: nth_append)
    next
      case 2 (* Case: idx lies inside the middle block. *)
      (* Goal: ?L2 ! idx = ?L1 ! (idx + 1). *)
      
      (* Step 3.1: compute ?L2 ! idx. *)
      (* Expand ?L2 into pre @ middle @ ... *)
      (* Since idx \<ge> k, the local offset is idx - k. *)
      (* The bound idx < k + mid_len shows that the lookup stays in middle. *)
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

      (* Step 3.3: compare the local indices. *)
      have "idx - ?k = ?idx_plus_1 - (?k + 1)" by arith
      
      show ?thesis using l2_val l1_val `idx - ?k = ?idx_plus_1 - (?k + 1)`
        by (smt (verit, ccfv_threshold) "2" leD not_less_iff_gr_or_eq) 
    next
      case 3 then show ?thesis by (simp add: nth_append)
    next
      case 4 then show ?thesis by (simp add: nth_append)
    qed
  qed

  (* Step 4: prove HB consistency for the reordered list. *)
  show ?thesis
    unfolding HB_consistent_def
  proof (intro allI impI)
    fix i j
    assume valid_and_hb: "i < length ?L2 \<and> j < length ?L2 \<and> HB H (?L2 ! i) (?L2 ! j)"
    
    have valid_i: "i < length ?L2" using valid_and_hb by simp
    have valid_j: "j < length ?L2" using valid_and_hb by simp
    have hb_ij: "HB H (?L2 ! i) (?L2 ! j)" using valid_and_hb by simp

    (* Step 4.1: map the HB relation back to L1. *)
    have hb_mapped: "HB H (?L1 ! (?f i)) (?L1 ! (?f j))"
      using hb_ij eq_nth[OF valid_i] eq_nth[OF valid_j] by simp

    (* Step 4.2: derive f i < f j from the consistency of L1. *)
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

    (* Step 4.3: prove i < j by contradiction. *)
    show "i < j"
    proof (rule ccontr)
      assume "\<not> i < j" 
      hence "j \<le> i" by simp
      
      (* Analyze the only possible forbidden inversion. *)
      (* The only dangerous case is when i points to x and j points into middle. *)
      (* This is the inversion created by moving x to the right. *)
      
      have "\<not> (i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len)"
      proof
        assume conflict: "i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len"
        (* In this situation, L2 ! i = x and L2 ! j comes from middle. *)
        let ?m = "?L2 ! j"
        
        (* Show that the selected element ?m indeed lies in middle. *)
        (* A short explicit index argument is enough here. *)
        have mid_idx: "j - ?k < length middle" using conflict by arith
        have m_is_mid: "?m = middle ! (j - ?k)"
          using conflict mid_idx by (simp add: nth_append)
          
        have "?m \<in> set middle"
          unfolding m_is_mid using mid_idx by (rule nth_mem)
          
        (* The HB assumption now yields HB H x m. *)
        (* And L2 ! i is exactly x. *)
        have "HB H x ?m" using hb_ij conflict by (simp add: nth_append)
        
        (* This contradicts not_HB_x_middle. *)
        thus False using not_HB_x_middle `?m \<in> set middle` by blast
      qed
      
      (* Outside the conflict case, f is weakly monotone. *)
      (* Concretely, j \<le> i implies f j \<le> f i. *)
      have "j \<le> i \<Longrightarrow> \<not> (i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len) \<Longrightarrow> ?f j \<le> ?f i"
        by (auto split: if_splits)
        
      (* Combined with f i < f j, this yields the contradiction. *)
      hence "?f j \<le> ?f i" using `j \<le> i` `\<not> (i = ?k + ?mid_len \<and> j \<ge> ?k \<and> j < ?k + ?mid_len)` by simp
      thus False using f_i_less_f_j by simp
    qed
  qed
qed


(* ========== No-HB consequences for TypeBT and active enqueue values ========== *)

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
proof (rule notI) (* Step 1: start with contradiction, following the existing proof style. *)
  
  (* Step 2: introduce the negated goal explicitly. *)
  assume hb: "HB_Act s x bt_act"

  (* Step 3: prepare the local invariants and abbreviations. *)
  from sys_inv have hi8: "hI16_BO_BT_No_HB s" unfolding system_invariant_def by auto
  from sys_inv have hi9: "hI17_BT_BT_No_HB s" unfolding system_invariant_def by auto
  let ?v = "op_val x"
  let ?bt_v = "op_val bt_act"
  
  have bt_in_SetBT: "?bt_v \<in> SetBT s" 
    using type_bt bt_val_valid unfolding SetBT_def by simp

  (* Step 4: establish the required HB_EnqRetCall fact. *)
  (* This version works directly from HB_Act and avoids unnecessary witness extraction. *)
  have val_hb: "HB_EnqRetCall s ?v ?bt_v"
  proof -
    (* Under the current definition, HB_EnqRetCall only needs a matching HB_Act witness. *)
    (* The assumption hb already provides the HB_Act instance. *)
    (* It remains to show that x and bt_act have the required mk_op enqueue shape. *)
    
    show ?thesis
      unfolding HB_EnqRetCall_def
      apply (rule exI[where x="op_pid x"])
      apply (rule exI[where x="op_pid bt_act"])
      using hb x_is_enq bt_is_enq
      (* A direct unfolding is sufficient here. *)
      unfolding mk_op_def
      by (metis op_name_def op_pid_def op_val_def split_pairs) 
  qed

  (* Step 5: split according to val_in_sets. *)
  (* The remainder follows the original case split unchanged. *)
  show False
    using val_in_sets
  proof (rule disjE) (* disjE now cleanly splits the SetBO/SetBT alternatives. *)
    
    (* Case 1: x lies in SetBO. *)
    assume in_BO: "op_val x \<in> SetBO s"
    have "\<not> HB_EnqRetCall s ?v ?bt_v"
      using hi8 in_BO bt_in_SetBT unfolding hI16_BO_BT_No_HB_def by blast
    then show False using val_hb by simp
    
  next (* Move to the SetBT branch. *)
  
    (* Case 2: x lies in SetBT. *)
    assume in_BT: "op_val x \<in> SetBT s"
    have "\<not> HB_EnqRetCall s ?v ?bt_v"
      using hi9 in_BT bt_in_SetBT unfolding hI17_BT_BT_No_HB_def by blast
    then show False using val_hb by simp    
  qed
qed 


(* ========================================================== *)
(* Values of enqueue operations in the linearization sequence  *)
(* ========================================================== *)
lemma lin_seq_enq_in_sets:
  assumes INV: "system_invariant s"
  assumes x_in_seq: "x \<in> set (lin_seq s)"
  assumes is_enq: "op_name x = enq"
  shows "op_val x \<in> SetA s \<union> SetB s"
proof -
  (* Step 1: extract lI1_Op_Sets_Equivalence from the system invariant. *)
  have lin_inv: "lI1_Op_Sets_Equivalence s" 
    using INV unfolding system_invariant_def by auto

  (* Step 2: classify the enqueue operation using lI1_Op_Sets_Equivalence. *)
  have "x \<in> OPLin s" 
    using x_in_seq unfolding OPLin_def by simp
  
  then have x_union: "x \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lin_inv unfolding lI1_Op_Sets_Equivalence_def by simp

  (* Step 3: exclude OP_A_deq immediately, since we are analyzing an enqueue operation. *)
  have "x \<notin> OP_A_deq s"
    unfolding OP_A_deq_def using is_enq
    by simp 
  
  then have x_source: "x \<in> OP_A_enq s \<union> OP_B_enq s"
    using x_union by blast

  (* Step 4: extract the correct 4-tuple structure from the remaining cases. *)
  show ?thesis
  proof (cases "x \<in> OP_A_enq s")
    case True
    (* Match the current 4-tuple representation (op, val, pid, sn). *)
    then obtain p a sn where "x = mk_op enq a p sn" "a \<in> SetA s"
      unfolding OP_A_enq_def by blast
      
    (* Read off op_val directly. *)
    then have "op_val x = a" 
      unfolding mk_op_def op_val_def by simp
      
    thus ?thesis using `a \<in> SetA s` by blast
  next
    case False
    (* If the action is not in OP_A_enq, it must be in OP_B_enq. *)
    with x_source have "x \<in> OP_B_enq s" by blast
    
    (* Extract the symmetric 4-tuple shape from OP_B_enq. *)
    then obtain p b sn where "x = mk_op enq b p sn" "b \<in> SetB s"
      unfolding OP_B_enq_def by blast
      
    (* Read off op_val directly. *)
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
  (* Step 1: use lin_seq_enq_in_sets to place the value of a in SetA \<union> SetB. *)
  have val_range: "op_val a \<in> SetA s \<union> SetB s"
    using lin_seq_enq_in_sets[OF INV a_in_seq is_enq] .

  (* Step 2: exclude SetA using the assumption op_val a \<notin> SetA s. *)
  have "op_val a \<in> SetB s"
    using val_range not_in_SetA by auto

  (* Step 3: refine SetB membership into SetBO \<union> SetBT. *)
  then show ?thesis
    unfolding SetB_partition by auto
qed

lemma TypeBT_No_HB_Target:
  (* Context assumptions. *)
  assumes INV: "system_invariant s"
  assumes L_def: "L = lin_seq s"
  assumes H_def: "H = his_seq s"
  
  (* Properties of the distinguished action bt_act. *)
  assumes bt_in_L: "bt_act \<in> set L" 
  assumes bt_is_enq: "op_name bt_act = enq"
  assumes bt_is_TypeBT: "TypeBT s (op_val bt_act)"
  
  (* Properties of the comparison action a. *)
  assumes a_in_L: "a \<in> set L"
  assumes a_is_enq: "op_name a = enq"
  assumes a_not_bt: "a \<noteq> bt_act"
  
  (* Key restriction: a must lie in the active enqueue region. *)
  assumes a_not_SetA: "op_val a \<notin> SetA s"
  
  (* Target conclusion: a cannot happen-before bt_act. *)
  shows "\<not> HB H a bt_act"
proof (rule notI)
  (* Assume the contrary HB relation. *)
  assume hb_rel: "HB H a bt_act"

  (* Step 1: show that the value of a lies in SetBO or SetBT. *)
  have val_in_sets: "op_val a \<in> SetBO s \<or> op_val a \<in> SetBT s"
  proof -
    (* Since a is an enqueue in the linearization, its value is in SetA \<union> SetB. *)
    (* The assumption excludes SetA, so the value must be in SetB. *)
    (* Finally, split SetB into SetBO \<union> SetBT. *)
    
    (* We carry this out through lI1_Op_Sets_Equivalence and the OP-set definitions. *)
    have "op_val a \<in> SetA s \<union> SetB s" 
      using INV a_in_L a_is_enq 
      unfolding system_invariant_def lI1_Op_Sets_Equivalence_def OP_A_enq_def OP_B_enq_def OPLin_def L_def
      using INV lin_seq_enq_in_sets by blast

    thus ?thesis 
      using a_not_SetA 
      unfolding SetB_def SetBO_def SetBT_def
      by (simp add: TypeBO_def) 
  qed

  (* Step 2: show that a is an active enqueue action. *)
  have a_is_active: "a \<in> active_enqs s"
  proof -
    (* First note that a is in OPLin. *)
    have "a \<in> OPLin s" using a_in_L unfolding OPLin_def L_def by simp
    
    (* Then classify a through lI1_Op_Sets_Equivalence. *)
    have "a \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
      using INV unfolding system_invariant_def lI1_Op_Sets_Equivalence_def
      using \<open>a \<in> OPLin s\<close> by blast 
      
    (* Exclude the dequeue class. *)
    have "a \<notin> OP_A_deq s" 
      using a_is_enq unfolding OP_A_deq_def mk_op_def op_name_def by auto
      
    (* Exclude OP_A_enq because the value of a is not in SetA. *)
    have "a \<notin> OP_A_enq s"
      using a_not_SetA unfolding OP_A_enq_def mk_op_def op_val_def by auto
      
    (* Hence a belongs to OP_B_enq, i.e. active_enqs. *)
    hence "a \<in> OP_B_enq s" 
      using `a \<in> OPLin s` `a \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s` `a \<notin> OP_A_deq s` 
      by auto
      
    thus ?thesis unfolding active_enqs_def .
  qed

  (* Step 3: show that the value carried by bt_act is valid. *)
  have bt_val_valid: "op_val bt_act \<in> Val"
  proof -
    (* Since bt_act is an enqueue in OPLin, it carries a valid queue value. *)
    have "op_val bt_act \<in> SetA s \<union> SetB s"
      using INV bt_in_L bt_is_enq 
      unfolding system_invariant_def lI1_Op_Sets_Equivalence_def OP_A_enq_def OP_B_enq_def OPLin_def L_def
      using INV lin_seq_enq_in_sets by blast
    thus ?thesis unfolding SetA_def SetB_def by auto
  qed

  (* Step 4: finish with the global lemma TypeBT_implies_no_HB. *)
  (* No additional bridge lemma is needed here: HB H a bt_act already matches the target form. *)
  
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

  (* Step 5: derive the contradiction. *)
  (* hb_rel: HB H a bt_act *)
  (* not_hb: \<not> HB_Act s a bt_act *)
  show False 
    using hb_rel `\<not> HB_Act s a bt_act` H_def 
    unfolding HB_Act_def 
    by simp
qed



(* ========================================================== *)
(* ========================================================== *)
(* Position order contradicts reversed HB dependencies         *)
(* ========================================================== *)
(* ========================================================== *)
lemma pos_order_contra_HB:
  assumes consist: "HB_consistent L H"
  assumes valid_idx: "i < length L" "j < length L"
  assumes at_i: "L ! i = a" 
  assumes at_j: "L ! j = b"
  assumes order: "i < j"
  shows "\<not> HB H b a"
proof (rule notI)
  (* Step 1: assume HB H b a. *)
  assume hb_ba: "HB H b a"
  
  (* Step 2: use HB_consistent to derive the opposite index order. *)
  (* HB_consistent L H \<equiv> \<forall>k1 k2. ... HB H (L!k1) (L!k2) \<longrightarrow> k1 < k2 *)
  (* Instantiate the definition with k1 = j and k2 = i. *)
  have "j < i"
    using consist hb_ba valid_idx at_i at_j
    unfolding HB_consistent_def
    by blast (* blast instantiates the indices and applies the implication automatically. *)
    
  (* Step 3: conclude the contradiction. *)
  thus False using order by simp
qed

lemma SetA_implies_in_SA:
  assumes sys_inv: "system_invariant s"
  assumes a_in_SetA: "a \<in> SetA s"
  shows "in_SA a (lin_seq s)"
proof -
  (* Step 1: extract lI2_Op_Cardinality from the system invariant. *)
  (* lI2_Op_Cardinality gives unique enqueue and dequeue counts for SetA values. *)
  have lI2_Op_Cardinality: "lI2_Op_Cardinality s" 
    using sys_inv unfolding system_invariant_def by auto

  (* Step 2: read off the cardinality constraints from lI2_Op_Cardinality. *)
  (* \<forall>a \<in> SetA s. card (EnqIdxs s a) = 1 \<and> card (DeqIdxs s a) = 1 *)
  have card_enq: "card (EnqIdxs s a) = 1" 
    using lI2_Op_Cardinality a_in_SetA unfolding lI2_Op_Cardinality_def by auto
    
  have card_deq: "card (DeqIdxs s a) = 1" 
    using lI2_Op_Cardinality a_in_SetA unfolding lI2_Op_Cardinality_def by auto

  let ?L = "lin_seq s"

  (* Step 3: show that find_unique_index returns Some for the enqueue witness. *)
  have enq_exists: "find_unique_index (\<lambda>x. op_name x = enq \<and> op_val x = a) ?L \<noteq> None"
  proof -
    let ?P = "\<lambda>x. op_name x = enq \<and> op_val x = a"
    
    (* Step 3.1: connect find_indices with EnqIdxs. *)
    (* find_indices produces a list, whereas EnqIdxs is a set; prove that their set views coincide. *)
    have "set (find_indices ?P ?L) = EnqIdxs s a"
      unfolding find_indices_def EnqIdxs_def 
      (* Use set_filter and set_upt to turn the filtered list into the corresponding set comprehension. *)
      using set_filter[of "\<lambda>i. ?P (?L ! i)" "[0..<length ?L]"]
      by simp
    
    (* Step 3.2: use card = 1 to obtain a singleton list. *)
    moreover have "distinct (find_indices ?P ?L)"
      unfolding find_indices_def by simp
    ultimately have "length (find_indices ?P ?L) = 1"
      using card_enq distinct_card by fastforce
      
    (* Step 3.3: a singleton witness list implies that find_unique_index is not None. *)
    thus ?thesis
      unfolding find_unique_index_def
      by (metis (mono_tags, lifting) emptyE empty_set less_one nth_mem
          option.discI)
  qed

  (* Step 4: prove the corresponding statement for dequeue witnesses. *)
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

  (* Step 5: combine the enqueue and dequeue witnesses to derive in_SA. *)
  show ?thesis
    unfolding in_SA_def
    using enq_exists deq_exists 
    (* Finish by unfolding the option cases in the definition. *)
    by (auto split: option.splits)
qed


(* ============================================================================ *)
(* ========================================================== *)
(* find_unique_index depends only on the underlying multiset   *)
(* ========================================================== *)
(* ============================================================================ *)

lemma find_unique_index_mset_eq:
  assumes "mset L1 = mset L2"
  shows "(find_unique_index P L1 \<noteq> None) \<longleftrightarrow> (find_unique_index P L2 \<noteq> None)"
proof -
  (* Step 1: state an auxiliary characterization of find_unique_index. *)
  have aux: "find_unique_index P L \<noteq> None \<longleftrightarrow> (\<exists>i<length L. P (L ! i))" for L
    unfolding find_unique_index_def find_indices_def Let_def
    by (auto split: if_splits simp: filter_empty_conv)

  (* Step 2: derive equality of the underlying sets. *)
  from assms have set_eq: "set L1 = set L2" by (metis mset_eq_setD)
  
  (* Step 3: prove both directions explicitly with iffI. *)
  show ?thesis
  proof (rule iffI)
    (* Direction 1: L1 -> L2. *)
    assume "find_unique_index P L1 \<noteq> None"
    then obtain i where "i < length L1" "P (L1 ! i)" using aux by blast
    then have "\<exists>a\<in>set L1. P a" using nth_mem by fastforce
    
    with set_eq obtain a where "a \<in> set L2" "P a" by auto
    (* Name the obtained witness j_props for later reuse. *)
    then obtain j where j_props: "j < length L2" "P (L2 ! j)"
      by (metis in_set_conv_nth)
      
    (* After the iffI split, the current subgoal is exactly the desired non-None statement for L2. *)
    show "find_unique_index P L2 \<noteq> None" 
      using aux j_props by auto

  next
    (* Direction 2: L2 -> L1. *)
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


(* in_SA is preserved by list permutations with the same multiset. *)
lemma in_SA_mset_eq:
  assumes "mset L1 = mset L2"
  shows "in_SA v L1 \<longleftrightarrow> in_SA v L2"
proof -
  (* The definition of in_SA only depends on the existence of the two unique witnesses. *)
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
  (* Step 1: show that d belongs to the linearization sequence. *)
  from d_in_l22 have "d \<in> set L" using L_def by auto
  then have d_in_lin: "d \<in> set (lin_seq s)" 
    using inv_mset by (metis mset_eq_setD)

  (* Step 2: show that d is a dequeue operation. *)
  have d_is_deq: "op_name d = deq" 
    using d_in_l22 l22_deqs by auto

  (* Step 3: invoke the validity lemma for dequeue actions in the linearization. *)
  (* That lemma states that any dequeue action occurring in the linearization carries a value from Val. *)
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

  (* Step 1: extract the first HB witness tuple by unfolding the matching predicates. *)
  from hb_d_bt obtain k1 k2 where k12: 
    "k1 < k2" 
    "match_ret H k1 d" 
    "match_call H k2 bt"
    "k1 < length H" "k2 < length H"
    unfolding HB_def match_ret_def match_call_def 
    by auto

  (* Step 2: extract the witness tuple for the second HB relation. *)
  from hb_b_o1 obtain k3 k4 where k34: 
    "k3 < k4" 
    "match_ret H k3 b" 
    "match_call H k4 o1"
    "k3 < length H" "k4 < length H"
    unfolding HB_def match_ret_def match_call_def 
    by auto

  (* Step 3: derive the necessary order relation by contradiction. *)
  have "k2 \<le> k3"
  proof (rule ccontr)
    assume "\<not> k2 \<le> k3"
    hence "k3 < k2" by simp
    (* If k3 < k2, then b would happen-before bt. *)
    with k34(3) k12(5) have "HB H b bt"
      unfolding HB_def
      using k12(3) k34(2) by auto 
    with not_hb_b_bt show False by contradiction
  qed

  (* Step 4: combine the inequalities to get k1 < k4. *)
  hence "k1 < k4"
    using k12(1) k34(1) by linarith

  (* Step 5: construct HB H d o1. *)
  have "HB H d o1"
    unfolding HB_def
    using \<open>k1 < k4\<close> k12(2,4) k34(3,5) by blast

  (* Step 6: use HB consistency to derive the final contradiction. *)
  hence "j < i"
    using hb_cons valid_idxs at_idxs
    unfolding HB_consistent_def by blast
  with order_in_L show False by simp
qed


lemma HB_jump_right_protection:
  assumes hb_cons: "HB_consistent L H"
  (* Positional assumption: d is before ou, or coincides with it. *)
  and valid_idxs: "i < length L" "j < length L"
  and at_idxs: "L ! i = d" "L ! j = ou"
  and order_in_L: "i \<le> j"
  (* HB assumptions. *)
  and c4: "HB H ou bt"           (* ou -> bt *)
  and not_hb_b_bt: "\<not> HB H b bt" (* b does not happen-before bt. *)
  (* Operation-shape assumptions. *)
  and b_enq: "op_name b = enq"
  and bt_enq: "op_name bt = enq"
  and d_deq: "op_name d = deq"
  and ou_deq: "op_name ou = deq"
  shows "\<not> HB H b d"
proof
  assume hb_b_d: "HB H b d"

  (* Step 1: extract the witness indices for ou -> bt using match_ret and match_call. *)
  obtain k_ou_ret k_bt_call where ou_bt:
    "k_ou_ret < k_bt_call"
    "match_ret H k_ou_ret ou"
    "match_call H k_bt_call bt"
    using c4 unfolding HB_def by blast

  (* Step 2: extract the witness indices for b -> d. *)
  obtain k_b_ret k_d_call where b_d:
    "k_b_ret < k_d_call"
    "match_ret H k_b_ret b"
    "match_call H k_d_call d"
    using hb_b_d unfolding HB_def by blast

  (* Step 3: prove that bt.call must occur no later than b.ret. *)
  (* Otherwise b.ret < bt.call would imply HB H b bt, contradicting the assumptions. *)
  have "k_bt_call \<le> k_b_ret"
  proof (rule ccontr)
    assume "\<not> k_bt_call \<le> k_b_ret"
    hence "k_b_ret < k_bt_call" by simp
    
    (* Construct the forbidden HB relation b -> bt. *)
    have "HB H b bt"
      unfolding HB_def
      using `k_b_ret < k_bt_call` b_d(2) ou_bt(3) by blast
    
    with not_hb_b_bt show False by contradiction
  qed

  (* Step 4: chain the witness inequalities together. *)
  (* Hence k_ou_ret < k_d_call. *)
  have "k_ou_ret < k_d_call"
    using ou_bt(1) `k_bt_call \<le> k_b_ret` b_d(1) by linarith

  (* Step 5: construct ou -> d. *)
  (* This follows by directly composing the matching predicates. *)
  have "HB H ou d"
    unfolding HB_def
    using `k_ou_ret < k_d_call` ou_bt(2) b_d(3) by blast

  (* Step 6: derive the final contradiction. *)
  (* By HB_consistent, the linearization sequence must respect HB order. *)
  (* Therefore HB H ou d forces j < i in L. *)
  have "j < i"
    using hb_cons `HB H ou d` valid_idxs at_idxs
    unfolding HB_consistent_def by blast

  (* This directly contradicts order_in_L. *)
  thus False using order_in_L by simp
qed


lemma modify_lin_structural_preservation:
  (* Define the shared SA-boundary index once and for all. *)
  defines "idx \<equiv> \<lambda>S. nat (find_last_SA S + 1)"
  shows "data_independent L \<Longrightarrow> 
         take (idx L) (modify_lin L H bt_val) = take (idx L) L \<and> 
         mset (drop (idx L) (modify_lin L H bt_val)) = mset (drop (idx L) L)"
proof (induct L H bt_val rule: modify_lin.induct)
  case (1 L H bt_val)
  note DI_L = "1.prems"
  (* Introduce the local abbreviation for the same boundary index. *)
  let ?idx = "nat (find_last_SA L + 1)"

  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    then show ?thesis by (subst modify_lin.simps, simp)
  next
    case True
    note do_modify = True
    
    (* Step 1: define the local abbreviations and decompositions. *)
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define remaining where "remaining = drop ?idx L"
    define l1 where "l1 = take ?idx L"
    
    have L_decomp: "L = l1 @ remaining"
      unfolding l1_def remaining_def by simp

    (* Use a small contradiction argument to recover bt_idx without a large split proof. *)
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
      (* The non-emptiness of l2 follows from the earlier argument and is reused here. *)
      (* If l2 were empty, then bt_idx would be 0, contradicting should_modify and the existence of a last enqueue. *)
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

    (* Step 2: perform the main case split. *)
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
                using `remaining \<noteq> []` apply simp (* the suffix is non-empty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* expand the definition of l1 *)
                using last_sa_pos_def apply simp (* expand the definition of last_sa_pos *)
                done

              show ?thesis
                using global_prop k_props len_l1 
                by auto
            qed
               
            (* preserve the in_SA characterization *)
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

      (* Reuse the induction hypothesis instead of hard-coding indices. *)
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

(* Key strategy: split the three conditional branches with consider so that the proof matches the current algorithm. *)
      consider 
          (c1) "happens_before o1 bt_act H" 
        | (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H"
        | (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast
          
      then show ?thesis
      proof cases
        case c1 
        (* Subcase c1: keep the existing proof structure. *)
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
                using `remaining \<noteq> []` apply simp (* the suffix is non-empty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* expand the definition of l1 *)
                using last_sa_pos_def apply simp (* expand the definition of last_sa_pos *)
                done

              show ?thesis
                using global_prop k_props len_l1 
                by auto
            qed
                
            (* preserve the in_SA characterization *)
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
        (* Subcase c2: keep the existing proof structure. *)
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
                using `remaining \<noteq> []` apply simp (* the suffix is non-empty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* expand the definition of l1 *)
                using last_sa_pos_def apply simp (* expand the definition of last_sa_pos *)
                done

              show ?thesis
                using global_prop k_props len_l1 
                by auto
            qed
                
            (* preserve the in_SA characterization *)
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
        (* Subcase c3: adapted from the c1 proof pattern. *)
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
                using `remaining \<noteq> []` apply simp (* the suffix is non-empty *)
                using l1_def last_sa_pos_def len_l1 apply simp (* expand the definition of l1 *)
                using last_sa_pos_def apply simp (* expand the definition of last_sa_pos *)
                done

              show ?thesis
                using global_prop k_props len_l1 
                by auto
            qed
                
            (* preserve the in_SA characterization *)
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

        (* Note that this branch uses the fourth induction hypothesis rather than the second one. *)
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
  (* Introduce short names for readability. *)
  let ?P_enq = "\<lambda>x. op_name x = enq \<and> op_val x \<noteq> bt_val"
  let ?P_deq = "\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val"

  show ?case
  proof (cases "should_modify L H bt_val")
    case False
    then show ?thesis by (subst modify_lin.simps, simp)
  next
    case True
    note do_modify = True
    
    (* Step 1: expose the local definitions in a normalized form. *)
    define last_sa_pos where "last_sa_pos = find_last_SA L"
    define l1 where "l1 = take (nat (last_sa_pos + 1)) L"
    define remaining where "remaining = drop (nat (last_sa_pos + 1)) L"

    (* Step 2: use a short contradiction argument instead of a large metis search. *)
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

    (* Key fact: bt_act is removed by both filters. *)
    have not_P_bt: "\<not> ?P_enq bt_act \<and> \<not> ?P_deq bt_act"
      unfolding bt_act_def using bt_idx_def find_unique_index_prop by auto 
      
    have bt_gone_enq: "filter ?P_enq [bt_act] = []" using not_P_bt by simp
    have bt_gone_deq: "filter ?P_deq [bt_act] = []" using not_P_bt by simp

    (* Extract the global decomposition of L. *)
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
      case True (* Case A: enqueue branch. *)
      define new_L where "new_L = l1 @ butlast l2 @ [bt_act] @ [l2_last] @ l3"
      
      have mod_eq: "modify_lin L H bt_val = modify_lin new_L H bt_val"
        unfolding l1_def remaining_def l2_def l3_def bt_act_def l2_last_def last_sa_pos_def
        using bt_idx_def do_modify True
        apply (subst modify_lin.simps)
        apply (simp only: Let_def case_prod_unfold)
        apply (subst if_not_P, simp)
        by (simp add: bt_act_def l1_def l2_def l2_last_def l3_def
            last_sa_pos_def new_L_def remaining_def)

      (* Identify the common skeleton shared by L and new_L. *)
      have l2_struct: "l2 = butlast l2 @ [l2_last]" using l2_not_nil l2_last_def by simp
      have L_full: "L = l1 @ butlast l2 @ [l2_last] @ [bt_act] @ l3" using L_struct l2_struct by simp

      (* Let simp discharge the filter equalities directly. *)
      have filter_eq_enq: "filter ?P_enq new_L = filter ?P_enq L"
        unfolding new_L_def L_full using bt_gone_enq
        by force 
        
      have filter_eq_deq: "filter ?P_deq new_L = filter ?P_deq L"
        unfolding new_L_def L_full using bt_gone_deq
        by force 

      (* Finish the branch with the induction hypothesis. *)
      have IH_res: "filter ?P_enq (modify_lin new_L H bt_val) = filter ?P_enq new_L \<and>
                    filter ?P_deq (modify_lin new_L H bt_val) = filter ?P_deq new_L"
        using  do_modify True bt_idx_def
        unfolding new_L_def l1_def l2_def l3_def bt_act_def l2_last_def remaining_def last_sa_pos_def
        by (metis (lifting) "1.hyps"(1) option.sel)

      show ?thesis using mod_eq filter_eq_enq filter_eq_deq IH_res
        by presburger

next
      case False (* Case B: non-enqueue branch. *)
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
      
      (* Prepare the blocks that will be removed by filtering. *)
      have b_act_gone_deq: "filter ?P_deq [b_act] = []" using b_act_enq by simp
      have l22_gone_enq: "filter ?P_enq l22 = []" using l22_all_deq by (auto simp: filter_empty_conv)
      have o1_gone_enq: "filter ?P_enq [o1] = []" using o1_deq by simp
      
      (* Split the proof according to the three current branches. *)
      consider 
          (c1) "happens_before o1 bt_act H" 
        | (c2) "\<not> happens_before o1 bt_act H \<and> happens_before b_act o1 H"
        | (c3) "\<not> happens_before o1 bt_act H \<and> \<not> happens_before b_act o1 H"
          by blast

      then show ?thesis
      proof cases
        (* Subcase 1: o1 happens-before bt_act. *)
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
        (* Subcase 2: b_act happens-before o1. *)
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
        (* Subcase 3: the additional branch, reusing the c1 pattern. *)
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

        (* This branch uses 1.hyps(4), which corresponds to the new recursive case. *)
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
(* ========================================================== *)
(* modify_lin preserves lI5_SA_Prefix                        *)
(* ========================================================== *)
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

  (* Step 1: invoke the structural preservation theorem. *)
  have take_eq: "take ?idx L' = take ?idx L"
    using modify_lin_structural_preservation[OF DI] unfolding L'_def by simp

  have drop_mset_eq: "mset (drop ?idx L') = mset (drop ?idx L)"
    using modify_lin_structural_preservation[OF DI] unfolding L'_def by simp

  have len_eq: "length L' = length L"
  proof -
    have "length L' = length (take ?idx L') + length (drop ?idx L')" by simp
    also have "... = length (take ?idx L) + length (drop ?idx L)"
      using take_eq drop_mset_eq by (metis mset_eq_length)
    also have "... = length L" by simp
    finally show ?thesis .
  qed

  (* Step 2: derive global multiset preservation. *)
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

  (* Step 3: prove that the SA boundary remains unchanged. *)
  have sa_stable: "find_last_SA L' = find_last_SA L"
  proof (rule find_last_SA_stable_prefix[OF len_eq take_eq])
    (* Step 3a: the suffix of L contains no SA values. *)
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

    (* Step 3b: the suffix of L' contains no SA values. *)
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

    (* Step 3c: preserve the in_SA predicate. *)
    show "\<forall>v. in_SA v L' = in_SA v L"
      using in_SA_eq by blast
  qed

  (* Step 4: close the definition of lI5_SA_Prefix_list. *)
  show ?thesis
    unfolding lI5_SA_Prefix_list_def
  proof (intro allI impI)
    fix k assume "k < length L'" "op_name (L' ! k) = enq"
    show "in_SA (op_val (L' ! k)) L' \<longleftrightarrow> int k \<le> find_last_SA L'"
    proof (cases "k < ?idx")
      case True
      (* Inside the prefix, positions are unchanged and the property is inherited from L. *)
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
      (* In the suffix, both sides are false because the position is beyond find_last_SA. *)
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
  (* Step 1: define the auxiliary variables. *)
  define last_sa where "last_sa = find_last_SA L"
  define rem where "rem = drop (nat (last_sa + 1)) L"

  (* Step 2: show that v is not in SA. *)
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

  (* Step 3: show that v occurs uniquely in remaining, using data_independent. *)
  have "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) rem \<noteq> None"
  proof -
    (* Introduce the predicate P for the target enqueue witness. *)
    define P where "P = (\<lambda>a. op_name a = enq \<and> op_val a = v)"
    
    (* Step 3A: show that v occurs in L. *)
    obtain k where k_props: "k < length L" "op_name (L!k) = enq" "op_val (L!k) = v" 
      using ex_v by blast
    hence P_Lk: "P (L ! k)" unfolding P_def by simp
      
    (* Step 3B: since v is not in SA, its position lies beyond the SA boundary. *)
    have k_ge: "k \<ge> nat (last_sa + 1)" 
      using v_not_in_SA k_props(2,3) lI5_SA_Prefix[unfolded lI5_SA_Prefix_list_def] last_sa_def 
      using k_props(1) by fastforce 
      
    (* Hence v appears in rem at index k_rem. *)
    define k_rem where "k_rem = k - nat (last_sa + 1)"
    have k_rem_len: "k_rem < length rem" 
      using k_props(1) k_ge rem_def k_rem_def by simp
      
    (* Step 3C: use data independence to prove global uniqueness in L. *)
    have L_unique: "find_indices P L = [k]"
      using indep k_props(1) k_props(2) k_props(3) unique_enq_index unfolding P_def by blast
      
    have P_iff_k: "\<forall>i < length L. P (L ! i) \<longleftrightarrow> i = k"
    proof (intro allI impI iffI)
      (* Left-to-right: if P(L ! i) holds, then i = k. *)
      fix i assume "i < length L"
      assume "P (L ! i)"
      hence "i \<in> set (find_indices P L)" 
        unfolding find_indices_def using `i < length L` by auto
      thus "i = k" using L_unique by simp
    next
      (* Right-to-left: if i = k, then P(L ! i) holds. *)
      fix i assume "i < length L" 
      assume "i = k"
      thus "P (L ! i)" using P_Lk by simp
    qed
    
    (* Step 3D: transfer uniqueness from L to rem. *)
    have "find_indices P rem = [k_rem]"
    proof -
      (* Step 3D.1: show that the filtered index set is exactly {k_rem}. *)
      have set_eq: "set (find_indices P rem) = {k_rem}"
      proof (rule set_eqI)
        fix j
        show "j \<in> set (find_indices P rem) \<longleftrightarrow> j \<in> {k_rem}"
        proof
          (* Forward direction: any matching index j must be k_rem. *)
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
          (* Backward direction: k_rem itself satisfies the predicate. *)
          assume "j \<in> {k_rem}"
          hence "j = k_rem" by simp
          have "P (rem ! k_rem)" 
            using P_Lk k_ge rem_def k_rem_def
            using k_props(1) by auto 
          thus "j \<in> set (find_indices P rem)"
            unfolding find_indices_def using `j = k_rem` k_rem_len by auto
        qed
      qed
      
      (* Step 3D.2: the filtered index list is distinct by construction. *)
      have dist: "distinct (find_indices P rem)" 
        unfolding find_indices_def by simp
        
      (* Step 3D.3: a distinct list whose set is singleton must itself be singleton. *)
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
    
    (* Step 3E: a singleton witness list forces find_unique_index to return Some. *)
    thus ?thesis unfolding find_unique_index_def P_def by simp
  qed

  then obtain bt_idx where bt_idx_eq: 
    "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) rem = Some bt_idx" 
    by blast
    
  define l2 where "l2 = take bt_idx rem"
  
(* Step 4: prove that l2 is non-empty from Distance \<noteq> 0. *)
  have l2_not_nil: "l2 \<noteq> []"
  proof (* Use a direct contradiction proof rather than an outer ccontr. *)
    assume "l2 = []"
    
    (* Step 4A: if l2 = take bt_idx rem were empty, then bt_idx would have to be 0. *)
    have "bt_idx = 0"
    proof (rule ccontr)
      assume "bt_idx \<noteq> 0"
      then have "bt_idx > 0" by simp
      have "bt_idx < length rem" 
        using bt_idx_eq find_unique_index_prop by blast
      with `bt_idx > 0` have "take bt_idx rem \<noteq> []" by auto
      with `l2 = []` l2_def show False by simp
    qed

    (* Step 4B: compute the absolute position pos_v of v in L. *)
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
      
    (* By find_unique_index_prop, rem ! 0 is exactly the enqueue action of v. *)
    have v_rem_props: "0 < length rem \<and> op_name (rem ! 0) = enq \<and> op_val (rem ! 0) = v"
      using find_unique_index_prop[OF bt_idx_eq] `bt_idx = 0` by auto
      
    have v_L_props: "op_name (L ! ?pos_v) = enq" "op_val (L ! ?pos_v) = v"
      using v_rem_props `rem ! 0 = L ! ?pos_v` by auto
      
    (* Data independence upgrades this to global uniqueness in L. *)
    have v_idx_L: "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L = Some ?pos_v"
      using unique_enq_index[OF indep v_L_props(1) v_L_props(2) pos_v_lt]
      unfolding find_unique_index_def Let_def by simp

    (* Step 4C: prove that every element has distance 0 to v. *)
    have all_dist_zero: "\<forall>x. distance_func x v L = 0"
    proof
      fix x
      show "distance_func x v L = 0"
      proof (cases "in_SA x L")
        case True 
        then show ?thesis unfolding distance_func_def by simp
      next
        case False
        (* For x outside SA, inspect whether it has an enqueue witness. *)
        show ?thesis
        proof (cases "find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x) L")
          case None 
          then show ?thesis unfolding distance_func_def using False by simp
        next
          case (Some pos_x)
          have px_props: "pos_x < length L" "op_name (L ! pos_x) = enq" "op_val (L ! pos_x) = x"
            using find_unique_index_prop[OF Some] by auto
            
          (* By lI5_SA_Prefix, any x outside SA appears beyond the synchronized prefix boundary. *)
          have "int pos_x > last_sa"
          proof (rule ccontr)
            assume "\<not> (int pos_x > last_sa)"
            then have "int pos_x \<le> last_sa" by simp
            with lI5_SA_Prefix px_props(1,2) have "in_SA x L" 
              unfolding lI5_SA_Prefix_list_def last_sa_def
              using px_props(3) by blast
            with False show False by contradiction
          qed
          
          (* Therefore pos_x \<ge> pos_v, so x cannot be placed before v. *)
          then have "pos_x \<ge> ?pos_v" by linarith
          then have "\<not> (pos_x < ?pos_v)" by simp
          
          (* The definition of distance_func then simplifies to 0. *)
          show ?thesis
            unfolding distance_func_def
            using False Some v_idx_L `\<not> (pos_x < ?pos_v)` by simp
        qed
      qed
    qed
    
    (* Step 4D: conclude Distance L v = 0 and obtain the contradiction. *)
    have "Distance L v = 0"
    proof -
      (* Use all_dist_zero and unfold Distance to simplify the sum. *)
      have "\<forall>x. distance_func x v L = 0" using all_dist_zero .
      thus ?thesis 
        unfolding Distance_def by simp
    qed
      
    (* simp now closes the contradiction with Distance \<noteq> 0. *)
    thus False using dist_not_zero by simp
  qed
  
  (* Step 5: prove existence of the structural decomposition once l2 is non-empty. *)
  have struct_ok: "(let l2_last = last l2 in
          op_name l2_last = enq \<or> 
          (case find_last_enq l2 of
             None \<Rightarrow> False
           | Some (l21, b_act, l22) \<Rightarrow> l22 \<noteq> []))"
  proof (cases "op_name (last l2) = enq")
    case True thus ?thesis by simp
  next
    case False
    (* The goal is to show that find_last_enq returns Some and that l22 is non-empty. *)
    
    (* Step 5A: show that l2 contains at least one enqueue operation. *)
    have has_enq: "\<exists>x \<in> set l2. op_name x = enq" 
    proof -
      (* Step 5A.1: prepare a small sum_list lemma before unfolding Distance. *)
      have sum_zero: "\<And>xs. (\<forall>x\<in>set xs. distance_func x v L = 0) \<Longrightarrow> sum_list (map (\<lambda>v'. distance_func v' v L) xs) = 0"
      proof -
        fix xs show "(\<forall>x\<in>set xs. distance_func x v L = 0) \<Longrightarrow> sum_list (map (\<lambda>v'. distance_func v' v L) xs) = 0"
          by (induct xs) auto
      qed

      (* Step 5A.2: use Distance \<noteq> 0 to obtain some x_val with positive distance. *)
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

      (* Step 5A.3: unpack the properties of x_val by hand from distance_func. *)
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

      (* Step 5A.4: identify the absolute position pos_v = offset + bt_idx. *)
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
        (* Use unique_enq_value from PureLib.thy for the contradiction. *)
        with indep pv_prop(1) pos_v_alt(1) pv_prop(2) pos_v_alt(2) 
        have "op_val (L ! pos_v) \<noteq> op_val (L ! (?offset + bt_idx))"
          using unique_enq_value by blast
        thus False using pv_prop(3) pos_v_alt(3) by simp
      qed

      (* Step 5A.5: lower-bound pos_x using lI5_SA_Prefix. *)
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

      (* Step 5A.6: map pos_x back into l2. *)
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
      
    (* Step 5B: show that find_last_enq succeeds. *)
    obtain l21 b_act l22 where split: "find_last_enq l2 = Some (l21, b_act, l22)"
    proof -
      (* Unfold the definition of find_last_enq. *)
      let ?indices = "find_indices (\<lambda>a. op_name a = enq) l2"
      
      (* Since an enqueue exists, the filtered index list is non-empty. *)
      have "?indices \<noteq> []"
      proof -
        (* Step 5B.1: pick a concrete enqueue action x. *)
        from has_enq obtain x where "x \<in> set l2" and "op_name x = enq" by blast
        (* Step 5B.2: convert set membership into an explicit index i. *)
        then obtain i where "i < length l2" and "l2 ! i = x" by (metis in_set_conv_nth)
        (* Step 5B.3: show that i satisfies the filter predicate. *)
        hence "op_name (l2 ! i) = enq" using `op_name x = enq` by simp
        moreover have "i \<in> set [0..<length l2]" using `i < length l2` by simp
        (* Step 5B.4: therefore the filtered list cannot be empty. *)
        ultimately show ?thesis 
          unfolding find_indices_def
          by (metis (mono_tags, lifting) empty_filter_conv)
        qed

        
      (* By definition, a non-empty result list yields Some (...). *)
      have "find_last_enq l2 \<noteq> None"
        unfolding find_last_enq_def Let_def
        using `?indices \<noteq> []` by simp
        
      (* Extract the returned witness as a concrete variable res. *)
      then obtain res where res_eq: "find_last_enq l2 = Some res" 
        by auto
        
      (* Unfold the tuple representation to obtain the required three-part decomposition. *)
      have "Some res = Some (fst res, fst (snd res), snd (snd res))" 
        by simp
      hence "find_last_enq l2 = Some (fst res, fst (snd res), snd (snd res))" 
        using res_eq by simp
        
      (* The resulting structure now matches the that rule directly. *)
      thus ?thesis using that by blast
    qed
      
    (* Step 5C: prove that l22 is non-empty. *)
    have "l22 \<noteq> []" 
    proof (* Again use a direct contradiction argument. *)
      assume "l22 = []"
      
      (* Use the existing PureLib decomposition L = ... @ [enq_act] @ after. *)
      have "l2 = l21 @ [b_act] @ l22" 
        using find_last_enq_props(1)[OF split] .
      
      (* If l22 were empty, then the last element of l2 would be b_act. *)
      hence "last l2 = b_act" 
        using `l22 = []` by simp
        
      (* But the find_last_enq witness guarantees that b_act is an enqueue. *)
      have "op_name b_act = enq"
        using find_last_enq_props(2)[OF split] .
        
      (* This contradicts the branch assumption op_name (last l2) \<noteq> enq. *)
      hence "op_name (last l2) = enq" 
        using `last l2 = b_act` by simp
        
      (* Use the branch assumptions directly instead of a generic using False step. *)
      thus False using `\<not> op_name (last l2) = enq` by simp
    qed
      
    thus ?thesis using split by auto
  qed
  
  (* Step 6: fold the local abbreviations back to reconstruct the target statement. *)
  show ?thesis
    (* Unfold the outer definitions. *)
    unfolding should_modify_def Let_def
    (* Fold the long expressions back into the local abbreviations. *)
    unfolding last_sa_def[symmetric] rem_def[symmetric]
    (* Rewrite find_unique_index as Some bt_idx. *)
    unfolding bt_idx_eq
    (* Fold take bt_idx rem back into l2. *)
    unfolding l2_def[symmetric]
    (* At this point the goal reduces to the conjunction of the previously established facts. *)
    using indep dist_not_zero l2_not_nil struct_ok
    using l2_def by auto 
qed


lemma HB_implies_InQBack:
  assumes INV: "system_invariant s"
  assumes HB_ab: "HB_EnqRetCall s a b"
  shows "InQBack s a"
proof -
  (* Step 1: unfold HB_EnqRetCall and extract its parameters. *)
  obtain p1 p2 sn1 sn2 where hb_act: "HB_Act s (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    using HB_ab unfolding HB_EnqRetCall_def by auto

  let ?act_a = "mk_op enq a p1 sn1"
  have a_props: "op_name ?act_a = enq" "op_val ?act_a = a"
    by (simp_all add: mk_op_def op_name_def op_val_def)

  (* Step 2: extract the return witness for ?act_a from hb_act. *)
  obtain k1 k2 where k_props: "k1 < k2" "match_ret (his_seq s) k1 ?act_a" "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
    using hb_act unfolding HB_Act_def HB_def by auto

  (* Step 3: use match_ret to obtain the corresponding EnqRetInHis fact with SSN. *)
  have ret_in_his: "EnqRetInHis s p1 a sn1"
  proof -
    from k_props(2) have "k1 < length (his_seq s)"
      and "act_pid (his_seq s ! k1) = p1"
      and "act_ssn (his_seq s ! k1) = sn1"
      and "act_name (his_seq s ! k1) = enq"
      and "act_cr (his_seq s ! k1) = ret"
      and "act_val (his_seq s ! k1) = a"
      (* The current tuple definition exposes all relevant fields directly. *)
      unfolding match_ret_def Let_def mk_op_def 
                op_name_def op_val_def op_pid_def op_ssn_def 
      by auto
      
    moreover have "his_seq s ! k1 \<in> set (his_seq s)" 
      using `k1 < length (his_seq s)` by simp
    ultimately show ?thesis 
      unfolding EnqRetInHis_def by blast
  qed

  (* Step 4: lI3_HB_Ret_Lin_Sync places ?act_a directly in the linearization sequence. *)
  have lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s" using INV unfolding system_invariant_def by auto
  
  obtain k_lin where k_lin: "k_lin < length (lin_seq s)" "lin_seq s ! k_lin = ?act_a"
  proof -
    (* In the current formulation, lI3_HB_Ret_Lin_Sync yields the full mk_op entity. *)
    from lI3_HB_Ret_Lin_Sync_s ret_in_his have "\<exists>k < length (lin_seq s). lin_seq s ! k = ?act_a"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
    thus ?thesis using that by blast
  qed

  have act_a_in_lin: "?act_a \<in> OPLin s"
    unfolding OPLin_def using k_lin(1) k_lin(2) by (metis nth_mem)

  (* Step 5: derive a \<in> SetA \<union> SetB directly. *)
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

  (* Step 6: argue by contradiction that a must belong to QBack. *)
  show "InQBack s a"
  proof (rule ccontr)
    assume "\<not> InQBack s a"

    (* If a is not in SetA, then it must lie in SetB. *)
    have "a \<in> SetB s"
    proof (rule ccontr)
      assume "a \<notin> SetB s"
      with a_in_sets have "a \<in> SetA s" by auto
      then have "InQBack s a" unfolding SetA_def TypeA_def by simp
      with `\<not> InQBack s a` show False by contradiction
    qed

    then have TypeB_a: "TypeB s a" unfolding SetB_def by auto

    (* If a is not in QBack, then by synchronization it cannot appear in Q either. *)
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

    (* Therefore a must be held by some E2 process. *)
    from TypeB_a `\<not> QHas s a` obtain p where p_E2: "program_counter s p = ''E2''" and v_p: "v_var s p = a"
      unfolding TypeB_def by auto

    (* The pending-enqueue invariant now yields HasPendingEnq s p a. *)
    have hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" using INV unfolding system_invariant_def by auto
    with p_E2 v_p have pending: "HasPendingEnq s p a"
      unfolding hI1_E_Phase_Pending_Enq_def by blast

    (* Extract the SSN and call witness of the pending enqueue. *)
    let ?cur_sn = "s_var s p"
    have call_in_his: "EnqCallInHis s p a ?cur_sn"
      using pending unfolding HasPendingEnq_def Let_def by blast

    (* The OP_B_enq classification gives an enqueue action for a with the current SSN. *)
    let ?act_B = "mk_op enq a p ?cur_sn"
    have "?act_B \<in> OP_B_enq s"
      unfolding OP_B_enq_def using `a \<in> SetB s` call_in_his by auto
    with lI1_Op_Sets_Equivalence_s have act_B_in_lin: "?act_B \<in> OPLin s"
      unfolding lI1_Op_Sets_Equivalence_def by blast
      
    then obtain k_B where k_B: "k_B < length (lin_seq s)" "lin_seq s ! k_B = ?act_B"
      unfolding OPLin_def by (meson in_set_conv_nth)

    (* Data independence now forces ?act_a and ?act_B to be the same operation. *)
    have di: "data_independent (lin_seq s)" using INV unfolding system_invariant_def by auto
    have "?act_a = ?act_B"
    proof (rule ccontr)
      assume "?act_a \<noteq> ?act_B"
      
      let ?S = "{i. i < length (lin_seq s) \<and> op_name (lin_seq s ! i) = enq \<and> op_val (lin_seq s ! i) = a}"
      
      (* Step 6.1: package the basic value and operation properties. *)
      have val_props: "op_val ?act_a = a" "op_val ?act_B = a" 
        by (simp_all add: mk_op_def op_val_def)
      have oper_props: "op_name ?act_a = enq" "op_name ?act_B = enq" 
        by (simp_all add: mk_op_def op_name_def)
      
      (* Step 6.2: show that the set has cardinality at most 1. *)
      have card_le_1: "card ?S \<le> 1"
        using di unfolding data_independent_def by blast
        
      (* Step 6.3: prove the required containment using those properties. *)
      have subset_S: "?S \<supseteq> {k_lin, k_B}"
        using k_lin(1) k_lin(2) k_B(1) k_B(2) val_props oper_props by auto 
        
      (* Step 6.4: show that the two indices are different. *)
      have neq_idx: "k_lin \<noteq> k_B" 
        using `?act_a \<noteq> ?act_B` k_lin(2) k_B(2) by auto
        
      (* Step 6.5: infer cardinality at least 2 from the two distinct indices. *)
      have card_ge_2: "card ?S \<ge> 2"
        using subset_S neq_idx
        using di unique_enq_value by fastforce 
        
      (* Step 6.6: contradiction between the upper and lower cardinality bounds. *)
      show False 
        using card_le_1 card_ge_2 by linarith
    qed

    (* Core contradiction: being the same operation forces both PID and SSN to coincide. *)
    hence pid_eq: "p1 = p" and ssn_eq: "sn1 = ?cur_sn"
      unfolding mk_op_def by auto

    (* But the k1 extracted earlier is already a return event for that same PID and SSN. *)
    have "act_pid (his_seq s ! k1) = p"
      and "act_ssn (his_seq s ! k1) = ?cur_sn"
      and "act_cr (his_seq s ! k1) = ret"
      using k_props(2) pid_eq ssn_eq unfolding match_ret_def Let_def 
            mk_op_def op_pid_def op_ssn_def by auto

    (* Pending status forbids such a matching return event. *)
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
(* ========================================================== *)
(* Counting lemmas for well-formed process histories           *)
(* ========================================================== *)
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

  (* Reuse the named fact wf_full directly. *)
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
  (* Assumption 1: every return is preceded by a matching call. *)
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
  (* Conclusion: the call/return counter difference behaves as expected. *)
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
  (* Base case: the empty list. *)
  then show ?case by (simp add: Let_def)
next
  case (snoc x xs)
  (* Step 1: collect the assumptions for the current induction step. *)
  note wf_full = snoc.prems(1)
  note wf_call_full = snoc.prems(2)

  (* Step 2: show that xs still satisfies wf. *)
  have wf_xs: "\<forall>k < length xs. let e_ret = xs ! k in act_cr e_ret = ret \<longrightarrow> 
               (\<exists>j < k. act_pid (xs ! j) = act_pid e_ret \<and> act_name (xs ! j) = act_name e_ret \<and> 
                        act_cr (xs ! j) = call \<and> (\<forall>m. j < m \<and> m < k \<longrightarrow> act_pid (xs ! m) \<noteq> act_pid e_ret))"
    using prefix_wf[OF wf_full] .

  (* Step 3: show that xs also satisfies wf_call by prefix closure. *)
  (* Any valid prefix property for xs @ [x] immediately transfers to xs. *)
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

  (* Step 4: invoke the induction hypothesis. *)
  note IH = snoc.IH[OF wf_xs wf_call_xs]

  (* Step 5: perform the main case analysis. *)
  show ?case
  proof (cases "act_pid x = q")
    (* Case False: x is not an event of process q, so q_his is unchanged. *)
    case False
    then show ?thesis
      using IH False by (auto simp add: Let_def)
  next
    (* Case True: x belongs to process q. *)
    case True
    note pid_x = True
    let ?q_his = "filter (\<lambda>e. act_pid e = q) xs"
    (* In this case, q_his is the old process history extended by x. *)
    have q_his_full_eq: "filter (\<lambda>e. act_pid e = q) (xs @ [x]) = ?q_his @ [x]"
      using True by simp

    show ?thesis
    proof (cases "act_cr x = ret")
      (* Branch A: x is a return event. *)
      case True
      (* Step A1: use wf_full to locate the matching call. *)
      have idx_x: "length xs < length (xs @ [x])" by simp
      have x_at_idx: "(xs @ [x]) ! length xs = x" by simp
      
      from wf_full[unfolded Let_def, rule_format, OF idx_x]
      obtain j where j_props:
        "j < length xs"
        "act_pid (xs ! j) = q"
        "act_cr (xs ! j) = call"
        "act_name (xs ! j) = act_name x"  (* The operation name must match as well. *)
        "\<forall>m. j < m \<and> m < length xs \<longrightarrow> act_pid (xs ! m) \<noteq> q"
        using True x_at_idx pid_x by (auto simp add: nth_append)
        
      (* Step A2: show that xs ! j is the last element of the previous q_his. *)
      have "xs = take j xs @ [xs ! j] @ drop (Suc j) xs"
        using j_props(1) by (metis append_Cons append_Nil id_take_nth_drop)
      moreover have "filter (\<lambda>e. act_pid e = q) (drop (Suc j) xs) = []"
        unfolding filter_empty_conv
      proof (intro ballI)
        (* An empty filter means that every element in the dropped suffix has pid different from q. *)
        fix e
        assume "e \<in> set (drop (Suc j) xs)"
        
        (* Step A2.1: every element e in the drop list has an internal index k. *)
        then obtain k where k_lt: "k < length (drop (Suc j) xs)" 
                        and e_val: "e = drop (Suc j) xs ! k"
          by (auto simp: in_set_conv_nth)
          
        (* Step A2.2: translate k back to the original xs index Suc j + k. *)
        hence e_eq: "e = xs ! (Suc j + k)" by simp
        
        (* Step A2.3: show that this index lies strictly between j and length xs. *)
        have bound1: "j < Suc j + k" by simp
        have bound2: "Suc j + k < length xs" 
          using k_lt by simp
          
        (* Step A2.4: apply j_props(4) to exclude pid q on this interval. *)
        have "act_pid (xs ! (Suc j + k)) \<noteq> q" 
          using j_props(5) bound1 bound2 by blast
          
        (* Hence e cannot have pid q. *)
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

      have last_oper_eq: "act_name (last ?q_his) = act_name x" (* Additional derived fact. *)
        using last_is_call j_props(4) by simp

      (* Step A3: combine this with the induction hypothesis; the final return decreases the difference from 1 to 0. *)
      show ?thesis
        using IH pid_x True last_cr_call last_oper_eq
        by (smt (verit, ccfv_SIG) add_le_same_cancel1 add_left_cancel
            append_is_Nil_conv count_invariant last_snoc le_add_diff_inverse
            le_eq_less_or_eq length_filter_append_singleton less_numeral_extra(1)
            linordered_semidom_class.add_diff_inverse not_one_le_zero
            q_his_full_eq q_his_structure zero_less_diff)

    next
      (* Branch B: x is not a return, hence it is a call. *)
      case False
      note x_not_ret = False
      
      show ?thesis
      proof (cases "act_name x = deq")
        case True
        (* Step B1: if x is a dequeue call, simple natural-number arithmetic yields diff = 1. *)
        
        (* Introduce short names C and R for the call and return counts. *)
        define C where "C = length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) ?q_his)"
        define R where "R = length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) ?q_his)"
        
        have new_C: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (?q_his @ [x])) = Suc C"
          using True x_not_ret
          using C_def cr_type.exhaust by auto
        have new_R: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (?q_his @ [x])) = R"
          using True x_not_ret by (simp add: R_def)
          
        (* Extract the bound (C + 1) - R \<le> 1 from the extended history invariant. *)
        have bound: "Suc C - R \<le> 1"
          using wf_call_full[rule_format, of "length (xs @ [x])"] pid_x
          using new_C new_R by fastforce 
          
        (* Also extract R \<le> C from the invariant on xs. *)
        have prev_bound: "R \<le> C"
          using wf_call_full[rule_format, of "length xs"] pid_x 
          by (simp add: Let_def R_def C_def)
          
        (* Elementary arithmetic then forces C = R. *)
        have "C = R" using bound prev_bound by simp
        
        (* Therefore the difference increases from 0 to 1. *)
        show ?thesis
          using IH pid_x True x_not_ret `C = R`
          by (auto simp add: Let_def q_his_full_eq C_def R_def)
      next
        case False
        (* Step B2: x is an enqueue call. *)
        
        (* Mutual exclusion implies that dequeue calls remain balanced in this branch. *)
        have deq_balanced: "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) (?q_his @ [x])) = 
                            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) (?q_his @ [x]))"
          using wf_call_full[rule_format, of "length (xs @ [x])"] pid_x x_not_ret False
          using cr_type.exhaust by auto
          
        (* Hence the difference is 0, exactly as required by the else branch. *)
        show ?thesis
          using pid_x x_not_ret False deq_balanced
          by (auto simp add: Let_def q_his_full_eq)
      qed
    qed
  qed
qed

(* ========================================================== *)
(* Irreflexivity of the HB relation for enqueue operations     *)
(* ========================================================== *)
(* Intuitively, an enqueue call can never happen after its own return. *)
lemma HB_irrefl:
  assumes INV: "system_invariant s"
  shows "\<not> HB_EnqRetCall s a a"
proof
  assume "HB_EnqRetCall s a a"
  
  (* Extract the current SSN-based uniqueness invariant. *)
  have wf: "hI7_His_WF s" and uniq: "hI8_Val_Unique s" 
    using INV unfolding system_invariant_def by auto

  (* Step 2: unfold HB and obtain the conflicting witness indices k1 and k2. *)
  (* Here a is the value component of mk_op; the process ids and SSNs are obtained existentially. *)
  from `HB_EnqRetCall s a a`
  obtain p1 p2 sn1 sn2 where "HB_Act s (mk_op enq a p1 sn1) (mk_op enq a p2 sn2)"
    unfolding HB_EnqRetCall_def by blast
    
  then obtain k1 k2 where hb_props:
    "k1 < k2"
    "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
    "match_call (his_seq s) k2 (mk_op enq a p2 sn2)"
    unfolding HB_Act_def HB_def by blast

  (* Analyze k1, the return witness, and recover act_val = a. *)
  have k1_props: "k1 < length (his_seq s)"
    "act_name (his_seq s ! k1) = enq"
    "act_cr (his_seq s ! k1) = ret"
    "act_val (his_seq s ! k1) = a"
    using hb_props(2) unfolding match_ret_def Let_def mk_op_def op_name_def op_val_def by auto

  (* Analyze k2, the call witness, and recover act_val = a. *)
  have k2_props: "k2 < length (his_seq s)"
    "act_name (his_seq s ! k2) = enq"
    "act_cr (his_seq s ! k2) = call"
    "act_val (his_seq s ! k2) = a"
    using hb_props(3) unfolding match_call_def Let_def mk_op_def op_name_def op_val_def by auto

  (* Step 3: by hI7_His_WF, the return at k1 has a matching earlier call at index k0. *)
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
    "act_val (his_seq s ! k0) = a"  (* This call inherits the same value as the return at k1. *)
    using k1_props by (auto simp: Let_def)
    
  (* Step 4: hI8_Val_Unique says that enqueue calls with value a are unique. *)
  (* Therefore the earlier call at k0 and the later call at k2 must be the same event. *)
  have k0_lt_len: "k0 < length (his_seq s)" using k0_props(1) k1_props(1) by simp
  
  have "k0 = k2"
    using uniq unfolding hI8_Val_Unique_def
    using k0_lt_len k2_props(1) k0_props(2,3,4) k2_props(2,3,4)
    by blast
    
  (* Step 5: conclude the contradiction from the resulting time-order cycle. *)
  (* Since k0 = k2, we obtain both k1 < k0 and k0 < k1. *)
  moreover have "k0 < k2" using `k0 < k1` hb_props(1) by simp
  ultimately show False by simp
qed



lemma no_bt_val_deq_in_L:
  assumes sys_inv: "system_invariant s"
  assumes L_def: "L = lin_seq s"
  assumes bt_type: "TypeBT s bt_val"
  shows "\<forall>x \<in> set L. op_name x = deq \<longrightarrow> op_val x \<noteq> bt_val"
proof -
  (* ========================================================== *)
  (* Step 1: use the physical-history invariants to show that bt_val is a valid value. *)
  (* ========================================================== *)
  
  (* Step 1.1: TypeBT implies membership in the Qback array. *)
  have "InQBack s bt_val"
    using bt_type unfolding TypeBT_def by auto
  hence "\<exists>k. Qback_arr s k = bt_val"
    unfolding InQBack_def by auto
  then obtain k where "Qback_arr s k = bt_val" by blast

  (* Step 1.2: hI10_Enq_Call_Existence yields an enqueue call with SSN in the history. *)
  have "hI10_Enq_Call_Existence s" using sys_inv unfolding system_invariant_def by simp
  (* Extract both the process id and the SSN from that witness. *)
  hence "\<exists>q sn. EnqCallInHis s q bt_val sn" 
    using `Qback_arr s k = bt_val` unfolding hI10_Enq_Call_Existence_def by blast
  then obtain q sn where "EnqCallInHis s q bt_val sn" by blast

  (* Step 1.3: unfold the history predicate to obtain the concrete enqueue event e. *)
  then obtain e where e_props:
    "e \<in> set (his_seq s)"
    "act_name e = enq"
    "act_val e = bt_val"
    unfolding EnqCallInHis_def by blast

  (* Step 1.4: hI20_Enq_Val_Valid puts the enqueue value in Val. *)
  have "hI20_Enq_Val_Valid s" using sys_inv unfolding system_invariant_def by simp
  hence "\<forall>ev \<in> set (his_seq s). act_name ev = enq \<longrightarrow> act_val ev \<in> Val"
    unfolding hI20_Enq_Val_Valid_def by (metis in_set_conv_nth)
  hence "act_val e \<in> Val" using e_props(1) e_props(2) by blast

  (* Hence bt_val belongs to Val. *)
  hence bt_in_val: "bt_val \<in> Val" using e_props(3) by simp


  (* ========================================================== *)
  (* Step 2: combine this with the order-preservation argument on the linearization sequence. *)
  (* ========================================================== *)
  
  have "bt_val \<in> SetB s"
    using bt_type bt_in_val unfolding TypeBT_def SetB_def by auto

  (* Step 2.1: use lI2_Op_Cardinality to show that DeqIdxs is empty. *)
  have "lI2_Op_Cardinality s" using sys_inv unfolding system_invariant_def by simp
  hence "card (DeqIdxs s bt_val) = 0"
    using `bt_val \<in> SetB s` unfolding lI2_Op_Cardinality_def by blast
    
  (* DeqIdxs is finite because it is bounded by the length of the sequence. *)
  moreover have "finite (DeqIdxs s bt_val)" 
    unfolding DeqIdxs_def by simp
    
  (* For finite sets, card = 0 is equivalent to emptiness. *)
  ultimately have "DeqIdxs s bt_val = {}" 
    by auto
    
  hence "\<forall>k < length L. op_name (L ! k) = deq \<longrightarrow> op_val (L ! k) \<noteq> bt_val"
    unfolding DeqIdxs_def L_def by auto
    
  thus ?thesis
    by (metis in_set_conv_nth) 
qed


(* ========================================================================= *)
(* ========================================================== *)
(* Order preservation for dequeue operations after modify_lin  *)
(* ========================================================== *)
(* ========================================================================= *)
lemma modify_preserves_deq_filter:
  assumes sys_inv: "system_invariant s"
    and L_def: "L = lin_seq s"
    and type_bt: "TypeBT s bt_val"
  shows "filter (\<lambda>a. op_name a = deq \<and> op_pid a = p) (modify_lin L H bt_val) = 
         filter (\<lambda>a. op_name a = deq \<and> op_pid a = p) L"
proof -
  have deq_order: "filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) (modify_lin L H bt_val) = 
                   filter (\<lambda>x. op_name x = deq \<and> op_val x \<noteq> bt_val) L"
    using modify_lin_preserves_orders by blast

  have no_bt_val_deq: "\<forall>x \<in> set L. op_name x = deq \<longrightarrow> op_val x \<noteq> bt_val"
    using no_bt_val_deq_in_L[OF sys_inv L_def type_bt] by simp

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
  (* Argue by contradiction: assume that the value at idx equals the current x_var of p. *)
  assume val_eq: "act_val (his_seq s ! idx) = x_var s p"
  let ?a = "x_var s p"
  let ?q = "act_pid (his_seq s ! idx)"
  
  (* Extract the SSN stored in the history witness. *)
  define sn_q where "sn_q = act_ssn (his_seq s ! idx)"

  (* Confirm that ?a is a valid non-BOT value. *)
  have x_val: "?a \<in> Val" "?a \<noteq> BOT"
    using INV pc unfolding system_invariant_def sI7_D4_Deq_Result_def TypeOK_def Val_def by auto

  (* This means that process ?q has already completed a dequeue of ?a in the history. *)
  have q_ret: "DeqRetInHis s ?q ?a sn_q"
    using idx deq_ret val_eq sn_q_def unfolding DeqRetInHis_def by auto

  consider (p_neq_q) "?q \<noteq> p" | (p_eq_q) "?q = p" by blast
  thus False
  proof cases
    case p_neq_q
    (* If another process had already returned ?a, hI15_Deq_Result_Exclusivity would be violated. *)
    have "?q = p"
      using INV x_val(1) q_ret pc p_neq_q
      unfolding system_invariant_def hI15_Deq_Result_Exclusivity_def by blast
    thus False using p_neq_q by contradiction
  next
    case p_eq_q
    (* If the same process had already returned ?a earlier, hI26_DeqRet_D4_Mutex would be violated. *)
    have "\<not> (DeqRetInHis s p ?a sn_q \<and> program_counter s p = ''D4'' \<and> x_var s p = ?a)"
      using INV x_val(1) unfolding system_invariant_def hI26_DeqRet_D4_Mutex_def by blast
    thus False using q_ret p_eq_q pc by auto
  qed
qed


(* ========================================================================= *)

lemma HB_enq_stable_deq_append:
  fixes H :: "ActRec list" and a b :: nat
  assumes h_eq: "H' = H @ [mk_act deq v p sn ret]"
  (* Introduce the SSNs sn1 and sn2 explicitly so that the mk_op terms match the current type. *)
  shows "(\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)) \<longleftrightarrow> 
         (\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2))"
proof
  (* Direction 1: H' -> H. *)
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

  (* The crucial point is that the last event of H' is a dequeue, while k2 refers to an enqueue already present in H. *)
  have k2_old: "k2 < length H"
  proof (rule ccontr)
    assume "\<not> k2 < length H"
    hence "k2 = length H" using k(3) h_eq by simp
    hence "act_name (H' ! k2) = deq" 
      using h_eq by (simp add: nth_append act_name_def mk_act_def)
    thus False using k(9) by simp
  qed
  hence k1_old: "k1 < length H" using k(1) by linarith

  (* Since the relevant indices lie in the old range and H' agrees with H there, the HB witness already exists in H. *)
  show "\<exists>p1 sn1 p2 sn2. HB H (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  proof -
    (* Step 1: provide the witness processes, SSNs, and indices explicitly. *)
    show ?thesis
      unfolding HB_def
    proof (intro exI conjI)
      show "k1 < k2" by (rule k(1))
      
      (* Step 2: prove the match_ret fact in H. *)
      show "match_ret H k1 (mk_op enq a p1 sn1)"
        unfolding match_ret_def mk_op_def
        using k(4,5,6,7,8) k1_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def 
                      op_name_def op_val_def op_pid_def op_ssn_def)

      (* Step 3: prove the match_call fact in H. *)
      show "match_call H k2 (mk_op enq b p2 sn2)"
        unfolding match_call_def mk_op_def
        using k(9,10,11,12,13) k2_old h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def 
                      op_name_def op_val_def op_pid_def op_ssn_def)
    qed
  qed

  next
  (* Direction 2: H -> H'. *)
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

  (* Appending one event at the end does not destroy existing enqueue HB relations. *)
  show "\<exists>p1 sn1 p2 sn2. HB H' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
  proof -
    (* Again give the witness processes, SSNs, and indices explicitly. *)
    show ?thesis
      unfolding HB_def
    proof (intro exI conjI)
      show "k1 < k2" by (rule k_old(1))

      (* Show that match_ret is preserved in H'. *)
      show "match_ret H' k1 (mk_op enq a p1 sn1)"
        unfolding match_ret_def mk_op_def
        using k_old(2,4,5,6,7,8) h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def 
                      op_name_def op_val_def op_pid_def op_ssn_def)

      (* Show that match_call is preserved in H'. *)
      show "match_call H' k2 (mk_op enq b p2 sn2)"
        unfolding match_call_def mk_op_def
        using k_old(1,3,9,10,11,12,13) h_eq
        by (auto simp: nth_append act_name_def act_pid_def act_val_def act_ssn_def act_cr_def 
                      op_name_def op_val_def op_pid_def op_ssn_def)
    qed
  qed
qed

(* Prefix-index lemma used in the proof of hI23_Deq_Call_Ret_Balanced. *)
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
(* Basic list lemma: any filtered element different from last occurs at an earlier index in the original list. *)
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
      (* If c is the head element, its original index is 0. *)
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
      (* Otherwise c occurs in the filtered tail. *)
      have c_in: "c \<in> set ?fxs" using Cons.prems(1) f_Cons False_c by auto
      have "?fxs \<noteq> []" using c_in
        by force 
      hence last_eq: "last (filter P (x # xs)) = last ?fxs" using f_Cons by simp
      have c_neq: "c \<noteq> last ?fxs" using Cons.prems(2) last_eq by simp
      
      (* Invoke the induction hypothesis. *)
      from Cons.IH[OF c_in c_neq] obtain i j where 
        "i < j" "j < length xs" "xs ! i = c" "xs ! j = last ?fxs" by blast
        
      hence "Suc i < Suc j" "Suc j < length (x # xs)" 
            "(x # xs) ! Suc i = c" "(x # xs) ! Suc j = last (filter P (x # xs))"
        using last_eq by auto
      thus ?thesis by blast
    qed
  next
    case False
    (* If the head is filtered away, reuse the induction hypothesis with the shifted index. *)
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
(* ========================================================== *)
(* A pending call is the last event of its process history     *)
(* ========================================================== *)
(* This proof uses HasPendingDeq together with the SSN bounds and SSN-order invariants. *)
(* ========================================================================= *)
lemma pending_call_is_last:
  assumes pending: "HasPendingDeq s p"
    and ai11: "hI2_SSN_Bounds s"
    and ssn_order: "hI6_SSN_Order s"
  shows "last (filter (\<lambda>e. act_pid e = p) (his_seq s)) = mk_act deq BOT p (s_var s p) call"
proof -
  let ?p_his = "filter (\<lambda>e. act_pid e = p) (his_seq s)"
  
  (* Step 1: obtain the pending call witness c. *)
  (* Unfold the tuple-level definitions so that Isabelle sees the concrete structure directly. *)
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

  (* Step 2: hI2_SSN_Bounds gives the maximal SSN bound for c. *)
  have ssn_bound: "\<forall>e \<in> set ?p_his. act_ssn e \<le> s_var s p"
    using ai11 unfolding hI2_SSN_Bounds_def Let_def by auto

  (* Step 3: pending status means that no matching return exists. *)
  have no_ret: "\<not> (\<exists>e \<in> set ?p_his. act_ssn e = s_var s p \<and> act_cr e = ret)"
    using pending unfolding HasPendingDeq_def DeqCallInHis_def Let_def by auto 

  (* Step 4: argue by contradiction using hI6_SSN_Order. *)
  show ?thesis 
  proof (rule ccontr)
    assume not_last: "last ?p_his \<noteq> mk_act deq BOT p (s_var s p) call"
    
    have last_is_mem: "last ?p_his \<in> set ?p_his" 
      using p_his_not_empty
      using last_in_set by blast
      
      (* Map c and last back to indices i and j in his_seq s. *)
          (* Apply the list-order lemma proved just above. *)
          have c_neq_last: "c \<noteq> last ?p_his" using not_last c_def by simp
          
          from filter_last_index_order[OF c_mem c_neq_last]
          obtain i j where idx_props:
            "i < j" "j < length (his_seq s)"
            "his_seq s ! i = c"
            "his_seq s ! j = last ?p_his"
            by blast
      
    have pid_eq: "act_pid (his_seq s ! i) = act_pid (his_seq s ! j)"
      using idx_props(3,4) c_mem last_is_mem by auto
      
    (* Now invoke hI6_SSN_Order. *)
    from ssn_order[unfolded hI6_SSN_Order_def, rule_format, OF _ idx_props(2)] idx_props(1) pid_eq
    have "act_ssn c < act_ssn (last ?p_his) \<or> 
          (act_ssn c = act_ssn (last ?p_his) \<and> act_cr c = call \<and> act_cr (last ?p_his) = ret)"
      using idx_props(3,4)
      using idx_props(2) by auto 
      
    (* Branch A: a larger SSN is impossible by hI2_SSN_Bounds. *)
    moreover have "\<not> (act_ssn c < act_ssn (last ?p_his))"
    proof -
      (* Step A1: use blast for the set-theoretic upper-bound argument. *)
      have "act_ssn (last ?p_his) \<le> s_var s p" 
        using ssn_bound last_is_mem by blast
        
      (* Step A2: use simp to recover the exact SSN of c. *)
      moreover have "act_ssn c = s_var s p" 
        using c_def by (simp add: mk_act_def act_ssn_def)
        
      (* Step A3: combine the two facts to derive the contradiction. *)
      ultimately show ?thesis by simp
    qed
      
    (* Branch B: an equal-SSN return is impossible because the call is still pending. *)
    moreover have "\<not> (act_ssn c = act_ssn (last ?p_his) \<and> act_cr c = call \<and> act_cr (last ?p_his) = ret)"
    proof -
      (* Step B1: unpack the properties of c. *)
      have c_props: "act_ssn c = s_var s p" "act_cr c = call"
        using c_def by (simp_all add: mk_act_def act_ssn_def act_cr_def)
        
      (* Step B2: use blast on the no_ret property to exclude a forbidden return event. *)
      moreover have "\<not> (act_ssn (last ?p_his) = s_var s p \<and> act_cr (last ?p_his) = ret)"
        using no_ret last_is_mem by blast
        
      (* Step B3: close the contradiction. *)
      ultimately show ?thesis using c_props by simp
    qed
      
    (* The contradiction proof is complete. *)
    ultimately show False by blast
  qed
qed


end