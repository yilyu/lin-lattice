theory SimLemmas
  imports Main 
    "HOL.List"
    "TSQModel"
    "../HWQ-U/PureLib"
    "../HWQ-U/DistLib"
    "../HWQ-U/DeqLib"
    "../HWQ-U/EnqLib"
begin

(* ========================================================== *)
(* NID uniqueness derived directly from data independence      *)
(* ========================================================== *)
lemma nid_uniqueness_from_data_indep [simp]:
  assumes "TSQ_State_Inv ts"
      and "(nid, v1, ts1) \<in> set (pools ts p)"
      and "(nid, v2, ts2) \<in> set (pools ts q)"
  shows "p = q \<and> v1 = v2 \<and> ts1 = ts2"
proof -
  (* Step 1: unfold the invariant just enough to extract the core mapping rule. *)
  have core_rule: "\<forall>p q nid1 nid2 v1 v2 ts1 ts2. 
         (nid1, v1, ts1) \<in> set (pools ts p) \<and> (nid2, v2, ts2) \<in> set (pools ts q) \<longrightarrow> 
         (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> p = q \<and> ts1 = ts2)"
    using assms(1) unfolding TSQ_State_Inv_def by simp
    
  (* Step 2: instantiate the core rule with assms(2) and assms(3). *)
  then show ?thesis 
    using assms(2) assms(3) by blast
qed

(* ========================================================== *)
(* Destructors for TSQ_State_Inv                               *)
(* ========================================================== *)

lemma TSQ_State_InvD_startTs_bound:
  assumes inv: "TSQ_State_Inv ts"
      and pc: "t_pc ts q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
  shows "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
proof -
  have H:
    "\<forall>q. t_pc ts q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
         t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
    using inv unfolding TSQ_State_Inv_def by simp
  from H pc show ?thesis by blast
qed

lemma TSQ_State_InvD_tts_bound:
  assumes inv: "TSQ_State_Inv ts"
      and nz: "t_ts ts p \<noteq> TOP"
  shows "t_ts ts p <\<^sub>t\<^sub>s TS (ts_counter ts)"
proof -
  have H:
    "\<forall>p. t_ts ts p \<noteq> TOP \<longrightarrow> t_ts ts p <\<^sub>t\<^sub>s TS (ts_counter ts)"
    using inv unfolding TSQ_State_Inv_def by simp
  from H nz show ?thesis by blast
qed

lemma TSQ_State_InvD_TE2:
  assumes inv: "TSQ_State_Inv ts"
      and pc: "t_pc ts p = ''TE2''"
  shows "t_ts ts p \<noteq> TOP \<and> (\<exists>v. (t_nid ts p, v, TOP) \<in> set (pools ts p))"
proof -
  have H:
    "\<forall>p. t_pc ts p = ''TE2'' \<longrightarrow>
         t_ts ts p \<noteq> TOP \<and> (\<exists>v. (t_nid ts p, v, TOP) \<in> set (pools ts p))"
    using inv unfolding TSQ_State_Inv_def by simp
  from H pc show ?thesis by blast
qed

lemma TSQ_State_InvD_TE2_not_top:
  assumes inv: "TSQ_State_Inv ts"
      and pc: "t_pc ts p = ''TE2''"
  shows "t_ts ts p \<noteq> TOP"
  using TSQ_State_InvD_TE2[OF inv pc] by simp

lemma TSQ_State_InvD_TE3:
  assumes inv: "TSQ_State_Inv ts"
      and pc: "t_pc ts p = ''TE3''"
  shows "t_ts ts p \<noteq> TOP"
proof -
  have H:
    "\<forall>p. t_pc ts p = ''TE3'' \<longrightarrow>
         t_ts ts p \<noteq> TOP"
    using inv unfolding TSQ_State_Inv_def by simp
  from H pc show ?thesis by blast
qed

lemma TSQ_State_InvD_TE3_not_top:
  assumes inv: "TSQ_State_Inv ts"
      and pc: "t_pc ts p = ''TE3''"
  shows "t_ts ts p \<noteq> TOP"
  using TSQ_State_InvD_TE3[OF inv pc] .

lemma TSQ_State_InvD_scanned_subset:
  assumes inv: "TSQ_State_Inv ts"
  shows "t_scanned ts p \<subseteq> ProcSet"
proof -
  have H: "\<forall>p. t_scanned ts p \<subseteq> ProcSet"
    using inv unfolding TSQ_State_Inv_def by simp
  from H show ?thesis by blast
qed

lemma TSQ_State_InvD_pool_ts_order:
  assumes inv: "TSQ_State_Inv ts"
      and in1: "(nid1, v1, ts1) \<in> set (pools ts p)"
      and in2: "(nid2, v2, ts2) \<in> set (pools ts q)"
      and nz1: "ts1 \<noteq> TOP"
      and nz2: "ts2 \<noteq> TOP"
  shows "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
proof -
  have H:
    "\<forall>p q nid1 nid2 v1 v2 ts1 ts2.
       (nid1, v1, ts1) \<in> set (pools ts p) \<and>
       (nid2, v2, ts2) \<in> set (pools ts q) \<and>
       ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
       (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
    using inv
    unfolding TSQ_State_Inv_def
    apply (elim conjE)
    apply assumption
    done
  from H in1 in2 nz1 nz2 show ?thesis
    by blast
qed

(* ========================================================== *)
(* Appending a TOP node does not change the oldest-node query  *)
(* ========================================================== *)
(* Appending a fresh TOP node to the end of a pool does not change the effective result of pool_getOldest.
   This fact is repeatedly used in the proofs for Condition 6. *)
lemma pool_getOldest_append_TOP [simp]:
  "fst (pool_getOldest (pool @ [(nid, val, TOP)])) = fst (pool_getOldest pool)"
  unfolding pool_getOldest_def
  by (cases pool) auto

(* ========================================================== *)
(* Set-theoretic properties of pool_setTs                       *)
(* ========================================================== *)

(* Lemma 1: when the target nid is hit, every matching TOP node is updated. *)
lemma pool_setTs_hit [simp]:
  "(nid, v, TOP) \<in> set pool \<Longrightarrow> 
   (nid, v, new_ts) \<in> set (pool_setTs pool nid new_ts)"
  by (induct pool) auto

(* Lemma 2: every element of the updated pool either comes from the old pool or is the newly updated node. *)
lemma pool_setTs_miss [simp]:
  "x \<in> set (pool_setTs pool nid new_ts) \<Longrightarrow>
   x \<in> set pool \<or> (\<exists>v. (nid, v, TOP) \<in> set pool \<and> x = (nid, v, new_ts))"
proof (induct pool arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a pool)
  (* Step 1: destruct the head tuple explicitly. *)
  obtain n v t where a_def: "a = (n, v, t)" by (cases a) auto
  
  show ?case
  proof (cases "n = nid \<and> t = TOP")
    case True
    (* Case A: the head node matches the target nid and is updated. *)
    have "pool_setTs (a # pool) nid new_ts = (nid, v, new_ts) # pool_setTs pool nid new_ts"
      using a_def True by simp
    with Cons.prems have "x = (nid, v, new_ts) \<or> x \<in> set (pool_setTs pool nid new_ts)"
      by auto
    then show ?thesis
    proof
      assume "x = (nid, v, new_ts)"
      moreover have "(nid, v, TOP) \<in> set (a # pool)" using a_def True by simp
      ultimately show ?thesis by blast (* blast discharges the existential witness directly. *)
    next
      assume "x \<in> set (pool_setTs pool nid new_ts)"
      with Cons.hyps have "x \<in> set pool \<or> (\<exists>v. (nid, v, TOP) \<in> set pool \<and> x = (nid, v, new_ts))" by simp
      then show ?thesis
        by (metis list.set_intros(2)) 
    qed
  next
    case False
    (* Case B: the head node does not match and is kept unchanged. *)
    have "pool_setTs (a # pool) nid new_ts = (n, v, t) # pool_setTs pool nid new_ts"
      using a_def False
      by auto 
    with Cons.prems have "x = (n, v, t) \<or> x \<in> set (pool_setTs pool nid new_ts)"
      by auto
    then show ?thesis
    proof
      assume "x = (n, v, t)"
      then have "x \<in> set (a # pool)" using a_def by simp
      then show ?thesis by blast
    next
      assume "x \<in> set (pool_setTs pool nid new_ts)"
      with Cons.hyps have "x \<in> set pool \<or> (\<exists>v. (nid, v, TOP) \<in> set pool \<and> x = (nid, v, new_ts))" by simp
      then show ?thesis
        by auto 
    qed
  qed
qed

(* ========================================================== *)
(* Helper lemma 3.1: cleanup property in explicit tuple form    *)
(* Use explicit tuples (n, v, ts) instead of a single variable x in the list induction.
   This avoids unnecessary fst/snd rewriting loops. *)
(* ========================================================== *)
lemma pool_setTs_clears_TOP_helper:
  "(n, v, ts) \<in> set (pool_setTs pool target_nid new_ts) \<Longrightarrow> new_ts \<noteq> TOP \<Longrightarrow> ts = TOP \<Longrightarrow> n \<noteq> target_nid"
  by (induct pool) (auto split: if_splits)

(* ========================================================== *)
(* Lemma 3: cleanup property for TOP nodes                      *)
(* Reconstruct the tuple explicitly and apply the helper lemma. *)
(* ========================================================== *)
lemma pool_setTs_clears_TOP [simp]:
  "new_ts \<noteq> TOP \<Longrightarrow> x \<in> set (pool_setTs pool target_nid new_ts) \<Longrightarrow> snd (snd x) = TOP \<Longrightarrow> fst x \<noteq> target_nid"
proof -
  assume prems: "new_ts \<noteq> TOP" "x \<in> set (pool_setTs pool target_nid new_ts)" "snd (snd x) = TOP"
  
  (* Rewrite x through its explicit tuple decomposition. *)
  have "(fst x, fst (snd x), snd (snd x)) \<in> set (pool_setTs pool target_nid new_ts)"
    using prems(2) by simp
    
  (* Feed the decomposed tuple into the helper lemma. *)
  with prems(1) prems(3) show "fst x \<noteq> target_nid"
    using pool_setTs_clears_TOP_helper by blast
qed

(* Lemma 4: non-TOP nodes are preserved by pool_setTs. *)
lemma pool_setTs_preserves_not_TOP [simp]:
  "(n, v, ts) \<in> set pool \<Longrightarrow> ts \<noteq> TOP \<Longrightarrow> (n, v, ts) \<in> set (pool_setTs pool target_nid new_ts)"
  by (induct pool) auto


lemma pool_node_value_is_v_var:
  assumes "Simulation_Inv (cs, us) ts"
      and "(nid, v, TOP) \<in> set (pools ts p)"
      and "c_program_counter cs p \<in> {''E1'', ''E2'', ''E3''}"
  shows "v = CState.v_var cs p"
proof -
  (* Step 0: unpack the three key assumptions. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
    using assms(1) unfolding Simulation_Inv_def by auto

  (* Step 1: extract Condition 3 from Simulation_R. *)
  from sim_r have cond3: "\<forall>q node. node \<in> set (pools ts q) \<and> snd (snd node) = TOP \<longrightarrow> 
    t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
    unfolding Simulation_R_def Let_def by auto

  (* Step 2: apply Condition 3 to the node under consideration. *)
  from assms(2) cond3 have nid_val: "t_nid ts p = nid" and tpc: "t_pc ts p = ''TE2''"
    apply auto[1]
    using assms(2) cond3 by auto

  (* Step 3: infer the corresponding concrete control state E2. *)
  from sim_r tpc have pc_E2: "c_program_counter cs p = ''E2''"
    unfolding Simulation_R_def Let_def
    using assms(3) by fastforce 

  (* Step 4: use sI3_E2_Slot_Exclusive to prove that the concrete slot is empty. *)
  from inv_sys pc_E2 have slot_empty: "CState.Q_arr cs (CState.i_var cs p) = BOT"
    unfolding system_invariant_def sI3_E2_Slot_Exclusive_def
    unfolding program_counter_def Q_arr_def i_var_def
    by auto

  (* Step 5: extract Condition 5.2 from Simulation_R to obtain the pending witness. *)
  from sim_r have cond52: "\<forall>u idx. CState.Q_arr cs idx = BOT \<and> 
    c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx \<longrightarrow> 
    (\<exists>nid. (nid, CState.v_var cs u, TOP) \<in> set (pools ts u))"
    unfolding Simulation_R_def Let_def by auto

  with pc_E2 slot_empty obtain nid' where 
    official: "(nid', CState.v_var cs p, TOP) \<in> set (pools ts p)" by blast

  (* Step 6: prove uniqueness of the nid using Condition 3. *)
  from official cond3 have "t_nid ts p = nid'"
    by (metis fst_conv snd_conv)
  with nid_val have id_match: "nid' = nid" by simp

  from official id_match have official_aligned: "(nid, CState.v_var cs p, TOP) \<in> set (pools ts p)" by simp
  
  (* Invoke the dedicated uniqueness lemma directly instead of unfolding the large definitions again. *)
  from nid_uniqueness_from_data_indep[OF inv_tsq official_aligned assms(2)] 
  show ?thesis by simp
qed

(* Every node in pool_setTs pool is either an old node or the uniquely updated TOP node. *)
lemma in_set_pool_setTs:
  "(nid, v, ts_val) \<in> set (pool_setTs pool target new_ts) \<Longrightarrow>
   (nid, v, ts_val) \<in> set pool \<or> (nid = target \<and> ts_val = new_ts \<and> (nid, v, TOP) \<in> set pool)"
  (* Proceed by the function-specific induction and let auto split the if-branches. *)
  by (induct pool target new_ts rule: pool_setTs.induct) (auto split: if_splits)


(* Core induction lemma over the number of remaining unscanned processes. *)
lemma Ghost_Fast_Forward_core:
  assumes "finite ProcSet"
  shows "card (ProcSet - t_scanned ts p) = n \<Longrightarrow>
         t_pc ts p = ''TD_Loop'' \<Longrightarrow>
         (\<forall>k \<in> ProcSet - t_scanned ts p. 
             fst (pool_getOldest (pools ts k)) = BOT \<or> 
             \<not> ts_less (snd (pool_getOldest (pools ts k))) (t_candTs ts p) \<or> 
             ts_less (t_startTs ts p) (snd (pool_getOldest (pools ts k)))) \<Longrightarrow>
         \<exists>ts_mid. T_D3_Scan_Star p ts ts_mid \<and> 
                  ProcSet \<subseteq> t_scanned ts_mid p \<and> 
                  t_candNid ts_mid p = t_candNid ts p"
proof (induction n arbitrary: ts)
  case 0
  (* Base case: no remaining process is left to scan. *)
  have "ProcSet - t_scanned ts p = {}" using 0 assms by auto
  then have "ProcSet \<subseteq> t_scanned ts p" by auto
  then show ?case using T_D3_Scan_Star.refl by blast
next
  case (Suc n ts)
  (* Inductive step: there remain Suc n processes to scan. *)
    have diff_nonempty: "ProcSet - t_scanned ts p \<noteq> {}"
    proof
      assume "ProcSet - t_scanned ts p = {}"
      with Suc.prems(1) show False by simp
    qed
  then obtain k where k_in_rem: "k \<in> ProcSet - t_scanned ts p" by blast
  
  then have k_proc: "k \<in> ProcSet" and k_not_scan: "k \<notin> t_scanned ts p" by auto
  
  (* Extract the facts about the pool of k. *)
  let ?nid = "fst (pool_getOldest (pools ts k))"
  let ?tstamp = "snd (pool_getOldest (pools ts k))"
  
  have k_cond: "?nid = BOT \<or> \<not> ts_less ?tstamp (t_candTs ts p) \<or> ts_less (t_startTs ts p) ?tstamp"
    using Suc.prems(3) k_in_rem by blast
    
  (* Show that the current branch cannot trigger an update. *)
  have not_update: "\<not> (?nid \<noteq> BOT \<and> ts_less ?tstamp (t_candTs ts p) \<and> \<not> ts_less (t_startTs ts p) ?tstamp)"
    using k_cond by auto
    
  (* Construct the intermediate one-step successor ts1. *)
  let ?ts1 = "ts\<lparr> 
    t_candNid := (\<lambda>x. if x = p then t_candNid ts p else t_candNid ts x),
    t_candTs  := (\<lambda>x. if x = p then t_candTs ts p else t_candTs ts x),
    t_candPid := (\<lambda>x. if x = p then t_candPid ts p else t_candPid ts x),
    t_scanned := (\<lambda>x. if x = p then t_scanned ts p \<union> {k} else t_scanned ts x) 
  \<rparr>"

  have step1: "T_D3_Scan p k ts ?ts1"
  proof -
    (* Step 1: obtain the relevant pool information explicitly. *)
    obtain n t where nt_eq: "pool_getOldest (pools ts k) = (n, t)" 
      by (cases "pool_getOldest (pools ts k)") auto
    
    (* Step 2: show that the non-updating branch indeed yields ?ts1. *)
    have record_match: "ts\<lparr>
          t_candNid := (\<lambda>x. if x = p then (if n \<noteq> BOT \<and> ts_less t (t_candTs ts p) \<and> \<not> ts_less (t_startTs ts p) t then n else t_candNid ts p) else t_candNid ts x),
          t_candTs  := (\<lambda>x. if x = p then (if n \<noteq> BOT \<and> ts_less t (t_candTs ts p) \<and> \<not> ts_less (t_startTs ts p) t then t else t_candTs ts p) else t_candTs ts x),
          t_candPid := (\<lambda>x. if x = p then (if n \<noteq> BOT \<and> ts_less t (t_candTs ts p) \<and> \<not> ts_less (t_startTs ts p) t then k else t_candPid ts p) else t_candPid ts x),
          t_scanned := (\<lambda>x. if x = p then t_scanned ts p \<union> {k} else t_scanned ts x)
       \<rparr> = ?ts1"
    proof -
      (* Extract the non-update premise. *)
      have not_upd: "\<not> (n \<noteq> BOT \<and> ts_less t (t_candTs ts p) \<and> \<not> ts_less (t_startTs ts p) t)"
        using k_cond nt_eq
        by simp 
      (* A small simp step is enough here; there is no need to unfold the whole record. *)
      show ?thesis by (simp add: not_upd)
    qed

    (* Step 3: unfold the definitions and close the goal via record_match. *)
    show ?thesis
      unfolding T_D3_Scan_def Let_def nt_eq prod.case
      using Suc.prems(2) k_proc k_not_scan record_match
      by simp
  qed
    
  (* Establish the properties of ts1 needed for the induction hypothesis. *)
  have pc_ts1: "t_pc ?ts1 p = ''TD_Loop''" using Suc.prems(2) by simp
  have cand_ts1: "t_candTs ?ts1 p = t_candTs ts p" by simp
  have start_ts1: "t_startTs ?ts1 p = t_startTs ts p" unfolding T_D3_Scan_def by simp
  
  (* Show that the number of remaining processes decreases by exactly one. *)
  have "ProcSet - t_scanned ?ts1 p = (ProcSet - t_scanned ts p) - {k}" by auto
  then have "card (ProcSet - t_scanned ?ts1 p) = card ((ProcSet - t_scanned ts p) - {k})" by simp
  also have "... = card (ProcSet - t_scanned ts p) - 1" 
    using assms k_in_rem by simp
  also have "... = n" using Suc.prems(1) by simp
  finally have card_ts1: "card (ProcSet - t_scanned ?ts1 p) = n" .
  
  (* Show that the remaining processes still satisfy the non-update premise in the new state. *)
  have cond_ts1: "\<forall>k' \<in> ProcSet - t_scanned ?ts1 p. 
      fst (pool_getOldest (pools ?ts1 k')) = BOT \<or> 
      \<not> ts_less (snd (pool_getOldest (pools ?ts1 k'))) (t_candTs ?ts1 p) \<or> 
      ts_less (t_startTs ?ts1 p) (snd (pool_getOldest (pools ?ts1 k')))"
  proof (intro ballI)
    fix k' assume "k' \<in> ProcSet - t_scanned ?ts1 p"
    then have "k' \<in> ProcSet - t_scanned ts p" and "k' \<noteq> k" by auto
    then have old_cond: "fst (pool_getOldest (pools ts k')) = BOT \<or> 
                         \<not> ts_less (snd (pool_getOldest (pools ts k'))) (t_candTs ts p) \<or> 
                         ts_less (t_startTs ts p) (snd (pool_getOldest (pools ts k')))"
      using Suc.prems(3) by blast
    (* Since the pools are unchanged, the corresponding fact is inherited directly. *)
    have "pools ?ts1 k' = pools ts k'" by simp
    with old_cond cand_ts1 start_ts1 show "fst (pool_getOldest (pools ?ts1 k')) = BOT \<or> \<not> ts_less (snd (pool_getOldest (pools ?ts1 k'))) (t_candTs ?ts1 p) \<or> ts_less (t_startTs ?ts1 p) (snd (pool_getOldest (pools ?ts1 k')))" by simp
  qed
  
  (* Apply the induction hypothesis. *)
  from Suc.IH[OF card_ts1 pc_ts1 cond_ts1] 
  obtain ts_mid where mid_star: "T_D3_Scan_Star p ?ts1 ts_mid"
                  and mid_scanned: "ProcSet \<subseteq> t_scanned ts_mid p"
                  and mid_cand: "t_candNid ts_mid p = t_candNid ?ts1 p" by blast
                  
  (* Combine the single-step transition with the remaining scan-star execution. *)
  have "T_D3_Scan_Star p ts ts_mid" 
    using T_D3_Scan_Star.step[OF step1 mid_star] by simp
  moreover have "t_candNid ts_mid p = t_candNid ts p" using mid_cand by simp
  ultimately show ?case using mid_scanned by blast
qed

(* Main wrapper lemma exported for later use. *)
lemma Ghost_Fast_Forward:
  assumes "t_pc ts p = ''TD_Loop''"
      and "\<forall>k \<in> ProcSet - t_scanned ts p. 
             (fst (pool_getOldest (pools ts k)) = BOT) \<or> 
             (\<not> ts_less (snd (pool_getOldest (pools ts k))) (t_candTs ts p)) \<or> 
             (ts_less (t_startTs ts p) (snd (pool_getOldest (pools ts k))))"
  shows "\<exists>ts_mid. T_D3_Scan_Star p ts ts_mid \<and> 
                  ProcSet \<subseteq> t_scanned ts_mid p \<and> 
                  t_candNid ts_mid p = t_candNid ts p"
  using Ghost_Fast_Forward_core[OF finite_ProcSet _ assms(1) assms(2)] by blast

(* ============================================================================== *)
(* Valid nodes of an unscanned process must have timestamps strictly later than the current startTs. *)
(* ============================================================================== *)
lemma pool_getOldest_SomeE:
  assumes "pool_getOldest pool = (nid, tstamp)" and "nid \<noteq> BOT"
  shows "\<exists>v. (nid, v, tstamp) \<in> set pool"
proof -
  obtain n v ts rest where "pool = (n, v, ts) # rest \<or> pool = []"
    by (cases pool) auto
  then show ?thesis
  proof
    assume "pool = []"
    then have "pool_getOldest pool = (BOT, TOP)"
      by (simp add: pool_getOldest_def) 
    with assms show ?thesis by simp
  next
    assume "pool = (n, v, ts) # rest"
    then have "pool_getOldest pool = (if ts \<noteq> TOP then (n, ts) else (BOT, TOP))"
      (* Unfold pool_getOldest explicitly at this point. *)
      by (simp add: pool_getOldest_def)
    with assms have "ts \<noteq> TOP" and "nid = n" and "tstamp = ts"
      by (auto split: if_splits)
    then show ?thesis using \<open>pool = (n, v, ts) # rest\<close> by auto
  qed
qed

lemma pool_setTs_set_cases:
  assumes "(nid, v, ts_val) \<in> set (pool_setTs pool target_nid new_ts)"
  shows "((nid, v, ts_val) \<in> set pool) \<or> 
         (ts_val = new_ts \<and> (nid, v, TOP) \<in> set pool \<and> nid = target_nid)"
  using assms
proof (induct pool arbitrary: nid v ts_val)
  case Nil
  then show ?case by simp
next
  case (Cons node pool')
  obtain n0 v0 t0 where node: "node = (n0, v0, t0)" by (cases node) auto
  show ?case
  proof (cases "n0 = target_nid \<and> t0 = TOP")
    case True
    (* The head node is updated. *)
    let ?rest = "pool_setTs pool' target_nid new_ts"
    have "pool_setTs (node # pool') target_nid new_ts = (target_nid, v0, new_ts) # ?rest"
      using node True by simp
    with Cons.prems have "((nid, v, ts_val) = (target_nid, v0, new_ts)) \<or> ((nid, v, ts_val) \<in> set ?rest)"
      by auto
    then show ?thesis
    proof
      assume eq: "(nid, v, ts_val) = (target_nid, v0, new_ts)"
      then have "nid = target_nid" "v = v0" "ts_val = new_ts" by auto
      moreover have "(target_nid, v0, TOP) \<in> set (node # pool')" using node True by simp
      ultimately show ?thesis by blast
    next
      assume "(nid, v, ts_val) \<in> set ?rest"
      from Cons.hyps[OF this] show ?thesis
        by auto
    qed
  next
    case False
    (* The head node is unchanged. *)
    let ?rest = "pool_setTs pool' target_nid new_ts"
    have "pool_setTs (node # pool') target_nid new_ts = node # ?rest"
      using node False
      using pool_setTs.simps(2) by presburger 
    with Cons.prems have "(nid, v, ts_val) = node \<or> (nid, v, ts_val) \<in> set ?rest"
      by auto
    then show ?thesis
    proof
      assume "(nid, v, ts_val) = node"
      then have "(nid, v, ts_val) \<in> set (node # pool')" by simp
      thus ?thesis by blast
    next
      assume "(nid, v, ts_val) \<in> set ?rest"
      from Cons.hyps[OF this] show ?thesis
        by auto 
    qed
  qed
qed



(* ========================================================================= *)
(* Core invariant lemma: timestamps of unscanned nodes lie in the future of the current startTs. *)
(* ========================================================================= *)
lemma unscanned_node_ts_gt_startTs:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes inv: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and pc:  "c_program_counter cs p = ''D3''"
      and end_scan: "CState.j_var cs p = CState.l_var cs p - 1"
      and last_bot: "CState.Q_arr cs (CState.j_var cs p) = BOT"
      and k_unscanned: "k \<in> ProcSet - t_scanned ts p"
      and k_oldest: "pool_getOldest (pools ts k) = (nid, tstamp)"
      and nid_valid: "nid \<noteq> BOT"
  shows "ts_less (t_startTs ts p) tstamp"
proof (rule ccontr)
  assume not_less: "\<not> ts_less (t_startTs ts p) tstamp"

  (* Key proof idea. *)
  from sim have cond10: "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
    and cond11: "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val"
    and cond13: "\<forall>q. c_program_counter cs q \<in> {''D2'',''D3'',''D4''} \<longrightarrow> 
         (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs q)"
    unfolding Simulation_R_def Let_def by auto

  (* Step 1: extract an actual node from the result of pool_getOldest. *)
  obtain v where in_pool: "(nid, v, tstamp) \<in> set (pools ts k)"
    using pool_getOldest_SomeE[OF k_oldest nid_valid] by blast

  (* Step 2: show that tstamp is not TOP. *)
  have "tstamp \<noteq> TOP"
  proof
    assume "tstamp = TOP"
    
    (* First, Simulation_R implies that p is in TD_Loop on the TSQ side. *)
    have "t_pc ts p = ''TD_Loop''"
      using sim pc unfolding Simulation_R_def Let_def
      by simp 
      
    (* Second, TSQ_State_Inv yields that startTs is below the current allocation counter in TD_Loop. *)
      have tpc_loop_set: "t_pc ts p \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
        using `t_pc ts p = ''TD_Loop''` by simp
      
      have "t_startTs ts p <\<^sub>t\<^sub>s TS (ts_counter ts)"
        using TSQ_State_InvD_startTs_bound[OF inv_tsq tpc_loop_set] .
    (* Third, any timestamp strictly below a TS counter value cannot be TOP. *)
    hence "t_startTs ts p \<noteq> TOP"
      by (cases "t_startTs ts p") auto
      
    (* Hence, if tstamp were TOP, startTs would be smaller than it immediately. *)
    have "ts_less (t_startTs ts p) tstamp"
      using `t_startTs ts p \<noteq> TOP` `tstamp = TOP` 
      by (cases "t_startTs ts p") auto
      
    (* This contradicts the assumption not_less. *)
    with not_less show False by simp
  qed
  then obtain n where tstamp_eq: "tstamp = TS n" by (cases tstamp) auto


  (* Step 4: use Condition 13 to place nid before l_var. *)
  from sim pc have cond13: "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts p) ts_val \<longrightarrow> nid < CState.l_var cs p"
    unfolding Simulation_R_def Let_def by auto
  with in_pool `tstamp \<noteq> TOP` not_less have nid_less_l: "nid < CState.l_var cs p" by blast

  (* Step 5: combine the result with end_scan to derive nid \<le> j_var. *)
  hence "nid \<le> CState.j_var cs p" using end_scan by simp

  (* Step 6: derive the contradiction by case analysis. *)
  show False
  proof (cases "nid = CState.j_var cs p")
    case True
    have "CState.Q_arr cs nid = BOT" using True last_bot by simp
     have "v = BOT"
      using \<open>CState.Q_arr cs nid = BOT\<close> cond10 in_pool tstamp_eq
      by blast
    (* Condition 11 yields v \<in> Val, hence v \<noteq> BOT. *)
    from sim have cond11: "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val"
      unfolding Simulation_R_def Let_def
      by meson 
    with in_pool have "v \<in> Val" by blast
    hence "v \<noteq> BOT" unfolding Val_def BOT_def by auto
    with `v = BOT` show False by simp
  next
    case False
    (* Step 1: record the relevant index relation. *)
    hence nid_lt: "nid < CState.j_var cs p" using `nid \<le> CState.j_var cs p` by simp

    (* Step 2: unfold the one-way direction of Condition 6. *)
    from sim pc have cond6_imp: "\<forall>v. 
        (\<exists>idx < CState.j_var cs p. 
          (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
          (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) 
        \<longrightarrow> v \<in> t_scanned ts p"
      unfolding Simulation_R_def Let_def
      by simp


    (* Step 3: show that the slot is non-empty using Conditions 10 and 11. *)
    have q_not_bot: "CState.Q_arr cs nid \<noteq> BOT"
    proof -
      from sim in_pool cond11 have "v \<in> Val" unfolding Simulation_R_def Let_def
        by meson 
      thus ?thesis using sim in_pool tstamp_eq unfolding Simulation_R_def Let_def
        by (metis BOT_def Val_def cond10 gr_implies_not0
            mem_Collect_eq)
    qed

    (* Step 4: show that k satisfies the scanning premise, using nid as the witness index. *)
    have "\<exists>idx < CState.j_var cs p. 
          (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid0 ts_val. (nid0, CState.Q_arr cs idx, ts_val) \<in> set (pools ts k) \<and> ts_val \<noteq> TOP))"
    proof -
      (* By data independence, the node stored at nid is exactly the one we need. *)
      have "(nid, CState.Q_arr cs nid, tstamp) \<in> set (pools ts k)"
        using cond10 in_pool tstamp_eq by blast
      with nid_lt q_not_bot `tstamp \<noteq> TOP` show ?thesis by blast
    qed

    (* Step 5: invoke cond6_imp to derive the contradiction. *)
    with cond6_imp have "k \<in> t_scanned ts p" by blast
    with k_unscanned show ?thesis by blast
  qed
qed

lemma T_D3_Scan_scanned_subset_step:
  assumes "T_D3_Scan p k ts ts'"
  shows "t_scanned ts p \<subseteq> ProcSet \<Longrightarrow> t_scanned ts' p \<subseteq> ProcSet"
  using assms
  unfolding T_D3_Scan_def Let_def
  by auto

(* Multi-step scans never introduce illegal process identifiers. *)
lemma T_D3_Scan_Star_scanned_subset:
  assumes "T_D3_Scan_Star p ts ts'"
  shows "t_scanned ts p \<subseteq> ProcSet \<Longrightarrow> t_scanned ts' p \<subseteq> ProcSet"
  using assms
proof (induct rule: T_D3_Scan_Star.induct)
  case refl
  then show ?case by simp
next
  case step
  then show ?case
    using T_D3_Scan_scanned_subset_step
    by blast
qed

(* ========================================================== *)
(* Concrete/TSQ correspondence for one empty-slot scan step.    *)
(* ========================================================== *)
(* ========================================================== *)
(* Helper lemma 1: global uniqueness of the active scan cursor  *)
(* ========================================================== *)
lemma i_var_uniqueness:
  assumes "system_invariant (cs, us)"
      and "c_program_counter cs k \<in> {''E2'', ''E3''}"
      and "c_program_counter cs v \<in> {''E2'', ''E3''}"
      and "CState.i_var cs k = CState.i_var cs v"
  shows "k = v"
proof (rule ccontr)
  assume "k \<noteq> v"
  have "CState.i_var cs k \<noteq> CState.i_var cs v"
  proof (cases "c_program_counter cs k = ''E2''")
    case True
    with assms `k \<noteq> v` show ?thesis unfolding system_invariant_def sI3_E2_Slot_Exclusive_def
      by (simp add: Model.i_var_def program_counter_def) 
  next
    case False
    with assms(2) have "c_program_counter cs k = ''E3''" by simp
    with assms `k \<noteq> v` show ?thesis unfolding system_invariant_def sI4_E3_Qback_Written_def
      by (metis Model.i_var_def fst_conv program_counter_def)
  qed
  with assms(4) show False by simp
qed

(* ========================================================== *)
(* An unscanned pending E2 process can only contribute TOP nodes. *)
(* The key contradiction uses Condition 15 to place every old node before the current cursor j. *)
(* ========================================================== *)
lemma unscanned_pending_has_no_old_nodes:
  assumes inv_sys: "system_invariant (cs, us)"
      and sim: "Simulation_R (cs, us) ts"
      and pc_p: "c_program_counter cs p = ''D3''"
      and pc_k: "c_program_counter cs k = ''E2''"  
      and i_var_k: "CState.i_var cs k = CState.j_var cs p"
      and q_bot: "CState.Q_arr cs (CState.j_var cs p) = BOT"
      and unscanned: "k \<notin> t_scanned ts p"
  shows "fst (pool_getOldest (pools ts k)) = BOT"
proof (rule ccontr)
  assume "fst (pool_getOldest (pools ts k)) \<noteq> BOT"
  then obtain nid0 tstamp0 where oldest: "pool_getOldest (pools ts k) = (nid0, tstamp0)" 
    by (cases "pool_getOldest (pools ts k)") auto
  with `fst (pool_getOldest (pools ts k)) \<noteq> BOT` have "nid0 \<noteq> BOT" by simp

  obtain v where node0: "(nid0, v, tstamp0) \<in> set (pools ts k)"
    using pool_getOldest_SomeE[OF oldest `nid0 \<noteq> BOT`] by blast

  have "tstamp0 \<noteq> TOP"
  proof
    assume "tstamp0 = TOP"
    have "nid0 = BOT"
      using oldest `tstamp0 = TOP` unfolding pool_getOldest_def
      by (cases "pools ts k") (auto split: if_splits)
    with `nid0 \<noteq> BOT` show False by simp
  qed
  then obtain n where "tstamp0 = TS n" by (cases tstamp0) auto
  with node0 have real_node: "(nid0, v, TS n) \<in> set (pools ts k)" by simp

  have "CState.Q_arr cs nid0 = v" using sim real_node unfolding Simulation_R_def Let_def
    by (metis fst_conv)
  have "v \<in> Val" using sim real_node unfolding Simulation_R_def Let_def
    by meson 
  then have "v \<noteq> BOT" unfolding Val_def BOT_def by auto
  then have q_nid0_not_bot: "CState.Q_arr cs nid0 \<noteq> BOT" using `CState.Q_arr cs nid0 = v` by simp

  (* Apply Condition 15 to obtain the required monotonicity fact. *)
  have "nid0 < CState.i_var cs k"
    using sim real_node `tstamp0 \<noteq> TOP` pc_k unfolding Simulation_R_def Let_def
    by (metis fst_conv ts_type.distinct(1))
    
  with i_var_k have nid0_less_j: "nid0 < CState.j_var cs p" by simp

  (* Extract the one-way form of Condition 6 exactly as stated. *)
  from sim pc_p have cond6_imp: "\<forall>v_proc. 
        (\<exists>idx < CState.j_var cs p. 
          (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>n ts_val. (n, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v_proc) \<and> ts_val \<noteq> TOP)) \<or> 
          (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v_proc = ''E2'' \<and> CState.i_var cs v_proc = idx \<and> idx \<noteq> BOT)) 
        \<longrightarrow> v_proc \<in> t_scanned ts p"
    unfolding Simulation_R_def Let_def by simp

  (* Use nid0 as the witness index for the existential premise. *)
  have "\<exists>idx < CState.j_var cs p. 
          (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>n ts_val. (n, CState.Q_arr cs idx, ts_val) \<in> set (pools ts k) \<and> ts_val \<noteq> TOP)) \<or> 
          (CState.Q_arr cs idx = BOT \<and> c_program_counter cs k = ''E2'' \<and> CState.i_var cs k = idx \<and> idx \<noteq> BOT)"
  proof -
    have "CState.Q_arr cs nid0 \<noteq> BOT \<and> (\<exists>n ts_val. (n, CState.Q_arr cs nid0, ts_val) \<in> set (pools ts k) \<and> ts_val \<noteq> TOP)"
      using q_nid0_not_bot real_node `tstamp0 \<noteq> TOP` `CState.Q_arr cs nid0 = v` by blast
    with nid0_less_j show ?thesis by blast
  qed

  (* Combine the two facts to finish the contradiction. *)
  with cond6_imp have "k \<in> t_scanned ts p" by blast
  with unscanned show False by simp
qed

(* ========================================================== *)
(* Main helper lemma: TSQ-side reconstruction for an empty-slot scan step. *)
(* This lemma also maintains the strengthened Condition 18 for the D3 scan phase. *)
(* It additionally maintains the strengthened pending-node protection constraint. *)
lemma D3_Scan_Empty_Slot_Helper:
  fixes cs :: CState and us :: UState and ts :: TState and p :: nat and cs' :: CState
  assumes inv_sys: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and pc: "c_program_counter cs p = ''D3''"
      and E2_in_ProcSet: "\<forall>q. c_program_counter cs q = ''E2'' \<longrightarrow> q \<in> ProcSet"
      and q_bot: "CState.Q_arr cs (CState.j_var cs p) = BOT"
      and not_end: "CState.j_var cs p < CState.l_var cs p - 1"
      and cs'_eq: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D3'' else c_program_counter cs x),
                          j_var := (\<lambda>x. if x = p then CState.j_var cs p + 1 else CState.j_var cs x),
                          x_var := (\<lambda>x. if x = p then BOT else CState.x_var cs x) \<rparr>"
  shows "\<exists>ts'. T_D3 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  let ?j = "CState.j_var cs p"
  have tpc_loop: "t_pc ts p = ''TD_Loop''" using sim pc unfolding Simulation_R_def Let_def by auto

  (* Split on whether the BOT slot is still owned by an E2 thread. *)
  have "(\<exists>k. CState.i_var cs k = ?j \<and> c_program_counter cs k = ''E2'') \<or> 
        (\<forall>k. CState.i_var cs k = ?j \<longrightarrow> c_program_counter cs k \<noteq> ''E2'')" by blast
  then consider (has_k) "\<exists>k. CState.i_var cs k = ?j \<and> c_program_counter cs k = ''E2''" 
              | (no_k)  "\<forall>k. CState.i_var cs k = ?j \<longrightarrow> c_program_counter cs k \<noteq> ''E2''" by blast
  then show ?thesis
  proof cases
    case no_k
    (* If no thread is pending in E2 and the concrete slot is BOT, the TSQ side may stutter. *)
    let ?ts' = ts
    have "Simulation_R (cs', us) ts"
    proof (unfold Simulation_R_def Let_def fst_conv snd_conv, intro conjI)
      (* Condition 6: one-way mapping in the no_k branch. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
        (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
          (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
          (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT))
        \<longrightarrow> v \<in> t_scanned ts q)"
      proof (intro allI impI)
        fix q v assume pc_q': "c_program_counter cs' q = ''D3''"
        assume "\<exists>idx<CState.j_var cs' q. 
               (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
               (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
        then obtain idx where idx_less: "idx < CState.j_var cs' q" and 
             cond: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                    (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
             by blast

        show "v \<in> t_scanned ts q"
        proof (cases "q = p")
          case False
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q' False cs'_eq by auto
          have j_q_eq: "CState.j_var cs' q = CState.j_var cs q" using False cs'_eq by simp
          have old_imp: "(\<exists>idx<CState.j_var cs q. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts q"
            using sim pc_q_old unfolding Simulation_R_def Let_def by simp

          have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by simp
          have i_var_eq: "CState.i_var cs' = CState.i_var cs" using cs'_eq by simp
          have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using cs'_eq pc by (cases "v = p") auto
          have old_rhs: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
            using cond unfolding q_arr_eq i_var_eq pc_v_eq by blast
            
          have "idx < CState.j_var cs q" using idx_less j_q_eq by simp
          with old_imp old_rhs show ?thesis by blast
        next
          case True
          have j_new: "CState.j_var cs' p = ?j + 1" using cs'_eq by simp
          have old_imp: "(\<exists>idx<?j. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts p"
            using sim pc unfolding Simulation_R_def Let_def by simp

          show ?thesis
          proof (cases "idx < ?j")
            case True
            have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by simp
            have i_var_eq: "CState.i_var cs' = CState.i_var cs" using cs'_eq by simp
            have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using cs'_eq pc by (cases "v = p") auto
            have old_rhs: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
              using cond True unfolding q_arr_eq i_var_eq pc_v_eq by blast
            with old_imp True have "v \<in> t_scanned ts p" by blast
            thus ?thesis using `q = p` by simp
          next
            case False
            with idx_less j_new `q = p` have idx_eq_j: "idx = ?j" by simp
            have q_bot_cs': "CState.Q_arr cs' idx = BOT" using q_bot cs'_eq idx_eq_j by simp
            
            have pc_v_cs': "c_program_counter cs' v = ''E2''" 
             and i_v_cs': "CState.i_var cs' v = ?j" 
              using cond q_bot_cs' idx_eq_j by auto
              
            have v_neq_p: "v \<noteq> p" using pc_v_cs' cs'_eq by force
            have pc_v_old: "c_program_counter cs v = ''E2''" using pc_v_cs' cs'_eq v_neq_p by auto
            have i_v_old: "CState.i_var cs v = ?j" using i_v_cs' cs'_eq by simp
            
            with pc_v_old no_k show ?thesis by blast
          qed
        qed
      qed

      (* The remaining unchanged-state obligations are discharged automatically. *)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ts q = ''TL0''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ts q = ''TE1''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ts q = ''TE2''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ts q = ''TE3''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ts q = ''TD1''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ts q = ''TD_Line4_Done''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq tpc_loop show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ts q = ''TD_Loop''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ts q = ''TD_Remove_Done''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      
      from sim cs'_eq show "\<forall>q. \<forall>node\<in>set (pools ts q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node" unfolding Simulation_R_def Let_def by (auto split: if_splits)
          from sim cs'_eq show
        "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow>
           (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
        unfolding Simulation_R_def Let_def
        by (auto split: if_splits)
  from sim cs'_eq show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ts u))" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      
      show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> 
            (\<forall>idx<CState.l_var cs' q. 
              (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)) \<and> 
              (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q))"
      proof (intro allI impI)
        fix q idx
        assume "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''"
           and "idx < CState.l_var cs' q"
        have pc_q: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" 
          using `c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''` cs'_eq pc by (auto split: if_splits)
        have l_var_eq: "CState.l_var cs q = CState.l_var cs' q" using cs'_eq by simp
        have idx_less: "idx < CState.l_var cs q" using `idx < CState.l_var cs' q` l_var_eq by simp
        
        show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)) \<and> 
              (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q)"
        proof
          show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)"
            using sim pc_q idx_less cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)
          show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q"
          proof (intro allI impI)
            fix u
            assume "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
            then have q_arr_bot: "CState.Q_arr cs idx = BOT" 
                  and pc_u: "c_program_counter cs u = ''E2''" 
                  and i_var_u: "CState.i_var cs u = idx" 
              using cs'_eq by (auto split: if_splits)
            have "\<forall>q. (c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3'') \<longrightarrow> 
                   (\<forall>idx<CState.l_var cs q. (\<forall>u. CState.Q_arr cs idx = BOT \<and> c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q))"
              using sim unfolding Simulation_R_def Let_def by simp 
            thus "t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q" using pc_q idx_less q_arr_bot pc_u i_var_u by blast
          qed
        qed
      qed

      from sim cs'_eq pc show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ts q = BOT \<and> t_candTs ts q = TOP" unfolding Simulation_R_def Let_def by (auto split: if_splits) 
      from sim cs'_eq show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "nid_counter ts = CState.X_var cs'" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ts q = CState.i_var cs' q" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      
      show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
           (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
      proof (intro allI impI)
        fix q u nid v ts_val
        assume "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
        then have "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" using cs'_eq pc by (auto split: if_splits)
        assume "(nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val"
        have cond13: "\<forall>q. c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
           (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs q)"
          using sim unfolding Simulation_R_def Let_def by auto 
        have "nid < CState.l_var cs q" 
          using cond13 `c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}` `(nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val` by blast
        thus "nid < CState.l_var cs' q" using cs'_eq by simp
      qed     
      
      show "\<forall>q u. c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' u \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts u) (t_ts ts q) \<longrightarrow> CState.i_var cs' q < CState.l_var cs' u"
      proof (intro allI impI)
        fix q u
        assume "c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' u \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts u) (t_ts ts q)"
        then have pc_q: "c_program_counter cs q \<in> {''E2'', ''E3''}"
              and pc_u: "c_program_counter cs u \<in> {''D2'', ''D3'', ''D4''}"
              and ts_cond: "\<not> ts_less (t_startTs ts u) (t_ts ts q)"
          using cs'_eq pc by (auto split: if_splits)
        have cond14: "\<forall>q1 q2. c_program_counter cs q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts q2) (t_ts ts q1) \<longrightarrow> CState.i_var cs q1 < CState.l_var cs q2"
          using sim unfolding Simulation_R_def Let_def by auto
        have "CState.i_var cs q < CState.l_var cs u"
          using cond14 pc_q pc_u ts_cond by blast
        thus "CState.i_var cs' q < CState.l_var cs' u" using cs'_eq by simp
      qed     
      
      from sim cs'_eq show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)" unfolding Simulation_R_def Let_def by (auto split: if_splits)

    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
      proof (intro allI impI)
        fix u nid v ts_val
        assume cond: "(nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP"
        have old_call: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
          using sim cond unfolding Simulation_R_def Let_def fst_conv snd_conv by blast
        have his_eq: "his_seq (cs', us) = his_seq (cs, us)"
          by (simp add: his_seq_def)
        show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
        proof -
          from old_call obtain sn where old_sn: "EnqCallInHis (cs, us) u v sn"
            by blast
          have "EnqCallInHis (cs', us) u v sn"
            using old_sn unfolding EnqCallInHis_def his_eq by simp
          thus ?thesis by blast
        qed
      qed

             (* Condition 17: one-way boundary condition for t_scanned. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ts q \<longrightarrow> 
            (\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
        proof (intro allI impI)
          fix q v
          assume pc_q_new: "c_program_counter cs' q = ''D3''"
             and v_in_scan: "v \<in> t_scanned ts q"

          have pc_global_eq: "c_program_counter cs' = c_program_counter cs"
            using cs'_eq pc by auto
          have pc_q_old: "c_program_counter cs q = ''D3''"
            using pc_q_new pc_global_eq by simp

          have old_cond17: "\<exists>idx < CState.j_var cs q. 
              (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            using sim pc_q_old v_in_scan
            unfolding Simulation_R_def Let_def
            by simp

          then obtain idx where idx_lt_old: "idx < CState.j_var cs q" and
               rhs_old: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
                         (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            by blast

          have idx_lt_new: "idx < CState.j_var cs' q"
            using idx_lt_old cs'_eq by (cases "q = p") auto

          show "\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
          proof (rule exI[where x=idx], rule conjI)
            show "idx < CState.j_var cs' q"
              by (rule idx_lt_new)
          next
            from rhs_old show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
            proof (elim disjE)
              assume "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
              thus ?thesis
                using pc_global_eq cs'_eq by auto
            next
              assume "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
              then obtain v_val sn where
                  his: "EnqCallInHis (cs, us) v v_val sn"
                and inq: "InQBack (cs, us) v_val"
                and idx_eq: "Idx (cs, us) v_val = idx"
                by blast

              have his_new: "EnqCallInHis (cs', us) v v_val sn"
                using his cs'_eq unfolding EnqCallInHis_def his_seq_def by simp

              have inq_new: "InQBack (cs', us) v_val"
              proof -
                from inq obtain k_pos where
                  k_val: "Qback_arr (cs, us) k_pos = v_val"
                  unfolding InQBack_def by blast
                have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
                  using cs'_eq unfolding Qback_arr_def by simp
                with k_val have "Qback_arr (cs', us) k_pos = v_val"
                  by simp
                thus ?thesis
                  unfolding InQBack_def by blast
              qed

              have idx_new: "Idx (cs', us) v_val = idx"
              proof -
                have "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
                  using cs'_eq unfolding AtIdx_def Qback_arr_def by simp
                thus ?thesis
                  using idx_eq unfolding Idx_def by presburger
              qed

              from his_new inq_new idx_new show ?thesis
                by blast
            qed
          qed
        qed

      (* Condition 18: inherited directly in the stuttering branch. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
        (\<forall>v \<in> t_scanned ts q. \<forall>nid v_val ts_val. 
          (nid, v_val, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
          nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ts q))"
      proof (intro allI impI ballI, elim conjE)
        fix q v nid v_val ts_val
        assume pc_q_new: "c_program_counter cs' q = ''D3''"
           and v_scan: "v \<in> t_scanned ts q"
           and in_pool: "(nid, v_val, ts_val) \<in> set (pools ts v)"
           and not_top: "ts_val \<noteq> TOP"
           
        have pc_q_old: "c_program_counter cs q = ''D3''"
          using pc_q_new cs'_eq pc by (cases "q = p") auto
          
        have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
          using sim pc_q_old v_scan in_pool not_top unfolding Simulation_R_def Let_def
          by (metis split_pairs2) 
          
        have j_new_ge: "CState.j_var cs q \<le> CState.j_var cs' q"
          using cs'_eq by simp
          
        from old_cond18 show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ts q)"
          using j_new_ge by auto
      qed

      (* Condition 19: inherited directly in the stuttering branch. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
        (\<forall>u \<in> t_scanned ts q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
          CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q))"
      proof (intro allI impI ballI)
        fix q u
        assume pc_q: "c_program_counter cs' q = ''D3''"
        assume u_scan: "u \<in> t_scanned ts q"
        assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
        
        have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q cs'_eq pc by (cases "q = p") auto
        
        have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}"
          using pc_u_new cs'_eq by (cases "u = p") auto
          
        have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
          using sim pc_q_old u_scan pc_u_old unfolding Simulation_R_def Let_def
          by (metis fst_conv) 
          
        have j_new_ge: "CState.j_var cs q \<le> CState.j_var cs' q" using cs'_eq by simp
        have i_eq: "CState.i_var cs' u = CState.i_var cs u" using cs'_eq by (cases "u = p") auto
        
        show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
          using old_cond19 j_new_ge i_eq by auto
      qed

      (* Condition 20.1: synchronization of the global value allocator. *)
      show "CState.V_var cs' = t_V_var ts" 
        using sim cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)

      (* Condition 20.2: synchronization of the local snapshots. *)
      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ts q" 
        using sim cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)

    qed
    
      (* The TSQ side performs a legal stuttering step. *)
      have "T_D3 p ts ts" 
        unfolding T_D3_def Let_def using tpc_loop by blast

    then show ?thesis using `Simulation_R (cs', us) ts` by blast
    
  next
    case has_k
    then obtain k where k_idx: "CState.i_var cs k = ?j" and pc_k: "c_program_counter cs k = ''E2''" by blast
    show ?thesis
    proof (cases "k \<in> t_scanned ts p")
      case True
      (* If k has already been scanned, the TSQ side may stutter. *)
      let ?ts' = ts
      have "Simulation_R (cs', us) ts"
      proof (unfold Simulation_R_def Let_def fst_conv snd_conv, intro conjI)
        
        (* Condition 6: updated one-way mapping in the has_k / True branch. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
            (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
            (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT))
          \<longrightarrow> v \<in> t_scanned ts q)"
        proof (intro allI impI)
          fix q v assume pc_q': "c_program_counter cs' q = ''D3''"
          assume "\<exists>idx<CState.j_var cs' q. 
                 (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                 (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
          then obtain idx where idx_less: "idx < CState.j_var cs' q" and 
               cond: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                      (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
                 by blast

          show "v \<in> t_scanned ts q"
          proof (cases "q = p")
            case False
            have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q' False cs'_eq by auto
            have j_q_eq: "CState.j_var cs' q = CState.j_var cs q" using False cs'_eq by simp
            have old_imp: "(\<exists>idx<CState.j_var cs q. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts q"
              using sim pc_q_old unfolding Simulation_R_def Let_def by simp

            have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by simp
            have i_var_eq: "CState.i_var cs' = CState.i_var cs" using cs'_eq by simp
            have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using cs'_eq pc by (cases "v = p") auto
            have old_rhs: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
              using cond True unfolding q_arr_eq i_var_eq pc_v_eq by blast
              
            have "idx < CState.j_var cs q" using idx_less j_q_eq by simp
            with old_imp old_rhs show ?thesis by blast
          next
            case True
            have j_new: "CState.j_var cs' p = ?j + 1" using cs'_eq by simp
            have old_imp: "(\<exists>idx<?j. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts p"
              using sim pc unfolding Simulation_R_def Let_def by simp

            show ?thesis
            proof (cases "idx < ?j")
              case True
              have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by simp
              have i_var_eq: "CState.i_var cs' = CState.i_var cs" using cs'_eq by simp
              have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using cs'_eq pc by (cases "v = p") auto
              have old_rhs: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
                using cond True unfolding q_arr_eq i_var_eq pc_v_eq by blast
                
              with old_imp True have "v \<in> t_scanned ts p" by blast
              thus ?thesis using `q = p` by simp
            next
              case False
              with idx_less j_new `q = p` have idx_eq_j: "idx = ?j" by simp
              have q_bot_cs': "CState.Q_arr cs' idx = BOT" using q_bot cs'_eq idx_eq_j by simp
              
              have pc_v_cs': "c_program_counter cs' v = ''E2''" and i_v_cs': "CState.i_var cs' v = ?j" 
                using cond q_bot_cs' idx_eq_j by auto
              have v_neq_p: "v \<noteq> p" using pc_v_cs' cs'_eq by force
              
              have pc_v_old: "c_program_counter cs v = ''E2''" using pc_v_cs' cs'_eq v_neq_p by auto
              have i_v_old: "CState.i_var cs v = ?j" using i_v_cs' cs'_eq by simp
              
              have "k = v"
              proof (rule ccontr)
                assume "k \<noteq> v"
                with inv_sys pc_k pc_v_old i_v_old k_idx show False unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def by fastforce
              qed
              with `k \<in> t_scanned ts p` `q = p` show ?thesis by simp
            qed
          qed
        qed

        (* The remaining obligations are inherited automatically. *)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ts q = ''TL0''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ts q = ''TE1''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ts q = ''TE2''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ts q = ''TE3''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ts q = ''TD1''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ts q = ''TD_Line4_Done''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq tpc_loop show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ts q = ''TD_Loop''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ts q = ''TD_Remove_Done''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        
        from sim cs'_eq show "\<forall>q. \<forall>node\<in>set (pools ts q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show
        "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow>
           (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
        unfolding Simulation_R_def Let_def
        by (auto split: if_splits)
        from sim cs'_eq show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ts u))" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        
        show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> 
              (\<forall>idx<CState.l_var cs' q. 
                (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)) \<and> 
                (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q))"
        proof (intro allI impI)
          fix q idx
          assume "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''" and "idx < CState.l_var cs' q"
          have pc_q: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" using `c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''` cs'_eq pc by (auto split: if_splits)
          have l_var_eq: "CState.l_var cs q = CState.l_var cs' q" using cs'_eq by simp
          have idx_less: "idx < CState.l_var cs q" using `idx < CState.l_var cs' q` l_var_eq by simp
          show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)) \<and> 
                (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q)"
          proof
            show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)" using sim pc_q idx_less cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)
            show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q"
            proof (intro allI impI)
              fix u
              assume "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
              then have q_arr_bot: "CState.Q_arr cs idx = BOT" and pc_u: "c_program_counter cs u = ''E2''" and i_var_u: "CState.i_var cs u = idx" using cs'_eq by (auto split: if_splits)
              have "\<forall>q. (c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3'') \<longrightarrow> 
                     (\<forall>idx<CState.l_var cs q. (\<forall>u. CState.Q_arr cs idx = BOT \<and> c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q))" using sim unfolding Simulation_R_def Let_def by simp 
              thus "t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q" using pc_q idx_less q_arr_bot pc_u i_var_u by blast
            qed
          qed
        qed

        from sim cs'_eq pc show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ts q = BOT \<and> t_candTs ts q = TOP" unfolding Simulation_R_def Let_def by (auto split: if_splits) 
        from sim cs'_eq show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "nid_counter ts = CState.X_var cs'" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ts q = CState.i_var cs' q" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        
        show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
             (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
        proof (intro allI impI)
          fix q u nid v ts_val
          assume "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
          then have "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" using cs'_eq pc by (auto split: if_splits)
          assume "(nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val"
          have cond13: "\<forall>q. c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
             (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs q)"
            using sim unfolding Simulation_R_def Let_def by auto 
          have "nid < CState.l_var cs q" using cond13 `c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}` `(nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val` by blast
          thus "nid < CState.l_var cs' q" using cs'_eq by simp
        qed     
        
        show "\<forall>q u. c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' u \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts u) (t_ts ts q) \<longrightarrow> CState.i_var cs' q < CState.l_var cs' u"
        proof (intro allI impI)
          fix q u
          assume "c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' u \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts u) (t_ts ts q)"
          then have pc_q: "c_program_counter cs q \<in> {''E2'', ''E3''}" and pc_u: "c_program_counter cs u \<in> {''D2'', ''D3'', ''D4''}" and ts_cond: "\<not> ts_less (t_startTs ts u) (t_ts ts q)" using cs'_eq pc by (auto split: if_splits)
          have cond14: "\<forall>q1 q2. c_program_counter cs q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts q2) (t_ts ts q1) \<longrightarrow> CState.i_var cs q1 < CState.l_var cs q2" using sim unfolding Simulation_R_def Let_def by auto
          have "CState.i_var cs q < CState.l_var cs u" using cond14 pc_q pc_u ts_cond by blast
          thus "CState.i_var cs' q < CState.l_var cs' u" using cs'_eq by simp
        qed     
        
        from sim cs'_eq show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)" unfolding Simulation_R_def Let_def by (auto split: if_splits)

               show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
        proof (intro allI impI)
          fix u nid v ts_val
          assume cond: "(nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP"
          have old_call: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
            using sim cond unfolding Simulation_R_def Let_def fst_conv snd_conv by blast
          have his_eq: "his_seq (cs', us) = his_seq (cs, us)"
            by (simp add: his_seq_def)
          show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
          proof -
            from old_call obtain sn where old_sn: "EnqCallInHis (cs, us) u v sn"
              by blast
            have "EnqCallInHis (cs', us) u v sn"
              using old_sn unfolding EnqCallInHis_def his_eq by simp
            thus ?thesis by blast
          qed
        qed

        (* Condition 17: one-way boundary condition for t_scanned. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ts q \<longrightarrow> 
            (\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
        proof (intro allI impI)
          fix q v
          assume pc_q_new: "c_program_counter cs' q = ''D3''"
             and v_in_scan: "v \<in> t_scanned ts q"

          have pc_global_eq: "c_program_counter cs' = c_program_counter cs"
            using cs'_eq pc by auto
          have pc_q_old: "c_program_counter cs q = ''D3''"
            using pc_q_new pc_global_eq by simp

          have old_cond17: "\<exists>idx < CState.j_var cs q. 
              (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            using sim pc_q_old v_in_scan unfolding Simulation_R_def Let_def
            by simp

          then obtain idx where idx_lt_old: "idx < CState.j_var cs q" and
               rhs_old: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
                         (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            by blast

          have idx_lt_new: "idx < CState.j_var cs' q"
            using idx_lt_old cs'_eq by (cases "q = p") auto

          show "\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
          proof (rule exI[where x=idx], rule conjI)
            show "idx < CState.j_var cs' q"
              by (rule idx_lt_new)
          next
            from rhs_old show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                                 (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
            proof (elim disjE)
              assume "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
              thus ?thesis using pc_global_eq cs'_eq by auto
            next
              assume "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
              then obtain v_val sn where
                  his: "EnqCallInHis (cs, us) v v_val sn"
                and inq: "InQBack (cs, us) v_val"
                and idx_eq: "Idx (cs, us) v_val = idx"
                by blast

              have his_new: "EnqCallInHis (cs', us) v v_val sn"
                using his cs'_eq unfolding EnqCallInHis_def his_seq_def by simp

              have inq_new: "InQBack (cs', us) v_val"
              proof -
                from inq obtain k_pos where
                  k_val: "Qback_arr (cs, us) k_pos = v_val"
                  unfolding InQBack_def by blast
                have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
                  using cs'_eq unfolding Qback_arr_def by simp
                with k_val have "Qback_arr (cs', us) k_pos = v_val"
                  by simp
                thus ?thesis unfolding InQBack_def by blast
              qed

              have idx_new: "Idx (cs', us) v_val = idx"
              proof -
                have "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
                  using cs'_eq unfolding AtIdx_def Qback_arr_def by simp
                thus ?thesis using idx_eq unfolding Idx_def by presburger
              qed

              from his_new inq_new idx_new show ?thesis by blast
            qed
          qed
        qed

        (* Condition 18: inherited directly in the stuttering branch. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v \<in> t_scanned ts q. \<forall>nid v_val ts_val. 
            (nid, v_val, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
            nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ts q))"
        proof (intro allI impI ballI, elim conjE)
          fix q v nid v_val ts_val
          assume pc_q_new: "c_program_counter cs' q = ''D3''"
             and v_scan: "v \<in> t_scanned ts q"
             and in_pool: "(nid, v_val, ts_val) \<in> set (pools ts v)"
             and not_top: "ts_val \<noteq> TOP"
             
          have pc_q_old: "c_program_counter cs q = ''D3''"
            using pc_q_new cs'_eq pc by (cases "q = p") auto
            
          have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
            using sim pc_q_old v_scan in_pool not_top unfolding Simulation_R_def Let_def
            by (metis split_pairs2) 
            
          have j_new_ge: "CState.j_var cs q \<le> CState.j_var cs' q"
            using cs'_eq by simp
            
          from old_cond18 show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ts q)"
            using j_new_ge by auto
        qed

        (* Condition 19: inherited directly in the stuttering branch. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>u \<in> t_scanned ts q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
            CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q))"
        proof (intro allI impI ballI)
          fix q u
          assume pc_q: "c_program_counter cs' q = ''D3''"
          assume u_scan: "u \<in> t_scanned ts q"
          assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
          
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q cs'_eq pc by (cases "q = p") auto
          have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new cs'_eq by (cases "u = p") auto
          
          have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
            using sim pc_q_old u_scan pc_u_old unfolding Simulation_R_def Let_def
            by (metis fst_conv)
            
          have j_new_ge: "CState.j_var cs q \<le> CState.j_var cs' q" using cs'_eq by simp
          have i_eq: "CState.i_var cs' u = CState.i_var cs u" using cs'_eq by (cases "u = p") auto
          
          show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
            using old_cond19 j_new_ge i_eq by auto
        qed

      (* Condition 20.1: synchronization of the global value allocator. *)
      show "CState.V_var cs' = t_V_var ts" 
        using sim cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)

      (* Condition 20.2: synchronization of the local snapshots. *)
      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ts q" 
        using sim cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)
      qed
      
      (* The TSQ side performs a legal stuttering step. *)
      have "T_D3 p ts ts" 
        unfolding T_D3_def Let_def using tpc_loop by blast

    then show ?thesis using `Simulation_R (cs', us) ts` by blast
    
  next
    case False
    (* If k has not been scanned yet, perform one real T_D3_Scan step and add k to the scanned set. *)
    have oldest_bot: "fst (pool_getOldest (pools ts k)) = BOT"
      using unscanned_pending_has_no_old_nodes[OF inv_sys sim pc pc_k k_idx q_bot False] .
      
    let ?ts_scan = "ts\<lparr> t_scanned := (\<lambda>x. if x = p then t_scanned ts p \<union> {k} else t_scanned ts x) \<rparr>"
    have step_scan: "T_D3_Scan p k ts ?ts_scan"
    proof -
      obtain nid0 tstamp0 where oldest_eq: "pool_getOldest (pools ts k) = (nid0, tstamp0)"
        by (cases "pool_getOldest (pools ts k)") auto
      with oldest_bot have "nid0 = BOT" by simp
      have eq_ext: "\<And>f. (\<lambda>x. if x = p then f p else f x) = f" by auto
        have "k \<in> ProcSet"
          using E2_in_ProcSet pc_k
          by blast
      show ?thesis unfolding T_D3_Scan_def Let_def using tpc_loop False oldest_eq `nid0 = BOT` `k \<in> ProcSet` eq_ext by (simp add: eq_ext)
    qed
      
    have "Simulation_R (cs', us) ?ts_scan"
    proof (unfold Simulation_R_def Let_def fst_conv snd_conv, intro conjI)

      (* Condition 6: updated one-way mapping in the has_k / False branch. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
        (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
          (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts_scan v) \<and> ts_val \<noteq> TOP)) \<or> 
          (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT))
        \<longrightarrow> v \<in> t_scanned ?ts_scan q)"
      proof (intro allI impI)
        fix q v assume pc_q': "c_program_counter cs' q = ''D3''"
        assume "\<exists>idx<CState.j_var cs' q. 
               (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts_scan v) \<and> ts_val \<noteq> TOP)) \<or> 
               (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
        then obtain idx where idx_less: "idx < CState.j_var cs' q" and 
             cond: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts_scan v) \<and> ts_val \<noteq> TOP)) \<or> 
                    (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
               by blast

        show "v \<in> t_scanned ?ts_scan q"
        proof (cases "q = p")
          case False
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q' False cs'_eq by auto
          have j_q_eq: "CState.j_var cs' q = CState.j_var cs q" using False cs'_eq by simp
          have old_imp: "(\<exists>idx<CState.j_var cs q. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts q"
            using sim pc_q_old unfolding Simulation_R_def Let_def by simp

          have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by simp
          have i_var_eq: "CState.i_var cs' = CState.i_var cs" using cs'_eq by simp
          have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using cs'_eq pc by (cases "v = p") auto
          have pools_eq: "pools ?ts_scan v = pools ts v" by simp
          
          have old_rhs: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
            using cond unfolding q_arr_eq i_var_eq pc_v_eq pools_eq by blast
            
          have "idx < CState.j_var cs q" using idx_less j_q_eq by simp
          with old_imp old_rhs have "v \<in> t_scanned ts q" by blast
          thus ?thesis using False by simp
        next
          case True
          have j_new: "CState.j_var cs' p = ?j + 1" using cs'_eq by simp
          have old_imp: "(\<exists>idx<?j. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts p"
            using sim pc unfolding Simulation_R_def Let_def by simp

          show ?thesis
          proof (cases "idx < ?j")
            case True
            have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by simp
            have i_var_eq: "CState.i_var cs' = CState.i_var cs" using cs'_eq by simp
            have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using cs'_eq pc by (cases "v = p") auto
            have pools_eq: "pools ?ts_scan v = pools ts v" by simp

            have old_rhs: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
              using cond True unfolding q_arr_eq i_var_eq pc_v_eq pools_eq by blast
            with old_imp True have "v \<in> t_scanned ts p" by blast
            thus ?thesis using `q = p` by auto
          next
            case False
            with idx_less j_new `q = p` have idx_eq_j: "idx = ?j" by simp
            have "CState.Q_arr cs' idx = BOT" using q_bot cs'_eq idx_eq_j by simp
            with cond have "c_program_counter cs' v = ''E2''" and "CState.i_var cs' v = ?j" using idx_eq_j by auto
            have q_bot_cs': "CState.Q_arr cs' idx = BOT" using q_bot cs'_eq idx_eq_j by simp
            have pc_v_cs': "c_program_counter cs' v = ''E2''" and i_v_cs': "CState.i_var cs' v = ?j" 
              using cond q_bot_cs' idx_eq_j by auto
            have v_neq_p: "v \<noteq> p" using pc_v_cs' cs'_eq by force
            
            have pc_v_old: "c_program_counter cs v = ''E2''" using pc_v_cs' cs'_eq v_neq_p by auto
            have i_v_old: "CState.i_var cs v = ?j" using i_v_cs' cs'_eq by simp
            
            have "k = v"
            proof (rule ccontr)
              assume "k \<noteq> v"
              with inv_sys pc_k pc_v_old i_v_old k_idx show False unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def by fastforce
            qed
            thus ?thesis using `q = p` by simp
          qed
        qed
      qed

      (* The remaining obligations are inherited automatically. *)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts_scan q = ''TL0''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts_scan q = ''TE1''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts_scan q = ''TE2''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts_scan q = ''TE3''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts_scan q = ''TD1''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts_scan q = ''TD_Line4_Done''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq tpc_loop show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts_scan q = ''TD_Loop''" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts_scan q = ''TD_Remove_Done''" unfolding Simulation_R_def Let_def by (auto split: if_splits)

      from sim cs'_eq show "\<forall>q. \<forall>node\<in>set (pools ?ts_scan q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts_scan q = ''TE2'' \<and> t_nid ?ts_scan q = fst node" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show
      "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow>
         (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts_scan u) \<and> ts_val \<noteq> TOP)"
      unfolding Simulation_R_def Let_def
      by (auto split: if_splits)
      from sim cs'_eq show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts_scan u))" unfolding Simulation_R_def Let_def by (auto split: if_splits)
        from sim cs'_eq show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts_scan q)) = 1" unfolding Simulation_R_def Let_def by (auto split: if_splits)

      show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> 
            (\<forall>idx<CState.l_var cs' q. 
              (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts_scan u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts_scan q)) \<and> 
              (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts_scan u <\<^sub>t\<^sub>s t_startTs ?ts_scan q))"
      proof (intro allI impI)
        fix q idx assume "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''" and "idx < CState.l_var cs' q"
        have ts_eq: "t_startTs ?ts_scan q = t_startTs ts q" by simp
        have pools_eq: "\<And>u. pools ?ts_scan u = pools ts u" by simp
        have t_ts_eq: "\<And>u. t_ts ?ts_scan u = t_ts ts u" by simp
        have pc_q_old: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" using `c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''` cs'_eq pc by (auto split: if_splits)
        have l_var_eq: "CState.l_var cs q = CState.l_var cs' q" using cs'_eq by simp
        have idx_less: "idx < CState.l_var cs q" using `idx < CState.l_var cs' q` l_var_eq by simp
        have old_cond8: "(CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)) \<and> 
                        (\<forall>u. CState.Q_arr cs idx = BOT \<and> c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q)"
          using sim pc_q_old idx_less unfolding Simulation_R_def Let_def by auto
        show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts_scan u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts_scan q)) \<and> 
              (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts_scan u <\<^sub>t\<^sub>s t_startTs ?ts_scan q)"
          using old_cond8 ts_eq pools_eq t_ts_eq cs'_eq by auto
      qed
      
    from sim cs'_eq pc tpc_loop show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts_scan q = BOT \<and> t_candTs ?ts_scan q = TOP" unfolding Simulation_R_def Let_def by (auto split: if_splits)
    from sim cs'_eq show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts_scan u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'" unfolding Simulation_R_def Let_def by (auto split: if_splits)
    from sim cs'_eq show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts_scan u) \<longrightarrow> v \<in> Val" unfolding Simulation_R_def Let_def by (auto split: if_splits)
    from sim cs'_eq show "nid_counter ?ts_scan = CState.X_var cs'" unfolding Simulation_R_def Let_def by (auto split: if_splits)
    from sim cs'_eq show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts_scan q = CState.i_var cs' q" unfolding Simulation_R_def Let_def by (auto split: if_splits)

      show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
            (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts_scan u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts_scan q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
      proof (intro allI impI)
        fix q u nid v ts_val
        assume pc_q_new: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
        assume node_cond: "(nid, v, ts_val) \<in> set (pools ?ts_scan u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts_scan q) ts_val"
        have startTs_eq: "t_startTs ?ts_scan q = t_startTs ts q" by simp
        have pools_eq: "pools ?ts_scan u = pools ts u" by simp
        have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" using pc_q_new cs'_eq pc by (auto split: if_splits)
        have old_cond13: "\<forall>q. c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
           (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs q)"
          using sim unfolding Simulation_R_def Let_def by simp
        from node_cond startTs_eq pools_eq have exist_witness: "\<exists>v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val" by auto
        have l_eq: "CState.l_var cs' q = CState.l_var cs q" using cs'_eq by simp
        have "nid < CState.l_var cs q" using old_cond13 pc_q_old exist_witness by blast
        show "nid < CState.l_var cs' q" using `nid < CState.l_var cs q` l_eq by simp
      qed

      show "\<forall>q u. c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' u \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts_scan u) (t_ts ?ts_scan q) \<longrightarrow> CState.i_var cs' q < CState.l_var cs' u"
      proof (intro allI impI)
        fix q u assume cond_new: "c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' u \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts_scan u) (t_ts ?ts_scan q)"
        have ts_u_eq: "t_startTs ?ts_scan u = t_startTs ts u" by simp
        have t_ts_q_eq: "t_ts ?ts_scan q = t_ts ts q" by simp
        have pc_q_old: "c_program_counter cs q \<in> {''E2'', ''E3''}" using cond_new cs'_eq by (auto split: if_splits)
        have pc_u_old: "c_program_counter cs u \<in> {''D2'', ''D3'', ''D4''}" using cond_new cs'_eq pc by (auto split: if_splits)
        have old_cond14: "\<forall>q u. c_program_counter cs q \<in> {''E2'', ''E3''} \<and> c_program_counter cs u \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts u) (t_ts ts q) \<longrightarrow> CState.i_var cs q < CState.l_var cs u"
          using sim unfolding Simulation_R_def Let_def by simp
        show "CState.i_var cs' q < CState.l_var cs' u" using old_cond14 pc_q_old pc_u_old ts_u_eq t_ts_q_eq cond_new cs'_eq by auto
      qed

      from sim cs'_eq show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts_scan u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)" unfolding Simulation_R_def Let_def by (auto split: if_splits)
      from sim cs'_eq show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts_scan u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)" unfolding Simulation_R_def Let_def by (auto split: if_splits)

           show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts_scan u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
      proof (intro allI impI)
        fix u nid v ts_val
        assume cond: "(nid, v, ts_val) \<in> set (pools ?ts_scan u) \<and> ts_val \<noteq> TOP"
        have in_old_pool: "(nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP"
          using cond by simp
        have old_call: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
          using sim in_old_pool unfolding Simulation_R_def Let_def fst_conv snd_conv by blast
        have his_eq: "his_seq (cs', us) = his_seq (cs, us)"
          by (simp add: his_seq_def)
        show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
        proof -
          from old_call obtain sn where old_sn: "EnqCallInHis (cs, us) u v sn"
            by blast
          have "EnqCallInHis (cs', us) u v sn"
            using old_sn unfolding EnqCallInHis_def his_eq by simp
          thus ?thesis by blast
        qed
      qed

      (* Condition 17: boundary condition for t_scanned. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
        (\<forall>v. v \<in> t_scanned ?ts_scan q \<longrightarrow> 
          (\<exists>idx < CState.j_var cs' q. 
            (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
            (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
      proof (intro allI impI)
        fix q v
        assume pc_q_new: "c_program_counter cs' q = ''D3''"
           and v_in_scan_new: "v \<in> t_scanned ?ts_scan q"

        have pc_global_eq: "c_program_counter cs' = c_program_counter cs"
          using cs'_eq pc by auto
        hence pc_q_old: "c_program_counter cs q = ''D3''"
          using pc_q_new by simp

        have j_eq: "CState.j_var cs' q = (if q = p then ?j + 1 else CState.j_var cs q)"
          using cs'_eq by simp
        have scan_eq: "t_scanned ?ts_scan q = (if q = p then t_scanned ts p \<union> {k} else t_scanned ts q)"
          by simp

        show "\<exists>idx < CState.j_var cs' q. 
            (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
            (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (cases "q = p \<and> v = k")
          case True
          have "v = k" and "q = p"
            using True by auto

          have "k \<noteq> p"
            using pc pc_k by auto

          have pc_k_new: "c_program_counter cs' v = ''E2''"
            using pc_k cs'_eq `v = k` `k \<noteq> p` pc by auto
          have i_k_new: "CState.i_var cs' v = ?j"
            using k_idx cs'_eq `v = k` `k \<noteq> p` by simp
          have idx_bound: "?j < CState.j_var cs' q"
            using j_eq `q = p` by simp

          show ?thesis
          proof (rule exI[where x="?j"], rule conjI)
            show "?j < CState.j_var cs' q"
              by (rule idx_bound)
          next
            show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = ?j) \<or> 
                  (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = ?j)"
              using pc_k_new i_k_new by simp
          qed

        next
          case False
          have v_in_scan_old: "v \<in> t_scanned ts q"
            using v_in_scan_new scan_eq False
            by (metis (lifting) Un_iff singletonD)

          have old_cond17: "\<exists>idx < CState.j_var cs q. 
              (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            using sim pc_q_old v_in_scan_old unfolding Simulation_R_def Let_def
            by simp

          then obtain idx where idx_lt_old: "idx < CState.j_var cs q" and
               rhs_old: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
                         (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            by blast

          have idx_lt_new: "idx < CState.j_var cs' q"
            using idx_lt_old j_eq by (cases "q = p") auto

          show ?thesis
          proof (rule exI[where x=idx], rule conjI)
            show "idx < CState.j_var cs' q"
              by (rule idx_lt_new)
          next
            from rhs_old show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                               (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
            proof (elim disjE)
              assume "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
              thus ?thesis
                using pc_global_eq cs'_eq by auto
            next
              assume "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
              then obtain v_val sn where
                  his: "EnqCallInHis (cs, us) v v_val sn"
                and inq: "InQBack (cs, us) v_val"
                and idx_eq: "Idx (cs, us) v_val = idx"
                by blast

              have his_new: "EnqCallInHis (cs', us) v v_val sn"
                using his cs'_eq unfolding EnqCallInHis_def his_seq_def by simp

              have inq_new: "InQBack (cs', us) v_val"
              proof -
                from inq obtain k_pos where
                  k_val: "Qback_arr (cs, us) k_pos = v_val"
                  unfolding InQBack_def by blast
                have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
                  using cs'_eq unfolding Qback_arr_def by simp
                with k_val have "Qback_arr (cs', us) k_pos = v_val"
                  by simp
                thus ?thesis
                  unfolding InQBack_def by blast
              qed

              have idx_new: "Idx (cs', us) v_val = idx"
              proof -
                have "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
                  using cs'_eq unfolding AtIdx_def Qback_arr_def by simp
                thus ?thesis
                  using idx_eq unfolding Idx_def by presburger
              qed

              from his_new inq_new idx_new show ?thesis
                by blast
            qed
          qed
        qed
      qed

      (* Condition 18: core verification in the branch with a real scan step. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
        (\<forall>v \<in> t_scanned ?ts_scan q. \<forall>nid v_val ts_val. 
          (nid, v_val, ts_val) \<in> set (pools ?ts_scan v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
          nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts_scan q))"
      proof (intro allI impI ballI, elim conjE)
        fix q v nid v_val ts_val
        assume pc_q_new: "c_program_counter cs' q = ''D3''"
           and v_scan: "v \<in> t_scanned ?ts_scan q"
           and in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts_scan v)"
           and not_top: "ts_val \<noteq> TOP"
           
        have pc_q_old: "c_program_counter cs q = ''D3''"
          using pc_q_new cs'_eq pc by (cases "q = p") auto
          
        have scan_eq: "t_scanned ?ts_scan q = (if q=p then t_scanned ts p \<union> {k} else t_scanned ts q)" 
          by simp
          
        show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts_scan q)"
        proof (cases "q = p \<and> v = k")
          case True
          (* Here v is exactly the newly scanned process k. *)
          have "v = k" and "q = p" using True by auto
          
          (* Step 1: transport the pool fact from the new state back to the old state. *)
          have in_pool_k: "(nid, v_val, ts_val) \<in> set (pools ts k)"
            using in_pool `v = k` by simp

          (* Step 2: extract Condition 15. *)
          have cond15: "\<forall>nid_x. (\<exists>v_x ts_x. (nid_x, v_x, ts_x) \<in> set (pools ts k) \<and> ts_x \<noteq> TOP) \<longrightarrow> nid_x < CState.i_var cs k"
            using sim pc_k unfolding Simulation_R_def Let_def by auto
            
          (* Step 3: show that its nid is strictly smaller than its current i_var. *)
          have "nid < CState.i_var cs k"
            using cond15 in_pool_k not_top by blast
            
          (* Step 4: identify the i_var of k with the old j_var of p. *)
          also have "... = ?j" using k_idx by simp
          
          (* Step 5: in the new state, the cursor of p has been incremented by one, so strict inequality follows. *)
          also have "... < CState.j_var cs' q" using cs'_eq `q = p` by simp
          
          finally have "nid < CState.j_var cs' q" .
          thus ?thesis by simp
          
        next
          case False
          (* If v is not k, then it is an old scanned process and the old invariant applies directly. *)
          have v_scan_old: "v \<in> t_scanned ts q"
            using v_scan scan_eq False by (metis (lifting) Un_iff singletonD)
            
          (* Rewrite the new-state pool fact back to the old-state pool fact. *)
          have in_pool_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" 
            using in_pool by simp
            
          have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
            using sim pc_q_old v_scan_old in_pool_old not_top unfolding Simulation_R_def Let_def
            by (metis fst_eqD) 
            
          have j_new_ge: "CState.j_var cs q \<le> CState.j_var cs' q"
            using cs'_eq by simp
            
          have start_eq: "t_startTs ?ts_scan q = t_startTs ts q" by simp
          
          from old_cond18 show ?thesis 
            using j_new_ge start_eq by auto
        qed
      qed

      (* Condition 19: core verification in the branch that scans a fresh process. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
        (\<forall>u \<in> t_scanned ?ts_scan q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
          CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts_scan u) (t_startTs ?ts_scan q))"
      proof (intro allI impI ballI)
        fix q u
        assume pc_q: "c_program_counter cs' q = ''D3''"
        assume u_scan: "u \<in> t_scanned ?ts_scan q"
        assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
        
        have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q cs'_eq pc by (cases "q = p") auto
        have scan_eq: "t_scanned ?ts_scan q = (if q=p then t_scanned ts p \<union> {k} else t_scanned ts q)" by simp
        have startTs_eq: "t_startTs ?ts_scan q = t_startTs ts q" by simp
        have ts_u_eq: "t_ts ?ts_scan u = t_ts ts u" by simp
        
        show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts_scan u) (t_startTs ?ts_scan q)"
        proof (cases "q = p \<and> u = k")
          case True
          (* The critical subcase is when u is the newly scanned process k. *)
          have "u = k" and "q = p" using True by auto
          
          (* In this subcase, k is in E2 and its current i_var is exactly the old j_var of p. *)
          have i_var_eq: "CState.i_var cs' u = ?j" using `u = k` k_idx cs'_eq pc pc_k by auto
          
          (* Proof note. *)
          have j_var_new: "CState.j_var cs' q = ?j + 1" using `q = p` cs'_eq by simp
          
          (* Proof note. *)
          have "CState.i_var cs' u < CState.j_var cs' q" using i_var_eq j_var_new by simp
          thus ?thesis by simp
        next
          case False
          (* Proof note. *)
          have u_scan_old: "u \<in> t_scanned ts q" using u_scan scan_eq False by (metis (lifting) Un_iff singletonD)
          
          have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}"
            using pc_u_new cs'_eq by (cases "u = p") auto
            
          have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
            using sim pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def
            by (metis fst_eqD)
            
          have j_new_ge: "CState.j_var cs q \<le> CState.j_var cs' q" using cs'_eq by simp
          have i_eq: "CState.i_var cs' u = CState.i_var cs u" using cs'_eq by (cases "u = p") auto
          
          show ?thesis using old_cond19 j_new_ge i_eq startTs_eq ts_u_eq by auto
        qed
      qed

      (* Condition 20.1: synchronization of the global value allocator. *)
      show "CState.V_var cs' = t_V_var ?ts_scan" 
        using sim cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)

      (* Condition 20.2: synchronization of the local snapshots. *)
      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts_scan q" 
        using sim cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)
    qed
    
        (* Proof note. *)
        have pc_loop: "t_pc ts p = ''TD_Loop''"
          using step_scan unfolding T_D3_Scan_def Let_def by auto
        
        have "T_D3 p ts ?ts_scan" 
          unfolding T_D3_def Let_def
          using pc_loop step_scan
          by blast
      
      then show ?thesis using `Simulation_R (cs', us) ?ts_scan` by blast
    qed
  qed
qed

lemma array_value_unique:
  fixes cs :: CState and us :: UState and i :: nat and j :: nat
  assumes inv_sys: "system_invariant (cs, us)" 
      and q_i_not_bot: "CState.Q_arr cs i \<noteq> BOT" 
      and q_eq: "CState.Q_arr cs i = CState.Q_arr cs j"
  shows "i = j"
proof -
  (* Proof note. *)
  from inv_sys have sI8_Q_Qback_Sync: "\<forall>k. CState.Q_arr cs k = CState.Qback_arr cs k \<or> CState.Q_arr cs k = BOT"
    unfolding system_invariant_def sI8_Q_Qback_Sync_def
    by (simp add: Model.Q_arr_def Model.Qback_arr_def)
  from inv_sys have sI10_Qback_Unique_Vals: "\<forall>k1 k2. k1 \<noteq> k2 \<and> CState.Qback_arr cs k1 \<noteq> BOT \<and> CState.Qback_arr cs k2 \<noteq> BOT \<longrightarrow> CState.Qback_arr cs k1 \<noteq> CState.Qback_arr cs k2"
    unfolding system_invariant_def sI10_Qback_Unique_Vals_def
    by (simp add: Model.Qback_arr_def)

  (* Pool/array correspondence note. *)
  have q_i: "CState.Q_arr cs i = CState.Qback_arr cs i"
    using sI8_Q_Qback_Sync q_i_not_bot by blast
  with q_eq have q_j_not_bot: "CState.Q_arr cs j \<noteq> BOT"
    using q_i_not_bot by auto 
  have q_j: "CState.Q_arr cs j = CState.Qback_arr cs j"
    using sI8_Q_Qback_Sync q_j_not_bot by blast

  (* Pool/array correspondence note. *)
  from q_i_not_bot q_i have "CState.Qback_arr cs i \<noteq> BOT" by simp
  from q_j_not_bot q_j have "CState.Qback_arr cs j \<noteq> BOT" by simp

  (* Proof note. *)
  show "i = j"
  proof (rule ccontr)
    assume "i \<noteq> j"
    with sI10_Qback_Unique_Vals[rule_format, of i j] `CState.Qback_arr cs i \<noteq> BOT` `CState.Qback_arr cs j \<noteq> BOT`
    have "CState.Qback_arr cs i \<noteq> CState.Qback_arr cs j" by simp
    with q_i q_j q_eq show False by simp
  qed
qed


lemma nid_tar_is_j_var:
  fixes cs :: CState and us :: UState and ts :: TState and p :: nat
  assumes inv_sys: "system_invariant (cs, us)"
      and sim: "Simulation_R (cs, us) ts"
      and tar_in: "(nid_tar, v_tar, ts_tar) \<in> set (pools ts u_tar)"
      and tar_not_top: "ts_tar \<noteq> TOP"
      and q_val_match: "v_tar = CState.Q_arr cs (CState.j_var cs p)"
      and q_not_bot: "v_tar \<noteq> BOT"
  shows "nid_tar = CState.j_var cs p"
proof -
  obtain n where "ts_tar = TS n" using tar_not_top by (cases ts_tar) auto
  with tar_in sim have "CState.Q_arr cs nid_tar = v_tar" unfolding Simulation_R_def Let_def
    by (metis fst_conv)
  with q_val_match have "CState.Q_arr cs nid_tar = CState.Q_arr cs (CState.j_var cs p)" by simp
  thus ?thesis using array_value_unique[OF inv_sys] q_val_match q_not_bot
    by metis 
qed



lemma D3_others_no_update_Helper:
  fixes cs :: CState and us :: UState and ts :: TState and p :: nat
  assumes inv_sys: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and pc: "c_program_counter cs p = ''D3''"
      (* Key proof idea. *)
      and first_non_bot: "\<forall>idx < CState.j_var cs p. CState.Q_arr cs idx = BOT"
      and q_not_bot: "CState.Q_arr cs (CState.j_var cs p) \<noteq> BOT"
      (* Proof note. *)
      and tar_in: "(nid_tar, CState.Q_arr cs (CState.j_var cs p), ts_tar) \<in> set (pools ts u_tar)"
      and tar_not_top: "ts_tar \<noteq> TOP"
  shows "\<forall>k \<in> ProcSet - (t_scanned ts p \<union> {u_tar}). 
           fst (pool_getOldest (pools ts k)) = BOT \<or> 
           \<not> ts_less (snd (pool_getOldest (pools ts k))) ts_tar"
proof (intro ballI)
  fix k assume k_in: "k \<in> ProcSet - (t_scanned ts p \<union> {u_tar})"
  let ?jp = "CState.j_var cs p"
  let ?oldest = "pool_getOldest (pools ts k)"
  
(* Nid-related proof note. *)
  have nid_eq: "nid_tar = ?jp" 
    using nid_tar_is_j_var[OF inv_sys sim tar_in tar_not_top _ q_not_bot] by simp

  show "fst ?oldest = BOT \<or> \<not> ts_less (snd ?oldest) ts_tar"
  proof (cases "fst ?oldest = BOT")
    case True then show ?thesis
      by (meson inv_sys nid_tar_is_j_var q_not_bot sim tar_in
          tar_not_top) 
  next
    case False
    obtain nid_k ts_k where oldest_k: "?oldest = (nid_k, ts_k)" by (cases ?oldest)
    from False oldest_k have "nid_k \<noteq> BOT" by auto
    
    obtain v_k where node_k: "(nid_k, v_k, ts_k) \<in> set (pools ts k)"
      using pool_getOldest_SomeE[OF oldest_k] `nid_k \<noteq> BOT`
      by blast
    
    have ts_k_not_top: "ts_k \<noteq> TOP"
      using oldest_k `nid_k \<noteq> BOT`
      unfolding pool_getOldest_def
      by (cases "pools ts k") (auto split: if_splits)

  (* Key proof idea. *)
    have ts_nid_order: "(ts_k <\<^sub>t\<^sub>s ts_tar) = (nid_k < nid_tar)"
      using TSQ_State_InvD_pool_ts_order[OF inv_tsq node_k tar_in ts_k_not_top tar_not_top] .
        
    show ?thesis
    proof (rule ccontr)
      assume "\<not> (fst ?oldest = BOT \<or> \<not> ts_less (snd ?oldest) ts_tar)"
      then have "ts_less ts_k ts_tar" using oldest_k by simp
      
      (* Proof note. *)
      then have "nid_k < nid_tar" using ts_nid_order by simp
      with nid_eq have "nid_k < ?jp"
        using \<open>nid_k < nid_tar\<close> inv_sys nid_tar_is_j_var q_not_bot sim tar_in
          tar_not_top by blast 
      
      (* Condition 10. *)
      obtain n where ts_k_shape: "ts_k = TS n"
        using ts_k_not_top by (cases ts_k) auto

      have "CState.Q_arr cs nid_k = v_k \<and> v_k \<in> Val" 
        using sim node_k ts_k_shape unfolding Simulation_R_def Let_def
        by (metis split_pairs2)
      then have "CState.Q_arr cs nid_k \<noteq> BOT" unfolding Val_def BOT_def by auto
      
      (* Proof note. *)
      with first_non_bot `nid_k < ?jp` show False by blast
    qed
  qed
qed


(* Nid-related proof note. *)
lemma sorted_nid [simp]:
  assumes "TSQ_State_Inv ts"
  shows "\<forall>p. sorted (map fst (pools ts p))"
proof -
  (* Proof note. *)
  show ?thesis
    using assms unfolding TSQ_State_Inv_def by simp
qed


lemma distinct_pools [simp]:
  assumes "TSQ_State_Inv ts"
  shows "distinct (map fst (pools ts p))"
  using assms unfolding TSQ_State_Inv_def by simp



(* Proof note. *)
lemma node_in_pool_implies_Q_nonempty:
  assumes "system_invariant (cs, us)" 
      and "Simulation_R (cs, us) ts"
      and "(n, v, ts_val) \<in> set (pools ts u)" 
      and "ts_val \<noteq> TOP"
  shows "CState.Q_arr cs n = v \<and> v \<noteq> BOT"
proof -
  (* Proof step. *)
  obtain m where ts_eq: "ts_val = TS m"
    using assms(4) by (cases ts_val) auto
    
  (* Proof step. *)
  have "CState.Q_arr cs n = v"
    using assms(2) assms(3) ts_eq unfolding Simulation_R_def Let_def
    by (metis fst_conv)
    
  (* v \<in> Val *)
  moreover have "v \<in> Val"
    using assms(2) assms(3) unfolding Simulation_R_def Let_def by meson
    
  (* Proof step. *)
  ultimately show ?thesis 
    unfolding Val_def BOT_def by auto
qed


lemma no_smaller_top:
  assumes inv_sys: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and idx_lt_jp: "idx < CState.j_var cs p"
      and node: "(idx, v, ts_x) \<in> set (pools ts u_tar)" 
      and ts_x_not_top: "ts_x \<noteq> TOP"
  shows "\<forall>m < idx. \<not>(\<exists>val. (m, val, TOP) \<in> set (pools ts u_tar))"
proof (intro allI impI notI)
  (* Proof step. *)
  fix m
  assume m_lt: "m < idx"
  
  (* Key proof idea. *)
  assume "\<exists>val. (m, val, TOP) \<in> set (pools ts u_tar)"
  then obtain val where top_node: "(m, val, TOP) \<in> set (pools ts u_tar)" by blast
  
  (* Proof note. *)
  have "t_pc ts u_tar = ''TE2'' \<and> t_nid ts u_tar = m"
  proof -
    have "\<forall>node\<in>set (pools ts u_tar). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts u_tar = ''TE2'' \<and> t_nid ts u_tar = fst node"
      using sim unfolding Simulation_R_def Let_def
      by meson 
    thus ?thesis using top_node by auto
  qed
  hence "t_pc ts u_tar = ''TE2''" and "t_nid ts u_tar = m" by auto
    
  (* Proof step. *)
  have pc_u: "c_program_counter cs u_tar = ''E2''"
  proof (rule ccontr)
    assume not_E2: "c_program_counter cs u_tar \<noteq> ''E2''"
    have valid_pc: "c_program_counter cs u_tar \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
      using inv_sys unfolding system_invariant_def TypeOK_def by (simp add: program_counter_def)
      
    have m1: "c_program_counter cs u_tar = ''L0'' \<Longrightarrow> t_pc ts u_tar = ''TL0''" using sim unfolding Simulation_R_def Let_def by simp
    have m2: "c_program_counter cs u_tar = ''E1'' \<Longrightarrow> t_pc ts u_tar = ''TE1''" using sim unfolding Simulation_R_def Let_def by simp
    have m3: "c_program_counter cs u_tar = ''E3'' \<Longrightarrow> t_pc ts u_tar = ''TE3''" using sim unfolding Simulation_R_def Let_def by simp
    have m4: "c_program_counter cs u_tar = ''D1'' \<Longrightarrow> t_pc ts u_tar = ''TD1''" using sim unfolding Simulation_R_def Let_def by simp
    have m5: "c_program_counter cs u_tar = ''D2'' \<Longrightarrow> t_pc ts u_tar = ''TD_Line4_Done''" using sim unfolding Simulation_R_def Let_def by simp
    have m6: "c_program_counter cs u_tar = ''D3'' \<Longrightarrow> t_pc ts u_tar = ''TD_Loop''" using sim unfolding Simulation_R_def Let_def by simp
    have m7: "c_program_counter cs u_tar = ''D4'' \<Longrightarrow> t_pc ts u_tar = ''TD_Remove_Done''" using sim unfolding Simulation_R_def Let_def by simp
    
    show False using valid_pc not_E2 `t_pc ts u_tar = ''TE2''` m1 m2 m3 m4 m5 m6 m7 by auto
  qed
  
  (* Proof step. *)
  have i_u: "CState.i_var cs u_tar = m"
    using sim pc_u `t_nid ts u_tar = m` unfolding Simulation_R_def Let_def
    by simp 
    
  (* Condition 15. *)
  have "idx < CState.i_var cs u_tar"
    using sim pc_u node ts_x_not_top unfolding Simulation_R_def Let_def
    by (metis split_pairs2) 
    
  (* Proof step. *)
  with i_u have "idx < m" by simp
  with m_lt show False by simp
qed

lemma no_smaller_non_top:
  assumes inv_sys: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and pc: "c_program_counter cs p = ''D3''"
      and jp_def: "jp = CState.j_var cs p"
      and q_not_bot: "CState.Q_arr cs jp \<noteq> BOT"
      and u_tar_unscanned: "u_tar \<notin> t_scanned ts p"
      (* Key proof idea. *)
      and tar_in: "(nid_tar, q_val, ts_tar) \<in> set (pools ts u_tar)" 
      and tar_not_top: "ts_tar \<noteq> TOP"
      and nid_eq: "nid_tar = jp"
  (* Key proof idea. *)
  shows "\<forall>n < nid_tar. \<not>(\<exists>v ts_val. (n, v, ts_val) \<in> set (pools ts u_tar) \<and> ts_val \<noteq> TOP)"
proof (intro allI impI notI)
  (* Proof step. *)
  fix n
  assume n_lt: "n < nid_tar"
  assume "\<exists>v ts_val. (n, v, ts_val) \<in> set (pools ts u_tar) \<and> ts_val \<noteq> TOP"
  then obtain v ts_val where node: "(n, v, ts_val) \<in> set (pools ts u_tar)" and ts_ne_top: "ts_val \<noteq> TOP" by blast

  (* Proof note. *)
  have q_n_props: "CState.Q_arr cs n = v \<and> v \<noteq> BOT"
    using node_in_pool_implies_Q_nonempty[OF inv_sys sim node ts_ne_top] .
  hence q_n_not_bot: "CState.Q_arr cs n \<noteq> BOT" by simp

  (* Proof note. *)
  have n_lt_jp: "n < CState.j_var cs p" using n_lt nid_eq jp_def by simp

  (* RHS \<longrightarrow> LHS *)
  from sim pc have cond6_imp: "
        (\<exists>idx < CState.j_var cs p. 
            (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_x. (nid, CState.Q_arr cs idx, ts_x) \<in> set (pools ts u_tar) \<and> ts_x \<noteq> TOP)) \<or> 
            (CState.Q_arr cs idx = BOT \<and> c_program_counter cs u_tar = ''E2'' \<and> CState.i_var cs u_tar = idx \<and> idx \<noteq> BOT))
        \<longrightarrow> (u_tar \<in> t_scanned ts p)"
    unfolding Simulation_R_def Let_def
    by simp

  (* Proof note. *)
  have rhs_true: "\<exists>idx < CState.j_var cs p. 
            (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_x. (nid, CState.Q_arr cs idx, ts_x) \<in> set (pools ts u_tar) \<and> ts_x \<noteq> TOP)) \<or> 
            (CState.Q_arr cs idx = BOT \<and> c_program_counter cs u_tar = ''E2'' \<and> CState.i_var cs u_tar = idx \<and> idx \<noteq> BOT)"
  proof -
    have "\<exists>nid ts_x. (nid, CState.Q_arr cs n, ts_x) \<in> set (pools ts u_tar) \<and> ts_x \<noteq> TOP"
    proof -
      have "CState.Q_arr cs n = v" using q_n_props by simp
      with node have "(n, CState.Q_arr cs n, ts_val) \<in> set (pools ts u_tar)" by simp
      thus ?thesis using ts_ne_top by blast
    qed
    with q_n_not_bot have "(CState.Q_arr cs n \<noteq> BOT \<and> (\<exists>nid ts_x. (nid, CState.Q_arr cs n, ts_x) \<in> set (pools ts u_tar) \<and> ts_x \<noteq> TOP))"
      by simp
    thus ?thesis using n_lt_jp by blast
  qed

  (* Proof step. *)
  have "u_tar \<in> t_scanned ts p" using cond6_imp rhs_true by blast
  with u_tar_unscanned show False by simp
qed


lemma scanned_non_top_updates_candidate:
  assumes step: "T_D3_Scan p k ts ts'"
      and oldest: "pool_getOldest (pools ts k) = (nid, tstamp)"
      and nid_not_bot: "nid \<noteq> BOT"
      and tstamp_not_top: "tstamp \<noteq> TOP"
      and cand_top: "t_candTs ts p = TOP"
      and start_not_less: "\<not> ts_less (t_startTs ts p) tstamp" 
  shows "t_candTs ts' p = tstamp"
proof -
  (* Key proof idea. *)
  have tstamp_less_cand: "tstamp <\<^sub>t\<^sub>s t_candTs ts p"
  proof -
    (* Proof note. *)
    from tstamp_not_top obtain m where "tstamp = TS m" 
      by (cases tstamp) auto
    (* Proof note. *)
    thus ?thesis using cand_top by simp
  qed

  (* nid\<noteq>BOT, tstamp < cand, \<not> start < tstamp *)
  show ?thesis
    using step oldest nid_not_bot tstamp_less_cand start_not_less
    unfolding T_D3_Scan_def Let_def
    by (auto split: if_splits)
qed


lemma Idx_of_Q_arr:
  assumes "system_invariant (cs, us)"
      and "CState.Q_arr cs k = v" 
      and "v \<noteq> BOT"
  shows "Idx (cs, us) v = k"
proof -
  let ?s = "(cs, us)"
  (* Proof step. *)
  have "Qback_arr ?s k = v"
    using assms(1) assms(2) assms(3) unfolding system_invariant_def sI8_Q_Qback_Sync_def Qback_arr_def Q_arr_def
    by (metis fst_eqD) 
  
  (* Proof step. *)
  have "\<forall>k'. Qback_arr ?s k' = v \<longrightarrow> k' = k"
  proof (intro allI impI)
    fix k' assume "Qback_arr ?s k' = v"
    show "k' = k"
    proof (rule ccontr)
      assume "k' \<noteq> k"
      have "v \<noteq> BOT" using assms(3) by simp
      with `Qback_arr ?s k = v` `Qback_arr ?s k' = v` `k' \<noteq> k` 
      have "Qback_arr ?s k' \<noteq> Qback_arr ?s k"
        using assms(1) unfolding system_invariant_def sI10_Qback_Unique_Vals_def
        by metis 
      thus False using `Qback_arr ?s k = v` `Qback_arr ?s k' = v` by simp
    qed
  qed
  
  (* Proof step. *)
  thus ?thesis
    unfolding Idx_def AtIdx_def using `Qback_arr ?s k = v`
    by blast 
qed


lemma D3_has_pending_deq:
  assumes inv_sys: "system_invariant (cs, us)" 
      and pc: "program_counter (cs, us) p = ''D3''"
  shows "HasPendingDeq (cs, us) p"
proof -
  have hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq (cs, us)"
    using inv_sys unfolding system_invariant_def by auto
  show ?thesis
    using hI12_D_Phase_Pending_Deq_s pc unfolding hI12_D_Phase_Pending_Deq_def by auto
qed

lemma same_thread_HB:
  assumes inv_sys: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and idx_lt: "idx < j"
      and node_x: "(idx, v_x, ts_x) \<in> set (pools ts u)" and not_top_x: "ts_x \<noteq> TOP"
      and node_y: "(j, v_y, ts_y) \<in> set (pools ts u)" and not_top_y: "ts_y \<noteq> TOP"
  shows "HB_EnqRetCall (cs, us) v_x v_y"
proof -
  define s where "s = (cs, us)"
  define H where "H = his_seq s"
  have inv: "system_invariant s" using inv_sys by (simp add: s_def)

(* Proof note. *)
  have arr_x: "CState.Q_arr cs idx = v_x"
  proof -
    (* Proof note. *)
    obtain n_x where "ts_x = TS n_x" 
      using not_top_x by (cases ts_x) auto
    with sim node_x show ?thesis 
      unfolding Simulation_R_def Let_def
      by (metis fst_conv) 
  qed

  have arr_y: "CState.Q_arr cs j = v_y"
  proof -
    (* Proof note. *)
    obtain n_y where "ts_y = TS n_y" 
      using not_top_y by (cases ts_y) auto
    with sim node_y show ?thesis 
      unfolding Simulation_R_def Let_def by (metis fst_conv) 
  qed

  (* Proof note. *)
  have "v_x \<noteq> v_y"
  proof -
    have "v_x \<noteq> BOT" using arr_x not_top_x inv unfolding system_invariant_def TypeOK_def Val_def
      by (metis inv node_in_pool_implies_Q_nonempty node_x s_def
          sim) 
    have "v_y \<noteq> BOT" using arr_y not_top_y inv unfolding system_invariant_def TypeOK_def Val_def
      by (metis inv node_in_pool_implies_Q_nonempty node_y s_def
          sim) 

    have "CState.Qback_arr cs idx = v_x" using inv arr_x `v_x \<noteq> BOT` unfolding system_invariant_def sI8_Q_Qback_Sync_def
      by (metis Model.Q_arr_def Model.Qback_arr_def fst_conv s_def) 
    have "CState.Qback_arr cs j = v_y" using inv arr_y `v_y \<noteq> BOT` unfolding system_invariant_def sI8_Q_Qback_Sync_def
      by (metis Model.Q_arr_def Model.Qback_arr_def fst_conv s_def) 
    with inv `CState.Qback_arr cs idx = v_x` `CState.Qback_arr cs j = v_y` idx_lt
    show ?thesis unfolding system_invariant_def sI10_Qback_Unique_Vals_def
      by (metis \<open>v_x \<noteq> BOT\<close> arr_x arr_y array_value_unique inv_sys
          order_less_imp_not_eq)
  qed

  (* Proof step. *)
  from sim node_x not_top_x have call_x: "\<exists>sn_x. EnqCallInHis s u v_x sn_x"
    unfolding Simulation_R_def Let_def s_def by blast
  from sim node_y not_top_y have call_y: "\<exists>sn_y. EnqCallInHis s u v_y sn_y"
    unfolding Simulation_R_def Let_def s_def by blast

  obtain sn_x where call_x_sn: "EnqCallInHis s u v_x sn_x"
    using call_x by blast
  obtain sn_y where call_y_sn: "EnqCallInHis s u v_y sn_y"
    using call_y by blast

  obtain e_x where
      e_x_in: "e_x \<in> set H"
    and e_x_pid: "act_pid e_x = u"
    and e_x_ssn: "act_ssn e_x = sn_x"
    and e_x_oper: "act_name e_x = enq"
    and e_x_cr: "act_cr e_x = call"
    and e_x_val: "act_val e_x = v_x"
    using call_x_sn unfolding EnqCallInHis_def H_def Let_def by blast

  obtain k_cx where
      k_cx: "k_cx < length H"
    and H_cx: "H ! k_cx = e_x"
    using e_x_in by (meson in_set_conv_nth)

  have H_cx_mk: "H ! k_cx = mk_act enq v_x u sn_x call"
    using H_cx e_x_pid e_x_ssn e_x_oper e_x_cr e_x_val
    unfolding mk_act_def act_name_def act_val_def act_pid_def act_ssn_def act_cr_def
    by (cases e_x) auto

  obtain e_y where
      e_y_in: "e_y \<in> set H"
    and e_y_pid: "act_pid e_y = u"
    and e_y_ssn: "act_ssn e_y = sn_y"
    and e_y_oper: "act_name e_y = enq"
    and e_y_cr: "act_cr e_y = call"
    and e_y_val: "act_val e_y = v_y"
    using call_y_sn unfolding EnqCallInHis_def H_def Let_def by blast

  obtain k_cy where
      k_cy: "k_cy < length H"
    and H_cy: "H ! k_cy = e_y"
    using e_y_in by (meson in_set_conv_nth)

  have H_cy_mk: "H ! k_cy = mk_act enq v_y u sn_y call"
    using H_cy e_y_pid e_y_ssn e_y_oper e_y_cr e_y_val
    unfolding mk_act_def act_name_def act_val_def act_pid_def act_ssn_def act_cr_def
    by (cases e_y) auto

  have "k_cx \<noteq> k_cy"
    using H_cx_mk H_cy_mk `v_x \<noteq> v_y` by (auto simp: mk_act_def)

  (* Proof step. *)
  have hI25_Enq_Call_Ret_Balanced: "hI25_Enq_Call_Ret_Balanced s"
    using inv unfolding system_invariant_def by blast
  have hI7_His_WF: "hI7_His_WF s"
    using inv unfolding system_invariant_def by blast

  have hb_candidate: "HB_EnqRetCall s v_x v_y \<or> HB_EnqRetCall s v_y v_x"
  proof (cases "k_cx < k_cy")
    case True
    (* Key proof idea. *)
    define u_enq where "u_enq = (\<lambda>e. act_pid e = u \<and> act_name e = enq)"
    have pred_cy: "k_cx < k_cy \<and> k_cy \<le> k_cy \<and> u_enq (H ! k_cy)"
      unfolding u_enq_def
      using True H_cy_mk
      by (auto simp: mk_act_def act_pid_def act_name_def)
      
    (* Proof note. *)
    define k_n where "k_n = (LEAST k. k_cx < k \<and> k \<le> k_cy \<and> u_enq (H ! k))"
    have kn_prop: "k_cx < k_n \<and> k_n \<le> k_cy \<and> u_enq (H ! k_n)"
      using LeastI[of "\<lambda>k. k_cx < k \<and> k \<le> k_cy \<and> u_enq (H ! k)" k_cy, OF pred_cy] unfolding k_n_def .
    have kn_least: "\<And>m. k_cx < m \<Longrightarrow> m < k_n \<Longrightarrow> \<not>(u_enq (H ! m))"
      using kn_prop not_less_Least[of _ "\<lambda>k. k_cx < k \<and> k \<le> k_cy \<and> u_enq (H ! k)"] 
      unfolding k_n_def
      by (meson dual_order.strict_trans linorder_not_less)

    (* Proof note. *)
    let ?mid = "drop (k_cx + 1) (take k_n H)"
    have empty_mid: "filter u_enq ?mid = []"
    proof -
      have "\<forall>x \<in> set ?mid. \<not> u_enq x"
      proof
        fix x assume "x \<in> set ?mid"
        (* Proof note. *)
        then obtain i where i_prop: "i < length ?mid" "x = ?mid ! i" 
          unfolding in_set_conv_nth by blast
        
        (* Proof note. *)
        have len_take: "length (take k_n H) = k_n" 
          using kn_prop k_cy by simp
          
        (* Proof note. *)
        have "x = take k_n H ! (k_cx + 1 + i)" 
          using i_prop
          by (metis kn_prop len_take less_iff_succ_less_eq nth_drop) 
        also have "... = H ! (k_cx + 1 + i)" 
          using i_prop(1) len_take by simp
        finally have x_val: "x = H ! (k_cx + 1 + i)" .
        
        have "k_cx < k_cx + 1 + i" by simp
        moreover have "k_cx + 1 + i < k_n" 
          using i_prop(1) len_take by auto
        ultimately show "\<not> u_enq x" 
          using kn_least x_val by auto
      qed
      thus ?thesis by (auto simp: filter_empty_conv)
    qed

    have eq_take: "take (k_n + 1) H = take (k_cx + 1) H @ ?mid @ [H ! k_n]"
    proof -
      (* Key proof idea. *)
      have "take (k_n + 1) H = take k_n H @ [H ! k_n]" 
        using take_Suc_conv_app_nth kn_prop k_cy
        by (metis Suc_eq_plus1 dual_order.strict_trans2) 
      moreover have "take k_n H = take (k_cx + 1) (take k_n H) @ drop (k_cx + 1) (take k_n H)"
        by (metis append_take_drop_id) 
      (* Key proof idea. *)
      moreover have "take (k_cx + 1) (take k_n H) = take (k_cx + 1) H" 
        using kn_prop by simp
      ultimately show ?thesis by simp
    qed

    have P_n_eq: "filter u_enq (take (k_n + 1) H) = filter u_enq (take (k_cx + 1) H) @ [H ! k_n]"
      unfolding eq_take using empty_mid kn_prop by simp

    (* Proof note. *)
    (* Proof note. *)
    have cr_kn: "act_cr (H ! k_n) = ret"
    proof (cases "act_cr (H ! k_n) = call")
      case True
      let ?count_C = "\<lambda>xs. length (filter (\<lambda>e. act_cr e = call) xs)"
      let ?count_R = "\<lambda>xs. length (filter (\<lambda>e. act_cr e = ret) xs)"
      
      have call_part:
        "filter (\<lambda>e. act_cr e = call) (filter u_enq (take (k_n + 1) H)) =
         filter (\<lambda>e. act_cr e = call) (filter u_enq (take (k_cx + 1) H)) @ [H ! k_n]"
        unfolding P_n_eq using True by simp
      hence C_n_eq:
        "?count_C (filter u_enq (take (k_n + 1) H)) =
         ?count_C (filter u_enq (take (k_cx + 1) H)) + 1"
        by simp
      
      have ret_part:
        "filter (\<lambda>e. act_cr e = ret) (filter u_enq (take (k_n + 1) H)) =
         filter (\<lambda>e. act_cr e = ret) (filter u_enq (take (k_cx + 1) H))"
        unfolding P_n_eq using True by simp
      hence R_n_eq:
        "?count_R (filter u_enq (take (k_n + 1) H)) =
         ?count_R (filter u_enq (take (k_cx + 1) H))"
        by simp

      have base_bound:
        "?count_C (filter u_enq (take k_cx H)) \<ge> ?count_R (filter u_enq (take k_cx H))"
        using hI25_Enq_Call_Ret_Balanced k_cx
        unfolding hI25_Enq_Call_Ret_Balanced_def Let_def H_def[symmetric] s_def[symmetric] u_enq_def
        by (meson linorder_le_less_linear order.asym)

      have cx_step:
        "filter u_enq (take (k_cx + 1) H) = filter u_enq (take k_cx H) @ [H ! k_cx]"
        using take_Suc_conv_app_nth[of k_cx H] k_cx H_cx_mk
        unfolding u_enq_def
        by (auto simp: mk_act_def act_pid_def act_name_def)
      
      have cx_C:
        "?count_C (filter u_enq (take (k_cx + 1) H)) =
         ?count_C (filter u_enq (take k_cx H)) + 1"
        unfolding cx_step using H_cx_mk by (simp add: mk_act_def act_cr_def)

      have cx_R:
        "?count_R (filter u_enq (take (k_cx + 1) H)) =
         ?count_R (filter u_enq (take k_cx H))"
        unfolding cx_step using H_cx_mk by (simp add: mk_act_def act_cr_def)
        
      have "?count_C (filter u_enq (take (k_n + 1) H)) -
            ?count_R (filter u_enq (take (k_n + 1) H)) \<ge> 2"
        using C_n_eq R_n_eq cx_C cx_R base_bound by simp
        
      moreover have "?count_C (filter u_enq (take (k_n + 1) H)) -
                     ?count_R (filter u_enq (take (k_n + 1) H)) \<le> 1"
        using hI25_Enq_Call_Ret_Balanced kn_prop k_cy
        unfolding hI25_Enq_Call_Ret_Balanced_def Let_def H_def[symmetric] s_def[symmetric] u_enq_def
        by simp
        
      ultimately show ?thesis by simp
    next
      case False
      thus ?thesis by (cases "act_cr (H ! k_n)") auto
    qed

    have wf: "hI7_His_WF s"
      using inv unfolding system_invariant_def by blast

    have bound_kn: "k_n < length H"
      using kn_prop k_cy by simp

    have pid_kn: "act_pid (H ! k_n) = u"                                             
      using kn_prop unfolding u_enq_def by simp

    have oper_kn: "act_name (H ! k_n) = enq"
      using kn_prop unfolding u_enq_def by simp

       have order_s: "hI6_SSN_Order s"
      using inv unfolding system_invariant_def by blast

    obtain j where
        j_lt: "j < k_n"
      and j_pid: "act_pid (H ! j) = u"
      and j_ssn: "act_ssn (H ! j) = act_ssn (H ! k_n)"
      and j_oper: "act_name (H ! j) = enq"
      and j_cr: "act_cr (H ! j) = call"
      and j_val: "act_val (H ! j) = act_val (H ! k_n)"
   proof -
  have wf_inst:
    "\<forall>k<length H.
      act_cr (H ! k) = ret \<longrightarrow>
      (\<exists>j<k.
         act_pid (H ! j) = act_pid (H ! k) \<and>
         act_ssn (H ! j) = act_ssn (H ! k) \<and>
         act_name (H ! j) = act_name (H ! k) \<and>
         act_cr (H ! j) = call \<and>
         (if act_name (H ! k) = enq
          then act_val (H ! j) = act_val (H ! k)
          else act_val (H ! j) = BOT))"
    using wf
    unfolding hI7_His_WF_def Let_def H_def[symmetric] s_def[symmetric]
    by auto

  have ex_j:
    "\<exists>j<k_n.
       act_pid (H ! j) = act_pid (H ! k_n) \<and>
       act_ssn (H ! j) = act_ssn (H ! k_n) \<and>
       act_name (H ! j) = act_name (H ! k_n) \<and>
       act_cr (H ! j) = call \<and>
       (if act_name (H ! k_n) = enq
        then act_val (H ! j) = act_val (H ! k_n)
        else act_val (H ! j) = BOT)"
    using wf_inst[rule_format, OF bound_kn cr_kn] .

  from ex_j obtain j where
      j0: "j < k_n"
    and j1: "act_pid (H ! j) = act_pid (H ! k_n)"
    and j2: "act_ssn (H ! j) = act_ssn (H ! k_n)"
    and j3: "act_name (H ! j) = act_name (H ! k_n)"
    and j4: "act_cr (H ! j) = call"
    and j5: "(if act_name (H ! k_n) = enq
             then act_val (H ! j) = act_val (H ! k_n)
             else act_val (H ! j) = BOT)"
    by auto

  have "act_pid (H ! j) = u"
    using j1 pid_kn by simp
  moreover have "act_ssn (H ! j) = act_ssn (H ! k_n)"
    using j2 by simp
  moreover have "act_name (H ! j) = enq"
    using j3 oper_kn by simp
  moreover have "act_cr (H ! j) = call"
    using j4 by simp
  moreover have "act_val (H ! j) = act_val (H ! k_n)"
    using j5 oper_kn by simp
  ultimately show ?thesis
    using j0 that by blast
qed

    have j_le_kcx: "j \<le> k_cx"
    proof (rule ccontr)
      assume "\<not> j \<le> k_cx"
      hence "k_cx < j" by simp
      moreover have "j < k_n"
        by (rule j_lt)
      moreover have "u_enq (H ! j)"
        unfolding u_enq_def using j_pid j_oper by simp
      ultimately show False
        using kn_least[of j] by simp
    qed

    have j_eq_kcx: "j = k_cx"
    proof (rule antisym)
      show "j \<le> k_cx" by (rule j_le_kcx)
    next
      show "k_cx \<le> j"
      proof (rule ccontr)
        assume "\<not> k_cx \<le> j"
        hence j_lt_kcx: "j < k_cx" by simp

        have ssn_order_inst:
          "\<And>i j. i < length H \<Longrightarrow> j < length H \<Longrightarrow> i < j \<Longrightarrow> act_pid (H ! i) = act_pid (H ! j) \<Longrightarrow>
             act_ssn (H ! i) < act_ssn (H ! j) \<or>
             (act_ssn (H ! i) = act_ssn (H ! j) \<and> act_cr (H ! i) = call \<and> act_cr (H ! j) = ret)"
          using order_s
          unfolding hI6_SSN_Order_def H_def[symmetric] s_def[symmetric]
          by simp

        have ssn_j_lt_cx: "act_ssn (H ! j) < act_ssn (H ! k_cx)"
        proof -
          have j_len: "j < length H"
            using j_lt kn_prop k_cy by simp
          have pid_eq: "act_pid (H ! j) = act_pid (H ! k_cx)"
            using j_pid H_cx_mk by (auto simp: mk_act_def act_pid_def)
          have order_case:
            "act_ssn (H ! j) < act_ssn (H ! k_cx) \<or>
             (act_ssn (H ! j) = act_ssn (H ! k_cx) \<and> act_cr (H ! j) = call \<and> act_cr (H ! k_cx) = ret)"
            using ssn_order_inst[OF j_len k_cx j_lt_kcx pid_eq] .
          then show ?thesis
          proof
            assume "act_ssn (H ! j) < act_ssn (H ! k_cx)"
            then show ?thesis .
          next
            assume eq_case: "act_ssn (H ! j) = act_ssn (H ! k_cx) \<and> act_cr (H ! j) = call \<and> act_cr (H ! k_cx) = ret"
            hence "act_cr (H ! k_cx) = ret"
              by simp
            thus ?thesis
              using H_cx_mk by (auto simp: mk_act_def act_cr_def)
          qed
        qed

        have ssn_cx_le_kn: "act_ssn (H ! k_cx) \<le> act_ssn (H ! k_n)"
        proof -
          have pid_eq: "act_pid (H ! k_cx) = act_pid (H ! k_n)"
            using kn_prop H_cx_mk unfolding u_enq_def
            by (auto simp: mk_act_def act_pid_def act_name_def)
          have "act_ssn (H ! k_cx) < act_ssn (H ! k_n) \<or>
                (act_ssn (H ! k_cx) = act_ssn (H ! k_n) \<and> act_cr (H ! k_cx) = call \<and> act_cr (H ! k_n) = ret)"
            using ssn_order_inst[OF _ _ _ pid_eq]
            using k_cx kn_prop k_cy
            by auto
          thus ?thesis
            using H_cx_mk cr_kn by (auto simp: mk_act_def act_cr_def)
        qed

        hence "act_ssn (H ! k_cx) \<le> act_ssn (H ! j)"
          using j_ssn by simp

        with ssn_j_lt_cx show False
          by linarith
      qed
    qed

    have ssn_rx: "act_ssn (H ! k_n) = sn_x"
      using j_eq_kcx j_ssn H_cx_mk
      by (auto simp: mk_act_def act_ssn_def)

    have val_rx: "act_val (H ! k_n) = v_x"
      using j_eq_kcx j_val H_cx_mk
      by (auto simp: mk_act_def act_val_def)

    have pid_rx: "act_pid (H ! k_n) = u"
      using kn_prop unfolding u_enq_def by simp
    have oper_rx: "act_name (H ! k_n) = enq"
      using kn_prop unfolding u_enq_def by simp

    have H_rx: "H ! k_n = mk_act enq v_x u sn_x ret"
      using pid_rx oper_rx val_rx ssn_rx cr_kn
      unfolding mk_act_def act_name_def act_val_def act_pid_def act_ssn_def act_cr_def
      by (cases "H ! k_n") auto
    
    have "k_n \<noteq> k_cy" using H_cy_mk H_rx by (auto simp: mk_act_def)
    hence "k_n < k_cy" using kn_prop by simp

    have kn_len: "k_n < length H" using `k_n < k_cy` k_cy by simp
    
    have hb_act: "HB_Act s (mk_op enq v_x u sn_x) (mk_op enq v_y u sn_y)"
    proof -
      have ret_match: "match_ret (his_seq s) k_n (mk_op enq v_x u sn_x)"
        unfolding match_ret_def Let_def H_def[symmetric] s_def[symmetric]
        using kn_len H_rx
        by (auto simp: mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
                       mk_act_def act_name_def act_pid_def act_val_def act_ssn_def act_cr_def)

      have call_match: "match_call (his_seq s) k_cy (mk_op enq v_y u sn_y)"
        unfolding match_call_def Let_def H_def[symmetric] s_def[symmetric]
        using k_cy H_cy_mk
        by (auto simp: mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
                       mk_act_def act_name_def act_pid_def act_val_def act_ssn_def act_cr_def)

      have "HB (his_seq s) (mk_op enq v_x u sn_x) (mk_op enq v_y u sn_y)"
        unfolding HB_def
        using `k_n < k_cy` ret_match call_match
        by blast
      thus ?thesis
        unfolding HB_Act_def by simp
    qed

    have "HB_EnqRetCall s v_x v_y"
      unfolding HB_EnqRetCall_def
      using hb_act by blast
      
    thus ?thesis by blast

  next
    case False
    with `k_cx \<noteq> k_cy` have "k_cy < k_cx" by simp
    define u_enq where "u_enq = (\<lambda>e. act_pid e = u \<and> act_name e = enq)"
    have pred_cx: "k_cy < k_cx \<and> k_cx \<le> k_cx \<and> u_enq (H ! k_cx)"
      unfolding u_enq_def using False `k_cx \<noteq> k_cy` H_cx_mk by (auto simp: mk_act_def act_pid_def act_name_def)

    define k_n where "k_n = (LEAST k. k_cy < k \<and> k \<le> k_cx \<and> u_enq (H ! k))"
    have kn_prop: "k_cy < k_n \<and> k_n \<le> k_cx \<and> u_enq (H ! k_n)"
      using LeastI[of "\<lambda>k. k_cy < k \<and> k \<le> k_cx \<and> u_enq (H ! k)" k_cx, OF pred_cx] unfolding k_n_def .
    have kn_least: "\<And>m. k_cy < m \<Longrightarrow> m < k_n \<Longrightarrow> \<not>(u_enq (H ! m))"
      using kn_prop not_less_Least[of _ "\<lambda>k. k_cy < k \<and> k \<le> k_cx \<and> u_enq (H ! k)"] 
      unfolding k_n_def
      by (meson linorder_not_less order_less_trans) 

    let ?mid = "drop (k_cy + 1) (take k_n H)"
    have empty_mid: "filter u_enq ?mid = []"
    proof -
      have "\<forall>x \<in> set ?mid. \<not> u_enq x"
      proof
        fix x assume "x \<in> set ?mid"
        (* Proof step. *)
        then obtain i where i_prop: "i < length ?mid" "x = ?mid ! i" 
          unfolding in_set_conv_nth by blast
        
        (* Proof step. *)
        (* Use kn_prop and k_cx to justify that take k_n H is in range. *)
        have len_take: "length (take k_n H) = k_n" 
          using kn_prop k_cx by simp
          
        (* Proof note. *)
        have "x = take k_n H ! (k_cy + 1 + i)" 
          using i_prop
          by (metis Suc_eq_plus1 Suc_leI kn_prop len_take nth_drop) 
        also have "... = H ! (k_cy + 1 + i)" 
          using i_prop(1) len_take by simp
        finally have x_val: "x = H ! (k_cy + 1 + i)" .
        
        (* k_cy, k_n *)
        have "k_cy < k_cy + 1 + i" by simp
        moreover have "k_cy + 1 + i < k_n" 
          using i_prop(1) len_take by auto
          
        (* Key proof idea. *)
        ultimately show "\<not> u_enq x" 
          using kn_least x_val by auto
      qed
      thus ?thesis by (auto simp: filter_empty_conv)
    qed

    have eq_take: "take (k_n + 1) H = take (k_cy + 1) H @ ?mid @ [H ! k_n]"
    proof -
      (* Key proof idea. *)
      have "take (k_n + 1) H = take k_n H @ [H ! k_n]" 
        using take_Suc_conv_app_nth kn_prop k_cx
        by (metis Suc_eq_plus1 dual_order.strict_trans2) 
      moreover have "take k_n H = take (k_cy + 1) (take k_n H) @ drop (k_cy + 1) (take k_n H)"
        by (metis append_take_drop_id) 
      (* Key proof idea. *)
      moreover have "take (k_cy + 1) (take k_n H) = take (k_cy + 1) H" 
        using kn_prop by simp
      ultimately show ?thesis by simp
    qed

    have P_n_eq: "filter u_enq (take (k_n + 1) H) = filter u_enq (take (k_cy + 1) H) @ [H ! k_n]"
      unfolding eq_take using empty_mid kn_prop by simp

    have cr_kn: "act_cr (H ! k_n) = ret"
    proof (cases "act_cr (H ! k_n) = call")
      case True
      let ?count_C = "\<lambda>xs. length (filter (\<lambda>e. act_cr e = call) xs)"
      let ?count_R = "\<lambda>xs. length (filter (\<lambda>e. act_cr e = ret) xs)"
      
      have "filter (\<lambda>e. act_cr e = call) (filter u_enq (take (k_n + 1) H)) = 
            filter (\<lambda>e. act_cr e = call) (filter u_enq (take (k_cy + 1) H)) @ [H ! k_n]"
        unfolding P_n_eq using True by simp
      hence C_n_eq: "?count_C (filter u_enq (take (k_n + 1) H)) = ?count_C (filter u_enq (take (k_cy + 1) H)) + 1" by simp
      
      have "filter (\<lambda>e. act_cr e = ret) (filter u_enq (take (k_n + 1) H)) = 
            filter (\<lambda>e. act_cr e = ret) (filter u_enq (take (k_cy + 1) H))"
        unfolding P_n_eq using True by simp 
      hence R_n_eq: "?count_R (filter u_enq (take (k_n + 1) H)) = ?count_R (filter u_enq (take (k_cy + 1) H))" by simp

      have hI25_Enq_Call_Ret_Balanced: "hI25_Enq_Call_Ret_Balanced s" using inv unfolding system_invariant_def by blast
      have base_bound: "?count_C (filter u_enq (take k_cy H)) \<ge> ?count_R (filter u_enq (take k_cy H))"
        using hI25_Enq_Call_Ret_Balanced `k_cy < length H` unfolding hI25_Enq_Call_Ret_Balanced_def Let_def H_def[symmetric] s_def[symmetric] u_enq_def
        by (meson linorder_le_less_linear order.asym) 
        
       have cy_step: "filter u_enq (take (k_cy + 1) H) = filter u_enq (take k_cy H) @ [H ! k_cy]"
        using take_Suc_conv_app_nth[of k_cy H] k_cy H_cy_mk
        unfolding u_enq_def
        by (auto simp: mk_act_def act_pid_def act_name_def)
        
      have cy_C: "?count_C (filter u_enq (take (k_cy + 1) H)) = ?count_C (filter u_enq (take k_cy H)) + 1"
        unfolding cy_step using H_cy_mk by (simp add: mk_act_def act_cr_def)
        
      have cy_R: "?count_R (filter u_enq (take (k_cy + 1) H)) = ?count_R (filter u_enq (take k_cy H))"
        unfolding cy_step using H_cy_mk by (simp add: mk_act_def act_cr_def)
        
      have "?count_C (filter u_enq (take (k_n + 1) H)) - ?count_R (filter u_enq (take (k_n + 1) H)) \<ge> 2"
        using C_n_eq R_n_eq cy_C cy_R base_bound by simp
        
      moreover have "?count_C (filter u_enq (take (k_n + 1) H)) - ?count_R (filter u_enq (take (k_n + 1) H)) \<le> 1"
        using hI25_Enq_Call_Ret_Balanced kn_prop k_cx unfolding hI25_Enq_Call_Ret_Balanced_def Let_def H_def[symmetric] s_def[symmetric] u_enq_def by simp
        
      ultimately show ?thesis by simp
    next
      case False
      thus ?thesis by (cases "act_cr (H ! k_n)") auto
    qed

    have wf: "hI7_His_WF s" using inv unfolding system_invariant_def by blast
    
    have bound_kn: "k_n < length H" using kn_prop k_cx by simp
    have pid_kn: "act_pid (H ! k_n) = u" using kn_prop unfolding u_enq_def by simp
    have oper_kn: "act_name (H ! k_n) = enq" using kn_prop unfolding u_enq_def by simp
    have order_s: "hI6_SSN_Order s"
      using inv unfolding system_invariant_def by blast
    
          obtain kj where
          kj_lt: "kj < k_n"
        and kj_pid: "act_pid (H ! kj) = u"
        and kj_ssn: "act_ssn (H ! kj) = act_ssn (H ! k_n)"
        and kj_oper: "act_name (H ! kj) = enq"
        and kj_cr: "act_cr (H ! kj) = call"
        and kj_val: "act_val (H ! kj) = act_val (H ! k_n)"
      proof -
        have wf_inst:
          "\<forall>k<length H.
            act_cr (H ! k) = ret \<longrightarrow>
            (\<exists>j<k.
               act_pid (H ! j) = act_pid (H ! k) \<and>
               act_ssn (H ! j) = act_ssn (H ! k) \<and>
               act_name (H ! j) = act_name (H ! k) \<and>
               act_cr (H ! j) = call \<and>
               (if act_name (H ! k) = enq
                then act_val (H ! j) = act_val (H ! k)
                else act_val (H ! j) = BOT))"
          using wf
          unfolding hI7_His_WF_def Let_def H_def[symmetric] s_def[symmetric]
          by auto

        have ex_j:
          "\<exists>j<k_n.
             act_pid (H ! j) = act_pid (H ! k_n) \<and>
             act_ssn (H ! j) = act_ssn (H ! k_n) \<and>
             act_name (H ! j) = act_name (H ! k_n) \<and>
             act_cr (H ! j) = call \<and>
             (if act_name (H ! k_n) = enq
              then act_val (H ! j) = act_val (H ! k_n)
              else act_val (H ! j) = BOT)"
          using wf_inst[rule_format, OF bound_kn cr_kn] .

        from ex_j obtain j0 where
            j0_lt: "j0 < k_n"
          and j0_pid: "act_pid (H ! j0) = act_pid (H ! k_n)"
          and j0_ssn: "act_ssn (H ! j0) = act_ssn (H ! k_n)"
          and j0_oper: "act_name (H ! j0) = act_name (H ! k_n)"
          and j0_cr: "act_cr (H ! j0) = call"
          and j0_val: "(if act_name (H ! k_n) = enq
                       then act_val (H ! j0) = act_val (H ! k_n)
                       else act_val (H ! j0) = BOT)"
          by auto

        have "act_pid (H ! j0) = u"
          using j0_pid pid_kn by simp
        moreover have "act_ssn (H ! j0) = act_ssn (H ! k_n)"
          using j0_ssn by simp
        moreover have "act_name (H ! j0) = enq"
          using j0_oper oper_kn by simp
        moreover have "act_cr (H ! j0) = call"
          using j0_cr by simp
        moreover have "act_val (H ! j0) = act_val (H ! k_n)"
          using j0_val oper_kn by simp
        ultimately show ?thesis
          using j0_lt that by blast
      qed

      have kj_le_kcy: "kj \<le> k_cy"
      proof (rule ccontr)
        assume "\<not> kj \<le> k_cy"
        hence "k_cy < kj" by simp
        moreover have "kj < k_n"
          by (rule kj_lt)
        moreover have "u_enq (H ! kj)"
          unfolding u_enq_def using kj_pid kj_oper by simp
        ultimately show False
          using kn_least[of kj] by simp
      qed

      have ssn_order_inst:
        "\<And>i j. i < length H \<Longrightarrow> j < length H \<Longrightarrow> i < j \<Longrightarrow> act_pid (H ! i) = act_pid (H ! j) \<Longrightarrow>
           act_ssn (H ! i) < act_ssn (H ! j) \<or>
           (act_ssn (H ! i) = act_ssn (H ! j) \<and> act_cr (H ! i) = call \<and> act_cr (H ! j) = ret)"
        using order_s
        unfolding hI6_SSN_Order_def H_def[symmetric] s_def[symmetric]
        by simp

      have kj_eq_kcy: "kj = k_cy"
      proof (rule antisym)
        show "kj \<le> k_cy" by (rule kj_le_kcy)
      next
        show "k_cy \<le> kj"
        proof (rule ccontr)
          assume "\<not> k_cy \<le> kj"
          hence kj_lt_kcy: "kj < k_cy" by simp

          have ssn_kj_lt_cy: "act_ssn (H ! kj) < act_ssn (H ! k_cy)"
          proof -
            have kj_len: "kj < length H"
              using kj_lt kn_prop k_cx by simp
            have pid_eq: "act_pid (H ! kj) = act_pid (H ! k_cy)"
              using kj_pid H_cy_mk by (auto simp: mk_act_def act_pid_def)
            have order_case:
              "act_ssn (H ! kj) < act_ssn (H ! k_cy) \<or>
               (act_ssn (H ! kj) = act_ssn (H ! k_cy) \<and> act_cr (H ! kj) = call \<and> act_cr (H ! k_cy) = ret)"
              using ssn_order_inst[OF kj_len k_cy kj_lt_kcy pid_eq] .
            then show ?thesis
            proof
              assume "act_ssn (H ! kj) < act_ssn (H ! k_cy)"
              then show ?thesis .
            next
              assume eq_case: "act_ssn (H ! kj) = act_ssn (H ! k_cy) \<and> act_cr (H ! kj) = call \<and> act_cr (H ! k_cy) = ret"
              hence "act_cr (H ! k_cy) = ret"
                by simp
              thus ?thesis
                using H_cy_mk by (auto simp: mk_act_def act_cr_def)
            qed
          qed

          have ssn_cy_le_kn: "act_ssn (H ! k_cy) \<le> act_ssn (H ! k_n)"
          proof -
            have pid_eq: "act_pid (H ! k_cy) = act_pid (H ! k_n)"
              using kn_prop H_cy_mk unfolding u_enq_def
              by (auto simp: mk_act_def act_pid_def act_name_def)
            have "act_ssn (H ! k_cy) < act_ssn (H ! k_n) \<or>
                  (act_ssn (H ! k_cy) = act_ssn (H ! k_n) \<and> act_cr (H ! k_cy) = call \<and> act_cr (H ! k_n) = ret)"
              using ssn_order_inst[OF _ _ _ pid_eq]
              using k_cy kn_prop k_cx by auto
            thus ?thesis
              using H_cy_mk cr_kn by (auto simp: mk_act_def act_cr_def)
          qed

          hence "act_ssn (H ! k_cy) \<le> act_ssn (H ! kj)"
            using kj_ssn by simp

          with ssn_kj_lt_cy show False
            by linarith
        qed
      qed

      have ssn_ry: "act_ssn (H ! k_n) = sn_y"
        using kj_eq_kcy kj_ssn H_cy_mk
        by (auto simp: mk_act_def act_ssn_def)

      have val_ry: "act_val (H ! k_n) = v_y"
        using kj_eq_kcy kj_val H_cy_mk
        by (auto simp: mk_act_def act_val_def)

      have pid_ry: "act_pid (H ! k_n) = u"
        using kn_prop unfolding u_enq_def by simp

      have oper_ry: "act_name (H ! k_n) = enq"
        using kn_prop unfolding u_enq_def by simp

      have H_ry: "H ! k_n = mk_act enq v_y u sn_y ret"
        using pid_ry oper_ry val_ry ssn_ry cr_kn
        unfolding mk_act_def act_name_def act_val_def act_pid_def act_ssn_def act_cr_def
        by (cases "H ! k_n") auto
    
      have "k_n \<noteq> k_cx"
        using H_cx_mk H_ry by (auto simp: mk_act_def)
      hence "k_n < k_cx"
        using kn_prop by simp

      have kn_len: "k_n < length H"
        using `k_n < k_cx` k_cx by simp
    
      have hb_act: "HB_Act s (mk_op enq v_y u sn_y) (mk_op enq v_x u sn_x)"
      proof -
        have ret_match: "match_ret (his_seq s) k_n (mk_op enq v_y u sn_y)"
          unfolding match_ret_def Let_def H_def[symmetric] s_def[symmetric]
          using kn_len H_ry
          by (auto simp: mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
                         mk_act_def act_name_def act_pid_def act_val_def act_ssn_def act_cr_def)

        have call_match: "match_call (his_seq s) k_cx (mk_op enq v_x u sn_x)"
          unfolding match_call_def Let_def H_def[symmetric] s_def[symmetric]
          using k_cx H_cx_mk
          by (auto simp: mk_op_def op_name_def op_pid_def op_val_def op_ssn_def
                         mk_act_def act_name_def act_pid_def act_val_def act_ssn_def act_cr_def)

        have "HB (his_seq s) (mk_op enq v_y u sn_y) (mk_op enq v_x u sn_x)"
          unfolding HB_def
          using `k_n < k_cx` ret_match call_match
          by blast
        thus ?thesis
          unfolding HB_Act_def by simp
      qed

      have "HB_EnqRetCall s v_y v_x"
        unfolding HB_EnqRetCall_def
        using hb_act by blast
      then have hb_candidate_yx: "HB_EnqRetCall s v_x v_y \<or> HB_EnqRetCall s v_y v_x"
        by blast
      from hb_candidate_yx show ?thesis
        by simp
  qed

  (* Proof step. *)
  have hI24_HB_Implies_Idx_Order: "hI24_HB_Implies_Idx_Order s"
    using inv unfolding system_invariant_def by blast

  show ?thesis
  proof (rule ccontr)
    assume not_thesis: "\<not> HB_EnqRetCall (cs, us) v_x v_y"
    have not_xy: "\<not> HB_EnqRetCall s v_x v_y"
      using not_thesis unfolding s_def by simp

    have y_first: "HB_EnqRetCall s v_y v_x"
    proof -
      from hb_candidate show ?thesis
      proof
        assume xy: "HB_EnqRetCall s v_x v_y"
        with not_xy show ?thesis by contradiction
      next
        assume yx: "HB_EnqRetCall s v_y v_x"
        then show ?thesis .
      qed
    qed

    obtain p1 p2 sy sx where
      act_yx: "HB_Act s (mk_op enq v_y p1 sy) (mk_op enq v_x p2 sx)"
      using y_first unfolding HB_EnqRetCall_def by blast

     have j_lt_idx': "j < idx"
      using act_yx hI24_HB_Implies_Idx_Order arr_x arr_y
      unfolding hI24_HB_Implies_Idx_Order_def s_def
      using HB_implies_idx_order inv inv_sys by blast

    show False
      using j_lt_idx' idx_lt by simp
  qed
qed

lemma oldest_node:
  assumes inv_sys: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and pc: "c_program_counter cs p = ''D3''"
      and q_not_bot: "CState.Q_arr cs (CState.j_var cs p) \<noteq> BOT"
      and node: "(nid_tar, CState.Q_arr cs (CState.j_var cs p), ts_tar) \<in> set (pools ts u_tar)"
      and not_top: "ts_tar \<noteq> TOP"
      and nid_eq: "nid_tar = CState.j_var cs p"
      and unscanned: "u_tar \<notin> t_scanned ts p"
  shows "pool_getOldest (pools ts u_tar) = (nid_tar, ts_tar)"
proof -
  let ?pool = "pools ts u_tar"
  let ?j = "CState.j_var cs p"
  have sorted: "sorted (map fst ?pool)" using sorted_nid[OF inv_tsq] by blast
  have nonempty: "?pool \<noteq> []" using node by auto

  obtain hd_n hd_v hd_ts where hd: "hd ?pool = (hd_n, hd_v, hd_ts)"
    by (cases "hd ?pool") auto
  have hd_in: "(hd_n, hd_v, hd_ts) \<in> set ?pool" using nonempty hd
    by (metis hd_in_set) 

  (* Proof note. *)
  have hd_n_is_hd: "hd_n = hd (map fst ?pool)" 
    using hd nonempty by (simp add: hd_map)
    
  (* Proof step. *)
  moreover have "nid_tar \<in> set (map fst ?pool)" 
    using node by force

  (* Proof step. *)
  ultimately have hd_n_le_tar: "hd_n \<le> nid_tar"
    using sorted nonempty
    by (metis list.sel(1) list.set_cases nle_le sorted_simps(2))

  have "hd_n = nid_tar"
  proof (rule ccontr)
    assume "hd_n \<noteq> nid_tar"
    with hd_n_le_tar have "hd_n < nid_tar" by simp

    show False
    proof (cases "hd_ts = TOP")
      case True
      (* Proof step. *)
      from True hd_in have top_node: "(hd_n, hd_v, TOP) \<in> set ?pool" by simp
      
      have "t_pc ts u_tar = ''TE2''" and "t_nid ts u_tar = hd_n"
        using sim top_node unfolding Simulation_R_def Let_def by auto
        
      (* Proof step. *)
      have pc_e2: "c_program_counter cs u_tar = ''E2''"
      proof -
        (* Proof note. *)
        have ok: "TypeOK (cs, us)" 
          using inv_sys unfolding system_invariant_def by blast
        
        (* cs, us *)
        have range: "program_counter (cs, us) u_tar \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
          using ok unfolding TypeOK_def by blast
          
        (* cs, us *)
        hence "c_program_counter cs u_tar \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
          unfolding program_counter_def by simp

        (* Key proof idea. *)
        thus ?thesis
          using sim `t_pc ts u_tar = ''TE2''` 
          unfolding Simulation_R_def Let_def 
          by auto
      qed

      (* Proof step. *)
      have "CState.i_var cs u_tar = hd_n"
        using sim pc_e2 `t_nid ts u_tar = hd_n` unfolding Simulation_R_def Let_def by auto
        
      (* Condition 15. *)
      have cond15: "\<forall>nid. (\<exists>v ts_val. (nid, v, ts_val) \<in> set ?pool \<and> ts_val \<noteq> TOP) \<longrightarrow> nid < CState.i_var cs u_tar"
        using sim pc_e2 unfolding Simulation_R_def Let_def by auto
        
      (* nid_tar, ... *)
      have "nid_tar < hd_n"
        using cond15 node not_top `CState.i_var cs u_tar = hd_n` by blast
        
      (* Nid-related proof note. *)
      with `hd_n < nid_tar` show False by simp
    next
      case False
      (* Proof note. *)
      have no_non_top: "\<forall>n < nid_tar. \<not>(\<exists>v ts. (n, v, ts) \<in> set ?pool \<and> ts \<noteq> TOP)"
        using inv_sys inv_tsq sim pc q_not_bot unscanned node not_top nid_eq
        by (metis no_smaller_non_top) 
        (* blast dest: no_smaller_non_top *)

      (* Nid-related proof note. *)
      with `hd_n < nid_tar` hd_in False show False by blast
    qed
  qed

  (* Nid-related proof note. *)
  from hd_in `hd_n = nid_tar` have "(nid_tar, hd_v, hd_ts) \<in> set ?pool" by simp
  
  (* Key proof idea. *)
  with node inv_tsq have data_eq: "hd_v = CState.Q_arr cs ?j \<and> hd_ts = ts_tar"
    unfolding TSQ_State_Inv_def by auto

  (* Key proof idea. *)
  have hd_ts_not_top: "hd_ts \<noteq> TOP"
    using data_eq not_top by simp

  (* Proof note. *)
  (* Pool/array correspondence note. *)
  obtain tail where pool_cons: "?pool = (hd_n, hd_v, hd_ts) # tail"
    using hd nonempty by (cases "?pool") auto

  (* Key proof idea. *)
  show ?thesis
    using pool_cons `hd_n = nid_tar` data_eq hd_ts_not_top
    unfolding pool_getOldest_def
    by simp
qed

(* ==================================================================== *)
(* Proof note. *)
(* ==================================================================== *)
lemma unscanned_target:
  assumes inv_sys: "system_invariant (cs, us)"
      and sim: "Simulation_R (cs, us) ts"
      and pc: "c_program_counter cs p = ''D3''"
      and q_not_bot: "CState.Q_arr cs (CState.j_var cs p) \<noteq> BOT"
      and node: "(nid_tar, CState.Q_arr cs (CState.j_var cs p), ts_tar) \<in> set (pools ts u_tar)"
      and not_top: "ts_tar \<noteq> TOP"
      and nid_eq: "nid_tar = CState.j_var cs p"
  shows "u_tar \<notin> t_scanned ts p"
proof
  assume scanned: "u_tar \<in> t_scanned ts p"
  let ?j = "CState.j_var cs p"

  (* t_startTs *)
  have ts_val_valid: "ts_tar <\<^sub>t\<^sub>s t_startTs ts p"
  proof -
    have j_lt_l: "?j < CState.l_var cs p"
      using pc inv_sys unfolding system_invariant_def sI6_D3_Scan_Pointers_def by (simp add: Model.j_var_def Model.l_var_def program_counter_def) 
    have "\<forall>idx < CState.l_var cs p. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> 
            (\<forall>u nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts p)"
      using sim pc unfolding Simulation_R_def Let_def by auto
    thus ?thesis using j_lt_l q_not_bot node nid_eq by auto
  qed

  (* Condition 18. *)
  have cond18_all:
    "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow>
      (\<forall>v \<in> t_scanned ts q. \<forall>nid v_val ts_val.
        (nid, v_val, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP \<longrightarrow>
        nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q))"
    using sim unfolding Simulation_R_def Let_def
    by (metis fst_eqD)

  have cond18: "\<forall>v \<in> t_scanned ts p. \<forall>nid v_val ts_val. 
        (nid, v_val, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
        nid < CState.j_var cs p \<or> \<not> ts_less ts_val (t_startTs ts p)"
    using cond18_all pc by blast

  (* Proof step. *)
  have "nid_tar < CState.j_var cs p \<or> \<not> ts_less ts_tar (t_startTs ts p)"
    using cond18 scanned node not_top by blast

  (* Key proof idea. *)
  thus False using nid_eq ts_val_valid by auto
qed

(* ==================================================================== *)
(* Proof note. *)
(* ==================================================================== *)

lemma D3_Eval_Success_Helper:
  fixes cs :: CState and us :: UState and ts :: TState and p :: nat and cs' :: CState
  assumes inv_sys: "system_invariant (cs, us)"
      and inv_tsq: "TSQ_State_Inv ts"
      and sim: "Simulation_R (cs, us) ts"
      and pc: "c_program_counter cs p = ''D3''"
      and q_not_bot: "CState.Q_arr cs (CState.j_var cs p) \<noteq> BOT"
      and cs'_eq: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D4'' else c_program_counter cs x),
                               Q_arr := (\<lambda>x. if x = CState.j_var cs p then BOT else CState.Q_arr cs x),
                               j_var := CState.j_var cs,
                               x_var := (\<lambda>x. if x = p then CState.Q_arr cs (CState.j_var cs p) else CState.x_var cs x) \<rparr>"
  shows "\<exists>ts'. T_D3 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  define s where "s = (cs, us)"
  have inv_s: "system_invariant s" and sim_s: "Simulation_R s ts"
    using inv_sys sim unfolding s_def by auto

  let ?j = "CState.j_var cs p"
  let ?val = "CState.Q_arr cs ?j"

  (* Proof note. *)
have ex_tar_all:
  "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow>
     (\<exists>u\<in>ProcSet. \<exists>nid ts_tar.
        (nid, CState.Q_arr cs idx, ts_tar) \<in> set (pools ts u) \<and> ts_tar \<noteq> TOP)"
  using sim
  unfolding Simulation_R_def Let_def
  by simp

have ex_tar:
  "\<exists>u\<in>ProcSet. \<exists>nid ts_tar.
      (nid, ?val, ts_tar) \<in> set (pools ts u) \<and> ts_tar \<noteq> TOP"
  using ex_tar_all q_not_bot
  by blast

then obtain u_tar where
  u_tar_in: "u_tar \<in> ProcSet"
  and ex_tar_u: "\<exists>nid ts_tar. (nid, ?val, ts_tar) \<in> set (pools ts u_tar) \<and> ts_tar \<noteq> TOP"
  by blast

from ex_tar_u obtain nid_tar ts_tar
  where node_in_pool: "(nid_tar, ?val, ts_tar) \<in> set (pools ts u_tar)"
    and ts_not_top: "ts_tar \<noteq> TOP"
  by blast

have nid_is_j: "nid_tar = ?j"
  using inv_s sim_s node_in_pool ts_not_top q_not_bot
  unfolding s_def by (metis nid_tar_is_j_var)

  (* Proof phase. *)
  have u_tar_unscanned: "u_tar \<notin> t_scanned ts p"
    using inv_sys inv_tsq sim pc q_not_bot node_in_pool ts_not_top nid_is_j
    using unscanned_target by blast

  have oldest_eq: "pool_getOldest (pools ts u_tar) = (nid_tar, ts_tar)"
    using inv_s inv_tsq sim_s pc q_not_bot node_in_pool ts_not_top nid_is_j u_tar_unscanned
    unfolding s_def by (metis oldest_node)

  (* Proof phase. *)
  define ts' where "ts' = ts\<lparr> 
    t_pc := (\<lambda>x. if x = p then ''TD_Remove_Done'' else t_pc ts x),
    t_retV := (\<lambda>x. if x = p then ?val else t_retV ts x),
    pools := (\<lambda>x. if x = u_tar then remove1 (nid_tar, ?val, ts_tar) (pools ts x) else pools ts x),
    t_candNid := (\<lambda>x. if x = p then nid_tar else t_candNid ts x),
    t_candTs := (\<lambda>x. if x = p then ts_tar else t_candTs ts x),
    t_candPid := (\<lambda>x. if x = p then u_tar else t_candPid ts x),
    t_scanned := (\<lambda>x. if x = p then ProcSet else t_scanned ts x)
  \<rparr>"

  (* Proof note. *)
  have ghost_step: "T_D3 p ts ts'"
  proof -
    let ?ts1 = "ts\<lparr> t_candNid := (\<lambda>x. if x = p then nid_tar else t_candNid ts x),
                     t_candTs := (\<lambda>x. if x = p then ts_tar else t_candTs ts x),
                     t_candPid := (\<lambda>x. if x = p then u_tar else t_candPid ts x),
                     t_scanned := (\<lambda>x. if x = p then t_scanned ts p \<union> {u_tar} else t_scanned ts x) \<rparr>"

    have step1: "T_D3_Scan p u_tar ts ?ts1"
    proof -
      have pc_loop: "t_pc ts p = ''TD_Loop''" using sim pc unfolding Simulation_R_def Let_def by auto
      have cand_bot: "t_candTs ts p = TOP" using sim pc unfolding Simulation_R_def Let_def by auto
      have nid_not_bot: "nid_tar \<noteq> BOT" using nid_is_j inv_sys pc unfolding system_invariant_def sI6_D3_Scan_Pointers_def
        using sI1_Zero_Index_BOT_def BOT_def Model.Q_arr_def q_not_bot by force

      have not_start_less: "\<not> ts_less (t_startTs ts p) ts_tar"
      proof -
        have "?j < CState.l_var cs p" using inv_sys pc unfolding system_invariant_def sI6_D3_Scan_Pointers_def
          by (simp add: Model.j_var_def Model.l_var_def program_counter_def)
        moreover have "\<forall>idx < CState.l_var cs p. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts p)"
          using sim pc unfolding Simulation_R_def Let_def by auto 
        ultimately have "ts_tar <\<^sub>t\<^sub>s t_startTs ts p" using q_not_bot node_in_pool nid_is_j by blast
        thus ?thesis using ts_less.simps by (cases "t_startTs ts p"; cases ts_tar) auto
      qed
      
      have ts_tar_less: "ts_less ts_tar (t_candTs ts p)" using cand_bot ts_not_top
        by (metis ts_less.simps(2) ts_type.exhaust) 
      
     have u_tar_lt: "u_tar < N_Procs"
  using u_tar_in
  by (simp add: ProcSet_def)

show ?thesis
  unfolding T_D3_Scan_def Let_def oldest_eq
  using pc_loop u_tar_unscanned nid_not_bot not_start_less ts_tar_less u_tar_lt
  by auto
    qed

    have ghost_cond: "\<forall>k \<in> ProcSet - t_scanned ?ts1 p. fst (pool_getOldest (pools ts k)) = BOT \<or> \<not> ts_less (snd (pool_getOldest (pools ts k))) ts_tar"
    proof (intro ballI)
      fix k assume k: "k \<in> ProcSet - t_scanned ?ts1 p"
      hence k_not_scan: "k \<notin> t_scanned ts p" by simp
      let ?oldest = "pool_getOldest (pools ts k)"
      
      obtain nid tstamp where old: "?oldest = (nid, tstamp)" by (cases ?oldest) auto
      
      show "fst ?oldest = BOT \<or> \<not> ts_less (snd ?oldest) ts_tar"
      proof (cases "nid = BOT")
        case True
        have "fst ?oldest = BOT" using old True by simp
        thus ?thesis by simp
      next
        case False
        have "\<not> ts_less tstamp ts_tar"
        proof
          assume "ts_less tstamp ts_tar"
          then obtain v where node: "(nid, v, tstamp) \<in> set (pools ts k)" and tstamp_not_top: "tstamp \<noteq> TOP"
            using False pool_getOldest_SomeE[OF old]
            by (smt (verit, best) ts_less.elims(1) ts_type.distinct(1)) 
            
           have ts_nid_order: "(tstamp <\<^sub>t\<^sub>s ts_tar) = (nid < nid_tar)"
        using TSQ_State_InvD_pool_ts_order[OF inv_tsq node node_in_pool tstamp_not_top ts_not_top] .
            
          have "nid < nid_tar"
            using `ts_less tstamp ts_tar` ts_nid_order by simp

          have "nid < ?j"
            using `nid < nid_tar` nid_is_j by simp
            
            obtain n where tstamp_shape: "tstamp = TS n"
              using tstamp_not_top by (cases tstamp) auto
            
            have "CState.Q_arr cs nid = v \<and> v \<in> Val"
              using sim node tstamp_shape
              unfolding Simulation_R_def Let_def
              by (metis fst_conv)
            
            then have "CState.Q_arr cs nid \<noteq> BOT"
              unfolding Val_def BOT_def by auto
          
          have cond6: "(\<exists>idx < ?j. 
                  (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid_x ts_y. (nid_x, CState.Q_arr cs idx, ts_y) \<in> set (pools ts k) \<and> ts_y \<noteq> TOP)) \<or> 
                  (CState.Q_arr cs idx = BOT \<and> c_program_counter cs k = ''E2'' \<and> CState.i_var cs k = idx \<and> idx \<noteq> BOT)) 
                  \<longrightarrow> k \<in> t_scanned ts p"
            using sim pc unfolding Simulation_R_def Let_def by simp
            
          have "CState.Q_arr cs nid \<noteq> BOT \<and> (\<exists>nid_x ts_y. (nid_x, CState.Q_arr cs nid, ts_y) \<in> set (pools ts k) \<and> ts_y \<noteq> TOP)"
            using `CState.Q_arr cs nid \<noteq> BOT` node tstamp_not_top inv_s node_in_pool_implies_Q_nonempty s_def sim_s
            by blast 
            
          hence "\<exists>idx < ?j. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid_x ts_y. (nid_x, CState.Q_arr cs idx, ts_y) \<in> set (pools ts k) \<and> ts_y \<noteq> TOP))"
            using `nid < ?j` by blast
            
          hence "k \<in> t_scanned ts p" using cond6 by blast
          with k_not_scan show False by simp
        qed
        
        hence "\<not> ts_less (snd ?oldest) ts_tar" using old by simp
        thus ?thesis by simp
      qed
    qed

    have pc_loop1: "t_pc ?ts1 p = ''TD_Loop''" 
      using step1 unfolding T_D3_Scan_def Let_def by auto
    
    have ghost_cond_aligned: "\<forall>k\<in>ProcSet - t_scanned ?ts1 p.
      fst (pool_getOldest (pools ?ts1 k)) = BOT \<or>
      \<not> snd (pool_getOldest (pools ?ts1 k)) <\<^sub>t\<^sub>s t_candTs ?ts1 p \<or>
      t_startTs ?ts1 p <\<^sub>t\<^sub>s snd (pool_getOldest (pools ?ts1 k))"
    proof -
      have "pools ?ts1 = pools ts" by simp
      moreover have "t_candTs ?ts1 p = ts_tar" by simp
      ultimately show ?thesis using ghost_cond by auto
    qed

    from Ghost_Fast_Forward[OF pc_loop1 ghost_cond_aligned] obtain ts_mid 
      where star: "T_D3_Scan_Star p ?ts1 ts_mid"
        and scanned_mid: "ProcSet \<subseteq> t_scanned ts_mid p"
        and cand_mid: "t_candNid ts_mid p = t_candNid ?ts1 p" 
      by blast

    have eval: "T_D3_Eval p ts_mid ts'"
    proof -
      define ts_start where "ts_start = ?ts1"
      
      define INV where "INV = (\<lambda>x::TState. 
        x = ts_start\<lparr> 
          t_candNid := (\<lambda>q. if q = p then t_candNid x p else t_candNid ts_start q),
          t_candTs  := (\<lambda>q. if q = p then t_candTs x p  else t_candTs ts_start q),
          t_candPid := (\<lambda>q. if q = p then t_candPid x p else t_candPid ts_start q),
          t_scanned := (\<lambda>q. if q = p then t_scanned x p else t_scanned ts_start q) 
        \<rparr> \<and> 
        t_candPid x p = u_tar \<and> 
        t_candTs x p = ts_tar \<and> 
        t_scanned ts_start p \<subseteq> t_scanned x p)"

      have init_clean: "INV ts_start"
      proof -
        have eq_nid: "(\<lambda>q. if q = p then t_candNid ts_start p else t_candNid ts_start q) = t_candNid ts_start" by auto
        have eq_ts:  "(\<lambda>q. if q = p then t_candTs ts_start p  else t_candTs ts_start q) = t_candTs ts_start" by auto
        have eq_pid: "(\<lambda>q. if q = p then t_candPid ts_start p else t_candPid ts_start q) = t_candPid ts_start" by auto
        have eq_scan: "(\<lambda>q. if q = p then t_scanned ts_start p else t_scanned ts_start q) = t_scanned ts_start"
        proof -
          have "\<forall>n. (if n = p then t_scanned ts_start p else t_scanned ts_start n) = t_scanned ts_start n"
            by moura
          then show ?thesis
            by blast
        qed 
        
        have eq_self: "ts_start = ts_start\<lparr> 
          t_candNid := (\<lambda>q. if q = p then t_candNid ts_start p else t_candNid ts_start q),
          t_candTs  := (\<lambda>q. if q = p then t_candTs ts_start p  else t_candTs ts_start q),
          t_candPid := (\<lambda>q. if q = p then t_candPid ts_start p else t_candPid ts_start q),
          t_scanned := (\<lambda>q. if q = p then t_scanned ts_start p else t_scanned ts_start q) 
        \<rparr>" 
          unfolding eq_nid eq_ts eq_pid eq_scan by simp
        
        have val_pid: "t_candPid ts_start p = u_tar" unfolding ts_start_def by simp
        have val_ts: "t_candTs ts_start p = ts_tar" unfolding ts_start_def by simp
        have val_scan: "t_scanned ts_start p \<subseteq> t_scanned ts_start p" by blast
        
        show ?thesis 
          unfolding INV_def
          using eq_self val_pid val_ts val_scan by blast
      qed

      have step_preserve: "\<And>tsa ts' k. INV tsa \<Longrightarrow> T_D3_Scan p k tsa ts' \<Longrightarrow> INV ts'"
      proof -
        fix tsa ts' k
        assume ih: "INV tsa"
        assume hyps: "T_D3_Scan p k tsa ts'"
        
        have "k \<in> ProcSet - t_scanned tsa p" 
          using hyps unfolding T_D3_Scan_def Let_def by auto
        hence k_proc: "k \<in> ProcSet" and k_not_scan: "k \<notin> t_scanned tsa p" by auto
        
        have "t_scanned ts_start p \<subseteq> t_scanned tsa p" using ih unfolding INV_def by blast
        with k_not_scan have "k \<notin> t_scanned ts_start p" by blast
        with k_proc have "k \<in> ProcSet - t_scanned ts_start p" by blast
        hence "k \<in> ProcSet - t_scanned ?ts1 p" unfolding ts_start_def by simp
        
        hence "fst (pool_getOldest (pools ts k)) = BOT \<or> \<not> ts_less (snd (pool_getOldest (pools ts k))) ts_tar"
          using ghost_cond by blast
          
        moreover have "pools tsa = pools ts_start" 
          using ih unfolding INV_def
          by (smt (verit, del_insts) TState.cases_scheme TState.select_convs(2)
              TState.update_convs(10,11,12,14)) 
        hence "pools tsa = pools ts" unfolding ts_start_def by simp
        ultimately have cond_false: "fst (pool_getOldest (pools tsa k)) = BOT \<or> \<not> ts_less (snd (pool_getOldest (pools tsa k))) ts_tar"
          by simp
          
        obtain nid tstamp where old_eq: "pool_getOldest (pools tsa k) = (nid, tstamp)"
          by (cases "pool_getOldest (pools tsa k)")
        have cond_flat: "nid = BOT \<or> \<not> ts_less tstamp ts_tar"
          using cond_false old_eq by simp
          
        have tsa_ts_tar: "t_candTs tsa p = ts_tar"
          using ih unfolding INV_def by simp
          
        have tsa_shape:
  "tsa =
    ts_start
    \<lparr>t_candNid := (\<lambda>q. if q = p then t_candNid tsa p else t_candNid ts_start q),
       t_candTs := (\<lambda>q. if q = p then t_candTs tsa p else t_candTs ts_start q),
       t_candPid := (\<lambda>q. if q = p then t_candPid tsa p else t_candPid ts_start q),
       t_scanned := (\<lambda>q. if q = p then t_scanned tsa p else t_scanned ts_start q)\<rparr>"
  using ih unfolding INV_def by blast

have pid_tsa: "t_candPid tsa p = u_tar"
  using ih unfolding INV_def by blast

have scan_sub_tsa: "t_scanned ts_start p \<subseteq> t_scanned tsa p"
  using ih unfolding INV_def by blast

have candNid_eq: "t_candNid ts' p = t_candNid tsa p"
  using hyps cond_flat old_eq tsa_ts_tar
  unfolding T_D3_Scan_def Let_def by auto

have candTs_eq: "t_candTs ts' p = t_candTs tsa p"
  using hyps cond_flat old_eq tsa_ts_tar
  unfolding T_D3_Scan_def Let_def by auto

have candPid_eq: "t_candPid ts' p = t_candPid tsa p"
  using hyps cond_flat old_eq tsa_ts_tar
  unfolding T_D3_Scan_def Let_def by auto

have scanned_eq: "t_scanned ts' p = insert k (t_scanned tsa p)"
  using hyps old_eq
  unfolding T_D3_Scan_def Let_def by auto

have cond_off:
  "\<not> (nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp)"
  using cond_flat tsa_ts_tar
  by auto

have ts'_exp:
  "ts' =
    tsa\<lparr>t_candNid :=
          (\<lambda>x. if x = p then
                 (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
                  then nid else t_candNid tsa p)
               else t_candNid tsa x),
        t_candTs :=
          (\<lambda>x. if x = p then
                 (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
                  then tstamp else t_candTs tsa p)
               else t_candTs tsa x),
        t_candPid :=
          (\<lambda>x. if x = p then
                 (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
                  then k else t_candPid tsa p)
               else t_candPid tsa x),
        t_scanned := (\<lambda>x. if x = p then t_scanned tsa p \<union> {k} else t_scanned tsa x)\<rparr>"
  using hyps old_eq
  unfolding T_D3_Scan_def Let_def
  by simp

have candNid_fun:
  "(\<lambda>x. if x = p then
          (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
           then nid else t_candNid tsa p)
        else t_candNid tsa x)
   = t_candNid tsa"
proof
  fix x
  show "(if x = p then
           (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
            then nid else t_candNid tsa p)
         else t_candNid tsa x)
      = t_candNid tsa x"
    using cond_off by (cases "x = p") auto
qed

have candTs_fun:
  "(\<lambda>x. if x = p then
          (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
           then tstamp else t_candTs tsa p)
        else t_candTs tsa x)
   = t_candTs tsa"
proof
  fix x
  show "(if x = p then
           (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
            then tstamp else t_candTs tsa p)
         else t_candTs tsa x)
      = t_candTs tsa x"
    using cond_off by (cases "x = p") auto
qed

have candPid_fun:
  "(\<lambda>x. if x = p then
          (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
           then k else t_candPid tsa p)
        else t_candPid tsa x)
   = t_candPid tsa"
proof
  fix x
  show "(if x = p then
           (if nid \<noteq> BOT \<and> ts_less tstamp (t_candTs tsa p) \<and> \<not> ts_less (t_startTs tsa p) tstamp
            then k else t_candPid tsa p)
         else t_candPid tsa x)
      = t_candPid tsa x"
    using cond_off by (cases "x = p") auto
qed

have ts'_from_tsa:
  "ts' =
    tsa\<lparr>t_scanned := (\<lambda>q. if q = p then t_scanned tsa p \<union> {k} else t_scanned tsa q)\<rparr>"
  using ts'_exp candNid_fun candTs_fun candPid_fun
  by simp

have candNid_fun_eq:
  "(\<lambda>q. if q = p then t_candNid ts' p else t_candNid ts_start q) =
   (\<lambda>q. if q = p then t_candNid tsa p else t_candNid ts_start q)"
  using candNid_eq
  by auto

have candTs_fun_eq:
  "(\<lambda>q. if q = p then t_candTs ts' p else t_candTs ts_start q) =
   (\<lambda>q. if q = p then t_candTs tsa p else t_candTs ts_start q)"
  using candTs_eq
  by auto

have candPid_fun_eq:
  "(\<lambda>q. if q = p then t_candPid ts' p else t_candPid ts_start q) =
   (\<lambda>q. if q = p then t_candPid tsa p else t_candPid ts_start q)"
  using candPid_eq
  by auto

have scanned_fun_eq':
  "(\<lambda>q. if q = p then t_scanned ts' p else t_scanned ts_start q) =
   (\<lambda>q. if q = p then t_scanned tsa p \<union> {k} else t_scanned ts_start q)"
proof
  fix q
  show "(if q = p then t_scanned ts' p else t_scanned ts_start q) =
        (if q = p then t_scanned tsa p \<union> {k} else t_scanned ts_start q)"
    using scanned_eq
    by (cases "q = p") auto
qed

have ts'_shape:
  "ts' =
    ts_start
    \<lparr>t_candNid := (\<lambda>q. if q = p then t_candNid ts' p else t_candNid ts_start q),
       t_candTs := (\<lambda>q. if q = p then t_candTs ts' p else t_candTs ts_start q),
       t_candPid := (\<lambda>q. if q = p then t_candPid ts' p else t_candPid ts_start q),
       t_scanned := (\<lambda>q. if q = p then t_scanned ts' p else t_scanned ts_start q)\<rparr>"
proof -
  have scan_eq_tsa:
    "t_scanned tsa = (\<lambda>r. if r = p then t_scanned tsa p else t_scanned ts_start r)"
  proof -
    from tsa_shape have
      "t_scanned tsa =
        t_scanned
          (ts_start
            \<lparr>t_candNid := (\<lambda>q. if q = p then t_candNid tsa p else t_candNid ts_start q),
               t_candTs := (\<lambda>q. if q = p then t_candTs tsa p else t_candTs ts_start q),
               t_candPid := (\<lambda>q. if q = p then t_candPid tsa p else t_candPid ts_start q),
               t_scanned := (\<lambda>q. if q = p then t_scanned tsa p else t_scanned ts_start q)\<rparr>)"
      by (rule arg_cong[where f=t_scanned])
    then show ?thesis
      by simp
  qed

  have scan_fun_eq_mid:
    "(\<lambda>q. if q = p then t_scanned tsa p \<union> {k} else t_scanned tsa q) =
     (\<lambda>q. if q = p then t_scanned tsa p \<union> {k} else t_scanned ts_start q)"
  proof
    fix q
    show "(if q = p then t_scanned tsa p \<union> {k} else t_scanned tsa q) =
          (if q = p then t_scanned tsa p \<union> {k} else t_scanned ts_start q)"
    proof (cases "q = p")
      case True
      then show ?thesis by simp
    next
      case False
      from scan_eq_tsa have scan_at_q:
        "t_scanned tsa q = (if q = p then t_scanned tsa p else t_scanned ts_start q)"
        by (rule fun_cong)
      from scan_at_q False have "t_scanned tsa q = t_scanned ts_start q"
        by simp
      then show ?thesis
        using False by simp
    qed
  qed

  have mid:
    "ts' =
      ts_start
      \<lparr>t_candNid := (\<lambda>q. if q = p then t_candNid tsa p else t_candNid ts_start q),
         t_candTs := (\<lambda>q. if q = p then t_candTs tsa p else t_candTs ts_start q),
         t_candPid := (\<lambda>q. if q = p then t_candPid tsa p else t_candPid ts_start q),
         t_scanned := (\<lambda>q. if q = p then t_scanned tsa p \<union> {k} else t_scanned ts_start q)\<rparr>"
  proof -
    from ts'_from_tsa have
      "ts' =
        (ts_start
          \<lparr>t_candNid := (\<lambda>q. if q = p then t_candNid tsa p else t_candNid ts_start q),
             t_candTs := (\<lambda>q. if q = p then t_candTs tsa p else t_candTs ts_start q),
             t_candPid := (\<lambda>q. if q = p then t_candPid tsa p else t_candPid ts_start q),
             t_scanned := (\<lambda>q. if q = p then t_scanned tsa p else t_scanned ts_start q)\<rparr>)
         \<lparr>t_scanned := (\<lambda>q. if q = p then t_scanned tsa p \<union> {k} else t_scanned tsa q)\<rparr>"
      using tsa_shape
      by simp
    also have "... =
      ts_start
      \<lparr>t_candNid := (\<lambda>q. if q = p then t_candNid tsa p else t_candNid ts_start q),
         t_candTs := (\<lambda>q. if q = p then t_candTs tsa p else t_candTs ts_start q),
         t_candPid := (\<lambda>q. if q = p then t_candPid tsa p else t_candPid ts_start q),
         t_scanned := (\<lambda>q. if q = p then t_scanned tsa p \<union> {k} else t_scanned ts_start q)\<rparr>"
      using scan_fun_eq_mid
      by simp
    finally show ?thesis .
  qed

  show ?thesis
    using mid candNid_fun_eq candTs_fun_eq candPid_fun_eq scanned_fun_eq'
    by simp
qed
note step_preserve = this
have pid_eq: "t_candPid ts' p = u_tar"
  using candPid_eq pid_tsa by simp

have ts_eq: "t_candTs ts' p = ts_tar"
  using candTs_eq tsa_ts_tar by simp

have scan_sub: "t_scanned ts_start p \<subseteq> t_scanned ts' p"
  using scan_sub_tsa scanned_eq by blast

have inv_ts': "INV ts'"
  unfolding INV_def
  using ts'_shape pid_eq ts_eq scan_sub
  by simp

show "INV ts'"
  using inv_ts' by simp
qed
     have star_clean: "T_D3_Scan_Star p ts_start ts_mid" 
        using star unfolding ts_start_def by simp

      (* Proof step. *)
      have star_preserve_gen: "T_D3_Scan_Star q a b \<Longrightarrow> q = p \<longrightarrow> INV a \<longrightarrow> INV b" for q a b
        apply (erule T_D3_Scan_Star.induct)
         apply simp
        apply (intro impI)
        using step_preserve by metis

      (* Proof step. *)
      have star_preserve: "T_D3_Scan_Star p a b \<Longrightarrow> INV a \<longrightarrow> INV b" for a b
        using star_preserve_gen by blast

      (* Proof note. *)
      have star_preserve: "T_D3_Scan_Star p a b \<Longrightarrow> INV a \<longrightarrow> INV b" for a b
        using star_preserve_gen by simp

      have mid_invs_clean: "INV ts_mid"
        using star_preserve[OF star_clean] init_clean by blast

      have ts_mid_eq: "ts_mid = ts_start\<lparr> 
          t_candNid := (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q),
          t_candTs  := (\<lambda>q. if q = p then t_candTs ts_mid p  else t_candTs ts_start q),
          t_candPid := (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q),
          t_scanned := (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) 
        \<rparr>" using mid_invs_clean unfolding INV_def by blast

      have mid_candPid_p: "t_candPid ts_mid p = u_tar" using mid_invs_clean unfolding INV_def by blast
      have mid_candTs_p: "t_candTs ts_mid p = ts_tar" using mid_invs_clean unfolding INV_def by blast
      have mid_candNid_p: "t_candNid ts_mid p = nid_tar" using cand_mid by simp

      have scanned_subset: "t_scanned ts_mid p \<subseteq> ProcSet"
        using T_D3_Scan_Star_scanned_subset[OF star]
        using TSQ_State_InvD_scanned_subset T_D3_Scan_Star.step
          T_D3_Scan_Star_scanned_subset inv_tsq star step1
        by blast 
      with scanned_mid have scanned_eq: "t_scanned ts_mid p = ProcSet" by blast

      have dist_pool: "distinct (map fst (pools ts u_tar))"
        using distinct_pools[OF inv_tsq] by blast

      have pool_rem_aux: "\<And>xs. distinct (map fst xs) \<Longrightarrow> (nid_tar, ?val, ts_tar) \<in> set xs \<Longrightarrow> ts_tar \<noteq> TOP \<Longrightarrow> 
        pool_remove xs nid_tar = (?val, remove1 (nid_tar, ?val, ts_tar) xs)"
      proof -
        fix xs
        show "distinct (map fst xs) \<Longrightarrow> (nid_tar, ?val, ts_tar) \<in> set xs \<Longrightarrow> ts_tar \<noteq> TOP \<Longrightarrow> pool_remove xs nid_tar = (?val, remove1 (nid_tar, ?val, ts_tar) xs)"
        proof (induction xs)
          case Nil thus ?case by simp
        next
          case (Cons a xs)
          obtain n v tstamp where a_eq: "a = (n, v, tstamp)" by (cases a)
          show ?case
          proof (cases "n = nid_tar")
            case True
            have "nid_tar \<notin> fst ` set xs" using Cons.prems(1) a_eq True by simp
            moreover have "(nid_tar, ?val, ts_tar) \<in> set (a # xs)" using Cons.prems(2) by simp
            ultimately have a_is_tar: "a = (nid_tar, ?val, ts_tar)" using a_eq True by force
            thus ?thesis using True a_eq Cons.prems by (auto split: prod.splits if_splits)
          next
            case False
            have "a \<noteq> (nid_tar, ?val, ts_tar)" using False a_eq by simp
            hence in_xs: "(nid_tar, ?val, ts_tar) \<in> set xs" using Cons.prems(2) by simp
            have dist_xs: "distinct (map fst xs)" using Cons.prems(1) by simp
            have ih: "pool_remove xs nid_tar = (?val, remove1 (nid_tar, ?val, ts_tar) xs)"
              using Cons.IH[OF dist_xs in_xs Cons.prems(3)] .
            show ?thesis using False a_eq ih Cons.prems by (auto split: prod.splits if_splits)
          qed
        qed
      qed

      have pool_rem: "pool_remove (pools ts u_tar) nid_tar = (?val, remove1 (nid_tar, ?val, ts_tar) (pools ts u_tar))"
        using pool_rem_aux[OF dist_pool node_in_pool ts_not_top] .

      have nid_not_bot: "nid_tar \<noteq> BOT"
        using nid_is_j inv_sys pc unfolding system_invariant_def
        by (metis sI1_Zero_Index_BOT_def BOT_def Model.Q_arr_def fst_conv q_not_bot)

      have mid_pc_p: "t_pc ts_mid p = ''TD_Loop''" 
      proof -
        from mid_invs_clean have eq_record: "ts_mid = ts_start\<lparr> 
          t_candNid := (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q),
          t_candTs  := (\<lambda>q. if q = p then t_candTs ts_mid p  else t_candTs ts_start q),
          t_candPid := (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q),
          t_scanned := (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) 
        \<rparr>" unfolding INV_def by blast
        
        hence "t_pc ts_mid = t_pc (ts_start\<lparr> 
          t_candNid := (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q),
          t_candTs  := (\<lambda>q. if q = p then t_candTs ts_mid p  else t_candTs ts_start q),
          t_candPid := (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q),
          t_scanned := (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) 
        \<rparr>)" by (rule arg_cong)
        
        hence "t_pc ts_mid = t_pc ts_start" by simp
        with ts_start_def show ?thesis
          using pc_loop1 by argo 
      qed

      have mid_pools_p: "pools ts_mid = pools ts" 
      proof -
        from mid_invs_clean have eq_record: "ts_mid = ts_start\<lparr> 
          t_candNid := (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q),
          t_candTs  := (\<lambda>q. if q = p then t_candTs ts_mid p  else t_candTs ts_start q),
          t_candPid := (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q),
          t_scanned := (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) 
        \<rparr>" unfolding INV_def by blast

        hence "pools ts_mid = pools (ts_start\<lparr> 
          t_candNid := (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q),
          t_candTs  := (\<lambda>q. if q = p then t_candTs ts_mid p  else t_candTs ts_start q),
          t_candPid := (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q),
          t_scanned := (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) 
        \<rparr>)" by (rule arg_cong)

        hence "pools ts_mid = pools ts_start" by simp
        with ts_start_def show ?thesis by simp
      qed

      have eval_raw: "T_D3_Eval p ts_mid ts' = 
          ((t_candNid ts_mid p \<noteq> BOT \<longrightarrow> 
            t_pc ts_mid p = ''TD_Loop'' \<and> t_scanned ts_mid p = ProcSet \<and> 
            (case pool_remove (pools ts_mid (t_candPid ts_mid p)) (t_candNid ts_mid p) of 
              (val, new_pool) \<Rightarrow> (val \<noteq> BOT \<longrightarrow> ts' = ts_mid\<lparr>pools := (pools ts_mid)(t_candPid ts_mid p := new_pool), t_retV := (t_retV ts_mid)(p := val), t_pc := (t_pc ts_mid)(p := ''TD_Remove_Done'')\<rparr>) 
                               \<and> (val = BOT \<longrightarrow> ts' = ts_mid\<lparr>t_pc := (t_pc ts_mid)(p := ''TD1'')\<rparr>))) 
          \<and> (t_candNid ts_mid p = BOT \<longrightarrow> t_pc ts_mid p = ''TD_Loop'' \<and> t_scanned ts_mid p = ProcSet \<and> ts' = ts_mid\<lparr>t_pc := (t_pc ts_mid)(p := ''TD1'')\<rparr>))"
        unfolding T_D3_Eval_def Let_def fun_upd_def
        by (auto split: if_splits)

      show ?thesis
      proof -
        note pass = mid_pc_p mid_pools_p q_not_bot nid_not_bot mid_candNid_p mid_candTs_p mid_candPid_p scanned_eq pool_rem
        
        have ts_mid_fields:
          "t_pc ts_mid = t_pc ts"
          "pools ts_mid = pools ts"
          "ts_counter ts_mid = ts_counter ts"
          "nid_counter ts_mid = nid_counter ts"
          "t_V_var ts_mid = t_V_var ts"
          "t_v ts_mid = t_v ts"
          "t_nid ts_mid = t_nid ts"
          "t_ts ts_mid = t_ts ts"
          "t_startTs ts_mid = t_startTs ts"
          "t_retV ts_mid = t_retV ts"
          "TState.more ts_mid = TState.more ts"
        proof -
          let ?Mid_Rec = "ts_start\<lparr> 
            t_candNid := (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q), 
            t_candTs  := (\<lambda>q. if q = p then t_candTs ts_mid p  else t_candTs ts_start q), 
            t_candPid := (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q), 
            t_scanned := (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) \<rparr>"
            
          from mid_invs_clean have eq: "ts_mid = ?Mid_Rec" unfolding INV_def by blast
          
          have "t_pc ts_mid = t_pc ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq1: "t_pc ts_mid = t_pc ts_start" by simp
          have "pools ts_mid = pools ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq2: "pools ts_mid = pools ts_start" by simp
          have "ts_counter ts_mid = ts_counter ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq3: "ts_counter ts_mid = ts_counter ts_start" by simp
          have "nid_counter ts_mid = nid_counter ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq4: "nid_counter ts_mid = nid_counter ts_start" by simp
          have "t_V_var ts_mid = t_V_var ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq5: "t_V_var ts_mid = t_V_var ts_start" by simp
          have "t_v ts_mid = t_v ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq6: "t_v ts_mid = t_v ts_start" by simp
          have "t_nid ts_mid = t_nid ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq7: "t_nid ts_mid = t_nid ts_start" by simp
          have "t_ts ts_mid = t_ts ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq8: "t_ts ts_mid = t_ts ts_start" by simp
          have "t_startTs ts_mid = t_startTs ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq9: "t_startTs ts_mid = t_startTs ts_start" by simp
          have "t_retV ts_mid = t_retV ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq10: "t_retV ts_mid = t_retV ts_start" by simp
          have "TState.more ts_mid = TState.more ?Mid_Rec" by (rule arg_cong[OF eq])
          hence eq11: "TState.more ts_mid = TState.more ts_start" by simp
          
          show 
            "t_pc ts_mid = t_pc ts" "pools ts_mid = pools ts" "ts_counter ts_mid = ts_counter ts"
            "nid_counter ts_mid = nid_counter ts" "t_V_var ts_mid = t_V_var ts" "t_v ts_mid = t_v ts"
            "t_nid ts_mid = t_nid ts" "t_ts ts_mid = t_ts ts" "t_startTs ts_mid = t_startTs ts"
            "t_retV ts_mid = t_retV ts" "TState.more ts_mid = TState.more ts"
            using eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11
            unfolding ts_start_def by simp_all
        qed

        have ts_mid_cand_fields:
          "t_candNid ts_mid = (\<lambda>x. if x = p then nid_tar else t_candNid ts x)"
          "t_candTs ts_mid = (\<lambda>x. if x = p then ts_tar else t_candTs ts x)"
          "t_candPid ts_mid = (\<lambda>x. if x = p then u_tar else t_candPid ts x)"
          "t_scanned ts_mid = (\<lambda>x. if x = p then ProcSet else t_scanned ts x)"
        proof -
          let ?Mid_Rec = "ts_start\<lparr> 
            t_candNid := (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q), 
            t_candTs  := (\<lambda>q. if q = p then t_candTs ts_mid p  else t_candTs ts_start q), 
            t_candPid := (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q), 
            t_scanned := (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) \<rparr>"
            
          from mid_invs_clean have eq: "ts_mid = ?Mid_Rec" unfolding INV_def by blast
          
          have eq_nid: "t_candNid ts_mid = (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q)" 
            using arg_cong[OF eq, of t_candNid] by simp

          have eq_ts:  "t_candTs ts_mid = (\<lambda>q. if q = p then t_candTs ts_mid p else t_candTs ts_start q)" 
            using arg_cong[OF eq, of t_candTs] by simp

          have eq_pid: "t_candPid ts_mid = (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q)" 
            using arg_cong[OF eq, of t_candPid] by simp

          have eq_scan: "t_scanned ts_mid = (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q)" 
            using arg_cong[OF eq, of t_scanned] by simp

          show "t_candNid ts_mid = (\<lambda>x. if x = p then nid_tar else t_candNid ts x)"
          proof (rule ext)
            fix x 
            have "t_candNid ts_mid x = (\<lambda>q. if q = p then t_candNid ts_mid p else t_candNid ts_start q) x"
              using eq_nid by (rule fun_cong)
            hence "t_candNid ts_mid x = (if x = p then t_candNid ts_mid p else t_candNid ts_start x)" by simp
            thus "t_candNid ts_mid x = (if x = p then nid_tar else t_candNid ts x)"
              using mid_candNid_p ts_start_def by simp
          qed

          show "t_candTs ts_mid = (\<lambda>x. if x = p then ts_tar else t_candTs ts x)"
          proof (rule ext)
            fix x 
            have "t_candTs ts_mid x = (\<lambda>q. if q = p then t_candTs ts_mid p else t_candTs ts_start q) x"
              using eq_ts by (rule fun_cong)
            hence "t_candTs ts_mid x = (if x = p then t_candTs ts_mid p else t_candTs ts_start x)" by simp
            thus "t_candTs ts_mid x = (if x = p then ts_tar else t_candTs ts x)"
              using mid_candTs_p ts_start_def by simp
          qed

          show "t_candPid ts_mid = (\<lambda>x. if x = p then u_tar else t_candPid ts x)"
          proof (rule ext)
            fix x 
            have "t_candPid ts_mid x = (\<lambda>q. if q = p then t_candPid ts_mid p else t_candPid ts_start q) x"
              using eq_pid by (rule fun_cong)
            hence "t_candPid ts_mid x = (if x = p then t_candPid ts_mid p else t_candPid ts_start x)" by simp
            thus "t_candPid ts_mid x = (if x = p then u_tar else t_candPid ts x)"
              using mid_candPid_p ts_start_def by simp
          qed

          show "t_scanned ts_mid = (\<lambda>x. if x = p then ProcSet else t_scanned ts x)"
          proof (rule ext)
            fix x 
            have "t_scanned ts_mid x = (\<lambda>q. if q = p then t_scanned ts_mid p else t_scanned ts_start q) x"
              using eq_scan by (rule fun_cong)
            hence "t_scanned ts_mid x = (if x = p then t_scanned ts_mid p else t_scanned ts_start x)" by simp
            thus "t_scanned ts_mid x = (if x = p then ProcSet else t_scanned ts x)"
              using scanned_eq ts_start_def by auto
          qed
        qed

        show ?thesis
          apply (subst eval_raw)
          apply (insert pass)
          apply (clarsimp split: prod.splits if_splits)
          apply (rule TState.equality)
                   apply (rule ext)
          apply (simp add: ts'_def ts_mid_fields)
          apply (rule ext)
          subgoal for x
          proof (cases "x = u_tar")
            case True
            have x_pid: "x = t_candPid ts_mid p" using True mid_candPid_p by simp
            show ?thesis
              unfolding ts'_def
              using ts_mid_fields(2) True x_pid mid_candNid_p mid_candTs_p
             by simp
          next
            case False
            have x_pid_neq: "x \<noteq> t_candPid ts_mid p" using False mid_candPid_p by simp
            show ?thesis
              unfolding ts'_def
              using ts_mid_fields(2) False x_pid_neq
             by simp
          qed
          apply (simp add: ts'_def ts_mid_fields)
          apply (simp add: ts'_def ts_mid_fields)
          apply (simp add: ts'_def ts_mid_fields)
          apply (simp add: ts'_def ts_mid_fields)
          apply (simp add: ts'_def ts_mid_fields)
          apply (simp add: ts'_def ts_mid_fields)
          apply (simp add: ts'_def ts_mid_fields)
          apply (rule ext)
          subgoal for x
            using ts_mid_cand_fields(1) unfolding ts'_def by force
          apply (rule ext)
          subgoal for x
            using ts_mid_cand_fields(2) unfolding ts'_def by force
          apply (rule ext)
          subgoal for x
            using ts_mid_cand_fields(3) unfolding ts'_def by force
          apply (rule ext)
          subgoal for x
          proof (cases "x = p")
            case True
            show ?thesis
              unfolding ts'_def
              using True
             by simp
          next
            case False
            show ?thesis
              unfolding ts'_def
              using False ts_mid_fields(10)
             by simp
          qed
          apply (rule ext)
          subgoal for x
            using ts_mid_cand_fields(4) unfolding ts'_def
           by simp
          using ts_mid_fields(10)
          unfolding ts'_def by simp
      qed
    qed
    
      have pc_loop: "t_pc ts p = ''TD_Loop''"
        using step1 unfolding T_D3_Scan_def Let_def by auto
      
      have scanned_full: "t_scanned ts_mid p = ProcSet"
        using eval unfolding T_D3_Eval_def by auto
      
      show ?thesis 
        using pc_loop T_D3_Scan_Star.step[OF step1 star] scanned_full eval
        unfolding T_D3_def 
        by blast
  qed 

  (* Proof phase. *)
  have sim_r_next: "Simulation_R (cs', us) ts'"
  proof (unfold Simulation_R_def Let_def fst_conv snd_conv, intro conjI)
    show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ts' q = ''TL0''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ts' q = ''TE1''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ts' q = ''TE2''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ts' q = ''TE3''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ts' q = ''TD1''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ts' q = ''TD_Line4_Done''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ts' q = ''TD_Loop''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ts' q = ''TD_Remove_Done''" using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto

    (* Cond 3 *)
    show "\<forall>q. \<forall>node\<in>set (pools ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts' q = ''TE2'' \<and> t_nid ts' q = fst node"
    proof (intro allI ballI)
      fix q node assume "node \<in> set (pools ts' q)"
      then have "node \<in> set (pools ts q)" using ts'_def by (auto split: if_splits dest: set_remove1_subset[THEN subsetD])
      with sim have cond: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
        unfolding Simulation_R_def Let_def by meson 
      show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts' q = ''TE2'' \<and> t_nid ts' q = fst node"
      proof (cases "q = p")
        case True
        have "t_pc ts p = ''TD_Loop''" using sim pc unfolding Simulation_R_def Let_def by simp 
        hence "t_pc ts p \<noteq> ''TE2''" by simp
        with cond True have "snd (snd node) \<noteq> TOP" by blast
        with ts'_def show ?thesis by auto
      next
        case False
        with cond ts'_def show ?thesis by auto
      qed
    qed

(* Cond 5.1 *)
    show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP)"
    proof (intro allI impI)
      fix idx 
      assume not_bot_cs': "CState.Q_arr cs' idx \<noteq> BOT" 
      
      have idx_neq_j: "idx \<noteq> ?j" using not_bot_cs' cs'_eq by auto
      
      then have "CState.Q_arr cs idx = CState.Q_arr cs' idx" using cs'_eq by simp
      with not_bot_cs' have not_bot_cs: "CState.Q_arr cs idx \<noteq> BOT" by simp
      
      (* Key proof idea. *)
      from sim this obtain u nid ts_val where u_in: "u \<in> ProcSet" 
                                          and old_in: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" 
                                          and not_top: "ts_val \<noteq> TOP"
        unfolding Simulation_R_def Let_def
        by (meson ex_tar_all) 
        
      show "\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP"
      proof (cases "u = u_tar \<and> (nid, CState.Q_arr cs idx, ts_val) = (nid_tar, ?val, ts_tar)")
        case True
        then have "CState.Q_arr cs idx = ?val" by auto
        with array_value_unique[OF inv_sys not_bot_cs] have "idx = ?j" by auto
        thus ?thesis using idx_neq_j by blast
      next
        case False
        then have "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts' u)"
          using old_in ts'_def by (cases "u = u_tar") auto
        (* Key proof idea. *)
        with not_top u_in show ?thesis
          using `CState.Q_arr cs idx = CState.Q_arr cs' idx`
          by fastforce 
      qed
    qed

    (* Cond 5.2 *)
    show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ts' u))"
    proof (intro allI impI, elim conjE)
      fix u idx
      assume q_bot_cs': "CState.Q_arr cs' idx = BOT" 
         and pc_E2_cs': "c_program_counter cs' u = ''E2''" 
         and i_eq_idx_cs': "CState.i_var cs' u = idx"
         
      have u_neq_p: "u \<noteq> p" using pc_E2_cs' cs'_eq by force
      
      have pc_E2_cs: "c_program_counter cs u = ''E2''" using pc_E2_cs' cs'_eq u_neq_p by auto
      have i_eq_idx_cs: "CState.i_var cs u = idx" using i_eq_idx_cs' cs'_eq u_neq_p by auto
      have v_var_eq: "CState.v_var cs' u = CState.v_var cs u" using cs'_eq u_neq_p by simp
      
      have q_bot_cs: "CState.Q_arr cs idx = BOT"
      proof (cases "idx = ?j")
        case True
        then have "CState.i_var cs u = ?j" using i_eq_idx_cs by simp
        with inv_s have q_bot_j: "CState.Q_arr cs ?j = BOT" 
          unfolding system_invariant_def sI3_E2_Slot_Exclusive_def s_def using ProcSet_def finite_ProcSet
          by (metis Model.Q_arr_def Model.i_var_def fst_eqD pc_E2_cs
              program_counter_def) 
        show ?thesis using q_bot_j q_not_bot by blast
      next
        case False
        then show ?thesis using q_bot_cs' cs'_eq by auto
      qed

      from sim q_bot_cs pc_E2_cs i_eq_idx_cs
      obtain nid where old_in: "(nid, CState.v_var cs u, TOP) \<in> set (pools ts u)" 
        unfolding Simulation_R_def Let_def by (metis split_pairs2)
        
      show "\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ts' u)"
      proof (cases "u = u_tar \<and> nid = nid_tar")
        case True
        with old_in have "(nid_tar, CState.v_var cs u, TOP) \<in> set (pools ts u_tar)" by auto
        with node_in_pool ts_not_top have False 
          using inv_tsq unfolding TSQ_State_Inv_def by auto
        thus ?thesis by simp
      next
        case False
        show ?thesis
        proof (cases "u = u_tar")
          case True
          with False have "nid \<noteq> nid_tar" by simp
          have tuple_safe: "(nid, CState.v_var cs u, TOP) \<in> set (remove1 (nid_tar, CState.Q_arr cs (CState.j_var cs p), ts_tar) (pools ts u))"
            using old_in `nid \<noteq> nid_tar` by auto
          have "(nid, CState.v_var cs' u, TOP) \<in> set (pools ts' u)"
            using tuple_safe ts'_def v_var_eq True by simp
          thus ?thesis by blast
        next
          case False
          have "(nid, CState.v_var cs' u, TOP) \<in> set (pools ts' u)"
            using old_in ts'_def v_var_eq False by simp
          thus ?thesis by blast
        qed
      qed
    qed

    (* Cond 6 *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
             (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
             (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) 
           \<longrightarrow> v \<in> t_scanned ts' q)"
    proof (intro allI impI)
      fix q v
      assume pc_q: "c_program_counter cs' q = ''D3''"
      
      have q_neq_p: "q \<noteq> p" using pc_q cs'_eq by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_neq_p cs'_eq by auto
      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_eq by simp
      have scan_eq: "t_scanned ts' q = t_scanned ts q" using q_neq_p ts'_def by auto
      
      have old_imp: "(\<exists>idx < CState.j_var cs q. 
             (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
             (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) 
           \<longrightarrow> v \<in> t_scanned ts q"
        using sim pc_q_old unfolding Simulation_R_def Let_def by simp

      assume "\<exists>idx < CState.j_var cs' q. 
             (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
             (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
      then obtain idx where idx_less: "idx < CState.j_var cs' q" and 
           cond: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
                  (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
           by blast

      have idx_neq_j: "idx \<noteq> ?j"
      proof
        assume idx_eq_j: "idx = ?j"
        hence "CState.Q_arr cs' idx = BOT" using cs'_eq by simp
        with cond have pc_v_cs': "c_program_counter cs' v = ''E2''" and i_v_cs': "CState.i_var cs' v = ?j"
          using idx_eq_j by auto
          
        have v_neq_p: "v \<noteq> p" using pc_v_cs' cs'_eq by force
        
        have pc_v_cs: "c_program_counter cs v = ''E2''" 
          using pc_v_cs' cs'_eq v_neq_p by auto
        have i_v_cs: "CState.i_var cs v = ?j" 
          using i_v_cs' cs'_eq v_neq_p by auto
        
        have "CState.Q_arr cs ?j = BOT"
        proof -
          have sI3_E2_Slot_Exclusive: "sI3_E2_Slot_Exclusive (cs, us)" 
            using inv_sys unfolding system_invariant_def by blast
          show ?thesis
            using sI3_E2_Slot_Exclusive pc_v_cs i_v_cs
            unfolding sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Model.Q_arr_def
            by auto
        qed
        
        moreover have "CState.Q_arr cs ?j \<noteq> BOT" using q_not_bot by simp
        ultimately show False by simp
      qed

      have old_rhs: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                     (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
      proof (cases "CState.Q_arr cs' idx = BOT")
        case True
        with cond have pc_v_new: "c_program_counter cs' v = ''E2''" 
                   and i_v_new: "CState.i_var cs' v = idx" 
                   and idx_not_bot: "idx \<noteq> BOT" by auto
        
        have v_neq_p: "v \<noteq> p" 
        proof
          assume "v = p"
          with pc_v_new cs'_eq have "''D4'' = ''E2''" by auto
          thus False by simp
        qed
        
        hence pc_v_old: "c_program_counter cs v = ''E2''" using pc_v_new cs'_eq by auto
        have i_v_old: "CState.i_var cs v = idx" using i_v_new cs'_eq v_neq_p by auto
        have q_bot_old: "CState.Q_arr cs idx = BOT" using True cs'_eq idx_neq_j by auto
        
        thus ?thesis using idx_not_bot
          using i_v_old pc_v_old by fastforce 
        
      next
        case False
        hence not_bot_new: "CState.Q_arr cs' idx \<noteq> BOT" by simp
        with cond obtain nid_x ts_x where 
          node_in_new: "(nid_x, CState.Q_arr cs' idx, ts_x) \<in> set (pools ts' v)" and 
          ts_not_top: "ts_x \<noteq> TOP" by blast
        
        have q_eq: "CState.Q_arr cs idx = CState.Q_arr cs' idx" using cs'_eq idx_neq_j by auto
        
        have node_in_old: "(nid_x, CState.Q_arr cs idx, ts_x) \<in> set (pools ts v)"
        proof (cases "v = u_tar")
          case True
          with node_in_new ts'_def have "(nid_x, CState.Q_arr cs' idx, ts_x) \<in> set (remove1 (nid_tar, ?val, ts_tar) (pools ts v))" by auto
          thus ?thesis using q_eq set_remove1_subset by fastforce
        next
          case False
          with node_in_new ts'_def show ?thesis using q_eq by auto
        qed
        
        with False q_eq ts_not_top show ?thesis by auto
      qed

      have "idx < CState.j_var cs q" using idx_less j_q_eq by simp
      with old_imp old_rhs have "v \<in> t_scanned ts q" by blast
      thus "v \<in> t_scanned ts' q" using scan_eq by simp
    qed

    (* Cond 7 *)
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts' q)) = 1"
    proof (intro allI impI)
      fix q assume pc_q_new: "c_program_counter cs' q = ''E2''"
      
      have q_neq_p: "q \<noteq> p" using pc_q_new cs'_eq by force
      
      have pc_q_old: "c_program_counter cs q = ''E2''" 
        using pc_q_new q_neq_p cs'_eq by auto
      
      have old_len: "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
        using sim pc_q_old unfolding Simulation_R_def Let_def by simp
        
      show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts' q)) = 1"
      proof (cases "q = u_tar")
        case True
        let ?tar_node = "(nid_tar, ?val, ts_tar)"
        have pools_update: "pools ts' q = remove1 ?tar_node (pools ts q)"
          using True ts'_def by simp
        
        have not_top_node: "snd (snd ?tar_node) \<noteq> TOP" using ts_not_top by simp
        
        have "filter (\<lambda>node. snd (snd node) = TOP) (remove1 ?tar_node (pools ts q)) = 
              filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)"
        proof (induction "pools ts q")
          case Nil thus ?case by simp
        next
          case (Cons a xs)
          then show ?case 
            using not_top_node by (simp add: filter_remove1)
        qed
        
        with pools_update old_len show ?thesis by simp
        
      next
        case False
        have "pools ts' q = pools ts q" 
          using False ts'_def by auto
        with old_len show ?thesis by simp
      qed
    qed

    (* Cond 8 *)
    show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> 
      (\<forall>idx < CState.l_var cs' q. 
        (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts' q)) \<and> 
        (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts' u <\<^sub>t\<^sub>s t_startTs ts' q))"
    proof (rule allI, rule impI, rule allI, rule impI)
      fix q idx assume pc_q_new: "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''"
      assume idx_less: "idx < CState.l_var cs' q"

      have q_neq_p: "q \<noteq> p" using pc_q_new cs'_eq by force
      hence pc_q_old: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" using pc_q_new cs'_eq by auto
      have l_eq: "CState.l_var cs' q = CState.l_var cs q" using q_neq_p cs'_eq by simp
      have startTs_eq: "t_startTs ts' q = t_startTs ts q" using q_neq_p ts'_def by auto

      show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts' q)) \<and> 
            (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts' u <\<^sub>t\<^sub>s t_startTs ts' q)"
      proof (rule conjI)
        show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts' q)"
        proof (rule impI, rule allI, rule allI, rule allI, rule impI)
          fix u nid ts_val 
          assume q_not_bot': "CState.Q_arr cs' idx \<noteq> BOT" 
          assume node_in': "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts' u)"
          
          have idx_neq_j: "idx \<noteq> ?j" using q_not_bot' cs'_eq by auto
          hence q_val_eq: "CState.Q_arr cs idx = CState.Q_arr cs' idx" using cs'_eq by simp
          
          have node_in_old: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)"
          proof (cases "u = u_tar")
            case True
            from node_in' True have "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (remove1 (nid_tar, ?val, ts_tar) (pools ts u))"
              unfolding ts'_def by simp
            thus ?thesis using q_val_eq set_remove1_subset by fastforce
          next
            case False
            from node_in' False show ?thesis 
              unfolding ts'_def q_val_eq by simp
          qed
          
          from sim pc_q_old idx_less l_eq q_not_bot' q_val_eq node_in_old 
          show "ts_val <\<^sub>t\<^sub>s t_startTs ts' q"
            unfolding Simulation_R_def Let_def startTs_eq
            by (metis split_pairs2) 
        qed

        show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ts' u <\<^sub>t\<^sub>s t_startTs ts' q"
        proof (rule allI, rule impI)
          fix u assume hyp: "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
          then have u_neq_p: "u \<noteq> p" using cs'_eq by force
          
          have idx_neq_j: "idx \<noteq> ?j"
          proof (rule notI) 
            assume "idx = ?j"
            with hyp u_neq_p have "c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = ?j" 
              using cs'_eq by auto
            hence "CState.Q_arr cs ?j = BOT" 
              using inv_s unfolding system_invariant_def sI3_E2_Slot_Exclusive_def s_def
              by (metis Model.Q_arr_def Model.i_var_def fst_conv program_counter_def) 
            with q_not_bot show False by simp
          qed
          
          from hyp idx_neq_j u_neq_p have "CState.Q_arr cs idx = BOT \<and> c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx" 
            using cs'_eq by auto
          with sim pc_q_old idx_less l_eq show "t_ts ts' u <\<^sub>t\<^sub>s t_startTs ts' q"
            unfolding Simulation_R_def Let_def startTs_eq ts'_def using u_neq_p by auto
        qed
      qed
    qed

    (* Cond 9 *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ts' q = BOT \<and> t_candTs ts' q = TOP" 
      using sim cs'_eq pc ts'_def unfolding Simulation_R_def Let_def by auto

    (* Cond 10 *)
    show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
    proof (intro allI impI)
      fix u nid v n assume node_in': "(nid, v, TS n) \<in> set (pools ts' u)"
      
      have nid_neq_j: "nid \<noteq> ?j"
      proof (rule notI)
        assume nid_eq: "nid = ?j"
        
        consider "u = u_tar" | "u \<noteq> u_tar" by blast
        thus False
        proof cases
          case 1 
          hence pools_upd: "pools ts' u = remove1 (nid_tar, ?val, ts_tar) (pools ts u)"
            using ts'_def by simp
          from node_in' pools_upd have in_rem: "(nid, v, TS n) \<in> set (remove1 (nid_tar, ?val, ts_tar) (pools ts u))"
            by simp
          
          have node_old: "(nid, v, TS n) \<in> set (pools ts u)"
            using in_rem by (meson set_remove1_subset subsetD)
          
          have triple_eq: "(nid, v, TS n) = (nid_tar, ?val, ts_tar)"
            using inv_tsq node_old node_in_pool nid_eq nid_is_j
            by (metis nid_uniqueness_from_data_indep)
          
          have ts_n_eq: "TS n = ts_tar"
            using triple_eq by simp
          
          have "distinct (map fst (pools ts u))"
            using distinct_pools[OF inv_tsq] by blast
          with node_old node_in_pool nid_eq nid_is_j have triple_eq: "(nid, v, TS n) = (nid_tar, ?val, ts_tar)"
            using inv_tsq nid_uniqueness_from_data_indep by blast

          have "distinct (pools ts u)" 
            using `distinct (map fst (pools ts u))`
            by (metis distinct_zipI1 zip_map_fst_snd) 
          
          hence "(nid, v, TS n) \<notin> set (remove1 (nid, v, TS n) (pools ts u))"
            by simp
          
          with triple_eq in_rem show False by simp            
        next
          case 2
          hence "pools ts' u = pools ts u" using ts'_def by simp
          with node_in' have node_old: "(nid, v, TS n) \<in> set (pools ts u)" by simp
          with nid_eq nid_is_j sim show False
            unfolding Simulation_R_def Let_def
            by (metis "2" inv_tsq nid_uniqueness_from_data_indep node_in_pool) 
        qed
      qed

      have old_in: "(nid, v, TS n) \<in> set (pools ts u)"
        using node_in' ts'_def by (cases "u = u_tar") (auto dest: set_remove1_subset[THEN subsetD])
      with sim have "CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
        unfolding Simulation_R_def Let_def by (metis fst_conv) 
      thus "CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
        using cs'_eq nid_neq_j by auto
    qed

    (* Cond 11 *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts' u) \<longrightarrow> v \<in> Val"
    proof (intro allI impI)
      fix u nid v ts_val
      assume node_in_ts': "(nid, v, ts_val) \<in> set (pools ts' u)"
      have node_in_ts: "(nid, v, ts_val) \<in> set (pools ts u)"
        using node_in_ts' ts'_def 
        by (cases "u = u_tar") (auto dest: set_remove1_subset[THEN subsetD])
      then show "v \<in> Val" 
        using sim unfolding Simulation_R_def Let_def by meson
    qed

    (* Cond 12 *)
    show "nid_counter ts' = CState.X_var cs'"
      using sim cs'_eq ts'_def unfolding Simulation_R_def Let_def by auto

    (* Cond 13 *)
    show "\<forall>p. c_program_counter cs' p \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ts' p = CState.i_var cs' p"
    proof (intro allI impI)
      fix q assume pc_q': "c_program_counter cs' q \<in> {''E2'', ''E3''}"
      have q_neq_p: "q \<noteq> p" using pc_q' cs'_eq by auto
      with sim pc_q' show "t_nid ts' q = CState.i_var cs' q"
        using ts'_def cs'_eq unfolding Simulation_R_def Let_def by auto
    qed

    (* Cond 14 *)
    show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
      (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts' q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
    proof (rule allI, rule impI, rule allI, rule allI, rule allI, rule allI, rule impI)
      fix q u nid v ts_val 
      assume pc_q': "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
      assume cond: "(nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts' q) ts_val"
      
      show "nid < CState.l_var cs' q"
      proof (cases "q = p")
        case True
        have pc_p_old: "c_program_counter cs p = ''D3''" using pc by simp
        have startTs_p: "t_startTs ts' p = t_startTs ts p" using ts'_def by simp
        have l_var_p: "CState.l_var cs' p = CState.l_var cs p" using cs'_eq by simp
        
        have old_node: "(nid, v, ts_val) \<in> set (pools ts u)"
          using cond ts'_def by (cases "u = u_tar") (auto dest: set_remove1_subset[THEN subsetD])
          
        with sim pc_p_old cond True startTs_p show ?thesis
          unfolding Simulation_R_def Let_def l_var_p
          by (metis fst_eqD insert_subset l_var_p subset_insertI) 
          
      next
        case False
        have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" 
          using pc_q' False cs'_eq by auto
        have startTs_q: "t_startTs ts' q = t_startTs ts q" 
          using False ts'_def by auto
        have l_var_q: "CState.l_var cs' q = CState.l_var cs q" 
          using False cs'_eq by simp
          
        have old_node: "(nid, v, ts_val) \<in> set (pools ts u)"
          using cond ts'_def by (cases "u = u_tar") (auto dest: set_remove1_subset[THEN subsetD])
          
        with sim pc_q_old cond False startTs_q show ?thesis
          unfolding Simulation_R_def Let_def l_var_q
          by (metis fst_eqD)
      qed
    qed

    (* Cond 15 *)
    show "\<forall>p' q'. c_program_counter cs' p' \<in> {''E2'', ''E3''} \<and> 
                  c_program_counter cs' q' \<in> {''D2'', ''D3'', ''D4''} \<and> 
                  \<not> ts_less (t_startTs ts' q') (t_ts ts' p') \<longrightarrow> 
                  CState.i_var cs' p' < CState.l_var cs' q'"
    proof (intro allI impI, elim conjE)
      fix p' q'
      assume pc_p': "c_program_counter cs' p' \<in> {''E2'', ''E3''}"
         and pc_q': "c_program_counter cs' q' \<in> {''D2'', ''D3'', ''D4''}"
         and not_less': "\<not> ts_less (t_startTs ts' q') (t_ts ts' p')"

      have p'_neq_p: "p' \<noteq> p" 
        using pc_p' cs'_eq by force
      hence i_var_p': "CState.i_var cs' p' = CState.i_var cs p'" 
        and t_ts_p': "t_ts ts' p' = t_ts ts p'"
        using cs'_eq ts'_def by auto

      show "CState.i_var cs' p' < CState.l_var cs' q'"
      proof (cases "q' = p")
        case True
        have i_var_eq: "CState.i_var cs' p' = CState.i_var cs p'" using cs'_eq p'_neq_p by simp
        have l_var_eq: "CState.l_var cs' p = CState.l_var cs p" using cs'_eq by simp
        
        have ts_p'_eq: "t_ts ts' p' = t_ts ts p'" using ts'_def p'_neq_p by simp
        have start_p_eq: "t_startTs ts' p = t_startTs ts p" using ts'_def by simp
        
        have old_cond15: "\<forall>p q. (c_program_counter cs p = ''E2'' \<or> c_program_counter cs p = ''E3'') \<and>
                                (c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3'' \<or> c_program_counter cs q = ''D4'') \<and>
                                \<not> ts_less (t_startTs ts q) (t_ts ts p) \<longrightarrow>
                                CState.i_var cs p < CState.l_var cs q"
          using sim unfolding Simulation_R_def Let_def by auto 
        have "c_program_counter cs p' \<in> {''E2'', ''E3''}" 
          using pc_p' p'_neq_p cs'_eq by auto
        moreover have "c_program_counter cs p = ''D3''" 
          using pc by simp
        moreover have "\<not> ts_less (t_startTs ts p) (t_ts ts p')" 
          using not_less' True ts_p'_eq start_p_eq by simp
        ultimately have "CState.i_var cs p' < CState.l_var cs p"
          using old_cond15 by blast
        
        thus ?thesis using True i_var_eq l_var_eq by simp
          
      next
        case False
        have pc_p_old: "c_program_counter cs p' \<in> {''E2'', ''E3''}"
          using pc_p' p'_neq_p cs'_eq by auto
        have pc_q_old: "c_program_counter cs q' \<in> {''D2'', ''D3'', ''D4''}" 
          using pc_q' False cs'_eq by auto
        
        have i_p_eq: "CState.i_var cs' p' = CState.i_var cs p'" using cs'_eq p'_neq_p by simp
        have l_q_eq: "CState.l_var cs' q' = CState.l_var cs q'" using cs'_eq False by simp
        
        have ts_p_eq: "t_ts ts' p' = t_ts ts p'" using ts'_def p'_neq_p by simp
        have startTs_q_eq: "t_startTs ts' q' = t_startTs ts q'" using ts'_def False by simp

        have old_cond15: "\<And>a b. \<lbrakk> c_program_counter cs a \<in> {''E2'', ''E3''}; 
                                 c_program_counter cs b \<in> {''D2'', ''D3'', ''D4''}; 
                                 \<not> ts_less (t_startTs ts b) (t_ts ts a) \<rbrakk> 
                                \<Longrightarrow> CState.i_var cs a < CState.l_var cs b"
          using sim unfolding Simulation_R_def Let_def by auto 

        have "CState.i_var cs p' < CState.l_var cs q'"
          apply (rule old_cond15)
          using pc_p_old pc_q_old not_less' ts_p_eq startTs_q_eq by auto
          
        thus ?thesis using i_p_eq l_q_eq by simp
      qed
    qed

    (* Cond 16.1 *)
    show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u_new: "c_program_counter cs' u = ''E2''"
      assume node_cond: "(nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP"

      have u_neq_p: "u \<noteq> p"
      proof
        assume "u = p"
        hence "c_program_counter cs' p = ''E2''" using pc_u_new by simp
        with cs'_eq show False by simp
      qed

      have pc_u_old: "c_program_counter cs u = ''E2''" 
        using pc_u_new u_neq_p cs'_eq by auto
      have i_var_eq: "CState.i_var cs' u = CState.i_var cs u" 
        using u_neq_p cs'_eq by simp
      
      have node_in_old: "(nid, v, ts_val) \<in> set (pools ts u)"
      proof (cases "u = u_tar")
        case True
        with node_cond ts'_def have "(nid, v, ts_val) \<in> set (remove1 (nid_tar, ?val, ts_tar) (pools ts u))" by simp
        thus ?thesis by (meson set_remove1_subset subsetD)
      next
        case False
        thus ?thesis using node_cond ts'_def by auto
      qed

      have old_rule: "\<And>u nid v ts_val. \<lbrakk> c_program_counter cs u = ''E2''; (nid, v, ts_val) \<in> set (pools ts u); ts_val \<noteq> TOP \<rbrakk> 
                       \<Longrightarrow> nid < CState.i_var cs u"
        using sim unfolding Simulation_R_def Let_def by (metis split_pairs2)

      show "nid < CState.i_var cs' u"
        using old_rule[OF pc_u_old node_in_old] node_cond i_var_eq by simp
    qed

    (* Cond 16.2 *)
    show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u_new: "c_program_counter cs' u = ''E3''"
      assume node_cond: "(nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP"

      have u_neq_p: "u \<noteq> p"
      proof
        assume "u = p"
        hence "c_program_counter cs' p = ''E3''" using pc_u_new by simp
        with cs'_eq show False by simp
      qed

      have pc_u_old: "c_program_counter cs u = ''E3''" 
        using pc_u_new u_neq_p cs'_eq by auto
      have i_var_eq: "CState.i_var cs' u = CState.i_var cs u" 
        using u_neq_p cs'_eq by simp
      
      have node_in_old: "(nid, v, ts_val) \<in> set (pools ts u)"
      proof (cases "u = u_tar")
        case True
        with node_cond ts'_def have "(nid, v, ts_val) \<in> set (remove1 (nid_tar, ?val, ts_tar) (pools ts u))" by simp
        thus ?thesis by (meson set_remove1_subset subsetD)
      next
        case False
        thus ?thesis using node_cond ts'_def by auto
      qed

      have old_rule: "\<And>u nid v ts_val. \<lbrakk> c_program_counter cs u = ''E3''; (nid, v, ts_val) \<in> set (pools ts u); ts_val \<noteq> TOP \<rbrakk> 
                       \<Longrightarrow> nid \<le> CState.i_var cs u"
        using sim unfolding Simulation_R_def Let_def by (metis split_pairs2) 

      show "nid \<le> CState.i_var cs' u"
        using old_rule[OF pc_u_old node_in_old] node_cond i_var_eq by simp
    qed

       (* Cond 16.3 *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
    proof (intro allI impI, elim conjE)
      fix u nid v ts_val 
      assume node_in_ts': "(nid, v, ts_val) \<in> set (pools ts' u)" and "ts_val \<noteq> TOP"

      have node_in_ts: "(nid, v, ts_val) \<in> set (pools ts u)"
      proof (cases "u = u_tar")
        case True
        with node_in_ts' ts'_def have "(nid, v, ts_val) \<in> set (remove1 (nid_tar, CState.Q_arr cs (CState.j_var cs p), ts_tar) (pools ts u))"
          by simp
        thus ?thesis by (meson set_remove1_subset subsetD)
      next
        case False
        with node_in_ts' ts'_def show ?thesis by simp
      qed

      from sim node_in_ts `ts_val \<noteq> TOP` have "\<exists>sn. EnqCallInHis (cs, us) u v sn"
        unfolding Simulation_R_def Let_def by blast

      thus "\<exists>sn. EnqCallInHis (cs', us) u v sn"
      proof -
        assume "\<exists>sn. EnqCallInHis (cs, us) u v sn"
        then obtain sn where his: "EnqCallInHis (cs, us) u v sn"
          by blast
        have "EnqCallInHis (cs', us) u v sn"
          using his cs'_eq unfolding EnqCallInHis_def his_seq_def by simp
        thus ?thesis by blast
      qed
    qed

    (* Cond 17 *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ts' q \<longrightarrow> 
               (\<exists>idx<CState.j_var cs' q. 
                    (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                    (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
    proof (intro allI impI)
      fix q v
      assume pc_q': "c_program_counter cs' q = ''D3''"
      assume scanned_new: "v \<in> t_scanned ts' q"

      have q_neq_p: "q \<noteq> p" using pc_q' cs'_eq pc by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q' q_neq_p cs'_eq by auto
      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_eq by simp
      have scanned_old: "v \<in> t_scanned ts q" using scanned_new q_neq_p ts'_def by auto

      have old_rule: "\<And>q. c_program_counter cs q = ''D3'' \<Longrightarrow> 
          (\<forall>v. v \<in> t_scanned ts q \<longrightarrow> 
               (\<exists>idx<CState.j_var cs q. 
                    (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
                    (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)))"
        using sim unfolding Simulation_R_def Let_def by simp

      from old_rule[OF pc_q_old] scanned_old
      obtain idx where idx_lt: "idx < CState.j_var cs q"
        and branches: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
                       (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        by blast

      show "\<exists>idx<CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
      proof (rule exI[where x=idx], rule conjI)
        show "idx < CState.j_var cs' q" using idx_lt j_q_eq by simp
      next
        from branches show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                            (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (elim disjE)
          assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
          have "v \<noteq> p" using b1 pc by auto
          thus ?thesis using b1 cs'_eq by auto
        next
          assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
          then obtain v_val sn where his: "EnqCallInHis (cs, us) v v_val sn" 
                              and inq: "InQBack (cs, us) v_val" 
                              and idx_eq: "Idx (cs, us) v_val = idx" by blast

          have inq_new: "InQBack (cs', us) v_val" 
          proof -
            from inq obtain k_pos where "Qback_arr (cs, us) k_pos = v_val" unfolding InQBack_def by blast
            moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos" using cs'_eq unfolding Qback_arr_def by simp
            ultimately show ?thesis unfolding InQBack_def by blast
          qed
            
          moreover have idx_new: "Idx (cs', us) v_val = idx" 
          proof -
            have "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
              using cs'_eq unfolding AtIdx_def Qback_arr_def by simp
            thus ?thesis using idx_eq unfolding Idx_def by presburger
          qed
            
          moreover have his_new: "EnqCallInHis (cs', us) v v_val sn" 
            using his cs'_eq unfolding EnqCallInHis_def his_seq_def by auto
            
          ultimately show ?thesis by blast
        qed
      qed
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>v \<in> t_scanned ts' q. \<forall>nid v_val ts_val.
         (nid, v_val, ts_val) \<in> set (pools ts' v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
         nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ts' q))"
    proof (intro allI impI ballI, elim conjE)
      fix q v nid v_val ts_val
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
         and v_scan_new: "v \<in> t_scanned ts' q"
         and node_in_new: "(nid, v_val, ts_val) \<in> set (pools ts' v)"
         and not_top: "ts_val \<noteq> TOP"

      (* Key proof idea. *)
      have q_neq_p: "q \<noteq> p" using pc_q_new cs'_eq pc by force

      (* Proof note. *)
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new cs'_eq q_neq_p by auto
      have v_scan_old: "v \<in> t_scanned ts q" using v_scan_new ts'_def q_neq_p by simp
      have node_in_old: "(nid, v_val, ts_val) \<in> set (pools ts v)"
        using node_in_new ts'_def by (cases "v = u_tar") (auto dest: set_remove1_subset[THEN subsetD])

      (* Proof note. *)
      have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
        using sim pc_q_old v_scan_old node_in_old not_top unfolding Simulation_R_def Let_def
        by auto 

      (* Proof note. *)
      have j_eq: "CState.j_var cs' q = CState.j_var cs q" using cs'_eq q_neq_p by simp
      have start_eq: "t_startTs ts' q = t_startTs ts q" using ts'_def q_neq_p by simp

      show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ts' q)"
        using old_cond18 j_eq start_eq by simp
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>u \<in> t_scanned ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
        CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ts' u) (t_startTs ts' q))"
    proof (intro allI impI ballI)
      fix q u
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume u_scan_new: "u \<in> t_scanned ts' q"
      assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"

      (* Key proof idea. *)
      have q_neq_p: "q \<noteq> p" using pc_q_new cs'_eq pc by force

      (* Proof note. *)
      have u_neq_p: "u \<noteq> p" using pc_u_new cs'_eq by force

      (* Proof note. *)
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new cs'_eq q_neq_p by auto
      have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new cs'_eq u_neq_p by auto
      
      have u_scan_old: "u \<in> t_scanned ts q" using u_scan_new ts'_def q_neq_p by simp
      
      (* Proof note. *)
      have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
        using sim pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def
        by (metis fst_conv)

      (* Proof note. *)
      have j_eq: "CState.j_var cs' q = CState.j_var cs q" using cs'_eq q_neq_p by simp
      have i_eq: "CState.i_var cs' u = CState.i_var cs u" using cs'_eq u_neq_p by simp
      have start_eq: "t_startTs ts' q = t_startTs ts q" using ts'_def q_neq_p by simp
      have ts_u_eq: "t_ts ts' u = t_ts ts u" using ts'_def u_neq_p by simp

      show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ts' u) (t_startTs ts' q)"
        using old_cond19 j_eq i_eq start_eq ts_u_eq by simp
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "CState.V_var cs' = t_V_var ts'" 
      using sim cs'_eq ts'_def unfolding Simulation_R_def Let_def by auto

    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ts' q" 
      using sim cs'_eq ts'_def unfolding Simulation_R_def Let_def by (auto split: if_splits)
  qed

  with ghost_step show ?thesis by blast
qed

end
