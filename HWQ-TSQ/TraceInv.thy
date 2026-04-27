theory TraceInv
   imports Main 
    TSQModel
    SimLemmas
    SimProof
    "../HWQ-U/SysInvProof"
begin

definition TE2_Pending_Order :: "TState \<Rightarrow> bool" where
  "TE2_Pending_Order ts \<equiv>
     (\<forall>p q nid v ts_val.
         t_pc ts p = ''TE2'' \<and>
         (nid, v, ts_val) \<in> set (pools ts q) \<and>
         ts_val \<noteq> TOP \<longrightarrow>
         (ts_val <\<^sub>t\<^sub>s t_ts ts p) = (nid < t_nid ts p)) \<and>
     (\<forall>p q.
         t_pc ts p = ''TE2'' \<and>
         t_pc ts q = ''TE2'' \<and>
         p \<noteq> q \<longrightarrow>
         (t_ts ts p <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts p < t_nid ts q))"

definition TSQ_State_Inv_Plus :: "TState \<Rightarrow> bool" where
  "TSQ_State_Inv_Plus ts \<equiv>
     TSQ_State_Inv ts \<and> TE2_Pending_Order ts"

lemma TSQ_State_Inv_PlusD_plain:
  assumes "TSQ_State_Inv_Plus ts"
  shows "TSQ_State_Inv ts"
  using assms unfolding TSQ_State_Inv_Plus_def by simp

lemma TSQ_State_Inv_PlusD_pending:                                  
  assumes "TSQ_State_Inv_Plus ts"
  shows "TE2_Pending_Order ts"
  using assms unfolding TSQ_State_Inv_Plus_def by simp

lemma TSQ_State_Inv_Init:
  assumes "T_Init ts"
  shows "TSQ_State_Inv ts"
  using assms
  unfolding T_Init_def TSQ_State_Inv_def BOT_def
  by auto

(* ========================================================== *)
(* Strengthened TSQ-side definitions                            *)
(* ========================================================== *)
lemma TSQ_State_Inv_Plus_Init:
  assumes "T_Init ts"
  shows "TSQ_State_Inv_Plus ts"
proof -
  have plain: "TSQ_State_Inv ts"
    using TSQ_State_Inv_Init assms by blast
  have pend: "TE2_Pending_Order ts"
    using assms unfolding T_Init_def TE2_Pending_Order_def by auto
  from plain pend show ?thesis
    unfolding TSQ_State_Inv_Plus_def by simp
qed

(* ========================================================== *)
(* Preservation of the strengthened TSQ invariants             *)
(* ========================================================== *)
lemma TSQ_State_Inv_Plus_Step:
  assumes inv: "TSQ_State_Inv_Plus ts"
      and step: "T_Next ts ts'"
  shows "TSQ_State_Inv_Plus ts'"
proof -
      have inv_plain: "TSQ_State_Inv ts"
    using TSQ_State_Inv_PlusD_plain assms(1) by blast

  have inv_pending:
    "TE2_Pending_Order ts"
    using TSQ_State_Inv_PlusD_pending assms(1) by blast
    (* ======================================================== *)
  (* Step 0: unpack the conjuncts of TSQ_State_Inv. *)
  (* A direct simp-based decomposition is more stable here than blast. *)
  (* ======================================================== *)
  have inv1:
    "\<forall>p q nid1 nid2 v1 v2 ts1 ts2.
        (nid1, v1, ts1) \<in> set (pools ts p) \<and> (nid2, v2, ts2) \<in> set (pools ts q) \<longrightarrow>
        (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> p = q \<and> ts1 = ts2)"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv2:
    "\<forall>p nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts p) \<and> ts_val \<noteq> TOP \<longrightarrow>
        ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
  proof -
    from inv_plain show ?thesis
      unfolding TSQ_State_Inv_def
      by (elim conjE) assumption
  qed

  have inv3:
    "\<forall>p. t_ts ts p \<noteq> TOP \<longrightarrow> t_ts ts p <\<^sub>t\<^sub>s TS (ts_counter ts)"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv4:
    "\<forall>q.
        t_pc ts q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
        t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv5:
    "\<forall>p.
        t_pc ts p = ''TE2'' \<longrightarrow>
        t_ts ts p \<noteq> TOP \<and>
        (\<exists>v. (t_nid ts p, v, TOP) \<in> set (pools ts p))"
    using inv_plain unfolding TSQ_State_Inv_def by simp

have inv6: 
  "\<forall>p.
      t_pc ts p = ''TE3'' \<longrightarrow>
      t_ts ts p \<noteq> TOP"
  using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv7:
    "\<forall>p. t_scanned ts p \<subseteq> ProcSet"
    using inv_plain unfolding TSQ_State_Inv_def by simp

have inv8:
  "\<forall>p q nid1 nid2 v1 v2 ts1 ts2.
      (nid1, v1, ts1) \<in> set (pools ts p) \<and>
      (nid2, v2, ts2) \<in> set (pools ts q) \<and>
      ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
      (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
  using inv_plain
  unfolding TSQ_State_Inv_def
  apply (elim conjE)
  apply assumption
  done

  have inv9:
    "BOT < t_V_var ts"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv10:
    "\<forall>p nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts p) \<longrightarrow>
        v < t_V_var ts"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv11:
    "\<forall>p nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts p) \<longrightarrow>
        nid < nid_counter ts"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv12:
    "\<forall>p nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts p) \<and> ts_val = TOP \<longrightarrow>
        t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv13:
    "\<forall>p q nid1 nid2 v1 v2 ts1 ts2.
        (nid1, v1, ts1) \<in> set (pools ts p) \<and>
        (nid2, v2, ts2) \<in> set (pools ts q) \<and>
        ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
        nid1 = nid2"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv14:
    "\<forall>p q nid v ts_val.
        t_pc ts p = ''TE2'' \<and>
        (nid, v, ts_val) \<in> set (pools ts q) \<and>
        ts_val \<noteq> TOP \<longrightarrow>
        t_ts ts p \<noteq> ts_val"
    using inv_plain
    unfolding TSQ_State_Inv_def
    by blast

  have inv15:
    "\<forall>p q.
        t_pc ts p = ''TE2'' \<and>
        t_pc ts q = ''TE2'' \<and>
        p \<noteq> q \<longrightarrow>
        t_ts ts p \<noteq> t_ts ts q"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv16:
    "\<forall>p. sorted (map fst (pools ts p)) \<and> distinct (map fst (pools ts p))"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv17:
    "\<forall>p.
        t_pc ts p = ''TE1'' \<longrightarrow>
        t_v ts p \<noteq> BOT \<and> t_v ts p < t_V_var ts"
    using inv_plain unfolding TSQ_State_Inv_def by simp

  have inv18:
    "\<forall>p q nid v ts_val.
        t_pc ts p = ''TE1'' \<and>
        (nid, v, ts_val) \<in> set (pools ts q) \<longrightarrow>
        t_v ts p \<noteq> v"
    using inv_plain
    unfolding TSQ_State_Inv_def
    by blast

  have inv19:
    "\<forall>p q.
        t_pc ts p = ''TE1'' \<and>
        t_pc ts q = ''TE1'' \<and>
        p \<noteq> q \<longrightarrow>
        t_v ts p \<noteq> t_v ts q"
    using inv_plain unfolding TSQ_State_Inv_def by simp

have inv20:
  "\<forall>p q nid v ts_val.
      t_pc ts p = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts p) = (nid < t_nid ts p)"
proof -
  have both:
    "(\<forall>p q nid v ts_val.
        t_pc ts p = ''TE2'' \<and>
        (nid, v, ts_val) \<in> set (pools ts q) \<and>
        ts_val \<noteq> TOP \<longrightarrow>
        (ts_val <\<^sub>t\<^sub>s t_ts ts p) = (nid < t_nid ts p)) \<and>
     (\<forall>p q.
        t_pc ts p = ''TE2'' \<and>
        t_pc ts q = ''TE2'' \<and>
        p \<noteq> q \<longrightarrow>
        (t_ts ts p <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts p < t_nid ts q))"
    using inv_pending unfolding TE2_Pending_Order_def by blast
  from conjunct1[OF both] show ?thesis .
qed

  have inv21:
    "\<forall>p q.
        t_pc ts p = ''TE2'' \<and>
        t_pc ts q = ''TE2'' \<and>
        p \<noteq> q \<longrightarrow>
        (t_ts ts p <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts p < t_nid ts q)"
    using inv_pending unfolding TE2_Pending_Order_def by simp
  (* ======================================================== *)
  (* Step 1: split T_Next into its process-indexed major cases. *)
  (* ======================================================== *)
  obtain p where p_in: "p \<in> ProcSet"
    and step_cases:
      "T_Call_Enq p ts ts' \<or>
       T_E1 p ts ts' \<or>
       T_E2 p ts ts' \<or>
       T_E3 p ts ts' \<or>
       T_Call_Deq p ts ts' \<or>
       T_D1 p ts ts' \<or>
       T_D2 p ts ts' \<or>
       T_D3 p ts ts' \<or>
       T_D4 p ts ts' \<or>
       ts' = ts"
    using step unfolding T_Next_def by blast

  from step_cases show ?thesis
  proof (elim disjE)

    (* ====================================================== *)
    (* Case 1: T_Call_Enq                                     *)
    (* ====================================================== *)
 assume h: "T_Call_Enq p ts ts'"
then have pc0: "t_pc ts p = ''TL0''"
  unfolding T_Call_Enq_def by simp
from h have ts'_def:
  "ts' =
    ts\<lparr>t_pc := (\<lambda>x. if x = p then ''TE1'' else t_pc ts x),
       t_V_var := t_V_var ts + 1,
       t_v := (\<lambda>x. if x = p then t_V_var ts else t_v ts x)\<rparr>"
  unfolding T_Call_Enq_def by simp

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
    show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
        (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
        (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
      using inv1 ts'_def by simp

    show "\<forall>pa nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
        ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
      using inv2 ts'_def by simp

    show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
      using inv3 ts'_def by simp

    show "\<forall>q.
        t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
        t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
      using inv4 ts'_def by simp

    show "\<forall>pa.
        t_pc ts' pa = ''TE2'' \<longrightarrow>
        t_ts ts' pa \<noteq> TOP \<and>
        (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
      using inv5 ts'_def by simp

    show "\<forall>pa.
      t_pc ts' pa = ''TE3'' \<longrightarrow>
      t_ts ts' pa \<noteq> TOP"
      using inv6 ts'_def by simp

    show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
      using inv7 ts'_def by simp

    show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
            ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
            (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      using inv8 ts'_def by simp

    show "BOT < t_V_var ts'"
      using inv9 ts'_def by simp

    show "\<forall>pa nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
        v < t_V_var ts'"
    proof (intro allI impI)
      fix pa nid v ts_val
      assume hin: "(nid, v, ts_val) \<in> set (pools ts' pa)"
      from ts'_def have pools_eq: "pools ts' pa = pools ts pa"
        by simp
      from hin have "(nid, v, ts_val) \<in> set (pools ts pa)"
        using pools_eq by simp
      then have "v < t_V_var ts"
        using inv10 by blast
      moreover from ts'_def have "t_V_var ts' = Suc (t_V_var ts)"
        by simp
      ultimately show "v < t_V_var ts'"
        by simp
    qed

    show "\<forall>pa nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
        nid < nid_counter ts'"
      using inv11 ts'_def by simp

    show "\<forall>pa nid v ts_val.
        (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
        t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
    proof (intro allI impI)
      fix pa nid v ts_val
      assume h:
        "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
      from h have hin': "(nid, v, ts_val) \<in> set (pools ts' pa)"
        by blast
      from h have htop: "ts_val = TOP"
        by simp
      have hin_top': "(nid, v, TOP) \<in> set (pools ts' pa)"
      proof -
        from hin' have "(nid, v, ts_val) \<in> set (pools ts' pa)" .
        also from htop have "(nid, v, ts_val) = (nid, v, TOP)"
          by simp
        finally show ?thesis .
      qed
      from ts'_def have pools_eq: "pools ts' pa = pools ts pa"
        by simp
      from hin_top' have hin_top: "(nid, v, TOP) \<in> set (pools ts pa)"
        using pools_eq by simp
      from hin_top have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
        using inv12 by blast
      then have old_pc: "t_pc ts pa = ''TE2''" and old_nid: "nid = t_nid ts pa"
        by simp_all
      have pa_neq: "pa \<noteq> p"
      proof
        assume eq: "pa = p"
        from old_pc eq have "t_pc ts p = ''TE2''"
          by simp
        with pc0 show False
          by simp
      qed
      hence "t_pc ts' pa = ''TE2''"
        using old_pc ts'_def by simp
      moreover from pa_neq ts'_def old_nid have "nid = t_nid ts' pa"
        by simp
      ultimately show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        by simp
    qed

    show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
        (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
        (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
        ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
        nid1 = nid2"
      using inv13 ts'_def by simp

    show "\<forall>pa q nid v ts_val.
        t_pc ts' pa = ''TE2'' \<and>
        (nid, v, ts_val) \<in> set (pools ts' q) \<and>
        ts_val \<noteq> TOP \<longrightarrow>
        t_ts ts' pa \<noteq> ts_val"
    proof (intro allI impI)
      fix pa q nid v ts_val
      assume h:
        "t_pc ts' pa = ''TE2'' \<and>
         (nid, v, ts_val) \<in> set (pools ts' q) \<and>
         ts_val \<noteq> TOP"
      then have hpc': "t_pc ts' pa = ''TE2''"
        by simp
      from h have hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
        by simp
      from h have hneq: "ts_val \<noteq> TOP"
        by simp
      from ts'_def have pools_eq: "pools ts' q = pools ts q"
        by simp
      from hin' have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
        using pools_eq by simp
      have pa_neq: "pa \<noteq> p"
      proof
        assume eq: "pa = p"
        from hpc' ts'_def eq have "''TE1'' = ''TE2''"
          by simp
        then show False
          by simp
      qed
      from hpc' pa_neq ts'_def have hpc: "t_pc ts pa = ''TE2''"
        by simp
      from hpc hin hneq have "t_ts ts pa \<noteq> ts_val"
        using inv14 by blast
      moreover from pa_neq ts'_def have "t_ts ts' pa = t_ts ts pa"
        by simp
      ultimately show "t_ts ts' pa \<noteq> ts_val"
        by simp
    qed

    show "\<forall>pa q.
        t_pc ts' pa = ''TE2'' \<and>
        t_pc ts' q = ''TE2'' \<and>
        pa \<noteq> q \<longrightarrow>
        t_ts ts' pa \<noteq> t_ts ts' q"
      using inv15 ts'_def by simp

    show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
      using inv16 ts'_def by simp

    show "\<forall>pa.
        t_pc ts' pa = ''TE1'' \<longrightarrow>
        t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
    proof (intro allI impI)
      fix pa
      assume hte1: "t_pc ts' pa = ''TE1''"
      show "t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
      proof (cases "pa = p")
        case True
        with ts'_def show ?thesis
          using inv9 by simp
      next
        case False
        with hte1 ts'_def have "t_pc ts pa = ''TE1''" by simp
        with inv17 have "t_v ts pa \<noteq> BOT \<and> t_v ts pa < t_V_var ts" by blast
        with False ts'_def show ?thesis by simp
      qed
    qed

    show "\<forall>pa q nid v ts_val.
        t_pc ts' pa = ''TE1'' \<and>
        (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
        t_v ts' pa \<noteq> v"
    proof (intro allI impI)
      fix pa q nid v ts_val
      assume hte1: "t_pc ts' pa = ''TE1'' \<and> (nid, v, ts_val) \<in> set (pools ts' q)"
      then have hpc: "t_pc ts' pa = ''TE1''" and hin: "(nid, v, ts_val) \<in> set (pools ts' q)" by simp_all
      show "t_v ts' pa \<noteq> v"
      proof (cases "pa = p")
        case True
        with ts'_def have "t_v ts' pa = t_V_var ts" by simp
        moreover from hin ts'_def have "(nid, v, ts_val) \<in> set (pools ts q)" by simp
        with inv10 have "v < t_V_var ts" by blast
        ultimately show ?thesis by simp
      next
        case False
        from hpc False ts'_def have hpc_old: "t_pc ts pa = ''TE1''"
          by simp
        from hin ts'_def have hin_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          by simp
        from hpc_old hin_old have "t_v ts pa \<noteq> v"
          using inv18 by blast
        moreover from False ts'_def have "t_v ts' pa = t_v ts pa"
          by simp
        ultimately show ?thesis
          by simp
      qed
    qed

    show "\<forall>pa q.
        t_pc ts' pa = ''TE1'' \<and>
        t_pc ts' q = ''TE1'' \<and>
        pa \<noteq> q \<longrightarrow>
        t_v ts' pa \<noteq> t_v ts' q"
    proof (intro allI impI)
      fix pa q
      assume hte1:
        "t_pc ts' pa = ''TE1'' \<and> t_pc ts' q = ''TE1'' \<and> pa \<noteq> q"
      then have hpa: "t_pc ts' pa = ''TE1''"
           and hq:  "t_pc ts' q = ''TE1''"
           and neq: "pa \<noteq> q" by simp_all
      show "t_v ts' pa \<noteq> t_v ts' q"
      proof (cases "pa = p \<or> q = p")
        case False
        from False hpa ts'_def have hpa_old: "t_pc ts pa = ''TE1''"
          by simp
        from False hq ts'_def have hq_old: "t_pc ts q = ''TE1''"
          by simp
        from hpa_old hq_old neq have "t_v ts pa \<noteq> t_v ts q"
          using inv19 by blast
        moreover from False ts'_def have "t_v ts' pa = t_v ts pa"
          by simp
        moreover from False ts'_def have "t_v ts' q = t_v ts q"
          by simp
        ultimately show ?thesis
          by simp
      next
        case True
        then show ?thesis
        proof
          assume "pa = p"
          then have paeq: "pa = p" .
          with neq have qneq: "q \<noteq> p" by simp
          from hq qneq ts'_def have "t_pc ts q = ''TE1''" by simp
          then have "t_v ts q < t_V_var ts"
            using inv17 by blast
          moreover from paeq ts'_def have "t_v ts' pa = t_V_var ts" by simp
          moreover from qneq ts'_def have "t_v ts' q = t_v ts q" by simp
          ultimately show ?thesis by simp
        next
          assume "q = p"
          then have qeq: "q = p" .
          with neq have pineq: "pa \<noteq> p" by simp
          from hpa pineq ts'_def have "t_pc ts pa = ''TE1''" by simp
          then have "t_v ts pa < t_V_var ts"
            using inv17 by blast
          moreover from qeq ts'_def have "t_v ts' q = t_V_var ts" by simp
          moreover from pineq ts'_def have "t_v ts' pa = t_v ts pa" by simp
          ultimately show ?thesis by simp
        qed
      qed
    qed
  qed

 show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    then have hpc': "t_pc ts' pa = ''TE2''"
      by simp
    from hpend have hmem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      by simp
    from hpend have hnz: "ts_val \<noteq> TOP"
      by simp

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpc' eq ts'_def show False
        by simp
    qed

    have hpc_old: "t_pc ts pa = ''TE2''"
      using hpc' pa_neq ts'_def by simp
    have hmem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
      using hmem' ts'_def by simp
    have tts_eq: "t_ts ts' pa = t_ts ts pa"
      using pa_neq ts'_def by simp
    have tnid_eq: "t_nid ts' pa = t_nid ts pa"
      using pa_neq ts'_def by simp

    have old_ord:
      "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
      using inv20 hpc_old hmem_old hnz by blast
    with tts_eq tnid_eq show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      by simp
  qed

  show "\<forall>pa q.
      t_pc ts' pa = ''TE2'' \<and>
      t_pc ts' q = ''TE2'' \<and>
      pa \<noteq> q \<longrightarrow>
      (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
  proof (intro allI impI)
    fix pa q
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       t_pc ts' q = ''TE2'' \<and>
       pa \<noteq> q"
    then have hpa': "t_pc ts' pa = ''TE2''"
      by simp
    from hpend have hq': "t_pc ts' q = ''TE2''"
      by simp
    from hpend have neq: "pa \<noteq> q"
      by simp

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpa' eq ts'_def show False
        by simp
    qed

    have q_neq: "q \<noteq> p"
    proof
      assume eq: "q = p"
      from hq' eq ts'_def show False
        by simp
    qed

    have hpa_old: "t_pc ts pa = ''TE2''"
      using hpa' pa_neq ts'_def by simp
    have hq_old: "t_pc ts q = ''TE2''"
      using hq' q_neq ts'_def by simp
    have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
      using pa_neq ts'_def by simp
    have tts_q_eq: "t_ts ts' q = t_ts ts q"
      using q_neq ts'_def by simp
    have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
      using pa_neq ts'_def by simp
    have tnid_q_eq: "t_nid ts' q = t_nid ts q"
      using q_neq ts'_def by simp

    have old_ord:
      "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
      using inv21 hpa_old hq_old neq by blast
    with tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
    show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      by simp
  qed
qed
qed



  next

    (* ====================================================== *)
    (* Case 2: T_E1                                           *)
    (* Append (new_nid, val, TOP) and move to TE2. *)
    (* ====================================================== *)
    assume h: "T_E1 p ts ts'"
    then have pc1: "t_pc ts p = ''TE1''"
      unfolding T_E1_def by simp
    from h have ts'_def:
      "ts' =
        ts\<lparr>nid_counter := Suc (nid_counter ts),
           ts_counter := Suc (ts_counter ts),
           t_nid := (\<lambda>x. if x = p then nid_counter ts else t_nid ts x),
           t_ts := (\<lambda>x. if x = p then TS (ts_counter ts) else t_ts ts x),
           pools := (\<lambda>x. if x = p then pools ts x @ [(nid_counter ts, t_v ts p, TOP)] else pools ts x),
           t_pc := (\<lambda>x. if x = p then ''TE2'' else t_pc ts x)\<rparr>"
      unfolding T_E1_def Let_def by simp

    have no_top_p:
      "\<forall>nid v. (nid, v, TOP) \<notin> set (pools ts p)"
    proof (intro allI)
      fix nid v
      show "(nid, v, TOP) \<notin> set (pools ts p)"
      proof
        assume hin: "(nid, v, TOP) \<in> set (pools ts p)"
        then have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts p)"
          by blast
        from inv12 hex have "t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
          by blast
        then have "t_pc ts p = ''TE2''"
          by simp
        with pc1 show False
          by simp
      qed
    qed

    show ?thesis
      unfolding TSQ_State_Inv_Plus_def
    proof
      show "TSQ_State_Inv ts'"
        unfolding TSQ_State_Inv_def
      proof (intro conjI)
               show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
          (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
      proof (intro allI impI)
        fix pa q nid1 nid2 v1 v2 ts1 ts2
        assume hmem:
          "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q)"
        then have in1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
          and in2': "(nid2, v2, ts2) \<in> set (pools ts' q)"
          by simp_all

        have old_rel:
          "\<And>r s a1 a2 b1 b2 c1 c2.
             (a1, b1, c1) \<in> set (pools ts r) \<Longrightarrow>
             (a2, b2, c2) \<in> set (pools ts s) \<Longrightarrow>
             (b1 = b2) = (a1 = a2) \<and> (a1 = a2 \<longrightarrow> r = s \<and> c1 = c2)"
          using inv1 by blast

        have old_val_neq:
          "\<And>r a b c. (a, b, c) \<in> set (pools ts r) \<Longrightarrow> b \<noteq> t_v ts p"
          using inv18 pc1 by blast

        have old_nid_lt:
          "\<And>r a b c. (a, b, c) \<in> set (pools ts r) \<Longrightarrow> a < nid_counter ts"
          using inv11 by blast

        show "(v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
        proof (cases "pa = p")
          case False
          have in1_old: "(nid1, v1, ts1) \<in> set (pools ts pa)"
            using in1' False ts'_def by simp
          show ?thesis
          proof (cases "q = p")
            case False
            have in2_old: "(nid2, v2, ts2) \<in> set (pools ts q)"
              using in2' False ts'_def by simp
            from old_rel[OF in1_old in2_old] show ?thesis
              by simp
          next
            case True
            have q_eq: "q = p"
              using True by simp
            have in2_cases:
              "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
               (nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
            proof -
              have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
              proof -
                from ts'_def have
                  "pools ts' q =
                     (if q = p then pools ts q @ [(nid_counter ts, t_v ts p, TOP)] else pools ts q)"
                  by simp
                also from q_eq have "... = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
                  by simp
                finally show ?thesis .
              qed
                from in2' have "(nid2, v2, ts2) \<in> set (pools ts' q)" .
                with pools_q have hmem_append:
                  "(nid2, v2, ts2) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
                  by simp
                have in2_cases:
                  "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
                   (nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
                proof -
                  from hmem_append show ?thesis
                  proof (induction "pools ts p")
                    case Nil
                    then show ?thesis by simp
                  next
                    case (Cons a xs)
                    then show ?thesis by auto
                  qed
                qed
              then have in2_cases:
                "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
                 (nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
                by simp
              then show ?thesis
                by simp
            qed
            from in2_cases show ?thesis
            proof
              assume in2_old: "(nid2, v2, ts2) \<in> set (pools ts p)"
              from old_rel[OF in1_old in2_old] have
                "(v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = p \<and> ts1 = ts2)"
                by simp
              thus ?thesis
                using q_eq by simp
            next
              assume new2: "(nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
              then have nid2_def: "nid2 = nid_counter ts"
                and v2_def: "v2 = t_v ts p"
                and ts2_def: "ts2 = TOP"
                by simp_all
              have v1_neq: "v1 \<noteq> t_v ts p"
                using old_val_neq[OF in1_old] by blast
              have nid1_neq: "nid1 \<noteq> nid_counter ts"
              proof
                assume eq: "nid1 = nid_counter ts"
                from old_nid_lt[OF in1_old] have "nid1 < nid_counter ts" .
                with eq show False by simp
              qed
              have "(v1 = v2) = (nid1 = nid2)"
                using v1_neq nid1_neq v2_def nid2_def by auto
              moreover have "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
                using nid1_neq nid2_def q_eq by auto
              ultimately show ?thesis
                by simp
            qed
          qed

        next
          case True
          have pa_eq: "pa = p"
            using True by simp
          have in1_cases:
            "(nid1, v1, ts1) \<in> set (pools ts p) \<or>
             (nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
          proof -
            have pools_pa: "pools ts' pa = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
            proof -
              from ts'_def have
                "pools ts' pa =
                   (if pa = p then pools ts pa @ [(nid_counter ts, t_v ts p, TOP)] else pools ts pa)"
                by simp
              also from pa_eq have "... = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
                by simp
              finally show ?thesis .
            qed
              from in1' have "(nid1, v1, ts1) \<in> set (pools ts' pa)" .
              with pools_pa have hmem_append:
                "(nid1, v1, ts1) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
                by simp
              have
                "(nid1, v1, ts1) \<in> set (pools ts p) \<or>
                 (nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
              proof -
                from hmem_append show ?thesis
                proof (induction "pools ts p")
                  case Nil
                  then show ?thesis by simp
                next
                  case (Cons a xs)
                  then show ?thesis by auto
                qed
              qed
            then show ?thesis
              by simp
          qed
          show ?thesis
          proof (cases "q = p")
            case False
            have in2_old: "(nid2, v2, ts2) \<in> set (pools ts q)"
              using in2' False ts'_def by simp
            from in1_cases show ?thesis
            proof
              assume in1_old: "(nid1, v1, ts1) \<in> set (pools ts p)"
              from old_rel[OF in1_old in2_old] have
                "(v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> p = q \<and> ts1 = ts2)"
                by simp
              thus ?thesis
                using pa_eq by simp
            next
              assume new1: "(nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
              then have nid1_def: "nid1 = nid_counter ts"
                and v1_def: "v1 = t_v ts p"
                and ts1_def: "ts1 = TOP"
                by simp_all
              have v2_neq: "v2 \<noteq> t_v ts p"
                using old_val_neq[OF in2_old] by blast
              have nid2_neq: "nid2 \<noteq> nid_counter ts"
              proof
                assume eq: "nid2 = nid_counter ts"
                from old_nid_lt[OF in2_old] have "nid2 < nid_counter ts" .
                with eq show False by simp
              qed
              have "(v1 = v2) = (nid1 = nid2)"
                using v2_neq nid2_neq v1_def nid1_def by auto
              moreover have "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
                using nid2_neq nid1_def pa_eq by auto
              ultimately show ?thesis
                by simp
            qed

          next
            case True
            have q_eq: "q = p"
              using True by simp
            have in2_cases:
              "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
               (nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
            proof -
              have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
              proof -
                from ts'_def have
                  "pools ts' q =
                     (if q = p then pools ts q @ [(nid_counter ts, t_v ts p, TOP)] else pools ts q)"
                  by simp
                also from q_eq have "... = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
                  by simp
                finally show ?thesis .
              qed
                  from in2' have "(nid2, v2, ts2) \<in> set (pools ts' q)" .
                  with pools_q have hmem_append:
                    "(nid2, v2, ts2) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
                    by simp
                  have in2_cases:
                    "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
                     (nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
                  proof -
                    from hmem_append show ?thesis
                    proof (induction "pools ts p")
                      case Nil
                      then show ?thesis by simp
                    next
                      case (Cons a xs)
                      then show ?thesis by auto
                    qed
                  qed
              then show ?thesis
                by simp
            qed
            from in1_cases show ?thesis
            proof
              assume in1_old: "(nid1, v1, ts1) \<in> set (pools ts p)"
              from in2_cases show ?thesis
              proof
                assume in2_old: "(nid2, v2, ts2) \<in> set (pools ts p)"
                from old_rel[OF in1_old in2_old] have
                  "(v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> p = p \<and> ts1 = ts2)"
                  by simp
                thus ?thesis
                  using pa_eq q_eq by simp
              next
                assume new2: "(nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
                then have nid2_def: "nid2 = nid_counter ts"
                  and v2_def: "v2 = t_v ts p"
                  and ts2_def: "ts2 = TOP"
                  by simp_all
                have v1_neq: "v1 \<noteq> t_v ts p"
                  using old_val_neq[OF in1_old] by blast
                have nid1_neq: "nid1 \<noteq> nid_counter ts"
                proof
                  assume eq: "nid1 = nid_counter ts"
                  from old_nid_lt[OF in1_old] have "nid1 < nid_counter ts" .
                  with eq show False by simp
                qed
                have "(v1 = v2) = (nid1 = nid2)"
                  using v1_neq nid1_neq v2_def nid2_def by auto
                moreover have "nid1 = nid2 \<longrightarrow> p = p \<and> ts1 = ts2"
                  using nid1_neq nid2_def by auto
                ultimately show ?thesis
                  using pa_eq q_eq by simp
              qed
            next
              assume new1: "(nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
              then have nid1_def: "nid1 = nid_counter ts"
                and v1_def: "v1 = t_v ts p"
                and ts1_def: "ts1 = TOP"
                by simp_all
              from in2_cases show ?thesis
              proof
                assume in2_old: "(nid2, v2, ts2) \<in> set (pools ts p)"
                have v2_neq: "v2 \<noteq> t_v ts p"
                  using old_val_neq[OF in2_old] by blast
                have nid2_neq: "nid2 \<noteq> nid_counter ts"
                proof
                  assume eq: "nid2 = nid_counter ts"
                  from old_nid_lt[OF in2_old] have "nid2 < nid_counter ts" .
                  with eq show False by simp
                qed
                have "(v1 = v2) = (nid1 = nid2)"
                  using v2_neq nid2_neq v1_def nid1_def by auto
                moreover have "nid1 = nid2 \<longrightarrow> p = p \<and> ts1 = ts2"
                  using nid2_neq nid1_def by auto
                ultimately show ?thesis
                  using pa_eq q_eq by simp
              next
                assume new2: "(nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
                then have nid2_def: "nid2 = nid_counter ts"
                  and v2_def: "v2 = t_v ts p"
                  and ts2_def: "ts2 = TOP"
                  by simp_all
                have "(v1 = v2) = (nid1 = nid2)"
                  using new1 new2 by simp
                moreover have "nid1 = nid2 \<longrightarrow> p = p \<and> ts1 = ts2"
                  using ts1_def ts2_def by simp
                ultimately show ?thesis
                  using pa_eq q_eq by simp
              qed
            qed
          qed
        qed
      qed

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
          ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume hmem: "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP"
        then have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
          and nz: "ts_val \<noteq> TOP"
          by simp_all
        show "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "pa = p")
          case False
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' False ts'_def by simp
          have old_bd: "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv2 mem nz by blast
          from old_bd ts'_def show ?thesis
            by (cases ts_val) simp_all
        next
          case True
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            using mem' True ts'_def by auto
          then show ?thesis
          proof
            assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
            have old_bd: "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
              using inv2 mem_old nz by blast
            from old_bd ts'_def show ?thesis
              by (cases ts_val) simp_all
          next
            assume newmem: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            with nz show ?thesis
              by simp
          qed
        qed
      qed

      show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix pa
        assume nz: "t_ts ts' pa \<noteq> TOP"
        show "t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "pa = p")
          case True
          with ts'_def show ?thesis
            by simp
        next
          case False
          have old_nz: "t_ts ts pa \<noteq> TOP"
            using False nz ts'_def by simp
          have old_bd: "t_ts ts pa <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv3 old_nz by blast
          from old_bd False ts'_def show ?thesis
            by (cases "t_ts ts pa") simp_all
        qed
      qed

      show "\<forall>q.
          t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
          t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix q
        assume hpc: "t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
        show "t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "q = p")
          case True
          with hpc ts'_def show ?thesis
            by simp
        next
          case False
          from False hpc ts'_def have hpc_old:
            "t_pc ts q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
            by simp
          have old_bd: "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv4 hpc_old by blast
          from old_bd False ts'_def show ?thesis
            by (cases "t_startTs ts q") simp_all
        qed
      qed

      show "\<forall>pa.
          t_pc ts' pa = ''TE2'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP \<and>
          (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
      proof (intro allI impI)
        fix pa
        assume hpc': "t_pc ts' pa = ''TE2''"
        show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
        proof (cases "pa = p")
          case True
          have tts_eq: "t_ts ts' pa = TS (ts_counter ts)"
            using True ts'_def by simp
          have tnid_eq: "t_nid ts' pa = nid_counter ts"
            using True ts'_def by simp
          have mem_new:
            "(nid_counter ts, t_v ts p, TOP) \<in> set (pools ts' pa)"
          proof -
            have pools_eq:
              "pools ts' pa = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
              using True ts'_def by simp
            then show ?thesis
              by simp
          qed
          have "\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa)"
          proof
            show "(t_nid ts' pa, t_v ts p, TOP) \<in> set (pools ts' pa)"
              using tnid_eq mem_new by simp
          qed
          with tts_eq show ?thesis
            by simp
        next
          case False
          have hpc: "t_pc ts pa = ''TE2''"
            using hpc' False ts'_def by simp
          from inv5 hpc have "t_ts ts pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts pa, v, TOP) \<in> set (pools ts pa))"
            by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

     show "\<forall>pa.
          t_pc ts' pa = ''TE3'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP"
      proof (intro allI impI)
        fix pa
        assume hpc': "t_pc ts' pa = ''TE3''"
        have "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TE2'' = ''TE3''"
            by simp
          then show False
            by simp
        qed
        then have hpc: "t_pc ts pa = ''TE3''"
          using hpc' ts'_def by simp
        from inv6 hpc have "t_ts ts pa \<noteq> TOP"
          by blast
        with `pa \<noteq> p` ts'_def show "t_ts ts' pa \<noteq> TOP"
          by simp
      qed

      show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
        using inv7 ts'_def by simp

      show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
          (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      proof (intro allI impI)
        fix pa qa nid1 nid2 v1 v2 ts1 ts2
        assume hmem:
          "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
           (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
           ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP"
        then have mem1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
          and mem2': "(nid2, v2, ts2) \<in> set (pools ts' qa)"
          and nz1: "ts1 \<noteq> TOP"
          and nz2: "ts2 \<noteq> TOP"
          by simp_all

        have old1: "(nid1, v1, ts1) \<in> set (pools ts pa)"
        proof (cases "pa = p")
          case False
          with mem1' ts'_def show ?thesis
            by simp
        next
          case True
          have mem_cases:
            "(nid1, v1, ts1) \<in> set (pools ts p) \<or>
             (nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
            using mem1' True ts'_def by auto
          then show ?thesis
         proof
            assume old1p: "(nid1, v1, ts1) \<in> set (pools ts p)"
            with True show ?thesis
              by simp
          next
            assume "(nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
            with nz1 show ?thesis
              by simp
          qed
        qed

        have old2: "(nid2, v2, ts2) \<in> set (pools ts qa)"
        proof (cases "qa = p")
          case False
          with mem2' ts'_def show ?thesis
            by simp
        next
          case True
          have mem_cases:
            "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
             (nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
            using mem2' True ts'_def by auto
          then show ?thesis
            proof
              assume old2p: "(nid2, v2, ts2) \<in> set (pools ts p)"
              with True show ?thesis
                by simp
            next
              assume "(nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
              with nz2 show ?thesis
                by simp
            qed
        qed

        from inv8 old1 old2 nz1 nz2
        show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
          by blast
      qed

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          nid < nid_counter ts'"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
        show "nid < nid_counter ts'"
        proof (cases "pa = p")
          case False
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' False ts'_def by simp
          have old_bd: "nid < nid_counter ts"
            using inv11 mem by blast
          from old_bd ts'_def show ?thesis
            by simp
        next
          case True
          have pools_pa: "pools ts' pa = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
            using True ts'_def by simp
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
          proof -
            from mem' pools_pa have hmem_append:
              "(nid, v, ts_val) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
              by simp
            from hmem_append show ?thesis
            proof (induction "pools ts p")
              case Nil
              then show ?thesis by simp
            next
              case (Cons a xs)
              then show ?thesis by auto
            qed
          qed
          then show ?thesis
          proof
            assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
            have old_bd: "nid < nid_counter ts"
              using inv11 mem_old by blast
            from old_bd ts'_def show ?thesis
              by simp
          next
            assume newmem: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            from newmem ts'_def show ?thesis
              by simp
          qed
        qed
      qed

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
          t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume htop: "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
        have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
          using htop by blast
        have ts_top: "ts_val = TOP"
          using htop by blast
        show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        proof (cases "pa = p")
          case True
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            using mem' True ts'_def by auto
          then show ?thesis
          proof
            assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
            from mem_old ts_top True have "(nid, v, TOP) \<in> set (pools ts p)"
              by simp
            with no_top_p show ?thesis
              by blast
          next
            assume newmem: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            with True ts'_def show ?thesis
              by simp
          qed
        next
          case False
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' False ts'_def by simp
          have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts pa)"
          proof -
            from mem ts_top have "(nid, v, TOP) \<in> set (pools ts pa)"
              by simp
            then show ?thesis
              by blast
          qed
          from inv12 hex have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
            by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

           show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
          nid1 = nid2"
      proof (intro allI impI)
        fix pa q nid1 nid2 v1 v2 ts1 ts2
        assume h:
          "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
           (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
           ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2"
        have in1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
          using h by blast
        have in2': "(nid2, v2, ts2) \<in> set (pools ts' q)"
          using h by blast
        have nz1: "ts1 \<noteq> TOP"
          using h by blast
        have nz2: "ts2 \<noteq> TOP"
          using h by blast
        have eqts: "ts1 = ts2"
          using h by blast

        have in1_old: "(nid1, v1, ts1) \<in> set (pools ts pa)"
        proof (cases "pa = p")
          case False
          then show ?thesis
            using in1' ts'_def by simp
        next
          case True
          have pools_pa: "pools ts' pa = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
            using True ts'_def by simp
          from in1' pools_pa have hmem_append:
            "(nid1, v1, ts1) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
            by simp
          have cases1:
            "(nid1, v1, ts1) \<in> set (pools ts p) \<or>
             (nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
          proof -
            from hmem_append show ?thesis
            proof (induction "pools ts p")
              case Nil
              then show ?thesis by simp
            next
              case (Cons a xs)
              then show ?thesis by auto
            qed
          qed
          from cases1 show ?thesis
            proof
              assume a: "(nid1, v1, ts1) \<in> set (pools ts p)"
              then show ?thesis
                using True by simp
            next
              assume b: "(nid1, v1, ts1) = (nid_counter ts, t_v ts p, TOP)"
              with nz1 show ?thesis
                by simp
            qed
        qed

        have in2_old: "(nid2, v2, ts2) \<in> set (pools ts q)"
        proof (cases "q = p")
          case False
          then show ?thesis
            using in2' ts'_def by simp
        next
          case True
          have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
            using True ts'_def by simp
          from in2' pools_q have hmem_append:
            "(nid2, v2, ts2) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
            by simp
          have cases2:
            "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
             (nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
          proof -
            from hmem_append show ?thesis
            proof (induction "pools ts p")
              case Nil
              then show ?thesis by simp
            next
              case (Cons a xs)
              then show ?thesis by auto
            qed
          qed
          from cases2 show ?thesis
              proof
                assume a: "(nid2, v2, ts2) \<in> set (pools ts p)"
                then show ?thesis
                  using True by simp
              next
                assume b: "(nid2, v2, ts2) = (nid_counter ts, t_v ts p, TOP)"
                with nz2 show ?thesis
                  by simp
              qed
        qed

        from inv13 in1_old in2_old nz1 nz2 eqts show "nid1 = nid2"
          by blast
      qed

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE2'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<and>
          ts_val \<noteq> TOP \<longrightarrow>
          t_ts ts' pa \<noteq> ts_val"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume h:
          "t_pc ts' pa = ''TE2'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q) \<and>
           ts_val \<noteq> TOP"
        have hpc': "t_pc ts' pa = ''TE2''"
          using h by blast
        have mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
          using h by blast
        have nz: "ts_val \<noteq> TOP"
          using h by blast
        show "t_ts ts' pa \<noteq> ts_val"
        proof (cases "pa = p")
          case True
          have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          proof (cases "q = p")
            case False
            then show ?thesis
              using mem' ts'_def by simp
          next
            case True
            have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
              using True ts'_def by simp
            from mem' pools_q have hmem_append:
              "(nid, v, ts_val) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
              by simp
            have casesq:
              "(nid, v, ts_val) \<in> set (pools ts p) \<or>
               (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            proof -
              from hmem_append show ?thesis
              proof (induction "pools ts p")
                case Nil
                then show ?thesis by simp
              next
                case (Cons a xs)
                then show ?thesis by auto
              qed
            qed
            from casesq show ?thesis
              proof
                assume a: "(nid, v, ts_val) \<in> set (pools ts p)"
                then show ?thesis
                  using True by simp
              next
                assume b: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
                with nz show ?thesis
                  by simp
              qed
          qed
          have old_bd: "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv2 mem_old nz by blast
          from True ts'_def old_bd show ?thesis
            by (cases ts_val) simp_all
        next
          case False
          have hpc0: "t_pc ts pa = ''TE2''"
            using hpc' False ts'_def by simp
          have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          proof (cases "q = p")
            case False
            then show ?thesis
              using mem' ts'_def by simp
          next
            case True
            have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
              using True ts'_def by simp
            from mem' pools_q have hmem_append:
              "(nid, v, ts_val) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
              by simp
            have casesq:
              "(nid, v, ts_val) \<in> set (pools ts p) \<or>
               (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            proof -
              from hmem_append show ?thesis
              proof (induction "pools ts p")
                case Nil
                then show ?thesis by simp
              next
                case (Cons a xs)
                then show ?thesis by auto
              qed
            qed
            from casesq show ?thesis
            proof
              assume a: "(nid, v, ts_val) \<in> set (pools ts p)"
              then show ?thesis
                using True by simp
            next
              assume b: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
              with nz show ?thesis
                by simp
            qed
          qed
          from inv14 hpc0 mem_old nz have "t_ts ts pa \<noteq> ts_val"
            by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE2'' \<and>
          t_pc ts' q = ''TE2'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_ts ts' pa \<noteq> t_ts ts' q"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE2'' \<and>
           t_pc ts' q = ''TE2'' \<and>
           pa \<noteq> q"
        have hpa': "t_pc ts' pa = ''TE2''"
          using h by blast
        have hq': "t_pc ts' q = ''TE2''"
          using h by blast
        have neq: "pa \<noteq> q"
          using h by blast
        show "t_ts ts' pa \<noteq> t_ts ts' q"
        proof (cases "pa = p")
          case True
          have q_neq: "q \<noteq> p"
            using True neq by simp
          have hq0: "t_pc ts q = ''TE2''"
            using hq' q_neq ts'_def by simp
          have old_bd: "t_ts ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv3 TSQ_State_InvD_TE2_not_top[OF inv_plain  hq0] by blast
          from True q_neq ts'_def old_bd show ?thesis
            by (cases "t_ts ts q") simp_all
        next
          case False
          show ?thesis
          proof (cases "q = p")
            case True
            have hpa0: "t_pc ts pa = ''TE2''"
              using hpa' False ts'_def by simp
            have old_bd: "t_ts ts pa <\<^sub>t\<^sub>s TS (ts_counter ts)"
              using inv3 TSQ_State_InvD_TE2_not_top[OF inv_plain hpa0] by blast
            from False True ts'_def old_bd show ?thesis
              by (cases "t_ts ts pa") simp_all
          next
            case False2: False
            have hpa0: "t_pc ts pa = ''TE2''"
              using hpa' False ts'_def by simp
            have hq0: "t_pc ts q = ''TE2''"
              using hq' False2 ts'_def by simp
            from inv15 hpa0 hq0 neq have "t_ts ts pa \<noteq> t_ts ts q"
              by blast
            with False False2 ts'_def show ?thesis
              by simp
          qed
        qed
      qed

      show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
      proof
        fix pa
        show "sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
        proof (cases "pa = p")
          case False
          then show ?thesis
            using inv16 ts'_def by simp
        next
          case True
          have sorted_old: "sorted (map fst (pools ts p))"
            using inv16 by blast
          have dist_old: "distinct (map fst (pools ts p))"
            using inv16 by blast

          have all_old_lt: "\<forall>x\<in>set (map fst (pools ts p)). x < nid_counter ts"
          proof
            fix x
            assume xin: "x \<in> set (map fst (pools ts p))"
            then obtain v0 t0 where node_in: "(x, v0, t0) \<in> set (pools ts p)"
              by auto
            from inv11 node_in show "x < nid_counter ts"
              by blast
          qed

          have sorted_append_last_nat:
            "\<And>l::nat list. sorted l \<Longrightarrow> (\<forall>x\<in>set l. x < nid_counter ts) \<Longrightarrow> sorted (l @ [nid_counter ts])"
          proof -
            fix l :: "nat list"
            assume s: "sorted l"
            assume ub: "\<forall>x\<in>set l. x < nid_counter ts"
            show "sorted (l @ [nid_counter ts])"
              using s ub
            proof (induction l)
              case Nil
              then show ?case
                by simp
            next
              case (Cons a l)
              have s_tail: "sorted l"
                using Cons.prems by simp
              have a_lt_new: "a < nid_counter ts"
                using Cons.prems by simp
              have ih: "sorted (l @ [nid_counter ts])"
                using Cons.IH s_tail Cons.prems by simp
              have a_le_all: "\<forall>y\<in>set (l @ [nid_counter ts]). a \<le> y"
              proof
                fix y
                assume yin: "y \<in> set (l @ [nid_counter ts])"
                show "a \<le> y"
                proof (cases "y = nid_counter ts")
                  case True
                  with a_lt_new show ?thesis
                    by simp
                next
                  case False
                  with yin have "y \<in> set l"
                    by auto
                  moreover have "\<forall>y\<in>set l. a \<le> y"
                    using Cons.prems by simp
                  ultimately show ?thesis
                    by blast
                qed
              qed
              from ih a_le_all show ?case
                by simp
            qed
          qed

          have fresh: "nid_counter ts \<notin> set (map fst (pools ts p))"
          proof
            assume hin: "nid_counter ts \<in> set (map fst (pools ts p))"
            from all_old_lt hin have "nid_counter ts < nid_counter ts"
              by blast
            then show False
              by simp
          qed

          have sorted_new:
            "sorted (map fst (pools ts p @ [(nid_counter ts, t_v ts p, TOP)]))"
          proof -
            have "sorted (map fst (pools ts p) @ [nid_counter ts])"
              using sorted_append_last_nat[OF sorted_old all_old_lt] .
            then show ?thesis
              by simp
          qed

          have dist_new:
            "distinct (map fst (pools ts p @ [(nid_counter ts, t_v ts p, TOP)]))"
          proof -
            have "distinct (map fst (pools ts p) @ [nid_counter ts])"
              using dist_old fresh by simp
            then show ?thesis
              by simp
          qed

          from sorted_new dist_new True ts'_def show ?thesis
            by simp
        qed
      qed


           show "\<forall>pa.
          t_pc ts' pa = ''TE1'' \<longrightarrow>
          t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
      proof (intro allI impI)
        fix pa
        assume hpc': "t_pc ts' pa = ''TE1''"
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TE2'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have hpc0: "t_pc ts pa = ''TE1''"
          using hpc' pa_neq ts'_def by simp
        have old_te1: "t_v ts pa \<noteq> BOT \<and> t_v ts pa < t_V_var ts"
          using inv17 hpc0 by blast
        have tv_eq: "t_v ts' pa = t_v ts pa"
          using pa_neq ts'_def by simp
        have tvv_eq: "t_V_var ts' = t_V_var ts"
          using ts'_def by simp
        from old_te1 tv_eq tvv_eq show "t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
          by simp
      qed

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE1'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
          t_v ts' pa \<noteq> v"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q)"
        have hpc': "t_pc ts' pa = ''TE1''"
          using h by blast
        have mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
          using h by blast
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TE2'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have hpc0: "t_pc ts pa = ''TE1''"
          using hpc' pa_neq ts'_def by simp
        have tv_eq: "t_v ts' pa = t_v ts pa"
          using pa_neq ts'_def by simp
        show "t_v ts' pa \<noteq> v"
        proof (cases "q = p")
          case False
          have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
            using mem' False ts'_def by simp
          have hex: "\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q)"
          proof
            show "(nid, v, ts_val) \<in> set (pools ts q)"
              using mem_old .
          qed
          have old_neq: "t_v ts pa \<noteq> v"
            using inv18 hpc0 hex by blast
          from old_neq tv_eq show ?thesis
            by simp
        next
          case True
          have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
            using True ts'_def by simp
          from mem' pools_q have hmem_append:
            "(nid, v, ts_val) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
            by simp
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
          proof -
            from hmem_append show ?thesis
            proof (induction "pools ts p")
              case Nil
              then show ?thesis by simp
            next
              case (Cons a xs)
              then show ?thesis by auto
            qed
          qed
          from mem_cases show ?thesis
          proof
            assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
            have hex: "\<exists>tsv. (nid, v, tsv) \<in> set (pools ts p)"
            proof
              show "(nid, v, ts_val) \<in> set (pools ts p)"
                using mem_old .
            qed
            have old_neq: "t_v ts pa \<noteq> v"
              using inv18 hpc0 hex by blast
            from old_neq tv_eq show ?thesis
              by simp
          next
            assume newmem: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            have old_neq: "t_v ts pa \<noteq> t_v ts p"
              using inv19 hpc0 pc1 pa_neq by blast
            from old_neq newmem tv_eq show ?thesis
              by simp
          qed
        qed
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE1'' \<and>
          t_pc ts' q = ''TE1'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_v ts' pa \<noteq> t_v ts' q"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           t_pc ts' q = ''TE1'' \<and>
           pa \<noteq> q"
        have hpa': "t_pc ts' pa = ''TE1''"
          using h by blast
        have hq': "t_pc ts' q = ''TE1''"
          using h by blast
        have neq: "pa \<noteq> q"
          using h by blast
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpa' eq ts'_def have "''TE2'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have q_neq: "q \<noteq> p"
        proof
          assume eq: "q = p"
          from hq' eq ts'_def have "''TE2'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have hpa0: "t_pc ts pa = ''TE1''"
          using hpa' pa_neq ts'_def by simp
        have hq0: "t_pc ts q = ''TE1''"
          using hq' q_neq ts'_def by simp
        have old_neq: "t_v ts pa \<noteq> t_v ts q"
          using inv19 hpa0 hq0 neq by blast
        have tv_pa_eq: "t_v ts' pa = t_v ts pa"
          using pa_neq ts'_def by simp
        have tv_q_eq: "t_v ts' q = t_v ts q"
          using q_neq ts'_def by simp
        from old_neq tv_pa_eq tv_q_eq show "t_v ts' pa \<noteq> t_v ts' q"
          by simp
      qed
      show "BOT < t_V_var ts'"
      proof -
        have "BOT < t_V_var ts"
          using inv9 by simp
        thus ?thesis
          using ts'_def by simp
      qed

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          v < t_V_var ts'"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
        show "v < t_V_var ts'"
        proof (cases "pa = p")
          case False
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' False ts'_def by simp
          have old_bd: "v < t_V_var ts"
            using inv10 mem by blast
          thus ?thesis
            using ts'_def by simp
        next
          case True
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            using mem' True ts'_def by auto
          then show ?thesis
          proof
            assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
            have old_bd: "v < t_V_var ts"
              using inv10 mem_old by blast
            thus ?thesis
              using ts'_def by simp
          next
            assume newmem: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            have tv_bd: "t_v ts p < t_V_var ts"
              using inv17 pc1 by blast
            from newmem tv_bd show ?thesis
              using ts'_def by simp
          qed
        qed

      qed
  qed

   show "TE2_Pending_Order ts'"
    unfolding TE2_Pending_Order_def
  proof (intro conjI)
    show "\<forall>pa q nid v ts_val.
        t_pc ts' pa = ''TE2'' \<and>
        (nid, v, ts_val) \<in> set (pools ts' q) \<and>
        ts_val \<noteq> TOP \<longrightarrow>
        (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
    proof (intro allI impI)
      fix pa q nid v ts_val
      assume hpend:
        "t_pc ts' pa = ''TE2'' \<and>
         (nid, v, ts_val) \<in> set (pools ts' q) \<and>
         ts_val \<noteq> TOP"
      have hpc': "t_pc ts' pa = ''TE2''"
        using hpend by blast
      have mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
        using hpend by blast
      have hnz: "ts_val \<noteq> TOP"
        using hpend by blast

      show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      proof (cases "pa = p")
        case True
        have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
        proof (cases "q = p")
          case False
          then show ?thesis
            using mem' ts'_def by simp
        next
          case True
          have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
            using True ts'_def by simp
          from mem' pools_q have hmem_append:
            "(nid, v, ts_val) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
            by simp
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
          proof -
            from hmem_append show ?thesis
            proof (induction "pools ts p")
              case Nil
              then show ?case by simp
            next
              case (Cons a xs)
              then show ?case by auto
            qed
          qed
          then show ?thesis
          proof
            assume mem_old_p: "(nid, v, ts_val) \<in> set (pools ts p)"
            then show ?thesis
              using True by simp
          next
            assume newmem: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            from newmem have "ts_val = TOP"
              by simp
            with hnz show ?thesis
              by simp
          qed
        qed

        have inv2_imp:
          "(nid, v, ts_val) \<in> set (pools ts q) \<and> ts_val \<noteq> TOP \<longrightarrow>
           ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
        proof -
          from inv2 have
            "\<forall>p nid v ts_val.
               (nid, v, ts_val) \<in> set (pools ts p) \<and> ts_val \<noteq> TOP \<longrightarrow>
               ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
            by blast
          then show ?thesis
            by blast
        qed
        have lhs_old: "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
          using inv2_imp mem_old hnz by blast

        have inv11_imp:
          "(nid, v, ts_val) \<in> set (pools ts q) \<longrightarrow> nid < nid_counter ts"
        proof -
          from inv11 have
            "\<forall>p nid v ts_val.
               (nid, v, ts_val) \<in> set (pools ts p) \<longrightarrow> nid < nid_counter ts"
            by blast
          then show ?thesis
            by blast
        qed
        have rhs_old: "nid < nid_counter ts"
          using inv11_imp mem_old by blast

        have tts_eq: "t_ts ts' pa = TS (ts_counter ts)"
          using True ts'_def by simp
        have tnid_eq: "t_nid ts' pa = nid_counter ts"
          using True ts'_def by simp

        from lhs_old rhs_old tts_eq tnid_eq
        show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
          by simp
      next
        case False
        have hpc_old: "t_pc ts pa = ''TE2''"
          using hpc' False ts'_def by simp

        have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
        proof (cases "q = p")
          case False
          then show ?thesis
            using mem' ts'_def by simp
        next
          case True
          have pools_q: "pools ts' q = pools ts p @ [(nid_counter ts, t_v ts p, TOP)]"
            using True ts'_def by simp
          from mem' pools_q have hmem_append:
            "(nid, v, ts_val) \<in> set (pools ts p @ [(nid_counter ts, t_v ts p, TOP)])"
            by simp
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
          proof -
            from hmem_append show ?thesis
            proof (induction "pools ts p")
              case Nil
              then show ?case by simp
            next
              case (Cons a xs)
              then show ?case by auto
            qed
          qed
          then show ?thesis
          proof
            assume mem_old_p: "(nid, v, ts_val) \<in> set (pools ts p)"
            then show ?thesis
              using True by simp
          next
            assume newmem: "(nid, v, ts_val) = (nid_counter ts, t_v ts p, TOP)"
            from newmem have "ts_val = TOP"
              by simp
            with hnz show ?thesis
              by simp
          qed
        qed

        have old_ord:
          "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
          using inv20 hpc_old mem_old hnz by blast

        have tts_eq: "t_ts ts' pa = t_ts ts pa"
          using False ts'_def by simp
        have tnid_eq: "t_nid ts' pa = t_nid ts pa"
          using False ts'_def by simp

        from old_ord tts_eq tnid_eq
        show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
          by simp
      qed
    qed

    show "\<forall>pa q.
        t_pc ts' pa = ''TE2'' \<and>
        t_pc ts' q = ''TE2'' \<and>
        pa \<noteq> q \<longrightarrow>
        (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
    proof (intro allI impI)
      fix pa q
      assume hpend:
        "t_pc ts' pa = ''TE2'' \<and>
         t_pc ts' q = ''TE2'' \<and>
         pa \<noteq> q"
      have hpa': "t_pc ts' pa = ''TE2''"
        using hpend by blast
      have hq': "t_pc ts' q = ''TE2''"
        using hpend by blast
      have neq: "pa \<noteq> q"
        using hpend by blast

      show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      proof (cases "pa = p")
        case True
        have q_neq: "q \<noteq> p"
          using True neq by simp
        have hq_old: "t_pc ts q = ''TE2''"
          using hq' q_neq ts'_def by simp
        have tts_pa: "t_ts ts' pa = TS (ts_counter ts)"
          using True ts'_def by simp
        have tnid_pa: "t_nid ts' pa = nid_counter ts"
          using True ts'_def by simp
        have tts_q: "t_ts ts' q = t_ts ts q"
          using q_neq ts'_def by simp
        have tnid_q: "t_nid ts' q = t_nid ts q"
          using q_neq ts'_def by simp

        have q_not_top: "t_ts ts q \<noteq> TOP"
          using TSQ_State_InvD_TE2_not_top[OF inv_plain hq_old] .
        have q_bd: "t_ts ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
          using inv3 q_not_top hq_old by blast
        have q_nid_bd: "t_nid ts q < nid_counter ts"
        proof -
          from inv5 hq_old obtain vv where "(t_nid ts q, vv, TOP) \<in> set (pools ts q)"
            by blast
          then show ?thesis
            using inv11 by blast
        qed

        from True tts_pa tnid_pa tts_q tnid_q q_bd q_nid_bd
        show ?thesis
          by (cases "t_ts ts q") simp_all
      next
        case False
        show ?thesis
        proof (cases "q = p")
          case True
          have pa_neq: "pa \<noteq> p"
            using False by simp
          have hpa_old: "t_pc ts pa = ''TE2''"
            using hpa' pa_neq ts'_def by simp
          have tts_q: "t_ts ts' q = TS (ts_counter ts)"
            using True ts'_def by simp
          have tnid_q: "t_nid ts' q = nid_counter ts"
            using True ts'_def by simp
          have tts_pa: "t_ts ts' pa = t_ts ts pa"
            using pa_neq ts'_def by simp
          have tnid_pa: "t_nid ts' pa = t_nid ts pa"
            using pa_neq ts'_def by simp

          have pa_not_top: "t_ts ts pa \<noteq> TOP"
            using TSQ_State_InvD_TE2_not_top[OF inv_plain hpa_old] .
          have pa_bd: "t_ts ts pa <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv3 pa_not_top hpa_old by blast
          have pa_nid_bd: "t_nid ts pa < nid_counter ts"
          proof -
            from inv5 hpa_old obtain vv where "(t_nid ts pa, vv, TOP) \<in> set (pools ts pa)"
              by blast
            then show ?thesis
              using inv11 by blast
          qed

          from True tts_q tnid_q tts_pa tnid_pa pa_bd pa_nid_bd
          show ?thesis
            by (cases "t_ts ts pa") simp_all
        next
          case False2: False
          have hpa_old: "t_pc ts pa = ''TE2''"
            using hpa' False ts'_def by simp
          have hq_old: "t_pc ts q = ''TE2''"
            using hq' False2 ts'_def by simp
          have old_ord:
            "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
            using inv21 hpa_old hq_old neq by blast
          have tts_pa: "t_ts ts' pa = t_ts ts pa"
            using False ts'_def by simp
          have tts_q: "t_ts ts' q = t_ts ts q"
            using False2 ts'_def by simp
          have tnid_pa: "t_nid ts' pa = t_nid ts pa"
            using False ts'_def by simp
          have tnid_q: "t_nid ts' q = t_nid ts q"
            using False2 ts'_def by simp
          from old_ord tts_pa tts_q tnid_pa tnid_q
          show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed




  next

    (* ====================================================== *)
    (* Case 3: T_E2                                           *)
    (* Replace the target TOP node by a real timestamp and move to TE3. *)
    (* ====================================================== *)
        assume h: "T_E2 p ts ts'"
    then have pc2: "t_pc ts p = ''TE2''"
      unfolding T_E2_def by simp
    from h have ts'_def:
      "ts' =
        ts\<lparr>pools := (\<lambda>x. if x = p then pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p) else pools ts x),
           t_pc := (\<lambda>x. if x = p then ''TE3'' else t_pc ts x)\<rparr>"
      unfolding T_E2_def by simp

    have tts_nonbot: "t_ts ts p \<noteq> TOP"
      using inv5 pc2 by blast

    have top_exists: "\<exists>v. (t_nid ts p, v, TOP) \<in> set (pools ts p)"
      using inv5 pc2 by blast

    have top_hit:
      "\<exists>v. (t_nid ts p, v, t_ts ts p) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
    proof -
      from top_exists obtain v where
        hv: "(t_nid ts p, v, TOP) \<in> set (pools ts p)"
        by blast
      hence "(t_nid ts p, v, t_ts ts p) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
        by simp
      then show ?thesis
        by blast
    qed

    have pool_other:
      "pa \<noteq> p \<Longrightarrow> pools ts' pa = pools ts pa"
      for pa
      using ts'_def by simp

    have pool_p:
      "pools ts' p = pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p)"
      using ts'_def by simp

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)

            show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
          (v1 = v2) = (nid1 = nid2) \<and>
          (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
      proof (intro allI impI)
        fix pa q nid1 nid2 v1 v2 ts1 ts2
        assume hmem:
          "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
           (nid2, v2, ts2) \<in> set (pools ts' q)"
        then have mem1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
          and mem2': "(nid2, v2, ts2) \<in> set (pools ts' q)"
          by simp_all

        have old_rel:
          "\<And>r s a1 a2 b1 b2 c1 c2.
             (a1, b1, c1) \<in> set (pools ts r) \<Longrightarrow>
             (a2, b2, c2) \<in> set (pools ts s) \<Longrightarrow>
             (b1 = b2) = (a1 = a2) \<and> (a1 = a2 \<longrightarrow> r = s \<and> c1 = c2)"
          using inv1 by blast

        show "(v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
        proof (cases "pa = p")
          case False
          have mem1_old: "(nid1, v1, ts1) \<in> set (pools ts pa)"
            using mem1' False ts'_def by simp
          show ?thesis
          proof (cases "q = p")
            case False
            have mem2_old: "(nid2, v2, ts2) \<in> set (pools ts q)"
              using mem2' False ts'_def by simp
            from old_rel[OF mem1_old mem2_old] show ?thesis
              by simp
          next
            case True
            have mem2_in_setTs:
              "(nid2, v2, ts2) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
              using mem2' True pool_p by simp
            
            have mem2_cases:
              "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
               (ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p) \<and> nid2 = t_nid ts p)"
              using mem2_in_setTs pool_setTs_set_cases by blast
            then show ?thesis
            proof
              assume mem2_old: "(nid2, v2, ts2) \<in> set (pools ts p)"
              from old_rel[OF mem1_old mem2_old] show ?thesis
                using True by simp
            next
              assume new2:
                "ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p) \<and> nid2 = t_nid ts p"
            from new2 obtain
              ts2eq: "ts2 = t_ts ts p" and
              top2_raw: "(nid2, v2, TOP) \<in> set (pools ts p)" and
              nid2eq: "nid2 = t_nid ts p"
              by blast
            
            have top2: "(t_nid ts p, v2, TOP) \<in> set (pools ts p)"
              using top2_raw nid2eq by simp
               have rel12_raw:
                "(v1 = v2) = (nid1 = t_nid ts p) \<and>
                 (nid1 = t_nid ts p \<longrightarrow> pa = p \<and> ts1 = TOP)"
                using old_rel[OF mem1_old top2] by blast
              
              have rel12:
                "(v1 = v2) = (nid1 = nid2) \<and>
                 (nid1 = nid2 \<longrightarrow> pa = p \<and> ts1 = TOP)"
                using rel12_raw nid2eq by simp
              have val_eq: "(v1 = v2) = (nid1 = nid2)"
                using rel12 by simp
              have eq_imp: "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
              proof
                assume eqn: "nid1 = nid2"
                from rel12 eqn have paq: "pa = p" and ts1_top: "ts1 = TOP"
                  by blast+
                from False paq have False
                  by simp
                then show "pa = q \<and> ts1 = ts2"
                  by blast
              qed
              from val_eq eq_imp show ?thesis
                by blast
            qed
          qed
         next
          case True
          have mem1_in_setTs:
            "(nid1, v1, ts1) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem1' True pool_p by simp

          have mem1_cases:
            "(nid1, v1, ts1) \<in> set (pools ts p) \<or>
             (ts1 = t_ts ts p \<and> (nid1, v1, TOP) \<in> set (pools ts p) \<and> nid1 = t_nid ts p)"
            using mem1_in_setTs pool_setTs_set_cases by blast

          show ?thesis
          proof (cases "q = p")
                       case False
            have mem2_old: "(nid2, v2, ts2) \<in> set (pools ts q)"
              using mem2' False ts'_def by simp
            from mem1_cases show ?thesis
                proof
              assume mem1_old: "(nid1, v1, ts1) \<in> set (pools ts p)"
              have val_eq: "(v1 = v2) = (nid1 = nid2)"
                using inv1 mem1_old mem2_old by blast
              have eq_imp: "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
              proof
                assume eqn: "nid1 = nid2"
                from inv1 mem1_old mem2_old eqn have pq: "p = q" and ts_eq: "ts1 = ts2"
                  by blast+
                from True have "pa = p"
                  by simp
                with pq ts_eq show "pa = q \<and> ts1 = ts2"
                  by simp
              qed
              from val_eq eq_imp show ?thesis
                by blast
            next
              assume new1:
                "ts1 = t_ts ts p \<and> (nid1, v1, TOP) \<in> set (pools ts p) \<and> nid1 = t_nid ts p"

              from new1 obtain
                ts1eq: "ts1 = t_ts ts p" and
                top1_raw: "(nid1, v1, TOP) \<in> set (pools ts p)" and
                nid1eq: "nid1 = t_nid ts p"
                by blast

              have top1: "(t_nid ts p, v1, TOP) \<in> set (pools ts p)"
                using top1_raw nid1eq by simp

              have val_eq_raw: "(v1 = v2) = (t_nid ts p = nid2)"
                using inv1 top1 mem2_old by blast

              have val_eq: "(v1 = v2) = (nid1 = nid2)"
                using val_eq_raw nid1eq by simp

              have eq_imp: "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
              proof
                assume eqn: "nid1 = nid2"
                from inv1 top1 mem2_old have
                  "t_nid ts p = nid2 \<longrightarrow> p = q \<and> TOP = ts2"
                  by blast
                moreover from eqn nid1eq have "t_nid ts p = nid2"
                  by simp
                ultimately have pq: "p = q" and ts2_top: "ts2 = TOP"
                  by blast+
                from False pq have False
                  by simp
                then show "pa = q \<and> ts1 = ts2"
                  by blast
              qed

              from val_eq eq_imp show ?thesis
                by blast
            qed
                  next
            case True
            have paeq: "pa = p"
              using \<open>pa = p\<close> by simp
            have qeq: "q = p"
              using True by simp

            have mem2_in_setTs:
              "(nid2, v2, ts2) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
              using mem2' qeq pool_p by simp

            have mem2_cases:
              "(nid2, v2, ts2) \<in> set (pools ts p) \<or>
               (ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p) \<and> nid2 = t_nid ts p)"
              using mem2_in_setTs pool_setTs_set_cases by blast

            have branch_goal:
              "(v1 = v2) = (nid1 = nid2) \<and>
               (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
            proof -
              from mem1_cases consider
                (old1) "(nid1, v1, ts1) \<in> set (pools ts p)" |
                (new1) "ts1 = t_ts ts p \<and> (nid1, v1, TOP) \<in> set (pools ts p) \<and> nid1 = t_nid ts p"
                by blast
              then show ?thesis
              proof cases
                case old1
                from mem2_cases consider
                  (old2) "(nid2, v2, ts2) \<in> set (pools ts p)" |
                  (new2) "ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p) \<and> nid2 = t_nid ts p"
                  by blast
                then show ?thesis
                proof cases
                  case old2
                  have val_eq: "(v1 = v2) = (nid1 = nid2)"
                    using inv1 old1 old2 by blast
                  have eq_imp: "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
                  proof
                    assume eqn: "nid1 = nid2"
                    from eqn inv1 old1 old2 have "ts1 = ts2"
                      by blast
                    with paeq qeq show "pa = q \<and> ts1 = ts2"
                      by simp
                  qed
                  from val_eq eq_imp show ?thesis
                    by blast
                next
                  case new2
                  from new2 obtain
                    ts2eq: "ts2 = t_ts ts p" and
                    top2_raw: "(nid2, v2, TOP) \<in> set (pools ts p)" and
                    nid2eq: "nid2 = t_nid ts p"
                    by blast

                  have top2: "(t_nid ts p, v2, TOP) \<in> set (pools ts p)"
                    using top2_raw nid2eq by simp

                  have rel12_raw:
                    "(v1 = v2) = (nid1 = t_nid ts p) \<and>
                     (nid1 = t_nid ts p \<longrightarrow> p = p \<and> ts1 = TOP)"
                    using inv1 old1 top2 by blast

                  have rel12:
                    "(v1 = v2) = (nid1 = nid2) \<and>
                     (nid1 = nid2 \<longrightarrow> p = p \<and> ts1 = TOP)"
                    using rel12_raw nid2eq by simp

                  have val_eq: "(v1 = v2) = (nid1 = nid2)"
                    using rel12 by simp

                  have eq_imp: "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
                  proof
                    assume eqn: "nid1 = nid2"
                    from rel12 eqn have ts1_top: "ts1 = TOP"
                      by blast
                    have mem1_top_new:
                      "(t_nid ts p, v1, TOP) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
                      using mem1' paeq eqn nid2eq ts1_top ts'_def by simp
                    have "fst (t_nid ts p, v1, TOP) \<noteq> t_nid ts p"
                      using tts_nonbot mem1_top_new
                      by (rule pool_setTs_clears_TOP, simp_all)
                    then have False
                      by simp
                    then show "pa = q \<and> ts1 = ts2"
                      by blast
                  qed

                  from val_eq eq_imp show ?thesis
                    by blast
                qed
              next
                case new1
                from new1 obtain
                  ts1eq: "ts1 = t_ts ts p" and
                  top1_raw: "(nid1, v1, TOP) \<in> set (pools ts p)" and
                  nid1eq: "nid1 = t_nid ts p"
                  by blast

                have top1: "(t_nid ts p, v1, TOP) \<in> set (pools ts p)"
                  using top1_raw nid1eq by simp

                from mem2_cases consider
                  (old2) "(nid2, v2, ts2) \<in> set (pools ts p)" |
                  (new2) "ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p) \<and> nid2 = t_nid ts p"
                  by blast
                then show ?thesis
                proof cases
                  case old2
                  have rel12_raw:
                    "(v1 = v2) = (t_nid ts p = nid2) \<and>
                     (t_nid ts p = nid2 \<longrightarrow> p = p \<and> TOP = ts2)"
                    using inv1 top1 old2 by blast

                  have rel12:
                    "(v1 = v2) = (nid1 = nid2) \<and>
                     (nid1 = nid2 \<longrightarrow> p = p \<and> TOP = ts2)"
                    using rel12_raw nid1eq by simp

                  have val_eq: "(v1 = v2) = (nid1 = nid2)"
                    using rel12 by simp

                  have eq_imp: "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
                  proof
                    assume eqn: "nid1 = nid2"
                    from rel12 eqn have ts2_top: "ts2 = TOP"
                      by blast
                    have mem2_top_new:
                      "(t_nid ts p, v2, TOP) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
                      using mem2' qeq eqn nid1eq ts2_top ts'_def by simp
                    have "fst (t_nid ts p, v2, TOP) \<noteq> t_nid ts p"
                      using tts_nonbot mem2_top_new
                      by (rule pool_setTs_clears_TOP, simp_all)
                    then have False
                      by simp
                    then show "pa = q \<and> ts1 = ts2"
                      by blast
                  qed

                  from val_eq eq_imp show ?thesis
                    by blast
                next
                  case new2
                  from new2 obtain
                    ts2eq: "ts2 = t_ts ts p" and
                    top2_raw: "(nid2, v2, TOP) \<in> set (pools ts p)" and
                    nid2eq: "nid2 = t_nid ts p"
                    by blast

                  have top2: "(t_nid ts p, v2, TOP) \<in> set (pools ts p)"
                    using top2_raw nid2eq by simp

                  have val_eq_raw:
                    "(v1 = v2) = (t_nid ts p = t_nid ts p)"
                    using inv1 top1 top2 by blast

                  have val_eq: "(v1 = v2) = (nid1 = nid2)"
                    using val_eq_raw nid1eq nid2eq by simp

                  have eq_imp: "nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2"
                  proof
                    assume "nid1 = nid2"
                    from paeq qeq ts1eq ts2eq show "pa = q \<and> ts1 = ts2"
                      by simp
                  qed

                  from val_eq eq_imp show ?thesis
                    by blast
                qed
              qed
            qed

            from branch_goal show ?thesis
              by blast
          qed
        qed
      qed

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
          ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume hmem: "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP"
        then have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)" and nz: "ts_val \<noteq> TOP"
          by simp_all
        show "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "pa = p")
          case False
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' False ts'_def by simp
        from inv2 mem nz show ?thesis
          using ts'_def by simp
        next
          case True
          have mem_in_setTs:
            "(nid, v, ts_val) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem' True pool_p by simp
        
          have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p))"
            using mem_in_setTs in_set_pool_setTs by blast
        
          then show ?thesis
          proof
            assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
            from inv2 mem_old nz show ?thesis
              using ts'_def by simp
          next
            assume newmem: "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p)"
            then have "ts_val = t_ts ts p"
              by simp
            moreover have "t_ts ts p <\<^sub>t\<^sub>s TS (ts_counter ts)"
              using inv3 tts_nonbot by blast
            ultimately show ?thesis
              using ts'_def by simp
          qed
        qed
      qed

      show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv3 ts'_def by simp

      show "\<forall>q.
          t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
          t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv4 ts'_def by simp

      show "\<forall>pa.
          t_pc ts' pa = ''TE2'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP \<and>
          (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
      proof (intro allI impI)
        fix pa
        assume hpc: "t_pc ts' pa = ''TE2''"
        from ts'_def hpc have "pa \<noteq> p" and oldpc: "t_pc ts pa = ''TE2''"
          by (auto split: if_splits)
        from inv5 oldpc have "t_ts ts pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts pa, v, TOP) \<in> set (pools ts pa))"
          by blast
        with `pa \<noteq> p` ts'_def show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
          by simp
      qed

      show "\<forall>pa.
          t_pc ts' pa = ''TE3'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP"
      proof (intro allI impI)
        fix pa
        assume hpc: "t_pc ts' pa = ''TE3''"
        show "t_ts ts' pa \<noteq> TOP"
        proof (cases "pa = p")
          case True
          with ts'_def show ?thesis
            using tts_nonbot by simp
        next
          case False
          have oldpc: "t_pc ts pa = ''TE3''"
            using hpc False ts'_def by simp
          from inv6 oldpc have "t_ts ts pa \<noteq> TOP"
            by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
        using inv7 ts'_def by simp

           show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
          (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      proof (intro allI impI)
        fix pa qa nid1 nid2 v1 v2 ts1 ts2
        assume hmem:
          "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
           (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
           ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP"
        then have mem1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
          and mem2': "(nid2, v2, ts2) \<in> set (pools ts' qa)"
          and nz1: "ts1 \<noteq> TOP" and nz2: "ts2 \<noteq> TOP"
          by simp_all

        have old1:
          "(nid1, v1, ts1) \<in> set (pools ts pa) \<or>
           (pa = p \<and> nid1 = t_nid ts p \<and> ts1 = t_ts ts p \<and> (nid1, v1, TOP) \<in> set (pools ts p))"
        proof (cases "pa = p")
          case False
          with mem1' ts'_def show ?thesis
            by simp
        next
          case True
          have mem1_in:
            "(nid1, v1, ts1) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem1' True pool_p by simp
          from mem1_in nz1 show ?thesis
            using True in_set_pool_setTs by blast
        qed

        have old2:
          "(nid2, v2, ts2) \<in> set (pools ts qa) \<or>
           (qa = p \<and> nid2 = t_nid ts p \<and> ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p))"
        proof (cases "qa = p")
          case False
          with mem2' ts'_def show ?thesis
            by simp
        next
          case True
          have mem2_in:
            "(nid2, v2, ts2) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem2' True pool_p by simp
          from mem2_in nz2 show ?thesis
            using True in_set_pool_setTs by blast
        qed
(* ---------------------------------------------------------- *)
(* Pending-order obligations for the TE2 update case           *)
(* ---------------------------------------------------------- *)
have pending_order:
  "\<And>q nid v ts_val.
     (nid, v, ts_val) \<in> set (pools ts q) \<Longrightarrow>
     ts_val \<noteq> TOP \<Longrightarrow>
     (ts_val <\<^sub>t\<^sub>s t_ts ts p) = (nid < t_nid ts p)"
proof -
  fix q nid v ts_val
  assume hmem: "(nid, v, ts_val) \<in> set (pools ts q)"
  assume hnz: "ts_val \<noteq> TOP"
  from inv20 pc2 hmem hnz
  show "(ts_val <\<^sub>t\<^sub>s t_ts ts p) = (nid < t_nid ts p)"
    by blast
qed
(* Final comparison subgoal for the TE2-order argument. *)
from old1 show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
proof
  assume old1_old: "(nid1, v1, ts1) \<in> set (pools ts pa)"
  from old2 show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
  proof
    assume old2_old: "(nid2, v2, ts2) \<in> set (pools ts qa)"
    have old_ord:
      "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      using TSQ_State_InvD_pool_ts_order[OF inv_plain old1_old old2_old nz1 nz2] .
    then show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      by simp
  next
    assume old2_new:
      "qa = p \<and> nid2 = t_nid ts p \<and> ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p)"
    from old2_new have nid2eq: "nid2 = t_nid ts p"
      by blast
    from old2_new have ts2eq: "ts2 = t_ts ts p"
      by blast
    have ord1:
      "(ts1 <\<^sub>t\<^sub>s t_ts ts p) = (nid1 < t_nid ts p)"
      using pending_order[OF old1_old nz1] .
    from ord1 nid2eq ts2eq show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      by simp
  qed
next
  assume old1_new:
    "pa = p \<and> nid1 = t_nid ts p \<and> ts1 = t_ts ts p \<and> (nid1, v1, TOP) \<in> set (pools ts p)"
  from old1_new have nid1eq: "nid1 = t_nid ts p"
    by blast
  from old1_new have ts1eq: "ts1 = t_ts ts p"
    by blast

  from old2 show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
  proof
    assume old2_old: "(nid2, v2, ts2) \<in> set (pools ts qa)"

    have ord2:
      "(ts2 <\<^sub>t\<^sub>s t_ts ts p) = (nid2 < t_nid ts p)"
      using pending_order[OF old2_old nz2] .

    have inv14_imp:
      "t_pc ts p = ''TE2'' \<and>
       (nid2, v2, ts2) \<in> set (pools ts qa) \<and>
       ts2 \<noteq> TOP \<longrightarrow>
       t_ts ts p \<noteq> ts2"
    proof -
      from inv14 have
        "\<forall>q nid v ts_val.
           t_pc ts p = ''TE2'' \<and>
           (nid, v, ts_val) \<in> set (pools ts q) \<and>
           ts_val \<noteq> TOP \<longrightarrow>
           t_ts ts p \<noteq> ts_val"
        by blast
      then show ?thesis
        by blast
    qed

    have neq_ts: "t_ts ts p \<noteq> ts2"
      using inv14_imp pc2 old2_old nz2 by blast

    have top_wit: "\<exists>v0. (t_nid ts p, v0, TOP) \<in> set (pools ts p)"
      using inv5 pc2 by blast

    have nid2_neq: "nid2 \<noteq> t_nid ts p"
    proof
      assume nid2eq: "nid2 = t_nid ts p"
      from top_wit obtain v0 where topmem:
        "(t_nid ts p, v0, TOP) \<in> set (pools ts p)"
        by blast
have inv1_imp:
  "(nid2, v2, ts2) \<in> set (pools ts qa) \<and>
   (t_nid ts p, v0, TOP) \<in> set (pools ts p) \<longrightarrow>
   (v2 = v0) = (nid2 = t_nid ts p) \<and>
   (nid2 = t_nid ts p \<longrightarrow> qa = p \<and> ts2 = TOP)"
proof -
  from inv1 have
    "\<forall>q nid1 nid2 v1 v2 ts1 ts2.
       (nid1, v1, ts1) \<in> set (pools ts qa) \<and>
       (nid2, v2, ts2) \<in> set (pools ts q) \<longrightarrow>
       (v1 = v2) = (nid1 = nid2) \<and>
       (nid1 = nid2 \<longrightarrow> qa = q \<and> ts1 = ts2)"
    by blast
  then show ?thesis
    by blast
qed
have same_nid_imp:
  "nid2 = t_nid ts p \<longrightarrow> qa = p \<and> ts2 = TOP"
  using inv1_imp old2_old topmem by blast
from same_nid_imp nid2eq have ts2_top: "ts2 = TOP"
  by blast
      with nz2 show False
        by simp
    qed

    have ord2':
      "(t_ts ts p <\<^sub>t\<^sub>s ts2) = (t_nid ts p < nid2)"
    proof (cases ts2)
      case TOP
      with nz2 show ?thesis
        by simp
    next
      case (TS k2)
      note ts2_TS = TS
      show ?thesis
      proof (cases "t_ts ts p")
        case TOP
        with tts_nonbot show ?thesis
          by simp
      next
        case (TS kp)
        note tts_TS = TS
        have lt_eq: "(k2 < kp) = (nid2 < t_nid ts p)"
          using ord2 ts2_TS tts_TS by simp
        have neq_nat: "kp \<noteq> k2"
          using neq_ts ts2_TS tts_TS by simp
        show ?thesis
        proof (cases "kp < k2")
          case True
          have lhs: "t_ts ts p <\<^sub>t\<^sub>s ts2"
            using True ts2_TS tts_TS by simp
          have not_k2_lt: "\<not> k2 < kp"
            using True by arith
          have not_nid2_lt: "\<not> nid2 < t_nid ts p"
          proof
            assume nid2_lt: "nid2 < t_nid ts p"
            from lt_eq nid2_lt have "k2 < kp"
              by simp
            with not_k2_lt show False
              by simp
          qed
          have rhs: "t_nid ts p < nid2"
            using not_nid2_lt nid2_neq by arith
          from lhs rhs show ?thesis
            by simp
        next
          case False
          have k2_lt: "k2 < kp"
            using False neq_nat by arith
          have nid2_lt: "nid2 < t_nid ts p"
            using lt_eq k2_lt by simp
          have not_lhs: "\<not> (t_ts ts p <\<^sub>t\<^sub>s ts2)"
          proof
            assume lhs: "t_ts ts p <\<^sub>t\<^sub>s ts2"
            from lhs False ts2_TS tts_TS show False
              by simp
          qed
          have not_rhs: "\<not> (t_nid ts p < nid2)"
            using nid2_lt by simp
          from not_lhs not_rhs show ?thesis
            by simp
        qed
      qed
    qed

    from ord2' nid1eq ts1eq show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      by simp
  next
    assume old2_new:
      "qa = p \<and> nid2 = t_nid ts p \<and> ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p)"
    from old2_new have nid2eq: "nid2 = t_nid ts p"
      by blast
    from old2_new have ts2eq: "ts2 = t_ts ts p"
      by blast
    have not_ts_less: "\<not> (ts1 <\<^sub>t\<^sub>s ts2)"
    proof
      assume hlt: "ts1 <\<^sub>t\<^sub>s ts2"
      from tts_nonbot obtain k where tts_TS: "t_ts ts p = TS k"
        by (cases "t_ts ts p") auto
      from ts1eq ts2eq tts_TS hlt show False
        by simp
    qed
    have not_nid_less: "\<not> (nid1 < nid2)"
    proof
      assume hlt: "nid1 < nid2"
      from nid1eq nid2eq hlt show False
        by simp
    qed
    from not_ts_less not_nid_less show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
      by simp
  qed
qed
 qed
(* Remaining local proof obligations for the current case. *)
      show "BOT < t_V_var ts'"
        using inv9 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          v < t_V_var ts'"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
        show "v < t_V_var ts'"
            proof (cases "pa = p")
              case False
              have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
                using mem' False ts'_def by simp
            have old_bd_imp:
              "(nid, v, ts_val) \<in> set (pools ts pa) \<longrightarrow> v < t_V_var ts"
              using inv10 by blast
            have old_bd: "v < t_V_var ts"
              using old_bd_imp mem by blast
              then show ?thesis
                using ts'_def by simp
            next
          case True
          have mem_in:
            "(nid, v, ts_val) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem' True pool_p by simp
          then have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p))"
            using in_set_pool_setTs by blast
          then show ?thesis
            proof
              assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
              have old_bd_imp:
                "(nid, v, ts_val) \<in> set (pools ts p) \<longrightarrow> v < t_V_var ts"
                using inv10 by blast
              have old_bd: "v < t_V_var ts"
                using old_bd_imp mem_old by blast
              then show ?thesis
                using ts'_def by simp
            next
              assume newmem: "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p)"
              then have topmem: "(t_nid ts p, v, TOP) \<in> set (pools ts p)"
                by blast
            then have "v < t_V_var ts"
              using inv10 by blast
            then show ?thesis
              using ts'_def by simp
          qed
        qed
      qed

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          nid < nid_counter ts'"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
        show "nid < nid_counter ts'"
        proof (cases "pa = p")
          case False
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' False ts'_def by simp
          have old_nid_imp:
            "(nid, v, ts_val) \<in> set (pools ts pa) \<longrightarrow> nid < nid_counter ts"
          proof -
            from inv11 have
              "\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts pa) \<longrightarrow> nid < nid_counter ts"
              by blast
            then show ?thesis
              by blast
          qed
          have old_nid: "nid < nid_counter ts"
            using old_nid_imp mem by blast
            then show ?thesis
              using ts'_def by simp
            next
              case True
              have mem_in:
                "(nid, v, ts_val) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
                using mem' True pool_p by simp
              then have mem_cases:
                "(nid, v, ts_val) \<in> set (pools ts p) \<or>
                 (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p))"
                using in_set_pool_setTs by blast
              then show ?thesis
              proof
                assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
                have old_nid_imp:
                  "(nid, v, ts_val) \<in> set (pools ts p) \<longrightarrow> nid < nid_counter ts"
                proof -
                  from inv11 have
                    "\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts p) \<longrightarrow> nid < nid_counter ts"
                    by blast
                  then show ?thesis
                    by blast
                qed
                have old_nid: "nid < nid_counter ts"
                  using old_nid_imp mem_old by blast
                then show ?thesis
                  using ts'_def by simp
              next
                assume newmem: "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p)"
                then have topmem: "(t_nid ts p, v, TOP) \<in> set (pools ts p)"
                  by blast
            from inv11 topmem have "t_nid ts p < nid_counter ts"
              by blast
            with newmem show ?thesis
              using ts'_def by simp
          qed
        qed
      qed

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
          t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume htop:
          "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
          from htop have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
            by blast
          from htop have ts_top: "ts_val = TOP"
            by blast
        show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        proof (cases "pa = p")
          case False
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' False ts'_def by simp
          from inv12 mem ts_top have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
            by blast
          with False ts'_def show ?thesis
            by simp
        next
         case True
          have mem_in:
            "(nid, v, TOP) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem' ts_top True pool_p by simp
          
          have nid_neq:
            "nid \<noteq> t_nid ts p"
          proof
            assume nid_eq: "nid = t_nid ts p"
            have top_in:
              "(nid, v, TOP) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
              using mem_in by simp
            have tuple_neq: "fst (nid, v, TOP) \<noteq> t_nid ts p"
              using tts_nonbot top_in
              by (rule pool_setTs_clears_TOP, simp_all)
            have "nid \<noteq> t_nid ts p"
              using tuple_neq by simp
            with nid_eq show False
              by simp
          qed
          
          have mem: "(nid, v, TOP) \<in> set (pools ts p)"
            using mem_in in_set_pool_setTs by blast
          
          have inv12_imp:
            "(nid, v, TOP) \<in> set (pools ts p) \<longrightarrow>
             t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
          proof -
            from inv12 have
              "\<forall>nid v ts_val.
                 (nid, v, ts_val) \<in> set (pools ts p) \<and> ts_val = TOP \<longrightarrow>
                 t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
              by blast
            then show ?thesis
              by blast
          qed
          
          have old_top:
            "t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
            using inv12_imp mem by blast
          then have nid_eq_old: "nid = t_nid ts p"
            by simp
          
          from nid_neq nid_eq_old show ?thesis
            by blast
        qed
      qed

      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
          nid1 = nid2"
      proof (intro allI impI)
        fix pa q nid1 nid2 v1 v2 ts1 ts2
        assume h:
          "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
           (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
           ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2"
      from h have mem1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
        by blast
      from h have mem2': "(nid2, v2, ts2) \<in> set (pools ts' q)"
        by blast
      from h have nz1: "ts1 \<noteq> TOP"
        by blast
      from h have nz2: "ts2 \<noteq> TOP"
        by blast
      from h have tseq: "ts1 = ts2"
        by blast

        have old1:
          "(nid1, v1, ts1) \<in> set (pools ts pa) \<or>
           (pa = p \<and> nid1 = t_nid ts p \<and> ts1 = t_ts ts p \<and> (nid1, v1, TOP) \<in> set (pools ts p))"
        proof (cases "pa = p")
          case False
          with mem1' ts'_def show ?thesis
            by simp
        next
          case True
          have mem1_in:
            "(nid1, v1, ts1) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem1' True pool_p by simp
          from mem1_in nz1 show ?thesis
            using True in_set_pool_setTs by blast
        qed

        have old2:
          "(nid2, v2, ts2) \<in> set (pools ts q) \<or>
           (q = p \<and> nid2 = t_nid ts p \<and> ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p))"
        proof (cases "q = p")
          case False
          with mem2' ts'_def show ?thesis
            by simp
        next
          case True
          have mem2_in:
            "(nid2, v2, ts2) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem2' True pool_p by simp
          from mem2_in nz2 show ?thesis
            using True in_set_pool_setTs by blast
        qed

        from old1 show "nid1 = nid2"
      proof
        assume old1_old: "(nid1, v1, ts1) \<in> set (pools ts pa)"
        from old2 show "nid1 = nid2"
        proof
          assume old2_old: "(nid2, v2, ts2) \<in> set (pools ts q)"
          have inv13_imp:
            "(nid1, v1, ts1) \<in> set (pools ts pa) \<and>
             (nid2, v2, ts2) \<in> set (pools ts q) \<and>
             ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
             nid1 = nid2"
          proof -
            from inv13 have
              "\<forall>q nid1 nid2 v1 v2 ts1 ts2.
                 (nid1, v1, ts1) \<in> set (pools ts pa) \<and>
                 (nid2, v2, ts2) \<in> set (pools ts q) \<and>
                 ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
                 nid1 = nid2"
              by blast
            then show ?thesis
              by blast
          qed
          from inv13_imp old1_old old2_old nz1 nz2 tseq show "nid1 = nid2"
            by blast
        next
          assume old2_new:
            "q = p \<and> nid2 = t_nid ts p \<and> ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p)"
          from old2_new have qeq: "q = p"
            by blast
          from old2_new have nid2eq: "nid2 = t_nid ts p"
            by blast
          from old2_new have ts2eq: "ts2 = t_ts ts p"
            by blast
      
          have inv14_imp:
            "t_pc ts p = ''TE2'' \<and>
             (nid1, v1, ts1) \<in> set (pools ts pa) \<and>
             ts1 \<noteq> TOP \<longrightarrow>
             t_ts ts p \<noteq> ts1"
          proof -
            from inv14 have
              "\<forall>q nid v ts_val.
                 t_pc ts p = ''TE2'' \<and>
                 (nid, v, ts_val) \<in> set (pools ts q) \<and>
                 ts_val \<noteq> TOP \<longrightarrow>
                 t_ts ts p \<noteq> ts_val"
              by blast
            then show ?thesis
              by blast
          qed
          have neq_ts: "t_ts ts p \<noteq> ts1"
            using inv14_imp pc2 old1_old nz1 by blast
          from tseq ts2eq neq_ts show "nid1 = nid2"
            by simp
        qed
      next
        assume old1_new:
          "pa = p \<and> nid1 = t_nid ts p \<and> ts1 = t_ts ts p \<and> (nid1, v1, TOP) \<in> set (pools ts p)"
        from old1_new have paeq: "pa = p"
          by blast
        from old1_new have nid1eq: "nid1 = t_nid ts p"
          by blast
        from old1_new have ts1eq: "ts1 = t_ts ts p"
          by blast
      
        from old2 show "nid1 = nid2"
        proof
          assume old2_old: "(nid2, v2, ts2) \<in> set (pools ts q)"
          have inv14_imp:
            "t_pc ts p = ''TE2'' \<and>
             (nid2, v2, ts2) \<in> set (pools ts q) \<and>
             ts2 \<noteq> TOP \<longrightarrow>
             t_ts ts p \<noteq> ts2"
          proof -
            from inv14 have
              "\<forall>q nid v ts_val.
                 t_pc ts p = ''TE2'' \<and>
                 (nid, v, ts_val) \<in> set (pools ts q) \<and>
                 ts_val \<noteq> TOP \<longrightarrow>
                 t_ts ts p \<noteq> ts_val"
              by blast
            then show ?thesis
              by blast
          qed
          have neq_ts: "t_ts ts p \<noteq> ts2"
            using inv14_imp pc2 old2_old nz2 by blast
          from tseq ts1eq neq_ts show "nid1 = nid2"
            by simp
        next
          assume old2_new:
            "q = p \<and> nid2 = t_nid ts p \<and> ts2 = t_ts ts p \<and> (nid2, v2, TOP) \<in> set (pools ts p)"
          from old2_new have nid2eq: "nid2 = t_nid ts p"
            by blast
          from nid1eq nid2eq show "nid1 = nid2"
            by simp
        qed
      qed
qed
    show "\<forall>pa q nid v ts_val.
        t_pc ts' pa = ''TE2'' \<and>
        (nid, v, ts_val) \<in> set (pools ts' q) \<and>
        ts_val \<noteq> TOP \<longrightarrow>
        t_ts ts' pa \<noteq> ts_val"
    proof (intro allI impI)
      fix pa q nid v ts_val
      assume h:
        "t_pc ts' pa = ''TE2'' \<and>
         (nid, v, ts_val) \<in> set (pools ts' q) \<and>
         ts_val \<noteq> TOP"
      from h have hpc': "t_pc ts' pa = ''TE2''"
        by blast
      from h have mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
        by blast
      from h have nz: "ts_val \<noteq> TOP"
        by blast
    
      have pa_neq: "pa \<noteq> p"
      proof
        assume "pa = p"
        with hpc' ts'_def show False
          by simp
      qed
    
      have oldpc: "t_pc ts pa = ''TE2''"
        using hpc' pa_neq ts'_def by simp
    
      show "t_ts ts' pa \<noteq> ts_val"
      proof (cases "q = p")
        case False
        have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          using mem' False ts'_def by simp
        have inv14_imp:
          "t_pc ts pa = ''TE2'' \<and>
           (nid, v, ts_val) \<in> set (pools ts q) \<and>
           ts_val \<noteq> TOP \<longrightarrow>
           t_ts ts pa \<noteq> ts_val"
        proof -
          from inv14 have
            "\<forall>q nid v ts_val.
               t_pc ts pa = ''TE2'' \<and>
               (nid, v, ts_val) \<in> set (pools ts q) \<and>
               ts_val \<noteq> TOP \<longrightarrow>
               t_ts ts pa \<noteq> ts_val"
            by blast
          then show ?thesis
            by blast
        qed
        have old_neq: "t_ts ts pa \<noteq> ts_val"
          using inv14_imp oldpc mem_old nz by blast
        then show ?thesis
          using pa_neq ts'_def by simp
      next
        case True
        have mem_in:
          "(nid, v, ts_val) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
          using mem' True pool_p by simp
        then have mem_cases:
          "(nid, v, ts_val) \<in> set (pools ts p) \<or>
           (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p))"
          using in_set_pool_setTs nz by blast
        from mem_cases show ?thesis
        proof
          assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
          have inv14_imp:
            "t_pc ts pa = ''TE2'' \<and>
             (nid, v, ts_val) \<in> set (pools ts p) \<and>
             ts_val \<noteq> TOP \<longrightarrow>
             t_ts ts pa \<noteq> ts_val"
          proof -
            from inv14 have
              "\<forall>q nid v ts_val.
                 t_pc ts pa = ''TE2'' \<and>
                 (nid, v, ts_val) \<in> set (pools ts q) \<and>
                 ts_val \<noteq> TOP \<longrightarrow>
                 t_ts ts pa \<noteq> ts_val"
              by blast
            then show ?thesis
              by blast
          qed
          have old_neq: "t_ts ts pa \<noteq> ts_val"
            using inv14_imp oldpc mem_old nz by blast
          then show ?thesis
            using pa_neq ts'_def by simp
        next
          assume newmem: "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p)"
          have inv15_imp:
            "t_pc ts pa = ''TE2'' \<and>
             t_pc ts p = ''TE2'' \<and>
             pa \<noteq> p \<longrightarrow>
             t_ts ts pa \<noteq> t_ts ts p"
          proof -
            from inv15 have
              "\<forall>p q.
                 t_pc ts p = ''TE2'' \<and>
                 t_pc ts q = ''TE2'' \<and>
                 p \<noteq> q \<longrightarrow>
                 t_ts ts p \<noteq> t_ts ts q"
              by blast
            then show ?thesis
              by blast
          qed
          have ts_neq: "t_ts ts pa \<noteq> t_ts ts p"
            using inv15_imp oldpc pc2 pa_neq by blast
          with newmem show ?thesis
            using pa_neq ts'_def by simp
        qed
      qed
    qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE2'' \<and>
          t_pc ts' q = ''TE2'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_ts ts' pa \<noteq> t_ts ts' q"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE2'' \<and>
           t_pc ts' q = ''TE2'' \<and>
           pa \<noteq> q"
        then have hpa': "t_pc ts' pa = ''TE2''"
          and hq': "t_pc ts' q = ''TE2''"
          and neq: "pa \<noteq> q"
          by simp_all

        have pa_neq: "pa \<noteq> p"
        proof
          assume "pa = p"
          with hpa' ts'_def show False
            by simp
        qed

        have q_neq: "q \<noteq> p"
        proof
          assume "q = p"
          with hq' ts'_def show False
            by simp
        qed

        have hpa: "t_pc ts pa = ''TE2''"
          using hpa' pa_neq ts'_def by simp
        have hq: "t_pc ts q = ''TE2''"
          using hq' q_neq ts'_def by simp

        from inv15 hpa hq neq show "t_ts ts' pa \<noteq> t_ts ts' q"
          using pa_neq q_neq ts'_def by simp
      qed

show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
proof (intro allI)
  fix pa
  show "sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
  proof (cases "pa = p")
    case False
    have pool_eq: "pools ts' pa = pools ts pa"
      using False ts'_def by simp
    have inv16_imp:
      "sorted (map fst (pools ts pa)) \<and> distinct (map fst (pools ts pa))"
    proof -
      from inv16 have
        "\<forall>p. sorted (map fst (pools ts p)) \<and> distinct (map fst (pools ts p))"
        by blast
      then show ?thesis
        by blast
    qed
    from inv16_imp pool_eq show ?thesis
      by simp
  next
    case True
    have map_fst_pool_setTs:
      "\<forall>xs target new_ts. map fst (pool_setTs xs target new_ts) = map fst xs"
    proof (intro allI)
      fix xs target new_ts
      show "map fst (pool_setTs xs target new_ts) = map fst xs"
        by (induct xs) auto
    qed
    then have map_eq:
      "map fst (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p)) = map fst (pools ts p)"
      by blast
    have inv16_imp:
      "sorted (map fst (pools ts p)) \<and> distinct (map fst (pools ts p))"
    proof -
      from inv16 have
        "\<forall>p. sorted (map fst (pools ts p)) \<and> distinct (map fst (pools ts p))"
        by blast
      then show ?thesis
        by blast
    qed
    from inv16_imp map_eq True ts'_def show ?thesis
      by simp
  qed
qed

      show "\<forall>pa.
          t_pc ts' pa = ''TE1'' \<longrightarrow>
          t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
      proof (intro allI impI)
        fix pa
        assume hpc': "t_pc ts' pa = ''TE1''"
        have pa_neq: "pa \<noteq> p"
        proof
          assume "pa = p"
          with hpc' ts'_def show False
            by simp
        qed
        have hpc: "t_pc ts pa = ''TE1''"
          using hpc' pa_neq ts'_def by simp
        from inv17 hpc show "t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
          using pa_neq ts'_def by simp
      qed

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE1'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
          t_v ts' pa \<noteq> v"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q)"
        then have hpc': "t_pc ts' pa = ''TE1''"
          and mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
          by simp_all

        have pa_neq: "pa \<noteq> p"
        proof
          assume "pa = p"
          with hpc' ts'_def show False
            by simp
        qed

        have hpc: "t_pc ts pa = ''TE1''"
          using hpc' pa_neq ts'_def by simp

        show "t_v ts' pa \<noteq> v"
        proof (cases "q = p")
          case False
          have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
            using mem' False ts'_def by simp
          have hex: "\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q)"
            using mem_old by blast
          from inv18 hpc hex show ?thesis
            using pa_neq ts'_def by simp
        next
          case True
          have mem_in:
            "(nid, v, ts_val) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
            using mem' True pool_p by simp
          then have mem_cases:
            "(nid, v, ts_val) \<in> set (pools ts p) \<or>
             (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p))"
            using in_set_pool_setTs by blast
          then show ?thesis
          proof
            assume mem_old: "(nid, v, ts_val) \<in> set (pools ts p)"
            have hex: "\<exists>tsv. (nid, v, tsv) \<in> set (pools ts p)"
              using mem_old by blast
            from inv18 hpc hex show ?thesis
              using pa_neq ts'_def by simp
          next
            assume newmem: "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p)"
            then have topmem: "(nid, v, TOP) \<in> set (pools ts p)"
              by blast
            have hex: "\<exists>tsv. (nid, v, tsv) \<in> set (pools ts p)"
              using topmem by blast
            from inv18 hpc hex show ?thesis
              using pa_neq ts'_def by simp
          qed
        qed
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE1'' \<and>
          t_pc ts' q = ''TE1'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_v ts' pa \<noteq> t_v ts' q"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           t_pc ts' q = ''TE1'' \<and>
           pa \<noteq> q"
        then have hpa': "t_pc ts' pa = ''TE1''"
          and hq': "t_pc ts' q = ''TE1''"
          and neq: "pa \<noteq> q"
          by simp_all

        have pa_neq: "pa \<noteq> p"
        proof
          assume "pa = p"
          with hpa' ts'_def show False
            by simp
        qed

        have q_neq: "q \<noteq> p"
        proof
          assume "q = p"
          with hq' ts'_def show False
            by simp
        qed

        have hpa: "t_pc ts pa = ''TE1''"
          using hpa' pa_neq ts'_def by simp
        have hq: "t_pc ts q = ''TE1''"
          using hq' q_neq ts'_def by simp

        from inv19 hpa hq neq show "t_v ts' pa \<noteq> t_v ts' q"
          using pa_neq q_neq ts'_def by simp
      qed
  qed

 show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    have hpc': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      using hpend by blast
    have hnz: "ts_val \<noteq> TOP"
      using hpend by blast

    show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
    proof (cases "pa = p")
      case True
      have False
        using hpc' True ts'_def by simp
      then show ?thesis
        by simp
    next
      case False
      have hpc_old: "t_pc ts pa = ''TE2''"
        using hpc' False ts'_def by simp

           show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      proof (cases "q = p")
        case False
        have mem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          using mem' False ts'_def by simp
        have old_ord:
          "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
          using inv20 hpc_old mem_old hnz by blast
        have tts_eq: "t_ts ts' pa = t_ts ts pa"
          using False ts'_def by simp
        have tnid_eq: "t_nid ts' pa = t_nid ts pa"
          using False ts'_def by simp
        from old_ord tts_eq tnid_eq
        show ?thesis
          by simp
      next
        case True
        have mem_in:
          "(nid, v, ts_val) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
          using mem' True ts'_def by simp
        have mem_cases:
          "(nid, v, ts_val) \<in> set (pools ts p) \<or>
           (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p))"
          using mem_in in_set_pool_setTs by blast
        from mem_cases show ?thesis
        proof
          assume mem_old_p: "(nid, v, ts_val) \<in> set (pools ts p)"
          have old_ord:
            "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
            using inv20 hpc_old mem_old_p hnz by blast
          have tts_eq: "t_ts ts' pa = t_ts ts pa"
            using False ts'_def by simp
          have tnid_eq: "t_nid ts' pa = t_nid ts pa"
            using False ts'_def by simp
          from old_ord tts_eq tnid_eq
          show ?thesis
            by simp
        next
          assume newmem: "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p)"
          have ord_ppa:
            "(t_ts ts p <\<^sub>t\<^sub>s t_ts ts pa) = (t_nid ts p < t_nid ts pa)"
            using inv21 pc2 hpc_old True False by blast
          have tts_eq: "t_ts ts' pa = t_ts ts pa"
            using False ts'_def by simp
          have tnid_eq: "t_nid ts' pa = t_nid ts pa"
            using False ts'_def by simp
          from newmem ord_ppa tts_eq tnid_eq
          show ?thesis
            by simp
        qed
      qed
    qed
  qed

  show "\<forall>pa q.
      t_pc ts' pa = ''TE2'' \<and>
      t_pc ts' q = ''TE2'' \<and>
      pa \<noteq> q \<longrightarrow>
      (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
  proof (intro allI impI)
    fix pa q
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       t_pc ts' q = ''TE2'' \<and>
       pa \<noteq> q"
    have hpa': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hq': "t_pc ts' q = ''TE2''"
      using hpend by blast
    have neq: "pa \<noteq> q"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpa' eq ts'_def show False
        by simp
    qed

    have q_neq: "q \<noteq> p"
    proof
      assume eq: "q = p"
      from hq' eq ts'_def show False
        by simp
    qed

    have hpa_old: "t_pc ts pa = ''TE2''"
      using hpa' pa_neq ts'_def by simp
    have hq_old: "t_pc ts q = ''TE2''"
      using hq' q_neq ts'_def by simp
    have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
      using pa_neq ts'_def by simp
    have tts_q_eq: "t_ts ts' q = t_ts ts q"
      using q_neq ts'_def by simp
    have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
      using pa_neq ts'_def by simp
    have tnid_q_eq: "t_nid ts' q = t_nid ts q"
      using q_neq ts'_def by simp

    have old_ord:
      "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
      using inv21 hpa_old hq_old neq by blast
    with tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
    show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      by simp
  qed
qed
qed



  next

    (* ====================================================== *)
    (* Case 4: T_E3                                           *)
    (* The pools are unchanged; only the enqueue-local variables of p are cleared. *)
    (* ====================================================== *)
    assume h: "T_E3 p ts ts'"
    then have pc3: "t_pc ts p = ''TE3''"
      unfolding T_E3_def by simp
    from h have ts'_def:
      "ts' =
        ts\<lparr>t_pc := (\<lambda>x. if x = p then ''TL0'' else t_pc ts x),
           t_v := (\<lambda>x. if x = p then BOT else t_v ts x),
           t_nid := (\<lambda>x. if x = p then BOT else t_nid ts x),
           t_ts := (\<lambda>x. if x = p then TOP else t_ts ts x)\<rparr>"
      unfolding T_E3_def by simp

    have no_top_p:
      "\<forall>nid v. (nid, v, TOP) \<notin> set (pools ts p)"
    proof (intro allI)
      fix nid v
      show "(nid, v, TOP) \<notin> set (pools ts p)"
      proof
        assume hin: "(nid, v, TOP) \<in> set (pools ts p)"
        then have hex: "\<exists>v. (nid, v, TOP) \<in> set (pools ts p)"
          by blast
        from inv12 hex have "t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
          by blast
        then have "t_pc ts p = ''TE2''"
          by simp
        with pc3 show False
          by simp
      qed
    qed

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
          (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
        using inv1 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
          ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv2 ts'_def by simp

      show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix pa
        assume hneq: "t_ts ts' pa \<noteq> TOP"
        show "t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "pa = p")
          case True
          with ts'_def have "t_ts ts' pa = TOP"
            by simp
          with hneq show ?thesis
            by simp
        next
          case False
          have tts_eq: "t_ts ts' pa = t_ts ts pa"
            using False ts'_def by simp
          have ctr_eq: "ts_counter ts' = ts_counter ts"
            using ts'_def by simp
          have old_nz: "t_ts ts pa \<noteq> TOP"
            using False hneq ts'_def by simp
          have old_bd: "t_ts ts pa <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv3 old_nz by blast
          from tts_eq ctr_eq old_bd show ?thesis
            by simp
        qed
      qed

      show "\<forall>q.
          t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
          t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv4 ts'_def by simp

      show "\<forall>pa.
          t_pc ts' pa = ''TE2'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP \<and>
          (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
      proof (intro allI impI)
        fix pa
        assume hpc: "t_pc ts' pa = ''TE2''"
        from ts'_def hpc have "pa \<noteq> p" and oldpc: "t_pc ts pa = ''TE2''"
          by (auto split: if_splits)
        from inv5 oldpc have "t_ts ts pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts pa, v, TOP) \<in> set (pools ts pa))"
          by blast
        with `pa \<noteq> p` ts'_def show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
          by simp
      qed

     show "\<forall>pa.
          t_pc ts' pa = ''TE3'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP"
      proof (intro allI impI)
        fix pa
        assume hpc: "t_pc ts' pa = ''TE3''"
        from ts'_def hpc have "pa \<noteq> p" and oldpc: "t_pc ts pa = ''TE3''"
          by (auto split: if_splits)
        from inv6 oldpc have "t_ts ts pa \<noteq> TOP"
          by blast
        with `pa \<noteq> p` ts'_def show "t_ts ts' pa \<noteq> TOP"
          by simp
      qed

      show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
        using inv7 ts'_def by simp

      show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
          (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
        using inv8 ts'_def by simp

      show "BOT < t_V_var ts'"
        using inv9 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          v < t_V_var ts'"
        using inv10 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          nid < nid_counter ts'"
        using inv11 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
          t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume htop:
          "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
        then have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
          by blast
        from htop have ts_top: "ts_val = TOP"
          by blast
        from ts'_def have pools_eq: "pools ts' pa = pools ts pa"
          by simp
        from mem' have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
          using pools_eq by simp
        show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        proof (cases "pa = p")
          case True
          from mem ts_top True have "(nid, v, TOP) \<in> set (pools ts p)"
            by simp
          with no_top_p show ?thesis
            by blast
        next
          case False
          from mem ts_top have "\<exists>v. (nid, v, TOP) \<in> set (pools ts pa)"
            by blast
          then have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
            using inv12 by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
          nid1 = nid2"
        using inv13 ts'_def by simp

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE2'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<and>
          ts_val \<noteq> TOP \<longrightarrow>
          t_ts ts' pa \<noteq> ts_val"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume hte2:
          "t_pc ts' pa = ''TE2'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q) \<and>
           ts_val \<noteq> TOP"
        then have hpc': "t_pc ts' pa = ''TE2''" and hin': "(nid, v, ts_val) \<in> set (pools ts' q)" and hneq: "ts_val \<noteq> TOP"
          by simp_all
        from hpc' ts'_def have pa_neq: "pa \<noteq> p" and hpc: "t_pc ts pa = ''TE2''"
          by (auto split: if_splits)
        from hin' ts'_def have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
          by simp
        from hpc hin hneq have "t_ts ts pa \<noteq> ts_val"
          using inv14 by blast
        with pa_neq ts'_def show "t_ts ts' pa \<noteq> ts_val"
          by simp
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE2'' \<and>
          t_pc ts' q = ''TE2'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_ts ts' pa \<noteq> t_ts ts' q"
        using inv15 ts'_def by (auto split: if_splits)

      show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
        using inv16 ts'_def by simp

      show "\<forall>pa.
          t_pc ts' pa = ''TE1'' \<longrightarrow>
          t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
        using inv17 ts'_def by (auto split: if_splits)

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE1'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
          t_v ts' pa \<noteq> v"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume hte1:
          "t_pc ts' pa = ''TE1'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q)"
        then have hpc': "t_pc ts' pa = ''TE1''" and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
          by simp_all
        show "t_v ts' pa \<noteq> v"
        proof (cases "pa = p")
          case True
          with hpc' ts'_def show ?thesis
            by simp
        next
          case False
          from hpc' False ts'_def have hpc: "t_pc ts pa = ''TE1''"
            by simp
          have pools_eq: "pools ts' q = pools ts q"
            using ts'_def by simp
          have hin_old: "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin' pools_eq by simp
          have hin: "(\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q))"
            using hin_old by blast
          from hpc hin have "t_v ts pa \<noteq> v"
            using inv18 by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE1'' \<and>
          t_pc ts' q = ''TE1'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_v ts' pa \<noteq> t_v ts' q"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           t_pc ts' q = ''TE1'' \<and>
           pa \<noteq> q"
        then have hpa': "t_pc ts' pa = ''TE1''" and hq': "t_pc ts' q = ''TE1''" and neq: "pa \<noteq> q"
          by simp_all
        show "t_v ts' pa \<noteq> t_v ts' q"
        proof (cases "pa = p \<or> q = p")
          case True
          then show ?thesis
          proof
            assume "pa = p"
            with hpa' ts'_def show ?thesis
              by simp
          next
            assume "q = p"
            with hq' ts'_def show ?thesis
              by simp
          qed
        next
          case False
          from False hpa' ts'_def have hpa: "t_pc ts pa = ''TE1''"
            by simp
          from False hq' ts'_def have hq: "t_pc ts q = ''TE1''"
            by simp
          from hpa hq neq have "t_v ts pa \<noteq> t_v ts q"
            using inv19 by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed
  qed

 show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    have hpc': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hmem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      using hpend by blast
    have hnz: "ts_val \<noteq> TOP"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpc' eq ts'_def show False
        by simp
    qed

    have hpc_old: "t_pc ts pa = ''TE2''"
      using hpc' pa_neq ts'_def by simp
    have hmem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
      using hmem' ts'_def by simp
    have tts_eq: "t_ts ts' pa = t_ts ts pa"
      using pa_neq ts'_def by simp
    have tnid_eq: "t_nid ts' pa = t_nid ts pa"
      using pa_neq ts'_def by simp

    have old_ord:
      "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
      using inv20 hpc_old hmem_old hnz by blast
    from old_ord tts_eq tnid_eq
    show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      by simp
  qed

  show "\<forall>pa q.
      t_pc ts' pa = ''TE2'' \<and>
      t_pc ts' q = ''TE2'' \<and>
      pa \<noteq> q \<longrightarrow>
      (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
  proof (intro allI impI)
    fix pa q
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       t_pc ts' q = ''TE2'' \<and>
       pa \<noteq> q"
    have hpa': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hq': "t_pc ts' q = ''TE2''"
      using hpend by blast
    have neq: "pa \<noteq> q"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpa' eq ts'_def show False
        by simp
    qed

    have q_neq: "q \<noteq> p"
    proof
      assume eq: "q = p"
      from hq' eq ts'_def show False
        by simp
    qed

    have hpa_old: "t_pc ts pa = ''TE2''"
      using hpa' pa_neq ts'_def by simp
    have hq_old: "t_pc ts q = ''TE2''"
      using hq' q_neq ts'_def by simp
    have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
      using pa_neq ts'_def by simp
    have tts_q_eq: "t_ts ts' q = t_ts ts q"
      using q_neq ts'_def by simp
    have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
      using pa_neq ts'_def by simp
    have tnid_q_eq: "t_nid ts' q = t_nid ts q"
      using q_neq ts'_def by simp

    have old_ord:
      "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
      using inv21 hpa_old hq_old neq by blast
    from old_ord tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
    show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      by simp
  qed
qed
qed
  next

    (* ====================================================== *)
    (* Case 5: T_Call_Deq                                     *)
    (* Move p from TL0 to TD1, leaving the data state unchanged. *)
    (* ====================================================== *)
    assume h: "T_Call_Deq p ts ts'"
    then have pc0: "t_pc ts p = ''TL0''"
      unfolding T_Call_Deq_def by simp
    from h have ts'_def:
      "ts' = ts\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts x)\<rparr>"
      unfolding T_Call_Deq_def by simp

    have no_top_p:
      "\<forall>nid v. (nid, v, TOP) \<notin> set (pools ts p)"
    proof (intro allI)
      fix nid v
      show "(nid, v, TOP) \<notin> set (pools ts p)"
      proof
        assume hin: "(nid, v, TOP) \<in> set (pools ts p)"
        then have hex: "\<exists>v. (nid, v, TOP) \<in> set (pools ts p)"
          by blast
        from inv12 hex have "t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
          by blast
        then have "t_pc ts p = ''TE2''"
          by simp
        with pc0 show False
          by simp
      qed
    qed

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
          (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
        using inv1 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
          ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv2 ts'_def by simp

      show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv3 ts'_def by simp

      show "\<forall>q.
          t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
          t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv4 ts'_def by simp

      show "\<forall>pa.
          t_pc ts' pa = ''TE2'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP \<and>
          (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
      proof (intro allI impI)
        fix pa
        assume hpc': "t_pc ts' pa = ''TE2''"
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' ts'_def eq have "''TD1'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        from pa_neq hpc' ts'_def have hpc: "t_pc ts pa = ''TE2''"
          by simp
        from inv5 hpc have "t_ts ts pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts pa, v, TOP) \<in> set (pools ts pa))"
          by blast
        with pa_neq ts'_def show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
          by simp
      qed

     show "\<forall>pa.
          t_pc ts' pa = ''TE3'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP"
        using inv6 ts'_def by simp

      show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
        using inv7 ts'_def by simp

      show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
          (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
        using inv8 ts'_def by simp

      show "BOT < t_V_var ts'"
        using inv9 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          v < t_V_var ts'"
        using inv10 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          nid < nid_counter ts'"
        using inv11 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
          t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume htop:
          "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
        then have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
          by blast
        from htop have ts_top: "ts_val = TOP"
          by blast
        from ts'_def have pools_eq: "pools ts' pa = pools ts pa"
          by simp
        from mem' have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
          using pools_eq by simp
        show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        proof (cases "pa = p")
          case True
          from mem ts_top True have "(nid, v, TOP) \<in> set (pools ts p)"
            by simp
          with no_top_p show ?thesis
            by blast
        next
          case False
          from mem ts_top have "\<exists>v. (nid, v, TOP) \<in> set (pools ts pa)"
            by blast
          then have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
            using inv12 by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
          nid1 = nid2"
        using inv13 ts'_def by simp

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE2'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<and>
          ts_val \<noteq> TOP \<longrightarrow>
          t_ts ts' pa \<noteq> ts_val"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume hte2:
          "t_pc ts' pa = ''TE2'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q) \<and>
           ts_val \<noteq> TOP"
        then have hpc': "t_pc ts' pa = ''TE2''"
          and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
          and hneq: "ts_val \<noteq> TOP"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' ts'_def eq have "''TD1'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        from pa_neq hpc' ts'_def have hpc: "t_pc ts pa = ''TE2''"
          by simp
        from hin' ts'_def have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
          by simp
        from hpc hin hneq have "t_ts ts pa \<noteq> ts_val"
          using inv14 by blast
        with pa_neq ts'_def show "t_ts ts' pa \<noteq> ts_val"
          by simp
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE2'' \<and>
          t_pc ts' q = ''TE2'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_ts ts' pa \<noteq> t_ts ts' q"
      proof (intro allI impI)
        fix pa q
        assume hte2:
          "t_pc ts' pa = ''TE2'' \<and>
           t_pc ts' q = ''TE2'' \<and>
           pa \<noteq> q"
        then have hpa': "t_pc ts' pa = ''TE2''"
          and hq': "t_pc ts' q = ''TE2''"
          and neq: "pa \<noteq> q"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpa' ts'_def eq have "''TD1'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        have q_neq: "q \<noteq> p"
        proof
          assume eq: "q = p"
          from hq' ts'_def eq have "''TD1'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        from pa_neq hpa' ts'_def have hpa: "t_pc ts pa = ''TE2''"
          by simp
        from q_neq hq' ts'_def have hq: "t_pc ts q = ''TE2''"
          by simp
        from hpa hq neq have "t_ts ts pa \<noteq> t_ts ts q"
          using inv15 by blast
        with pa_neq q_neq ts'_def show "t_ts ts' pa \<noteq> t_ts ts' q"
          by simp
      qed

      show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
        using inv16 ts'_def by simp

      show "\<forall>pa.
          t_pc ts' pa = ''TE1'' \<longrightarrow>
          t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
        using inv17 ts'_def by simp

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE1'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
          t_v ts' pa \<noteq> v"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume hte1:
          "t_pc ts' pa = ''TE1'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q)"
        then have hpc': "t_pc ts' pa = ''TE1''"
          and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' ts'_def eq have "''TD1'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        from pa_neq hpc' ts'_def have hpc: "t_pc ts pa = ''TE1''"
          by simp
        have pools_eq: "pools ts' q = pools ts q"
          using ts'_def by simp
        have hin_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          using hin' pools_eq by simp
        have hin: "(\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q))"
        proof
          show "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin_old .
        qed
        from hpc hin have "t_v ts pa \<noteq> v"
          using inv18 by blast
        with pa_neq ts'_def show "t_v ts' pa \<noteq> v"
          by simp
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE1'' \<and>
          t_pc ts' q = ''TE1'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_v ts' pa \<noteq> t_v ts' q"
      proof (intro allI impI)
        fix pa q
        assume hte1:
          "t_pc ts' pa = ''TE1'' \<and>
           t_pc ts' q = ''TE1'' \<and>
           pa \<noteq> q"
        then have hpa': "t_pc ts' pa = ''TE1''"
          and hq': "t_pc ts' q = ''TE1''"
          and neq: "pa \<noteq> q"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpa' ts'_def eq have "''TD1'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have q_neq: "q \<noteq> p"
        proof
          assume eq: "q = p"
          from hq' ts'_def eq have "''TD1'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        from pa_neq hpa' ts'_def have hpa: "t_pc ts pa = ''TE1''"
          by simp
        from q_neq hq' ts'_def have hq: "t_pc ts q = ''TE1''"
          by simp
        from hpa hq neq have "t_v ts pa \<noteq> t_v ts q"
          using inv19 by blast
        with pa_neq q_neq ts'_def show "t_v ts' pa \<noteq> t_v ts' q"
          by simp
      qed
     qed

  show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    have hpc': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hmem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      using hpend by blast
    have hnz: "ts_val \<noteq> TOP"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpc' eq ts'_def show False
        by simp
    qed

    have hpc_old: "t_pc ts pa = ''TE2''"
      using hpc' pa_neq ts'_def by simp
    have hmem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
      using hmem' ts'_def by simp
    have tts_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tnid_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp

    have old_ord:
      "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
      using inv20 hpc_old hmem_old hnz by blast
    from old_ord tts_eq tnid_eq
    show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      by simp
  qed

  show "\<forall>pa q.
      t_pc ts' pa = ''TE2'' \<and>
      t_pc ts' q = ''TE2'' \<and>
      pa \<noteq> q \<longrightarrow>
      (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
  proof (intro allI impI)
    fix pa q
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       t_pc ts' q = ''TE2'' \<and>
       pa \<noteq> q"
    have hpa': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hq': "t_pc ts' q = ''TE2''"
      using hpend by blast
    have neq: "pa \<noteq> q"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpa' eq ts'_def show False
        by simp
    qed

    have q_neq: "q \<noteq> p"
    proof
      assume eq: "q = p"
      from hq' eq ts'_def show False
        by simp
    qed

    have hpa_old: "t_pc ts pa = ''TE2''"
      using hpa' pa_neq ts'_def by simp
    have hq_old: "t_pc ts q = ''TE2''"
      using hq' q_neq ts'_def by simp
    have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tts_q_eq: "t_ts ts' q = t_ts ts q"
      using ts'_def by simp
    have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp
    have tnid_q_eq: "t_nid ts' q = t_nid ts q"
      using ts'_def by simp

    have old_ord:
      "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
      using inv21 hpa_old hq_old neq by blast
    from old_ord tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
    show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      by simp
  qed
qed
qed
  next

    (* ====================================================== *)
    (* Case 6: T_D1                                           *)
    (* Create a fresh startTs and initialize the local dequeue-scan state. *)
    (* ====================================================== *)
    assume h: "T_D1 p ts ts'"
    then have pc1: "t_pc ts p = ''TD1''"
      unfolding T_D1_def by simp
    from h have ts'_def:
      "ts' =
        ts\<lparr>ts_counter := ts_counter ts + 1,
           t_startTs := (\<lambda>x. if x = p then TS (ts_counter ts) else t_startTs ts x),
           t_candNid := (\<lambda>x. if x = p then BOT else t_candNid ts x),
           t_candTs := (\<lambda>x. if x = p then TOP else t_candTs ts x),
           t_candPid := (\<lambda>x. if x = p then BOT else t_candPid ts x),
           t_scanned := (\<lambda>x. if x = p then {} else t_scanned ts x),
           t_pc := (\<lambda>x. if x = p then ''TD_Line4_Done'' else t_pc ts x)\<rparr>"
      unfolding T_D1_def Let_def by simp

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
          (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
        using inv1 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
          ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume h:
          "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP"
        then have hin': "(nid, v, ts_val) \<in> set (pools ts' pa)"
          by simp
        from h have hneq: "ts_val \<noteq> TOP"
          by simp
        have pools_eq: "pools ts' pa = pools ts pa"
          using ts'_def by simp
        have hin: "(nid, v, ts_val) \<in> set (pools ts pa)"
          using hin' pools_eq by simp
        have old_bd: "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
          using inv2 hin hneq by blast
        have ctr_eq: "ts_counter ts' = Suc (ts_counter ts)"
          using ts'_def by simp
        show "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases ts_val)
          case TOP
          with old_bd show ?thesis
            by simp
        next
          case (TS n)
          with old_bd ctr_eq show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix pa
        assume hneq: "t_ts ts' pa \<noteq> TOP"
        show "t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "pa = p")
          case True
          have tts_eq: "t_ts ts' pa = t_ts ts pa"
            using True ts'_def by simp
          have ctr_eq: "ts_counter ts' = Suc (ts_counter ts)"
            using ts'_def by simp
          have old_nz: "t_ts ts pa \<noteq> TOP"
            using True hneq ts'_def by simp
          have old_bd: "t_ts ts pa <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv3 old_nz by blast
          show ?thesis
          proof (cases "t_ts ts pa")
            case TOP
            with old_nz show ?thesis
              by simp
          next
            case (TS n)
            with tts_eq ctr_eq old_bd show ?thesis
              by simp
          qed
        next
          case False
          have tts_eq: "t_ts ts' pa = t_ts ts pa"
            using False ts'_def by simp
          have ctr_eq: "ts_counter ts' = Suc (ts_counter ts)"
            using ts'_def by simp
          have old_nz: "t_ts ts pa \<noteq> TOP"
            using False hneq ts'_def by simp
          have old_bd: "t_ts ts pa <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv3 old_nz by blast
          show ?thesis
          proof (cases "t_ts ts pa")
            case TOP
            with old_nz show ?thesis
              by simp
          next
            case (TS n)
            with tts_eq ctr_eq old_bd show ?thesis
              by simp
          qed
        qed
      qed

      show "\<forall>q.
          t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
          t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix q
        assume hpc: "t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
        show "t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "q = p")
          case True
          with ts'_def show ?thesis by simp
        next
          case False
          from False hpc ts'_def have hpc_old:
            "t_pc ts q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
            by simp
          have old_bd: "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using inv4 hpc_old by blast
          have sts_eq: "t_startTs ts' q = t_startTs ts q"
            using False ts'_def by simp
          have ctr_eq: "ts_counter ts' = Suc (ts_counter ts)"
            using ts'_def by simp
          show ?thesis
          proof (cases "t_startTs ts q")
            case TOP
            with old_bd show ?thesis
              by simp
          next
            case (TS n)
            with old_bd sts_eq ctr_eq show ?thesis
              by simp
          qed
        qed
      qed

      show "\<forall>pa.
          t_pc ts' pa = ''TE2'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP \<and>
          (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
        using inv5 ts'_def by simp

    show "\<forall>pa.
          t_pc ts' pa = ''TE3'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP"
        using inv6 ts'_def by simp

      show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
        using inv7 ts'_def by simp

      show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
          (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
        using inv8 ts'_def by simp

      show "BOT < t_V_var ts'"
        using inv9 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          v < t_V_var ts'"
        using inv10 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          nid < nid_counter ts'"
        using inv11 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
          t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume h:
          "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
        then have hin': "(nid, v, ts_val) \<in> set (pools ts' pa)"
          by blast
        from h have htop: "ts_val = TOP"
          by blast
        have pools_eq: "pools ts' pa = pools ts pa"
          using ts'_def by simp
        have hin: "(nid, v, ts_val) \<in> set (pools ts pa)"
          using hin' pools_eq by simp
        have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts pa)"
        proof -
          from hin htop have "(nid, v, TOP) \<in> set (pools ts pa)"
            by simp
          then show ?thesis
            by blast
        qed
        from inv12 hex have old_pc_nid: "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
          by blast
        then have old_pc: "t_pc ts pa = ''TE2''" and old_nid: "nid = t_nid ts pa"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from old_pc eq have "t_pc ts p = ''TE2''"
            by simp
          with pc1 show False
            by simp
        qed
        from old_pc pa_neq ts'_def have "t_pc ts' pa = ''TE2''"
          by simp
        moreover from old_nid pa_neq ts'_def have "nid = t_nid ts' pa"
          by simp
        ultimately show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
          by simp
      qed

      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
          nid1 = nid2"
        using inv13 ts'_def by simp

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE2'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<and>
          ts_val \<noteq> TOP \<longrightarrow>
          t_ts ts' pa \<noteq> ts_val"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume h:
          "t_pc ts' pa = ''TE2'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q) \<and>
           ts_val \<noteq> TOP"
        then have hpc': "t_pc ts' pa = ''TE2''"
          and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
          and hneq: "ts_val \<noteq> TOP"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TD_Line4_Done'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        have hpc: "t_pc ts pa = ''TE2''"
          using hpc' pa_neq ts'_def by simp
        have pools_eq: "pools ts' q = pools ts q"
          using ts'_def by simp
        have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
          using hin' pools_eq by simp
        have old_neq: "t_ts ts pa \<noteq> ts_val"
          using inv14 hpc hin hneq by blast
        have tts_eq: "t_ts ts' pa = t_ts ts pa"
          using pa_neq ts'_def by simp
        from old_neq tts_eq show "t_ts ts' pa \<noteq> ts_val"
          by simp
      qed
      show "\<forall>pa q.
          t_pc ts' pa = ''TE2'' \<and>
          t_pc ts' q = ''TE2'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_ts ts' pa \<noteq> t_ts ts' q"
        using inv15 ts'_def by simp

      show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
        using inv16 ts'_def by simp

      show "\<forall>pa.
          t_pc ts' pa = ''TE1'' \<longrightarrow>
          t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
        using inv17 ts'_def by simp

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE1'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
          t_v ts' pa \<noteq> v"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q)"
        then have hpc': "t_pc ts' pa = ''TE1''"
          and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TD_Line4_Done'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have hpc: "t_pc ts pa = ''TE1''"
          using hpc' pa_neq ts'_def by simp
        have pools_eq: "pools ts' q = pools ts q"
          using ts'_def by simp
        have hin_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          using hin' pools_eq by simp
        have hex: "(\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q))"
        proof
          show "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin_old .
        qed
        have old_neq: "t_v ts pa \<noteq> v"
          using inv18 hpc hex by blast
        have tv_eq: "t_v ts' pa = t_v ts pa"
          using pa_neq ts'_def by simp
        from old_neq tv_eq show "t_v ts' pa \<noteq> v"
          by simp
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE1'' \<and>
          t_pc ts' q = ''TE1'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_v ts' pa \<noteq> t_v ts' q"
        using inv19 ts'_def by simp
    qed


  show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    have hpc': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hmem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      using hpend by blast
    have hnz: "ts_val \<noteq> TOP"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpc' eq ts'_def show False
        by simp
    qed

    have hpc_old: "t_pc ts pa = ''TE2''"
      using hpc' pa_neq ts'_def by simp
    have hmem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
      using hmem' ts'_def by simp
    have tts_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tnid_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp

    have old_ord:
      "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
      using inv20 hpc_old hmem_old hnz by blast
    from old_ord tts_eq tnid_eq
    show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      by simp
  qed

  show "\<forall>pa q.
      t_pc ts' pa = ''TE2'' \<and>
      t_pc ts' q = ''TE2'' \<and>
      pa \<noteq> q \<longrightarrow>
      (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
  proof (intro allI impI)
    fix pa q
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       t_pc ts' q = ''TE2'' \<and>
       pa \<noteq> q"
    have hpa': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hq': "t_pc ts' q = ''TE2''"
      using hpend by blast
    have neq: "pa \<noteq> q"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpa' eq ts'_def show False
        by simp
    qed

    have q_neq: "q \<noteq> p"
    proof
      assume eq: "q = p"
      from hq' eq ts'_def show False
        by simp
    qed

    have hpa_old: "t_pc ts pa = ''TE2''"
      using hpa' pa_neq ts'_def by simp
    have hq_old: "t_pc ts q = ''TE2''"
      using hq' q_neq ts'_def by simp
    have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tts_q_eq: "t_ts ts' q = t_ts ts q"
      using ts'_def by simp
    have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp
    have tnid_q_eq: "t_nid ts' q = t_nid ts q"
      using ts'_def by simp

    have old_ord:
      "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
      using inv21 hpa_old hq_old neq by blast
    from old_ord tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
    show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      by simp
  qed
qed
qed

  next

    (* ====================================================== *)
    (* Case 7: T_D2                                           *)
    (* The D2 step splits into the EnterLoop and BackToD1 branches. *)
    (* ====================================================== *)
    assume h: "T_D2 p ts ts'"
    then show ?thesis
    proof (unfold T_D2_def, elim disjE)

      (* ==================================================== *)
      (* Case 7.1: T_D2_EnterLoop                             *)
      (* Move p from TD_Line4_Done to TD_Loop and clear the scan-candidate fields. *)
      (* ==================================================== *)
      assume h1: "T_D2_EnterLoop p ts ts'"
      then have pc_done: "t_pc ts p = ''TD_Line4_Done''"
        unfolding T_D2_EnterLoop_def by simp
      from h1 have ts'_def:
        "ts' =
          ts\<lparr>t_pc := (\<lambda>x. if x = p then ''TD_Loop'' else t_pc ts x),
             t_scanned := (\<lambda>x. if x = p then {} else t_scanned ts x),
             t_candNid := (\<lambda>x. if x = p then BOT else t_candNid ts x),
             t_candPid := (\<lambda>x. if x = p then BOT else t_candPid ts x),
             t_candTs := (\<lambda>x. if x = p then TOP else t_candTs ts x)\<rparr>"
        unfolding T_D2_EnterLoop_def by simp

      have no_top_p:
        "\<forall>nid v. (nid, v, TOP) \<notin> set (pools ts p)"
      proof (intro allI)
        fix nid v
        show "(nid, v, TOP) \<notin> set (pools ts p)"
        proof
          assume hin: "(nid, v, TOP) \<in> set (pools ts p)"
          then have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts p)"
            by blast
          from inv12 hex have "t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
            by blast
          then have "t_pc ts p = ''TE2''"
            by simp
          with pc_done show False
            by simp
        qed
      qed

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
        show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
            (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
          using inv1 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
            ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
          using inv2 ts'_def by simp

        show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
          using inv3 ts'_def by simp

        show "\<forall>q.
            t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
            t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (intro allI impI)
          fix q
          assume hpc: "t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
          show "t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
          proof (cases "q = p")
            case True
            from pc_done have "t_startTs ts p <\<^sub>t\<^sub>s TS (ts_counter ts)"
              using inv4 by blast
            with True ts'_def show ?thesis
              by simp
          next
            case False
            from False hpc ts'_def have hpc_old:
              "t_pc ts q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
              by simp
            from hpc_old have "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
              using inv4 by blast
            with False ts'_def show ?thesis
              by simp
          qed
        qed

        show "\<forall>pa.
            t_pc ts' pa = ''TE2'' \<longrightarrow>
            t_ts ts' pa \<noteq> TOP \<and>
            (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
        proof (intro allI impI)
          fix pa
          assume hpc': "t_pc ts' pa = ''TE2''"
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpc' eq ts'_def have "''TD_Loop'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          from hpc' pa_neq ts'_def have hpc: "t_pc ts pa = ''TE2''"
            by simp
          from inv5 hpc have "t_ts ts pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts pa, v, TOP) \<in> set (pools ts pa))"
            by blast
          with pa_neq ts'_def show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
            by simp
        qed

       show "\<forall>pa.
            t_pc ts' pa = ''TE3'' \<longrightarrow>
            t_ts ts' pa \<noteq> TOP"
          using inv6 ts'_def by simp

        show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
          using inv7 ts'_def by simp

        show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
            ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
            (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
          using inv8 ts'_def by simp

        show "BOT < t_V_var ts'"
          using inv9 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
            v < t_V_var ts'"
          using inv10 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
            nid < nid_counter ts'"
          using inv11 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
            t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        proof (intro allI impI)
          fix pa nid v ts_val
          assume htop:
            "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
          then have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
            by blast
          from htop have ts_top: "ts_val = TOP"
            by blast
          have pools_eq: "pools ts' pa = pools ts pa"
            using ts'_def by simp
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' pools_eq by simp
          show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
          proof (cases "pa = p")
            case True
            from mem ts_top True have "(nid, v, TOP) \<in> set (pools ts p)"
              by simp
            with no_top_p show ?thesis
              by blast
          next
            case False
            have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts pa)"
            proof -
              from mem ts_top have "(nid, v, TOP) \<in> set (pools ts pa)"
                by simp
              then show ?thesis
                by blast
            qed
            from inv12 hex have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
              by blast
            with False ts'_def show ?thesis
              by simp
          qed
        qed

        show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
            ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
            nid1 = nid2"
          using inv13 ts'_def by simp

        show "\<forall>pa q nid v ts_val.
            t_pc ts' pa = ''TE2'' \<and>
            (nid, v, ts_val) \<in> set (pools ts' q) \<and>
            ts_val \<noteq> TOP \<longrightarrow>
            t_ts ts' pa \<noteq> ts_val"
        proof (intro allI impI)
          fix pa q nid v ts_val
          assume h:
            "t_pc ts' pa = ''TE2'' \<and>
             (nid, v, ts_val) \<in> set (pools ts' q) \<and>
             ts_val \<noteq> TOP"
          then have hpc': "t_pc ts' pa = ''TE2''"
            and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
            and hneq: "ts_val \<noteq> TOP"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpc' eq ts'_def have "''TD_Loop'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          have hpc: "t_pc ts pa = ''TE2''"
            using hpc' pa_neq ts'_def by simp
          have pools_eq: "pools ts' q = pools ts q"
            using ts'_def by simp
          have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin' pools_eq by simp
          from hpc hin hneq have "t_ts ts pa \<noteq> ts_val"
            using inv14 by blast
          with pa_neq ts'_def show "t_ts ts' pa \<noteq> ts_val"
            by simp
        qed

        show "\<forall>pa q.
            t_pc ts' pa = ''TE2'' \<and>
            t_pc ts' q = ''TE2'' \<and>
            pa \<noteq> q \<longrightarrow>
            t_ts ts' pa \<noteq> t_ts ts' q"
        proof (intro allI impI)
          fix pa q
          assume h:
            "t_pc ts' pa = ''TE2'' \<and>
             t_pc ts' q = ''TE2'' \<and>
             pa \<noteq> q"
          then have hpa': "t_pc ts' pa = ''TE2''"
            and hq': "t_pc ts' q = ''TE2''"
            and neq: "pa \<noteq> q"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpa' eq ts'_def have "''TD_Loop'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          have q_neq: "q \<noteq> p"
          proof
            assume eq: "q = p"
            from hq' eq ts'_def have "''TD_Loop'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          have hpa: "t_pc ts pa = ''TE2''"
            using hpa' pa_neq ts'_def by simp
          have hq: "t_pc ts q = ''TE2''"
            using hq' q_neq ts'_def by simp
          from hpa hq neq have "t_ts ts pa \<noteq> t_ts ts q"
            using inv15 by blast
          with pa_neq q_neq ts'_def show "t_ts ts' pa \<noteq> t_ts ts' q"
            by simp
        qed

        show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
          using inv16 ts'_def by simp

        show "\<forall>pa.
            t_pc ts' pa = ''TE1'' \<longrightarrow>
            t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
          using inv17 ts'_def by simp

        show "\<forall>pa q nid v ts_val.
            t_pc ts' pa = ''TE1'' \<and>
            (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
            t_v ts' pa \<noteq> v"
        proof (intro allI impI)
          fix pa q nid v ts_val
          assume h:
            "t_pc ts' pa = ''TE1'' \<and>
             (nid, v, ts_val) \<in> set (pools ts' q)"
          then have hpc': "t_pc ts' pa = ''TE1''"
            and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpc' eq ts'_def have "''TD_Loop'' = ''TE1''"
              by simp
            then show False
              by simp
          qed
          have hpc: "t_pc ts pa = ''TE1''"
            using hpc' pa_neq ts'_def by simp
          have pools_eq: "pools ts' q = pools ts q"
            using ts'_def by simp
          have hin_old: "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin' pools_eq by simp
          have hex: "(\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q))"
          proof
            show "(nid, v, ts_val) \<in> set (pools ts q)"
              using hin_old .
          qed
          from hpc hex have "t_v ts pa \<noteq> v"
            using inv18 by blast
          with pa_neq ts'_def show "t_v ts' pa \<noteq> v"
            by simp
        qed

        show "\<forall>pa q.
            t_pc ts' pa = ''TE1'' \<and>
            t_pc ts' q = ''TE1'' \<and>
            pa \<noteq> q \<longrightarrow>
            t_v ts' pa \<noteq> t_v ts' q"
        proof (intro allI impI)
          fix pa q
          assume h:
            "t_pc ts' pa = ''TE1'' \<and>
             t_pc ts' q = ''TE1'' \<and>
             pa \<noteq> q"
          then have hpa': "t_pc ts' pa = ''TE1''"
            and hq': "t_pc ts' q = ''TE1''"
            and neq: "pa \<noteq> q"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpa' eq ts'_def have "''TD_Loop'' = ''TE1''"
              by simp
            then show False
              by simp
          qed
          have q_neq: "q \<noteq> p"
          proof
            assume eq: "q = p"
            from hq' eq ts'_def have "''TD_Loop'' = ''TE1''"
              by simp
            then show False
              by simp
          qed
          have hpa: "t_pc ts pa = ''TE1''"
            using hpa' pa_neq ts'_def by simp
          have hq: "t_pc ts q = ''TE1''"
            using hq' q_neq ts'_def by simp
          from hpa hq neq have "t_v ts pa \<noteq> t_v ts q"
            using inv19 by blast
          with pa_neq q_neq ts'_def show "t_v ts' pa \<noteq> t_v ts' q"
            by simp
        qed
        qed

show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    have hpc': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hmem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      using hpend by blast
    have hnz: "ts_val \<noteq> TOP"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpc' eq ts'_def show False
        by simp
    qed

    have hpc_old: "t_pc ts pa = ''TE2''"
      using hpc' pa_neq ts'_def by simp
    have hmem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
      using hmem' ts'_def by simp
    have tts_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tnid_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp

    have old_ord:
      "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
      using inv20 hpc_old hmem_old hnz by blast
    from old_ord tts_eq tnid_eq
    show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      by simp
  qed

  show "\<forall>pa q.
      t_pc ts' pa = ''TE2'' \<and>
      t_pc ts' q = ''TE2'' \<and>
      pa \<noteq> q \<longrightarrow>
      (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
  proof (intro allI impI)
    fix pa q
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       t_pc ts' q = ''TE2'' \<and>
       pa \<noteq> q"
    have hpa': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hq': "t_pc ts' q = ''TE2''"
      using hpend by blast
    have neq: "pa \<noteq> q"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpa' eq ts'_def show False
        by simp
    qed

    have q_neq: "q \<noteq> p"
    proof
      assume eq: "q = p"
      from hq' eq ts'_def show False
        by simp
    qed

    have hpa_old: "t_pc ts pa = ''TE2''"
      using hpa' pa_neq ts'_def by simp
    have hq_old: "t_pc ts q = ''TE2''"
      using hq' q_neq ts'_def by simp
    have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tts_q_eq: "t_ts ts' q = t_ts ts q"
      using ts'_def by simp
    have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp
    have tnid_q_eq: "t_nid ts' q = t_nid ts q"
      using ts'_def by simp

    have old_ord:
      "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
      using inv21 hpa_old hq_old neq by blast
    from old_ord tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
    show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      by simp
  qed
qed
qed
    next

      (* ==================================================== *)
      (* Case 7.2: T_D2_BackToD1                              *)
      (* Move p from TD_Line4_Done back to TD1. *)
      (* ==================================================== *)
      assume h2: "T_D2_BackToD1 p ts ts'"
      then have pc_done: "t_pc ts p = ''TD_Line4_Done''"
        unfolding T_D2_BackToD1_def by simp
      from h2 have ts'_def:
        "ts' = ts\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts x)\<rparr>"
        unfolding T_D2_BackToD1_def by simp

      have no_top_p:
        "\<forall>nid v. (nid, v, TOP) \<notin> set (pools ts p)"
      proof (intro allI)
        fix nid v
        show "(nid, v, TOP) \<notin> set (pools ts p)"
        proof
          assume hin: "(nid, v, TOP) \<in> set (pools ts p)"
          then have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts p)"
            by blast
          from inv12 hex have "t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
            by blast
          then have "t_pc ts p = ''TE2''"
            by simp
          with pc_done show False
            by simp
        qed
      qed

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
        show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
            (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
          using inv1 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
            ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
          using inv2 ts'_def by simp

        show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
          using inv3 ts'_def by simp

        show "\<forall>q.
            t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
            t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (intro allI impI)
          fix q
          assume hpc: "t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
          show "t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
          proof (cases "q = p")
            case True
            from hpc True ts'_def show ?thesis
              by simp
          next
            case False
            from False hpc ts'_def have hpc_old:
              "t_pc ts q = ''TD_Line4_Done'' \<or>
               t_pc ts q = ''TD_Loop'' \<or>
               t_pc ts q = ''TD_Remove_Done''"
              by simp
            have old_bd: "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
            proof (cases "t_pc ts q = ''TD_Line4_Done''")
              case True
              with inv4 show ?thesis
                by blast
            next
              case False1: False
              show ?thesis
              proof (cases "t_pc ts q = ''TD_Loop''")
                case True
                with inv4 show ?thesis
                  by blast
              next
                case False2: False
                from hpc_old False1 False2 have "t_pc ts q = ''TD_Remove_Done''"
                  by blast
                with inv4 show ?thesis
                  by blast
              qed
            qed
            from old_bd False ts'_def show ?thesis
              by simp
          qed
        qed

        show "\<forall>pa.
            t_pc ts' pa = ''TE2'' \<longrightarrow>
            t_ts ts' pa \<noteq> TOP \<and>
            (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
        proof (intro allI impI)
          fix pa
          assume hpc': "t_pc ts' pa = ''TE2''"
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpc' eq ts'_def have "''TD1'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          from hpc' pa_neq ts'_def have hpc: "t_pc ts pa = ''TE2''"
            by simp
          from inv5 hpc have "t_ts ts pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts pa, v, TOP) \<in> set (pools ts pa))"
            by blast
          with pa_neq ts'_def show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
            by simp
        qed

       show "\<forall>pa.
            t_pc ts' pa = ''TE3'' \<longrightarrow>
            t_ts ts' pa \<noteq> TOP"
          using inv6 ts'_def by simp

        show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
          using inv7 ts'_def by simp

        show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
            ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
            (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
          using inv8 ts'_def by simp

        show "BOT < t_V_var ts'"
          using inv9 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
            v < t_V_var ts'"
          using inv10 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
            nid < nid_counter ts'"
          using inv11 ts'_def by simp

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
            t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        proof (intro allI impI)
          fix pa nid v ts_val
          assume htop:
            "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
          then have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
            by blast
          from htop have ts_top: "ts_val = TOP"
            by blast
          have pools_eq: "pools ts' pa = pools ts pa"
            using ts'_def by simp
          have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
            using mem' pools_eq by simp
          show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
          proof (cases "pa = p")
            case True
            from mem ts_top True have "(nid, v, TOP) \<in> set (pools ts p)"
              by simp
            with no_top_p show ?thesis
              by blast
          next
            case False
            have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts pa)"
            proof -
              from mem ts_top have "(nid, v, TOP) \<in> set (pools ts pa)"
                by simp
              then show ?thesis
                by blast
            qed
            from inv12 hex have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
              by blast
            with False ts'_def show ?thesis
              by simp
          qed
        qed

        show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
            ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
            nid1 = nid2"
          using inv13 ts'_def by simp

        show "\<forall>pa q nid v ts_val.
            t_pc ts' pa = ''TE2'' \<and>
            (nid, v, ts_val) \<in> set (pools ts' q) \<and>
            ts_val \<noteq> TOP \<longrightarrow>
            t_ts ts' pa \<noteq> ts_val"
        proof (intro allI impI)
          fix pa q nid v ts_val
          assume h:
            "t_pc ts' pa = ''TE2'' \<and>
             (nid, v, ts_val) \<in> set (pools ts' q) \<and>
             ts_val \<noteq> TOP"
          then have hpc': "t_pc ts' pa = ''TE2''"
            and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
            and hneq: "ts_val \<noteq> TOP"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpc' eq ts'_def have "''TD1'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          have hpc: "t_pc ts pa = ''TE2''"
            using hpc' pa_neq ts'_def by simp
          have pools_eq: "pools ts' q = pools ts q"
            using ts'_def by simp
          have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin' pools_eq by simp
          from hpc hin hneq have "t_ts ts pa \<noteq> ts_val"
            using inv14 by blast
          with pa_neq ts'_def show "t_ts ts' pa \<noteq> ts_val"
            by simp
        qed

        show "\<forall>pa q.
            t_pc ts' pa = ''TE2'' \<and>
            t_pc ts' q = ''TE2'' \<and>
            pa \<noteq> q \<longrightarrow>
            t_ts ts' pa \<noteq> t_ts ts' q"
        proof (intro allI impI)
          fix pa q
          assume h:
            "t_pc ts' pa = ''TE2'' \<and>
             t_pc ts' q = ''TE2'' \<and>
             pa \<noteq> q"
          then have hpa': "t_pc ts' pa = ''TE2''"
            and hq': "t_pc ts' q = ''TE2''"
            and neq: "pa \<noteq> q"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpa' eq ts'_def have "''TD1'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          have q_neq: "q \<noteq> p"
          proof
            assume eq: "q = p"
            from hq' eq ts'_def have "''TD1'' = ''TE2''"
              by simp
            then show False
              by simp
          qed
          have hpa: "t_pc ts pa = ''TE2''"
            using hpa' pa_neq ts'_def by simp
          have hq: "t_pc ts q = ''TE2''"
            using hq' q_neq ts'_def by simp
          from hpa hq neq have "t_ts ts pa \<noteq> t_ts ts q"
            using inv15 by blast
          with pa_neq q_neq ts'_def show "t_ts ts' pa \<noteq> t_ts ts' q"
            by simp
        qed

        show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
          using inv16 ts'_def by simp

        show "\<forall>pa.
            t_pc ts' pa = ''TE1'' \<longrightarrow>
            t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
          using inv17 ts'_def by simp

        show "\<forall>pa q nid v ts_val.
            t_pc ts' pa = ''TE1'' \<and>
            (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
            t_v ts' pa \<noteq> v"
        proof (intro allI impI)
          fix pa q nid v ts_val
          assume h:
            "t_pc ts' pa = ''TE1'' \<and>
             (nid, v, ts_val) \<in> set (pools ts' q)"
          then have hpc': "t_pc ts' pa = ''TE1''"
            and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpc' eq ts'_def have "''TD1'' = ''TE1''"
              by simp
            then show False
              by simp
          qed
          have hpc: "t_pc ts pa = ''TE1''"
            using hpc' pa_neq ts'_def by simp
          have pools_eq: "pools ts' q = pools ts q"
            using ts'_def by simp
          have hin_old: "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin' pools_eq by simp
          have hex: "(\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q))"
          proof
            show "(nid, v, ts_val) \<in> set (pools ts q)"
              using hin_old .
          qed
          from hpc hex have "t_v ts pa \<noteq> v"
            using inv18 by blast
          with pa_neq ts'_def show "t_v ts' pa \<noteq> v"
            by simp
        qed

        show "\<forall>pa q.
            t_pc ts' pa = ''TE1'' \<and>
            t_pc ts' q = ''TE1'' \<and>
            pa \<noteq> q \<longrightarrow>
            t_v ts' pa \<noteq> t_v ts' q"
        proof (intro allI impI)
          fix pa q
          assume h:
            "t_pc ts' pa = ''TE1'' \<and>
             t_pc ts' q = ''TE1'' \<and>
             pa \<noteq> q"
          then have hpa': "t_pc ts' pa = ''TE1''"
            and hq': "t_pc ts' q = ''TE1''"
            and neq: "pa \<noteq> q"
            by simp_all
          have pa_neq: "pa \<noteq> p"
          proof
            assume eq: "pa = p"
            from hpa' eq ts'_def have "''TD1'' = ''TE1''"
              by simp
            then show False
              by simp
          qed
          have q_neq: "q \<noteq> p"
          proof
            assume eq: "q = p"
            from hq' eq ts'_def have "''TD1'' = ''TE1''"
              by simp
            then show False
              by simp
          qed
          have hpa: "t_pc ts pa = ''TE1''"
            using hpa' pa_neq ts'_def by simp
          have hq: "t_pc ts q = ''TE1''"
            using hq' q_neq ts'_def by simp
          from hpa hq neq have "t_v ts pa \<noteq> t_v ts q"
            using inv19 by blast
          with pa_neq q_neq ts'_def show "t_v ts' pa \<noteq> t_v ts' q"
            by simp
        qed
      qed

 show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    have hpc': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hmem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      using hpend by blast
    have hnz: "ts_val \<noteq> TOP"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpc' eq ts'_def show False
        by simp
    qed

    have hpc_old: "t_pc ts pa = ''TE2''"
      using hpc' pa_neq ts'_def by simp
    have hmem_old: "(nid, v, ts_val) \<in> set (pools ts q)"
      using hmem' ts'_def by simp
    have tts_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tnid_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp

    have old_ord:
      "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
      using inv20 hpc_old hmem_old hnz by blast
    from old_ord tts_eq tnid_eq
    show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      by simp
  qed

  show "\<forall>pa q.
      t_pc ts' pa = ''TE2'' \<and>
      t_pc ts' q = ''TE2'' \<and>
      pa \<noteq> q \<longrightarrow>
      (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
  proof (intro allI impI)
    fix pa q
    assume hpend:
      "t_pc ts' pa = ''TE2'' \<and>
       t_pc ts' q = ''TE2'' \<and>
       pa \<noteq> q"
    have hpa': "t_pc ts' pa = ''TE2''"
      using hpend by blast
    have hq': "t_pc ts' q = ''TE2''"
      using hpend by blast
    have neq: "pa \<noteq> q"
      using hpend by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpa' eq ts'_def show False
        by simp
    qed

    have q_neq: "q \<noteq> p"
    proof
      assume eq: "q = p"
      from hq' eq ts'_def show False
        by simp
    qed

    have hpa_old: "t_pc ts pa = ''TE2''"
      using hpa' pa_neq ts'_def by simp
    have hq_old: "t_pc ts q = ''TE2''"
      using hq' q_neq ts'_def by simp
    have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
      using ts'_def by simp
    have tts_q_eq: "t_ts ts' q = t_ts ts q"
      using ts'_def by simp
    have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
      using ts'_def by simp
    have tnid_q_eq: "t_nid ts' q = t_nid ts q"
      using ts'_def by simp

    have old_ord:
      "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
      using inv21 hpa_old hq_old neq by blast
    from old_ord tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
    show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      by simp
  qed
qed
qed
qed

  next

    (* ====================================================== *)
    (* Case 8: T_D3                                           *)
    (* This is the heaviest branch: one-step scan / stuttering / Scan* followed by Eval. *)
    (* ====================================================== *)
    assume h: "T_D3 p ts ts'"
    then show ?thesis
    proof (unfold T_D3_def, elim conjE disjE exE)
      assume loop_pc: "t_pc ts p = ''TD_Loop''"
      fix k
      assume scan: "T_D3_Scan p k ts ts'"

      from scan have pc_loop: "t_pc ts p = ''TD_Loop''"
        unfolding T_D3_Scan_def by simp

      from scan have ts'_def:
        "(case pool_getOldest (pools ts k) of
           (nid, tstamp) =>
             ts' =
             ts\<lparr> t_candNid :=
                    (\<lambda>x. if x = p then
                           (if nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s t_candTs ts p \<and> \<not> t_startTs ts p <\<^sub>t\<^sub>s tstamp
                            then nid else t_candNid ts p)
                         else t_candNid ts x),
                  t_candTs :=
                    (\<lambda>x. if x = p then
                           (if nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s t_candTs ts p \<and> \<not> t_startTs ts p <\<^sub>t\<^sub>s tstamp
                            then tstamp else t_candTs ts p)
                         else t_candTs ts x),
                  t_candPid :=
                    (\<lambda>x. if x = p then
                           (if nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s t_candTs ts p \<and> \<not> t_startTs ts p <\<^sub>t\<^sub>s tstamp
                            then k else t_candPid ts p)
                         else t_candPid ts x),
                  t_scanned := (\<lambda>x. if x = p then t_scanned ts p \<union> {k} else t_scanned ts x)\<rparr>)"
        unfolding T_D3_Scan_def by auto

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
        show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
            (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
          using inv1 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
            ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
          using inv2 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
          using inv3 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>q.
            t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
            t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
          using inv4 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa.
            t_pc ts' pa = ''TE2'' \<longrightarrow>
            t_ts ts' pa \<noteq> TOP \<and>
            (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
          using inv5 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa.
            t_pc ts' pa = ''TE3'' \<longrightarrow>
            t_ts ts' pa \<noteq> TOP"
          using inv6 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
        proof
          fix pa
          show "t_scanned ts' pa \<subseteq> ProcSet"
          proof (cases "pa = p")
            case True
            have k_in: "k \<in> ProcSet"
              using scan unfolding T_D3_Scan_def by auto
            have old_sub: "t_scanned ts p \<subseteq> ProcSet"
              using inv7 by blast
            have scanned_eq: "t_scanned ts' pa = t_scanned ts p \<union> {k}"
              using True ts'_def by (simp split: prod.splits if_splits)
            show ?thesis
            proof
              fix x
              assume xin: "x \<in> t_scanned ts' pa"
              from xin scanned_eq have "x \<in> t_scanned ts p \<or> x = k"
                by blast
              then show "x \<in> ProcSet"
                using old_sub k_in by blast
            qed
          next
            case False
            then show ?thesis
              using inv7 ts'_def by (simp split: prod.splits if_splits)
          qed
        qed

        show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
            ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
            (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
          using inv8 ts'_def
          by (simp split: prod.splits if_splits)

        show "BOT < t_V_var ts'"
          using inv9 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
            v < t_V_var ts'"
          using inv10 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
            nid < nid_counter ts'"
          using inv11 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa nid v ts_val.
            (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
            t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
          using inv12 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
            (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
            (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
            ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
            nid1 = nid2"
          using inv13 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa q nid v ts_val.
            t_pc ts' pa = ''TE2'' \<and>
            (nid, v, ts_val) \<in> set (pools ts' q) \<and>
            ts_val \<noteq> TOP \<longrightarrow>
            t_ts ts' pa \<noteq> ts_val"
          using inv14 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa q.
            t_pc ts' pa = ''TE2'' \<and>
            t_pc ts' q = ''TE2'' \<and>
            pa \<noteq> q \<longrightarrow>
            t_ts ts' pa \<noteq> t_ts ts' q"
          using inv15 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
          using inv16 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa.
            t_pc ts' pa = ''TE1'' \<longrightarrow>
            t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
          using inv17 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa q nid v ts_val.
            t_pc ts' pa = ''TE1'' \<and>
            (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
            t_v ts' pa \<noteq> v"
          using inv18 ts'_def
          by (simp split: prod.splits if_splits)

        show "\<forall>pa q.
            t_pc ts' pa = ''TE1'' \<and>
            t_pc ts' q = ''TE1'' \<and>
            pa \<noteq> q \<longrightarrow>
            t_v ts' pa \<noteq> t_v ts' q"
          using inv19 ts'_def
          by (simp split: prod.splits if_splits)
      qed
    show "TE2_Pending_Order ts'"
    using inv_pending ts'_def
    unfolding TE2_Pending_Order_def
    by (simp split: prod.splits if_splits)
qed

    next
      assume loop_pc: "t_pc ts p = ''TD_Loop''"
      assume idle: "ts' = ts"

have "TSQ_State_Inv_Plus ts'"
  using assms(1) idle by simp
then show ?thesis .

    next
      assume loop_pc: "t_pc ts p = ''TD_Loop''"
      fix ts_mid
      assume star: "T_D3_Scan_Star p ts ts_mid"
      assume scanned_full: "t_scanned ts_mid p = ProcSet"
      assume eval: "T_D3_Eval p ts_mid ts'"

      have eval_cases:
        "t_pc ts_mid p = ''TD_Loop'' \<and>
         t_scanned ts_mid p = ProcSet"
        using eval unfolding T_D3_Eval_def by auto

      (* ---------------------------------------------------- *)
      (* This is the heaviest macro-step branch for D3. *)
      (* First prove that Scan_Star preserves TSQ_State_Inv. *)
      (* Then analyze the three outcomes of Eval separately: *)
      (*   1) cNid = BOT        -> return to TD1 *)
      (*   2) cNid \<noteq> BOT but remove fails -> return to TD1 *)
      (*   3) cNid \<noteq> BOT and remove succeeds -> move to TD_Remove_Done *)
      (* The first two outcomes mostly change control fields, whereas the third one actually updates the pools. *)
      (* ---------------------------------------------------- *)

      have scan_preserve:
        "\<And>s s' k. TSQ_State_Inv s \<Longrightarrow> T_D3_Scan p k s s' \<Longrightarrow> TSQ_State_Inv s'"
      proof -
        fix s s' k
        assume invs: "TSQ_State_Inv s"
        assume step_scan: "T_D3_Scan p k s s'"

        obtain nid tstamp where oldest_eq:
          "pool_getOldest (pools s k) = (nid, tstamp)"
          by force

        from step_scan have k_in: "k \<in> ProcSet"
          unfolding T_D3_Scan_def by auto

        from step_scan have s'_def:
          "s' =
            s\<lparr> t_candNid :=
                  (\<lambda>x. if x = p then
                         (if nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s t_candTs s p \<and> \<not> t_startTs s p <\<^sub>t\<^sub>s tstamp
                          then nid else t_candNid s p)
                       else t_candNid s x),
                t_candTs :=
                  (\<lambda>x. if x = p then
                         (if nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s t_candTs s p \<and> \<not> t_startTs s p <\<^sub>t\<^sub>s tstamp
                          then tstamp else t_candTs s p)
                       else t_candTs s x),
                t_candPid :=
                  (\<lambda>x. if x = p then
                         (if nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s t_candTs s p \<and> \<not> t_startTs s p <\<^sub>t\<^sub>s tstamp
                          then k else t_candPid s p)
                       else t_candPid s x),
                t_scanned := (\<lambda>x. if x = p then t_scanned s p \<union> {k} else t_scanned s x)\<rparr>"
          unfolding T_D3_Scan_def Let_def oldest_eq
          by auto

        show "TSQ_State_Inv s'"
          unfolding TSQ_State_Inv_def
        proof (intro conjI)
          show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
              (nid1, v1, ts1) \<in> set (pools s' pa) \<and> (nid2, v2, ts2) \<in> set (pools s' q) \<longrightarrow>
              (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa nid v ts_val.
              (nid, v, ts_val) \<in> set (pools s' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
              ts_val <\<^sub>t\<^sub>s TS (ts_counter s')"
          proof (intro allI impI)
            fix pa nid v ts_val
            assume hmem: "(nid, v, ts_val) \<in> set (pools s' pa) \<and> ts_val \<noteq> TOP"
            have mem_old: "(nid, v, ts_val) \<in> set (pools s pa)"
              using hmem s'_def by simp
            have nz: "ts_val \<noteq> TOP"
              using hmem by simp
            have bound_rule:
              "\<forall>p nid v ts_val.
                 (nid, v, ts_val) \<in> set (pools s p) \<and> ts_val \<noteq> TOP \<longrightarrow>
                 ts_val <\<^sub>t\<^sub>s TS (ts_counter s)"
              using invs
              unfolding TSQ_State_Inv_def
              apply (elim conjE)
              apply assumption
              done
            have "ts_val <\<^sub>t\<^sub>s TS (ts_counter s)"
              using bound_rule mem_old nz by blast
            with s'_def show "ts_val <\<^sub>t\<^sub>s TS (ts_counter s')"
              by simp
          qed

          show "\<forall>pa. t_ts s' pa \<noteq> TOP \<longrightarrow> t_ts s' pa <\<^sub>t\<^sub>s TS (ts_counter s')"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>q.
              t_pc s' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
              t_startTs s' q <\<^sub>t\<^sub>s TS (ts_counter s')"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa.
              t_pc s' pa = ''TE2'' \<longrightarrow>
              t_ts s' pa \<noteq> TOP \<and>
              (\<exists>v. (t_nid s' pa, v, TOP) \<in> set (pools s' pa))"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

         show "\<forall>pa.
              t_pc s' pa = ''TE3'' \<longrightarrow>
              t_ts s' pa \<noteq> TOP"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa. t_scanned s' pa \<subseteq> ProcSet"
          proof
            fix pa
            show "t_scanned s' pa \<subseteq> ProcSet"
            proof (cases "pa = p")
              case True
              have old_sub: "t_scanned s p \<subseteq> ProcSet"
                using invs unfolding TSQ_State_Inv_def by simp
              have eq_scanned: "t_scanned s' pa = t_scanned s p \<union> {k}"
                using True s'_def by simp
              show ?thesis
              proof
                fix x
                assume xin: "x \<in> t_scanned s' pa"
                from xin eq_scanned have "x \<in> t_scanned s p \<or> x = k"
                  by blast
                then show "x \<in> ProcSet"
                  using old_sub k_in by blast
              qed
            next
              case False
              then show ?thesis
                using invs s'_def unfolding TSQ_State_Inv_def by simp
            qed
          qed

         show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
              (nid1, v1, ts1) \<in> set (pools s' pa) \<and>
              (nid2, v2, ts2) \<in> set (pools s' qa) \<and>
              ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
              (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
          proof -
            have old_inv8:
              "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
                  (nid1, v1, ts1) \<in> set (pools s pa) \<and>
                  (nid2, v2, ts2) \<in> set (pools s qa) \<and>
                  ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
                  (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
              using invs
              unfolding TSQ_State_Inv_def
              apply (elim conjE)
              apply assumption
              done
            then show ?thesis
              using s'_def by simp
          qed
          show "BOT < t_V_var s'"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa nid v ts_val.
              (nid, v, ts_val) \<in> set (pools s' pa) \<longrightarrow>
              v < t_V_var s'"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa nid v ts_val.
              (nid, v, ts_val) \<in> set (pools s' pa) \<longrightarrow>
              nid < nid_counter s'"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa nid v ts_val.
              (nid, v, ts_val) \<in> set (pools s' pa) \<and> ts_val = TOP \<longrightarrow>
              t_pc s' pa = ''TE2'' \<and> nid = t_nid s' pa"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
              (nid1, v1, ts1) \<in> set (pools s' pa) \<and>
              (nid2, v2, ts2) \<in> set (pools s' q) \<and>
              ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
              nid1 = nid2"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa q nid v ts_val.
              t_pc s' pa = ''TE2'' \<and>
              (nid, v, ts_val) \<in> set (pools s' q) \<and>
              ts_val \<noteq> TOP \<longrightarrow>
              t_ts s' pa \<noteq> ts_val"
          proof (intro allI impI)
            fix pa q nid0 v0 ts_val
            assume h:
              "t_pc s' pa = ''TE2'' \<and>
               (nid0, v0, ts_val) \<in> set (pools s' q) \<and>
               ts_val \<noteq> TOP"
            have hpc': "t_pc s' pa = ''TE2''"
              using h by blast
            have mem': "(nid0, v0, ts_val) \<in> set (pools s' q)"
              using h by blast
            have nz: "ts_val \<noteq> TOP"
              using h by blast

            have hpc0: "t_pc s pa = ''TE2''"
              using hpc' s'_def by simp
            have mem_old: "(nid0, v0, ts_val) \<in> set (pools s q)"
              using mem' s'_def by simp

            have neq_rule:
              "\<forall>p q nid v ts_val.
                 t_pc s p = ''TE2'' \<and>
                 (nid, v, ts_val) \<in> set (pools s q) \<and>
                 ts_val \<noteq> TOP \<longrightarrow>
                 t_ts s p \<noteq> ts_val"
              using invs
              unfolding TSQ_State_Inv_def
              apply (elim conjE)
              apply assumption
              done

            have old_neq: "t_ts s pa \<noteq> ts_val"
              using neq_rule hpc0 mem_old nz by blast

            with s'_def show "t_ts s' pa \<noteq> ts_val"
              by simp
          qed

          show "\<forall>pa q.
              t_pc s' pa = ''TE2'' \<and>
              t_pc s' q = ''TE2'' \<and>
              pa \<noteq> q \<longrightarrow>
              t_ts s' pa \<noteq> t_ts s' q"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa. sorted (map fst (pools s' pa)) \<and> distinct (map fst (pools s' pa))"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa.
              t_pc s' pa = ''TE1'' \<longrightarrow>
              t_v s' pa \<noteq> BOT \<and> t_v s' pa < t_V_var s'"
            using invs s'_def unfolding TSQ_State_Inv_def by simp

          show "\<forall>pa q nid v ts_val.
              t_pc s' pa = ''TE1'' \<and>
              (nid, v, ts_val) \<in> set (pools s' q) \<longrightarrow>
              t_v s' pa \<noteq> v"
          proof (intro allI impI)
            fix pa q nid0 v0 ts_val
            assume h:
              "t_pc s' pa = ''TE1'' \<and>
               (nid0, v0, ts_val) \<in> set (pools s' q)"
            have hpc': "t_pc s' pa = ''TE1''"
              using h by blast
            have mem': "(nid0, v0, ts_val) \<in> set (pools s' q)"
              using h by blast

            have hpc0: "t_pc s pa = ''TE1''"
              using hpc' s'_def by simp
            have mem_old: "(nid0, v0, ts_val) \<in> set (pools s q)"
              using mem' s'_def by simp

            have neq_rule:
              "\<forall>p q nid v ts_val.
                 t_pc s p = ''TE1'' \<and>
                 (nid, v, ts_val) \<in> set (pools s q) \<longrightarrow>
                 t_v s p \<noteq> v"
              using invs
              unfolding TSQ_State_Inv_def
              apply (elim conjE)
              apply assumption
              done

            have old_neq: "t_v s pa \<noteq> v0"
              using neq_rule hpc0 mem_old by blast

            with s'_def show "t_v s' pa \<noteq> v0"
              by simp
          qed

          show "\<forall>pa q.
              t_pc s' pa = ''TE1'' \<and>
              t_pc s' q = ''TE1'' \<and>
              pa \<noteq> q \<longrightarrow>
              t_v s' pa \<noteq> t_v s' q"
            using invs s'_def unfolding TSQ_State_Inv_def by simp
        qed
      qed

have scan_preserve_gen:
  "T_D3_Scan q k s s' \<Longrightarrow> q = p \<longrightarrow> TSQ_State_Inv s \<longrightarrow> TSQ_State_Inv s'" for q k s s'
  using scan_preserve by metis

have scan_plus_preserve:
  "T_D3_Scan p k s s' \<Longrightarrow> TSQ_State_Inv_Plus s \<Longrightarrow> TSQ_State_Inv_Plus s'" for k s s'
proof -
  assume scan: "T_D3_Scan p k s s'"
  assume invs: "TSQ_State_Inv_Plus s"

  have inv_plain: "TSQ_State_Inv s"
    using TSQ_State_Inv_PlusD_plain[OF invs] .

  have inv_pending: "TE2_Pending_Order s"
    using TSQ_State_Inv_PlusD_pending[OF invs] .

  have plain_preserved: "TSQ_State_Inv s'"
    using scan_preserve_gen[OF scan] inv_plain by simp

  have pending_preserved: "TE2_Pending_Order s'"
    using inv_pending scan
    unfolding TE2_Pending_Order_def T_D3_Scan_def Let_def
    by (auto split: prod.splits if_splits)

  show "TSQ_State_Inv_Plus s'"
    unfolding TSQ_State_Inv_Plus_def
    using plain_preserved pending_preserved by simp
qed

have scan_star_preserve_gen:
  "T_D3_Scan_Star q a b \<Longrightarrow> q = p \<longrightarrow> TSQ_State_Inv_Plus a \<longrightarrow> TSQ_State_Inv_Plus b" for q a b
  apply (erule T_D3_Scan_Star.induct)
   apply simp
  apply (intro impI)
  using scan_plus_preserve
  by metis

have scan_star_preserve:
  "T_D3_Scan_Star p a b \<Longrightarrow> TSQ_State_Inv_Plus a \<longrightarrow> TSQ_State_Inv_Plus b" for a b
  using scan_star_preserve_gen by blast

have inv_mid_plus: "TSQ_State_Inv_Plus ts_mid"
  using scan_star_preserve[OF star] assms(1) by blast
      
      have inv_mid: "TSQ_State_Inv ts_mid"
        using TSQ_State_Inv_PlusD_plain[OF inv_mid_plus] .
      
      have inv_mid_pending: "TE2_Pending_Order ts_mid"
        using TSQ_State_Inv_PlusD_pending[OF inv_mid_plus] .
      
      have loop_mid: "t_pc ts_mid p = ''TD_Loop''"
        using eval unfolding T_D3_Eval_def by auto
      
      have scanned_mid: "t_scanned ts_mid p = ProcSet"
        using eval unfolding T_D3_Eval_def by auto
         have td1_preserve:
        "ts' = ts_mid\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts_mid x)\<rparr> \<Longrightarrow>
         t_pc ts_mid p = ''TD_Loop'' \<Longrightarrow>
         TSQ_State_Inv_Plus ts'"
      proof -
        assume ts'_def_eval: "ts' = ts_mid\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts_mid x)\<rparr>"
        assume pc_loop_mid: "t_pc ts_mid p = ''TD_Loop''"
        show "TSQ_State_Inv_Plus ts'"
          unfolding TSQ_State_Inv_Plus_def
        proof
          show "TSQ_State_Inv ts'"
            unfolding TSQ_State_Inv_def
          proof (intro conjI)
            show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
                (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
                (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa nid v ts_val.
                (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
                ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
            proof (intro allI impI)
              fix pa nid v ts_val
              assume hmem: "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP"
              have mem_old: "(nid, v, ts_val) \<in> set (pools ts_mid pa)"
                using hmem ts'_def_eval by simp
              have nz: "ts_val \<noteq> TOP"
                using hmem by simp
              have bound_rule:
                "\<forall>p nid v ts_val.
                   (nid, v, ts_val) \<in> set (pools ts_mid p) \<and> ts_val \<noteq> TOP \<longrightarrow>
                   ts_val <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                using inv_mid
                unfolding TSQ_State_Inv_def
                apply (elim conjE)
                apply assumption
                done
              have "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                using bound_rule mem_old nz by blast
              with ts'_def_eval show "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
                by simp
            qed

            show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>q.
                t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
                t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
            proof (intro allI impI)
              fix q
              assume hpc': "t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
              show "t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
              proof (cases "q = p")
                case True
                then have "t_pc ts' q = ''TD1''"
                  using ts'_def_eval by simp
                with hpc' show ?thesis
                  by simp
              next
                case False
                have hpc_mid: "t_pc ts_mid q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
                  using hpc' False ts'_def_eval by simp
                have inv4_mid:
                  "\<forall>q. t_pc ts_mid q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
                       t_startTs ts_mid q <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                  using inv_mid
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  apply assumption
                  done
                have start_old: "t_startTs ts_mid q <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                  using inv4_mid hpc_mid by blast
                from start_old False ts'_def_eval show ?thesis
                  by simp
              qed
            qed

            show "\<forall>pa.
                t_pc ts' pa = ''TE2'' \<longrightarrow>
                t_ts ts' pa \<noteq> TOP \<and>
                (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa.
                t_pc ts' pa = ''TE3'' \<longrightarrow>
                t_ts ts' pa \<noteq> TOP"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp
          
            show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
                (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
                ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
                (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
            proof -
              have old_inv8:
                "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
                    (nid1, v1, ts1) \<in> set (pools ts_mid pa) \<and>
                    (nid2, v2, ts2) \<in> set (pools ts_mid qa) \<and>
                    ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
                    (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
                using inv_mid
                unfolding TSQ_State_Inv_def
                apply (elim conjE)
                apply assumption
                done
              then show ?thesis
                using ts'_def_eval by simp
            qed

            show "BOT < t_V_var ts'"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa nid v ts_val.
                (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
                v < t_V_var ts'"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa nid v ts_val.
                (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
                nid < nid_counter ts'"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa nid v ts_val.
                (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
                t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
            proof (intro allI impI)
              fix pa nid v ts_val
              assume htop: "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
              have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
                using htop by blast
              have top: "ts_val = TOP"
                using htop by blast
              show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
              proof (cases "pa = p")
                case True
                have pools_eq: "pools ts' p = pools ts_mid p"
                  using ts'_def_eval by simp
                have mem_old: "(nid, v, ts_val) \<in> set (pools ts_mid p)"
                  using mem' True pools_eq by simp
                have inv12_mid:
                  "\<forall>p nid. (\<exists>v. (nid, v, TOP) \<in> set (pools ts_mid p)) \<longrightarrow>
                           t_pc ts_mid p = ''TE2'' \<and> nid = t_nid ts_mid p"
                proof -
                  have H:
                    "\<forall>p nid. (\<exists>v. (nid, v, TOP) \<in> set (pools ts_mid p)) \<longrightarrow>
                             t_pc ts_mid p = ''TE2'' \<and> nid = t_nid ts_mid p"
                    using inv_mid unfolding TSQ_State_Inv_def by simp
                  from H show ?thesis .
                qed
                have hex: "\<exists>v. (nid, v, TOP) \<in> set (pools ts_mid p)"
                  using mem_old top by auto
                from inv12_mid hex have "t_pc ts_mid p = ''TE2''"
                  by blast
                with pc_loop_mid show ?thesis
                  using True by simp
              next
                case False
                have mem_old: "(nid, v, ts_val) \<in> set (pools ts_mid pa)"
                  using mem' False ts'_def_eval by simp
                have inv12_mid:
                  "\<forall>p nid. (\<exists>v. (nid, v, TOP) \<in> set (pools ts_mid p)) \<longrightarrow>
                           t_pc ts_mid p = ''TE2'' \<and> nid = t_nid ts_mid p"
                proof -
                  have H:
                    "\<forall>p nid. (\<exists>v. (nid, v, TOP) \<in> set (pools ts_mid p)) \<longrightarrow>
                             t_pc ts_mid p = ''TE2'' \<and> nid = t_nid ts_mid p"
                    using inv_mid unfolding TSQ_State_Inv_def by simp
                  from H show ?thesis .
                qed
                have hex: "\<exists>v. (nid, v, TOP) \<in> set (pools ts_mid pa)"
                  using mem_old top by auto
                have mid_res: "t_pc ts_mid pa = ''TE2'' \<and> nid = t_nid ts_mid pa"
                  using inv12_mid hex by blast
                from mid_res False ts'_def_eval show ?thesis
                  by simp
              qed
            qed

            show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
                (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
                ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
                nid1 = nid2"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa q nid v ts_val.
                t_pc ts' pa = ''TE2'' \<and>
                (nid, v, ts_val) \<in> set (pools ts' q) \<and>
                ts_val \<noteq> TOP \<longrightarrow>
                t_ts ts' pa \<noteq> ts_val"
            proof (intro allI impI)
              fix pa q nid v ts_val
              assume h:
                "t_pc ts' pa = ''TE2'' \<and>
                 (nid, v, ts_val) \<in> set (pools ts' q) \<and>
                 ts_val \<noteq> TOP"
              have hpc': "t_pc ts' pa = ''TE2''"
                using h by blast
              show "t_ts ts' pa \<noteq> ts_val"
              proof (cases "pa = p")
                case True
                then have "t_pc ts' pa = ''TD1''"
                  using ts'_def_eval by simp
                with hpc' show ?thesis
                  by simp
              next
                case False
                have hpc_mid: "t_pc ts_mid pa = ''TE2''"
                  using hpc' False ts'_def_eval by simp
                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid q)"
                  using h False ts'_def_eval by simp
                have nz: "ts_val \<noteq> TOP"
                  using h by blast
                have old_neq: "t_ts ts_mid pa \<noteq> ts_val"
                proof
                  assume eq: "t_ts ts_mid pa = ts_val"
                  from inv_mid have
                    "\<forall>p q nid v ts_val.
                       t_pc ts_mid p = ''TE2'' \<and>
                       (nid, v, ts_val) \<in> set (pools ts_mid q) \<and>
                       ts_val \<noteq> TOP \<longrightarrow>
                       t_ts ts_mid p \<noteq> ts_val"
                    unfolding TSQ_State_Inv_def
                    by blast
                  then have "t_ts ts_mid pa \<noteq> ts_val"
                    using hpc_mid mem_mid nz by blast
                  with eq show False
                    by simp
                qed
                from old_neq False ts'_def_eval show ?thesis
                  by simp
              qed
            qed

            show "\<forall>pa q.
                t_pc ts' pa = ''TE2'' \<and>
                t_pc ts' q = ''TE2'' \<and>
                pa \<noteq> q \<longrightarrow>
                t_ts ts' pa \<noteq> t_ts ts' q"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa.
                t_pc ts' pa = ''TE1'' \<longrightarrow>
                t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
              using inv_mid ts'_def_eval unfolding TSQ_State_Inv_def by simp

            show "\<forall>pa q nid v ts_val.
                t_pc ts' pa = ''TE1'' \<and>
                (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
                t_v ts' pa \<noteq> v"
            proof (intro allI impI)
              fix pa q nid v ts_val
              assume h:
                "t_pc ts' pa = ''TE1'' \<and>
                 (nid, v, ts_val) \<in> set (pools ts' q)"
              have hpc': "t_pc ts' pa = ''TE1''"
                using h by blast
              show "t_v ts' pa \<noteq> v"
              proof (cases "pa = p")
                case True
                then have "t_pc ts' pa = ''TD1''"
                  using ts'_def_eval by simp
                with hpc' show ?thesis
                  by simp
              next
                case False
                have hpc_mid: "t_pc ts_mid pa = ''TE1''"
                  using hpc' False ts'_def_eval by simp
                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid q)"
                  using h False ts'_def_eval by simp
                have old_neq: "t_v ts_mid pa \<noteq> v"
                proof
                  assume eq: "t_v ts_mid pa = v"
                  from inv_mid have
                    "\<forall>p q nid v ts_val.
                       t_pc ts_mid p = ''TE1'' \<and>
                       (nid, v, ts_val) \<in> set (pools ts_mid q) \<longrightarrow>
                       t_v ts_mid p \<noteq> v"
                    unfolding TSQ_State_Inv_def
                    by blast
                  then have "t_v ts_mid pa \<noteq> v"
                    using hpc_mid mem_mid by blast
                  with eq show False
                    by simp
                qed
                from old_neq False ts'_def_eval show ?thesis
                  by simp
              qed
            qed

            show "\<forall>pa q.
                t_pc ts' pa = ''TE1'' \<and>
                t_pc ts' q = ''TE1'' \<and>
                pa \<noteq> q \<longrightarrow>
                t_v ts' pa \<noteq> t_v ts' q"
            proof (intro allI impI)
              fix pa q
              assume h:
                "t_pc ts' pa = ''TE1'' \<and>
                 t_pc ts' q = ''TE1'' \<and>
                 pa \<noteq> q"
              have hpa': "t_pc ts' pa = ''TE1''"
                using h by blast
              have hq': "t_pc ts' q = ''TE1''"
                using h by blast
              have neq: "pa \<noteq> q"
                using h by blast
              show "t_v ts' pa \<noteq> t_v ts' q"
              proof (cases "pa = p")
                case True
                then have "t_pc ts' pa = ''TD1''"
                  using ts'_def_eval by simp
                with hpa' show ?thesis
                  by simp
              next
                case False
                show ?thesis
                proof (cases "q = p")
                  case True
                  then have "t_pc ts' q = ''TD1''"
                    using ts'_def_eval by simp
                  with hq' show ?thesis
                    by simp
                next
                  case False2: False
                  have hpa_mid: "t_pc ts_mid pa = ''TE1''"
                    using hpa' False ts'_def_eval by simp
                  have hq_mid: "t_pc ts_mid q = ''TE1''"
                    using hq' False2 ts'_def_eval by simp
                  have old_neq: "t_v ts_mid pa \<noteq> t_v ts_mid q"
                  proof
                    assume eq: "t_v ts_mid pa = t_v ts_mid q"
                    from inv_mid have
                      "\<forall>p q. t_pc ts_mid p = ''TE1'' \<and> t_pc ts_mid q = ''TE1'' \<and> p \<noteq> q \<longrightarrow>
                             t_v ts_mid p \<noteq> t_v ts_mid q"
                      unfolding TSQ_State_Inv_def
                      by blast
                    then have "t_v ts_mid pa \<noteq> t_v ts_mid q"
                      using hpa_mid hq_mid neq by blast
                    with eq show False
                      by simp
                  qed
                  from old_neq False False2 ts'_def_eval show ?thesis
                    by simp
                qed
              qed
            qed
          qed

show "TE2_Pending_Order ts'"
  unfolding TE2_Pending_Order_def
proof (intro conjI)
  show "\<forall>pa q nid v ts_val.
      t_pc ts' pa = ''TE2'' \<and>
      (nid, v, ts_val) \<in> set (pools ts' q) \<and>
      ts_val \<noteq> TOP \<longrightarrow>
      (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
  proof (intro allI impI)
    fix pa q nid v ts_val
    assume h:
      "t_pc ts' pa = ''TE2'' \<and>
       (nid, v, ts_val) \<in> set (pools ts' q) \<and>
       ts_val \<noteq> TOP"
    have hpc': "t_pc ts' pa = ''TE2''"
      using h by blast
    have mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
      using h by blast
    have nz: "ts_val \<noteq> TOP"
      using h by blast

    have pa_neq: "pa \<noteq> p"
    proof
      assume eq: "pa = p"
      from hpc' eq ts'_def_eval show False
        by simp
    qed

    have hpc_mid: "t_pc ts_mid pa = ''TE2''"
      using hpc' pa_neq ts'_def_eval by simp
    have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid q)"
      using mem' ts'_def_eval by simp
    have tts_eq: "t_ts ts' pa = t_ts ts_mid pa"
      using ts'_def_eval by simp
    have tnid_eq: "t_nid ts' pa = t_nid ts_mid pa"
      using ts'_def_eval by simp

    have old_ord:
      "(ts_val <\<^sub>t\<^sub>s t_ts ts_mid pa) = (nid < t_nid ts_mid pa)"
    proof -
      from inv_mid_pending have
        "\<forall>p q nid v ts_val.
            t_pc ts_mid p = ''TE2'' \<and>
            (nid, v, ts_val) \<in> set (pools ts_mid q) \<and>
            ts_val \<noteq> TOP \<longrightarrow>
            (ts_val <\<^sub>t\<^sub>s t_ts ts_mid p) = (nid < t_nid ts_mid p)"
        unfolding TE2_Pending_Order_def by blast
      then show ?thesis
        using hpc_mid mem_mid nz by blast
    qed

    from old_ord tts_eq tnid_eq
    show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
      by simp
  qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE2'' \<and>
          t_pc ts' q = ''TE2'' \<and>
          pa \<noteq> q \<longrightarrow>
          (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE2'' \<and>
           t_pc ts' q = ''TE2'' \<and>
           pa \<noteq> q"
        have hpa': "t_pc ts' pa = ''TE2''"
          using h by blast
        have hq': "t_pc ts' q = ''TE2''"
          using h by blast
        have neq: "pa \<noteq> q"
          using h by blast
    
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpa' eq ts'_def_eval show False
            by simp
        qed
    
        have q_neq: "q \<noteq> p"
        proof
          assume eq: "q = p"
          from hq' eq ts'_def_eval show False
            by simp
        qed
    
        have hpa_mid: "t_pc ts_mid pa = ''TE2''"
          using hpa' pa_neq ts'_def_eval by simp
        have hq_mid: "t_pc ts_mid q = ''TE2''"
          using hq' q_neq ts'_def_eval by simp
        have tts_pa_eq: "t_ts ts' pa = t_ts ts_mid pa"
          using ts'_def_eval by simp
        have tts_q_eq: "t_ts ts' q = t_ts ts_mid q"
          using ts'_def_eval by simp
        have tnid_pa_eq: "t_nid ts' pa = t_nid ts_mid pa"
          using ts'_def_eval by simp
        have tnid_q_eq: "t_nid ts' q = t_nid ts_mid q"
          using ts'_def_eval by simp
    
        have old_ord:
          "(t_ts ts_mid pa <\<^sub>t\<^sub>s t_ts ts_mid q) = (t_nid ts_mid pa < t_nid ts_mid q)"
        proof -
          from inv_mid_pending have
            "\<forall>p q.
                t_pc ts_mid p = ''TE2'' \<and>
                t_pc ts_mid q = ''TE2'' \<and>
                p \<noteq> q \<longrightarrow>
                (t_ts ts_mid p <\<^sub>t\<^sub>s t_ts ts_mid q) = (t_nid ts_mid p < t_nid ts_mid q)"
            unfolding TE2_Pending_Order_def by blast
          then show ?thesis
            using hpa_mid hq_mid neq by blast
        qed
    
        from old_ord tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
        show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
          by simp
      qed
    qed
        qed
      qed

      show ?thesis
      proof (cases "t_candNid ts_mid p = BOT")
        case True
        have ts'_def_eval:
          "ts' = ts_mid\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts_mid x)\<rparr>"
          using eval loop_mid scanned_mid True
          unfolding T_D3_Eval_def Let_def
          by (simp split: if_splits prod.splits)

        have td1_now: "TSQ_State_Inv_Plus ts'"
        proof (rule td1_preserve)
          show "ts' = ts_mid\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts_mid x)\<rparr>"
            using ts'_def_eval by simp
          show "t_pc ts_mid p = ''TD_Loop''"
            using loop_mid by simp
        qed
        from td1_now show ?thesis .

      next
        case False
        note cand_nonbot_outer = False
        show ?thesis
        proof (cases "fst (pool_remove (pools ts_mid (t_candPid ts_mid p)) (t_candNid ts_mid p)) = BOT")
          case True
          have ts'_def_eval:
            "ts' = ts_mid\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts_mid x)\<rparr>"
            using eval loop_mid scanned_mid False True
            unfolding T_D3_Eval_def Let_def
            by (simp split: if_splits prod.splits)
    
          have td1_preserve_now: "TSQ_State_Inv_Plus ts'"
          proof (rule td1_preserve)
            show "ts' = ts_mid\<lparr>t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts_mid x)\<rparr>"
              using ts'_def_eval by simp
            show "t_pc ts_mid p = ''TD_Loop''"
              using loop_mid by simp
          qed
          from td1_preserve_now show ?thesis .
    
        next
          case False
          obtain rv new_pool where rem_eq:
            "pool_remove (pools ts_mid (t_candPid ts_mid p)) (t_candNid ts_mid p) = (rv, new_pool)"
            by force
    
          have cand_nonbot: "t_candNid ts_mid p \<noteq> BOT"
            using cand_nonbot_outer by simp
    
          have rv_nonbot: "rv \<noteq> BOT"
          proof
            assume rv_bot: "rv = BOT"
            have "fst (pool_remove (pools ts_mid (t_candPid ts_mid p)) (t_candNid ts_mid p)) = BOT"
              using rem_eq rv_bot by simp
            with False show False
              by simp
          qed
    
          have ts'_def_eval:
            "ts' =
              ts_mid\<lparr>pools := (\<lambda>x. if x = t_candPid ts_mid p then new_pool else pools ts_mid x),
                      t_retV := (\<lambda>x. if x = p then rv else t_retV ts_mid x),
                      t_pc := (\<lambda>x. if x = p then ''TD_Remove_Done'' else t_pc ts_mid x)\<rparr>"
            using eval loop_mid scanned_mid cand_nonbot rv_nonbot rem_eq
            unfolding T_D3_Eval_def Let_def
            by simp
    
          have ret_nonbot:
            "t_retV ts' p \<noteq> BOT"
            using ts'_def_eval rv_nonbot by simp
  
  (* Final remaining proof block for this macro-step branch. *)
       then show ?thesis
          proof -
            let ?old_pool = "pools ts_mid (t_candPid ts_mid p)"

            have pool_remove_subset_aux:
              "pool_remove xs target = (rv0, ys) \<Longrightarrow> set ys \<subseteq> set xs"
              for xs target rv0 ys
            proof (induction xs arbitrary: rv0 ys)
              case Nil
              then show ?case
                by simp
            next
              case (Cons a xs)
              obtain nid0 v0 ts0 where a_def: "a = (nid0, v0, ts0)"
                by (cases a) auto
              show ?case
              proof (cases "nid0 = target \<and> ts0 \<noteq> TOP")
                case True
                with Cons.prems a_def show ?thesis
                  by auto
              next
                case False
                then obtain rv1 ys1 where rec:
                  "pool_remove xs target = (rv1, ys1)"
                  by (cases "pool_remove xs target") auto
                from Cons.prems False a_def rec have ys_def:
                  "ys = a # ys1"
                  by simp
                have sub_tail: "set ys1 \<subseteq> set xs"
                  using Cons.IH rec by blast
                from ys_def sub_tail show ?thesis
                  by auto
              qed
            qed

            have new_pool_subset:
              "set new_pool \<subseteq> set ?old_pool"
              using pool_remove_subset_aux rem_eq by blast

           have start_p_old:
              "t_startTs ts_mid p <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
            proof -
              from inv_mid have
                "(\<forall>q. t_pc ts_mid q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
                     t_startTs ts_mid q <\<^sub>t\<^sub>s TS (ts_counter ts_mid))"
                unfolding TSQ_State_Inv_Plus_def TSQ_State_Inv_def
                by simp
              with loop_mid show ?thesis
                by simp
            qed
(* Proceed to the first four subgoals needed for plain_now. *)
                        have plain_now: "TSQ_State_Inv ts'"
              unfolding TSQ_State_Inv_def
            proof (intro conjI)
              show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
                  (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                  (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
                  (v1 = v2) = (nid1 = nid2) \<and>
                  (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
              proof (intro allI impI)
                fix pa q nid1 nid2 v1 v2 ts1 ts2
                assume h:
                  "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                   (nid2, v2, ts2) \<in> set (pools ts' q)"
                have mem1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
                  using h by blast
                have mem2': "(nid2, v2, ts2) \<in> set (pools ts' q)"
                  using h by blast

                have mem1_mid: "(nid1, v1, ts1) \<in> set (pools ts_mid pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  then have "(nid1, v1, ts1) \<in> set new_pool"
                    using mem1' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem1' ts'_def_eval show ?thesis
                    by simp
                qed

                have mem2_mid: "(nid2, v2, ts2) \<in> set (pools ts_mid q)"
                proof (cases "q = t_candPid ts_mid p")
                  case True
                  then have "(nid2, v2, ts2) \<in> set new_pool"
                    using mem2' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem2' ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_indep:
                  "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
                     (nid1, v1, ts1) \<in> set (pools ts_mid pa) \<and>
                     (nid2, v2, ts2) \<in> set (pools ts_mid q) \<longrightarrow>
                     (v1 = v2) = (nid1 = nid2) \<and>
                     (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast
                then show
                  "(v1 = v2) = (nid1 = nid2) \<and>
                   (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
                  using mem1_mid mem2_mid
                  by blast
              qed

              show "\<forall>pa nid v ts_val.
                  (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
                  ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
              proof (intro allI impI)
                fix pa nid v ts_val
                assume h:
                  "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP"
                have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
                  using h by blast
                have nz: "ts_val \<noteq> TOP"
                  using h by blast

                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  then have "(nid, v, ts_val) \<in> set new_pool"
                    using mem' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem' ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_bound:
                  "\<forall>pa nid v ts_val.
                     (nid, v, ts_val) \<in> set (pools ts_mid pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
                     ts_val <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                  using mid_bound mem_mid nz by blast
                then show "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
                  using ts'_def_eval by simp
              qed

              show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
                using inv_mid ts'_def_eval
                unfolding TSQ_State_Inv_def
                by simp

              show "\<forall>q.
                  t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
                  t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
              proof (intro allI impI)
                fix q
                assume hq:
                  "t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
                show "t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
                proof (cases "q = p")
                  case True
                  with start_p_old ts'_def_eval show ?thesis
                    by simp
                next
                  case False
                  from inv_mid have mid_start:
                    "\<forall>q. t_pc ts_mid q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
                         t_startTs ts_mid q <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                    unfolding TSQ_State_Inv_Plus_def TSQ_State_Inv_def
                    by simp
                  have "t_pc ts_mid q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
                    using hq False ts'_def_eval by simp
                  hence "t_startTs ts_mid q <\<^sub>t\<^sub>s TS (ts_counter ts_mid)"
                    using mid_start by blast
                  thus ?thesis
                    using False ts'_def_eval by simp
                qed
              qed
(* Continue with the remaining TSQ_State_Inv obligations. *)
              show "\<forall>pa.
                  t_pc ts' pa = ''TE2'' \<longrightarrow>
                  t_ts ts' pa \<noteq> TOP \<and>
                  (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
              proof (intro allI impI)
                fix pa
                assume hpa: "t_pc ts' pa = ''TE2''"
              have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with hpa ts'_def_eval show False
                    by simp
                qed

                have hpa_mid: "t_pc ts_mid pa = ''TE2''"
                  using hpa pa_ne_p ts'_def_eval by simp

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_te2:
                  "\<forall>pa.
                     t_pc ts_mid pa = ''TE2'' \<longrightarrow>
                     t_ts ts_mid pa \<noteq> TOP \<and>
                     (\<exists>v. (t_nid ts_mid pa, v, TOP) \<in> set (pools ts_mid pa))"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                from mid_te2 hpa_mid have ts_mid_nz:
                  "t_ts ts_mid pa \<noteq> TOP"
                  by blast

                from mid_te2 hpa_mid obtain v0 where top_mid:
                  "(t_nid ts_mid pa, v0, TOP) \<in> set (pools ts_mid pa)"
                  by blast

(* Auxiliary lemma for preservation under pool_remove. *)
have top_preserved_aux:
  "pool_remove xs target = (rv0, ys) \<Longrightarrow>
   (nid, v, TOP) \<in> set xs \<Longrightarrow>
   (nid, v, TOP) \<in> set ys"
  for xs target rv0 ys nid v
proof (induction xs arbitrary: rv0 ys)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  obtain nid0 v0 ts0 where a_def: "a = (nid0, v0, ts0)"
    by (cases a) auto
  show ?case
  proof (cases "a = (nid, v, TOP)")
    case True
    then have ts0_top: "ts0 = TOP"
      using a_def by simp
    from Cons.prems obtain rv1 ys1 where rec:
      "pool_remove xs target = (rv1, ys1)"
      by (cases "pool_remove xs target") auto
    have ys_def: "ys = a # ys1"
      using Cons.prems a_def ts0_top rec by simp
    from True ys_def show ?thesis
      by simp
  next
    case False
    from Cons.prems False have mem_tail:
      "(nid, v, TOP) \<in> set xs"
      by simp
    show ?thesis
    proof (cases "nid0 = target \<and> ts0 \<noteq> TOP")
      case True
      from Cons.prems a_def True have ys_def: "ys = xs"
        by simp
      from mem_tail ys_def show ?thesis
        by simp
    next
      case False
      from Cons.prems obtain rv1 ys1 where rec:
        "pool_remove xs target = (rv1, ys1)"
        by (cases "pool_remove xs target") auto
      have ys_def: "ys = a # ys1"
        using Cons.prems a_def False rec by simp
      have "(nid, v, TOP) \<in> set ys1"
        using Cons.IH rec mem_tail by blast
      with ys_def show ?thesis
        by simp
    qed
  qed
qed

         have top_now:
                  "(t_nid ts' pa, v0, TOP) \<in> set (pools ts' pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                 have top_mid':
                    "(t_nid ts_mid pa, v0, TOP) \<in> set (pools ts_mid (t_candPid ts_mid p))"
                    using top_mid True by simp
                  have "(t_nid ts_mid pa, v0, TOP) \<in> set new_pool"
                    using top_preserved_aux[OF rem_eq top_mid'] .
                  with True pa_ne_p ts'_def_eval show ?thesis
                    by simp
                next
                  case False
                  with top_mid pa_ne_p ts'_def_eval show ?thesis
                    by simp
                qed

                show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
                proof
                  show "t_ts ts' pa \<noteq> TOP"
                    using ts_mid_nz pa_ne_p ts'_def_eval by simp
                  show "\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa)"
                    using top_now by blast
                qed
              qed

              show "\<forall>pa. t_pc ts' pa = ''TE3'' \<longrightarrow> t_ts ts' pa \<noteq> TOP"
              proof (intro allI impI)
                fix pa
                assume hpa: "t_pc ts' pa = ''TE3''"
              have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with hpa ts'_def_eval show False
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_te3:
                  "\<forall>pa. t_pc ts_mid pa = ''TE3'' \<longrightarrow> t_ts ts_mid pa \<noteq> TOP"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "t_pc ts_mid pa = ''TE3''"
                  using hpa pa_ne_p ts'_def_eval by simp
                hence "t_ts ts_mid pa \<noteq> TOP"
                  using mid_te3 by blast
                thus "t_ts ts' pa \<noteq> TOP"
                  using pa_ne_p ts'_def_eval by simp
              qed

              show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
              proof (intro allI)
                fix pa
                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_scanned:
                  "\<forall>pa. t_scanned ts_mid pa \<subseteq> ProcSet"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                show "t_scanned ts' pa \<subseteq> ProcSet"
                  using mid_scanned ts'_def_eval by simp
              qed

              show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
                  (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                  (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
                  ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
                  (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
              proof (intro allI impI)
                fix pa qa nid1 nid2 v1 v2 ts1 ts2
                assume h:
                  "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                   (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
                   ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP"
                have mem1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
                  using h by blast
                have mem2': "(nid2, v2, ts2) \<in> set (pools ts' qa)"
                  using h by blast
                have nz1: "ts1 \<noteq> TOP"
                  using h by blast
                have nz2: "ts2 \<noteq> TOP"
                  using h by blast

                have mem1_mid: "(nid1, v1, ts1) \<in> set (pools ts_mid pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  then have "(nid1, v1, ts1) \<in> set new_pool"
                    using mem1' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem1' ts'_def_eval show ?thesis
                    by simp
                qed

                have mem2_mid: "(nid2, v2, ts2) \<in> set (pools ts_mid qa)"
                proof (cases "qa = t_candPid ts_mid p")
                  case True
                  then have "(nid2, v2, ts2) \<in> set new_pool"
                    using mem2' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem2' ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_ts_order:
                  "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
                     (nid1, v1, ts1) \<in> set (pools ts_mid pa) \<and>
                     (nid2, v2, ts2) \<in> set (pools ts_mid qa) \<and>
                     ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
                     (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                show "(ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
                  using mid_ts_order mem1_mid mem2_mid nz1 nz2 by blast
              qed

              show "BOT < t_V_var ts'"
              proof -
                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_bot: "BOT < t_V_var ts_mid"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                show ?thesis
                  using mid_bot ts'_def_eval by simp
              qed
(* One more invariant clause remains to be discharged here. *)
                           show "\<forall>pa nid v ts_val.
                  (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
                  v < t_V_var ts'"
              proof (intro allI impI)
                fix pa nid v ts_val
                assume h:
                  "(nid, v, ts_val) \<in> set (pools ts' pa)"

                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  then have "(nid, v, ts_val) \<in> set new_pool"
                    using h ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with h ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_v_bound:
                  "\<forall>pa nid v ts_val.
                     (nid, v, ts_val) \<in> set (pools ts_mid pa) \<longrightarrow>
                     v < t_V_var ts_mid"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "v < t_V_var ts_mid"
                  using mid_v_bound mem_mid by blast
                thus "v < t_V_var ts'"
                  using ts'_def_eval by simp
              qed

              show "\<forall>pa nid v ts_val.
                  (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
                  nid < nid_counter ts'"
              proof (intro allI impI)
                fix pa nid v ts_val
                assume h:
                  "(nid, v, ts_val) \<in> set (pools ts' pa)"

                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  then have "(nid, v, ts_val) \<in> set new_pool"
                    using h ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with h ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_nid_bound:
                  "\<forall>pa nid v ts_val.
                     (nid, v, ts_val) \<in> set (pools ts_mid pa) \<longrightarrow>
                     nid < nid_counter ts_mid"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "nid < nid_counter ts_mid"
                  using mid_nid_bound mem_mid by blast
                thus "nid < nid_counter ts'"
                  using ts'_def_eval by simp
              qed

              show "\<forall>pa nid v ts_val.
                  (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
                  t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
              proof (intro allI impI)
                fix pa nid v ts_val
                assume h:
                  "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
                have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
                  using h by blast
                have topv: "ts_val = TOP"
                  using h by blast

                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  then have "(nid, v, ts_val) \<in> set new_pool"
                    using mem' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem' ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_top:
                  "\<forall>pa nid v ts_val.
                     (nid, v, ts_val) \<in> set (pools ts_mid pa) \<and> ts_val = TOP \<longrightarrow>
                     t_pc ts_mid pa = ''TE2'' \<and> nid = t_nid ts_mid pa"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

               have mid_top_fact: "t_pc ts_mid pa = ''TE2'' \<and> nid = t_nid ts_mid pa"
                  using mid_top mem_mid topv by blast

               have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with mid_top_fact loop_mid show False
                    by simp
                qed

                from mid_top_fact show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
                  using pa_ne_p ts'_def_eval
                  by simp
              qed

              show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
                  (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                  (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
                  ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
                  nid1 = nid2"
              proof (intro allI impI)
                fix pa q nid1 nid2 v1 v2 ts1 ts2
                assume h:
                  "(nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
                   (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
                   ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2"

                have mem1': "(nid1, v1, ts1) \<in> set (pools ts' pa)"
                  using h by blast
                have mem2': "(nid2, v2, ts2) \<in> set (pools ts' q)"
                  using h by blast
                have nz1: "ts1 \<noteq> TOP"
                  using h by blast
                have nz2: "ts2 \<noteq> TOP"
                  using h by blast
                have eqts: "ts1 = ts2"
                  using h by blast

                have mem1_mid: "(nid1, v1, ts1) \<in> set (pools ts_mid pa)"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  then have "(nid1, v1, ts1) \<in> set new_pool"
                    using mem1' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem1' ts'_def_eval show ?thesis
                    by simp
                qed

                have mem2_mid: "(nid2, v2, ts2) \<in> set (pools ts_mid q)"
                proof (cases "q = t_candPid ts_mid p")
                  case True
                  then have "(nid2, v2, ts2) \<in> set new_pool"
                    using mem2' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem2' ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_same_ts:
                  "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
                     (nid1, v1, ts1) \<in> set (pools ts_mid pa) \<and>
                     (nid2, v2, ts2) \<in> set (pools ts_mid q) \<and>
                     ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
                     nid1 = nid2"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                show "nid1 = nid2"
                  using mid_same_ts mem1_mid mem2_mid nz1 nz2 eqts by blast
              qed
(* Continue with the remaining pending-order subgoal. *)
                           show "\<forall>pa q nid v ts_val.
                  t_pc ts' pa = ''TE2'' \<and>
                  (nid, v, ts_val) \<in> set (pools ts' q) \<and>
                  ts_val \<noteq> TOP \<longrightarrow>
                  t_ts ts' pa \<noteq> ts_val"
              proof (intro allI impI)
                fix pa q nid v ts_val
                assume h:
                  "t_pc ts' pa = ''TE2'' \<and>
                   (nid, v, ts_val) \<in> set (pools ts' q) \<and>
                   ts_val \<noteq> TOP"

                have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with h ts'_def_eval show False
                    by simp
                qed

                have hpc_mid: "t_pc ts_mid pa = ''TE2''"
                  using h pa_ne_p ts'_def_eval by simp

                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid q)"
                proof (cases "q = t_candPid ts_mid p")
                  case True
                  then have "(nid, v, ts_val) \<in> set new_pool"
                    using h ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with h ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_te2_neq:
                  "\<forall>pa q nid v ts_val.
                     t_pc ts_mid pa = ''TE2'' \<and>
                     (nid, v, ts_val) \<in> set (pools ts_mid q) \<and>
                     ts_val \<noteq> TOP \<longrightarrow>
                     t_ts ts_mid pa \<noteq> ts_val"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "t_ts ts_mid pa \<noteq> ts_val"
                  using mid_te2_neq hpc_mid mem_mid h by blast
                thus "t_ts ts' pa \<noteq> ts_val"
                  using pa_ne_p ts'_def_eval by simp
              qed

              show "\<forall>pa q.
                  t_pc ts' pa = ''TE2'' \<and>
                  t_pc ts' q = ''TE2'' \<and>
                  pa \<noteq> q \<longrightarrow>
                  t_ts ts' pa \<noteq> t_ts ts' q"
              proof (intro allI impI)
                fix pa q
                assume h:
                  "t_pc ts' pa = ''TE2'' \<and>
                   t_pc ts' q = ''TE2'' \<and>
                   pa \<noteq> q"

                have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with h ts'_def_eval show False
                    by simp
                qed

                have q_ne_p: "q \<noteq> p"
                proof
                  assume "q = p"
                  with h ts'_def_eval show False
                    by simp
                qed

                have hpa_mid: "t_pc ts_mid pa = ''TE2''"
                  using h pa_ne_p ts'_def_eval by simp
                have hq_mid: "t_pc ts_mid q = ''TE2''"
                  using h q_ne_p ts'_def_eval by simp

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_te2_pair:
                  "\<forall>pa q.
                     t_pc ts_mid pa = ''TE2'' \<and>
                     t_pc ts_mid q = ''TE2'' \<and>
                     pa \<noteq> q \<longrightarrow>
                     t_ts ts_mid pa \<noteq> t_ts ts_mid q"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "t_ts ts_mid pa \<noteq> t_ts ts_mid q"
                  using mid_te2_pair hpa_mid hq_mid h by blast
                thus "t_ts ts' pa \<noteq> t_ts ts' q"
                  using pa_ne_p q_ne_p ts'_def_eval by simp
              qed

              show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
              proof (intro allI)
                fix pa
                show "sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
                proof (cases "pa = t_candPid ts_mid p")
                  case True
                  have inv_mid_plain: "TSQ_State_Inv ts_mid"
                    using inv_mid
                    unfolding TSQ_State_Inv_Plus_def
                    by simp

                  have mid_sorted_distinct:
                    "\<forall>pa. sorted (map fst (pools ts_mid pa)) \<and> distinct (map fst (pools ts_mid pa))"
                    using inv_mid_plain
                    unfolding TSQ_State_Inv_def
                    apply (elim conjE)
                    by blast

                  have old_sorted: "sorted (map fst ?old_pool)"
                    using mid_sorted_distinct by simp
                  have old_distinct: "distinct (map fst ?old_pool)"
                    using mid_sorted_distinct by simp

                  have new_pool_sorted:
                    "sorted (map fst new_pool)"
                  proof -
                    have pool_remove_sorted_aux:
                      "sorted (map fst xs) \<Longrightarrow>
                       pool_remove xs target = (rv0, ys) \<Longrightarrow>
                       sorted (map fst ys)"
                      for xs target rv0 ys
                    proof (induction xs arbitrary: rv0 ys)
                      case Nil
                      then show ?case
                        by simp
                    next
                      case (Cons a xs)
                      obtain nid0 v0 ts0 where a_def: "a = (nid0, v0, ts0)"
                        by (cases a) auto
                      show ?case
                      proof (cases "nid0 = target \<and> ts0 \<noteq> TOP")
                        case True
                        with Cons.prems a_def show ?thesis
                          by simp
                          next
                        case False
                        then obtain rv1 ys1 where rec:
                          "pool_remove xs target = (rv1, ys1)"
                          by (cases "pool_remove xs target") auto
                        have rvys:
                          "rv0 = rv1 \<and> ys = (nid0, v0, ts0) # ys1"
                          using Cons.prems False a_def rec
                          by simp
                        then have ys_def: "ys = (nid0, v0, ts0) # ys1"
                          by simp
                        have sorted_xs: "sorted (map fst xs)"
                          using Cons.prems a_def by simp
                        have sorted_ys1: "sorted (map fst ys1)"
                          using Cons.IH[OF sorted_xs rec] .
                        have subset_ys1: "set ys1 \<subseteq> set xs"
                          using pool_remove_subset_aux[OF rec] .
                        have lower_ys1: "\<forall>z\<in>set ys1. nid0 \<le> fst z"
                        proof
                          fix z
                          assume "z \<in> set ys1"
                          hence "z \<in> set xs"
                            using subset_ys1 by blast
                          thus "nid0 \<le> fst z"
                            using Cons.prems a_def by simp
                        qed
                                               have "sorted (map fst ((nid0, v0, ts0) # ys1))"
                        proof (cases ys1)
                          case Nil
                          then show ?thesis
                            by simp
                        next
                          case (Cons b ys1')
                          then obtain nid1 v1 ts1 where b_def: "b = (nid1, v1, ts1)"
                            by (cases b) auto
                          have ys1_def: "ys1 = (nid1, v1, ts1) # ys1'"
                            using Cons b_def by simp
                          have head_le: "nid0 \<le> nid1"
                            using lower_ys1 ys1_def by auto
                         have lower_map_ys1: "\<forall>y\<in>set (map fst ys1). nid0 \<le> y"
                            using lower_ys1 by force
                          have "sorted (map fst ((nid0, v0, ts0) # ys1))"
                            using lower_map_ys1 sorted_ys1
                            by simp
                          thus ?thesis .
                        qed
                        with ys_def show ?thesis
                          by simp
                      qed
                    qed
                    from pool_remove_sorted_aux[OF old_sorted rem_eq] show ?thesis .
                  qed

                  have new_pool_distinct:
                    "distinct (map fst new_pool)"
                  proof -
                    have pool_remove_distinct_aux:
                      "distinct (map fst xs) \<Longrightarrow>
                       pool_remove xs target = (rv0, ys) \<Longrightarrow>
                       distinct (map fst ys)"
                      for xs target rv0 ys
                    proof (induction xs arbitrary: rv0 ys)
                      case Nil
                      then show ?case
                        by simp
                    next
                      case (Cons a xs)
                      obtain nid0 v0 ts0 where a_def: "a = (nid0, v0, ts0)"
                        by (cases a) auto
                      show ?case
                      proof (cases "nid0 = target \<and> ts0 \<noteq> TOP")
                        case True
                        with Cons.prems a_def show ?thesis
                          by simp
                                           next
                        case False
                        then obtain rv1 ys1 where rec:
                          "pool_remove xs target = (rv1, ys1)"
                          by (cases "pool_remove xs target") auto
                        have rvys:
                          "rv0 = rv1 \<and> ys = (nid0, v0, ts0) # ys1"
                          using Cons.prems False a_def rec
                          by simp
                        then have ys_def: "ys = (nid0, v0, ts0) # ys1"
                          by simp
                        have dist_xs: "distinct (map fst xs)"
                          using Cons.prems a_def by simp
                        have dist_ys1: "distinct (map fst ys1)"
                          using Cons.IH[OF dist_xs rec] .
                        have subset_ys1: "set ys1 \<subseteq> set xs"
                          using pool_remove_subset_aux[OF rec] .
                        have notin_ys1: "nid0 \<notin> fst ` set ys1"
                        proof
                          assume "nid0 \<in> fst ` set ys1"
                          then obtain z where z_in: "z \<in> set ys1" and z_fst: "fst z = nid0"
                            by blast
                          have z_in_xs: "z \<in> set xs"
                            using z_in subset_ys1 by blast
                          have notin_xs: "nid0 \<notin> fst ` set xs"
                            using Cons.prems a_def by simp
                          from z_in_xs z_fst notin_xs show False
                            by blast
                        qed
                        have "distinct (map fst ((nid0, v0, ts0) # ys1))"
                          using dist_ys1 notin_ys1
                          by auto
                        with ys_def show ?thesis
                          by simp
                      qed
                    qed
                    from pool_remove_distinct_aux[OF old_distinct rem_eq] show ?thesis .
                  qed
                  have "sorted (map fst (pools ts' pa))"
                    using True ts'_def_eval new_pool_sorted
                    by simp
                  moreover have "distinct (map fst (pools ts' pa))"
                    using True ts'_def_eval new_pool_distinct
                    by simp
                  ultimately show ?thesis
                    by simp
                next
                  case False
                  have inv_mid_plain: "TSQ_State_Inv ts_mid"
                    using inv_mid
                    unfolding TSQ_State_Inv_Plus_def
                    by simp

                  have mid_sorted_distinct:
                    "\<forall>pa. sorted (map fst (pools ts_mid pa)) \<and> distinct (map fst (pools ts_mid pa))"
                    using inv_mid_plain
                    unfolding TSQ_State_Inv_def
                    apply (elim conjE)
                    by blast

                  with False ts'_def_eval show ?thesis
                    by simp
                qed
              qed

              show "\<forall>pa. t_pc ts' pa = ''TE1'' \<longrightarrow> t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
              proof (intro allI impI)
                fix pa
                assume hpa: "t_pc ts' pa = ''TE1''"
                have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with hpa ts'_def_eval show False
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_te1:
                  "\<forall>pa. t_pc ts_mid pa = ''TE1'' \<longrightarrow> t_v ts_mid pa \<noteq> BOT \<and> t_v ts_mid pa < t_V_var ts_mid"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "t_pc ts_mid pa = ''TE1''"
                  using hpa pa_ne_p ts'_def_eval by simp
                hence "t_v ts_mid pa \<noteq> BOT \<and> t_v ts_mid pa < t_V_var ts_mid"
                  using mid_te1 by blast
                thus "t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
                  using pa_ne_p ts'_def_eval by simp
              qed

              show "\<forall>pa q nid v ts_val.
                  t_pc ts' pa = ''TE1'' \<and>
                  (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
                  t_v ts' pa \<noteq> v"
              proof (intro allI impI)
                fix pa q nid v ts_val
                assume h:
                  "t_pc ts' pa = ''TE1'' \<and>
                   (nid, v, ts_val) \<in> set (pools ts' q)"

                have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with h ts'_def_eval show False
                    by simp
                qed

                have hpc_mid: "t_pc ts_mid pa = ''TE1''"
                  using h pa_ne_p ts'_def_eval by simp

                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid q)"
                proof (cases "q = t_candPid ts_mid p")
                  case True
                  then have "(nid, v, ts_val) \<in> set new_pool"
                    using h ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with h ts'_def_eval show ?thesis
                    by simp
                qed

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_te1_neq:
                  "\<forall>pa q nid v ts_val.
                     t_pc ts_mid pa = ''TE1'' \<and>
                     (nid, v, ts_val) \<in> set (pools ts_mid q) \<longrightarrow>
                     t_v ts_mid pa \<noteq> v"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "t_v ts_mid pa \<noteq> v"
                  using mid_te1_neq hpc_mid mem_mid by blast
                thus "t_v ts' pa \<noteq> v"
                  using pa_ne_p ts'_def_eval by simp
              qed

              show "\<forall>pa q.
                  t_pc ts' pa = ''TE1'' \<and>
                  t_pc ts' q = ''TE1'' \<and>
                  pa \<noteq> q \<longrightarrow>
                  t_v ts' pa \<noteq> t_v ts' q"
              proof (intro allI impI)
                fix pa q
                assume h:
                  "t_pc ts' pa = ''TE1'' \<and>
                   t_pc ts' q = ''TE1'' \<and>
                   pa \<noteq> q"

                have pa_ne_p: "pa \<noteq> p"
                proof
                  assume "pa = p"
                  with h ts'_def_eval show False
                    by simp
                qed

                have q_ne_p: "q \<noteq> p"
                proof
                  assume "q = p"
                  with h ts'_def_eval show False
                    by simp
                qed

                have hpa_mid: "t_pc ts_mid pa = ''TE1''"
                  using h pa_ne_p ts'_def_eval by simp
                have hq_mid: "t_pc ts_mid q = ''TE1''"
                  using h q_ne_p ts'_def_eval by simp

                have inv_mid_plain: "TSQ_State_Inv ts_mid"
                  using inv_mid
                  unfolding TSQ_State_Inv_Plus_def
                  by simp

                have mid_te1_pair:
                  "\<forall>pa q.
                     t_pc ts_mid pa = ''TE1'' \<and>
                     t_pc ts_mid q = ''TE1'' \<and>
                     pa \<noteq> q \<longrightarrow>
                     t_v ts_mid pa \<noteq> t_v ts_mid q"
                  using inv_mid_plain
                  unfolding TSQ_State_Inv_def
                  apply (elim conjE)
                  by blast

                have "t_v ts_mid pa \<noteq> t_v ts_mid q"
                  using mid_te1_pair hpa_mid hq_mid h by blast
                thus "t_v ts' pa \<noteq> t_v ts' q"
                  using pa_ne_p q_ne_p ts'_def_eval by simp
              qed
            qed
(* Final local obligation of this case split. *)
            have pending_now: "TE2_Pending_Order ts'"
              unfolding TE2_Pending_Order_def
            proof (intro conjI)
              show "\<forall>pa q nid v ts_val.
                  t_pc ts' pa = ''TE2'' \<and>
                  (nid, v, ts_val) \<in> set (pools ts' q) \<and>
                  ts_val \<noteq> TOP \<longrightarrow>
                  (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
              proof (intro allI impI)
                fix pa q nid v ts_val
                assume h:
                  "t_pc ts' pa = ''TE2'' \<and>
                   (nid, v, ts_val) \<in> set (pools ts' q) \<and>
                   ts_val \<noteq> TOP"
                have hpc': "t_pc ts' pa = ''TE2''"
                  using h by blast
                have mem': "(nid, v, ts_val) \<in> set (pools ts' q)"
                  using h by blast
                have nz: "ts_val \<noteq> TOP"
                  using h by blast

                have pa_neq: "pa \<noteq> p"
                proof
                  assume eq: "pa = p"
                  from hpc' eq ts'_def_eval show False
                    by simp
                qed

                have hpc_mid: "t_pc ts_mid pa = ''TE2''"
                  using hpc' pa_neq ts'_def_eval by simp

                have mem_mid: "(nid, v, ts_val) \<in> set (pools ts_mid q)"
                proof (cases "q = t_candPid ts_mid p")
                  case True
                  then have "(nid, v, ts_val) \<in> set new_pool"
                    using mem' ts'_def_eval by simp
                  with new_pool_subset True show ?thesis
                    by auto
                next
                  case False
                  with mem' ts'_def_eval show ?thesis
                    by simp
                qed

                have tts_eq: "t_ts ts' pa = t_ts ts_mid pa"
                  using ts'_def_eval by simp
                have tnid_eq: "t_nid ts' pa = t_nid ts_mid pa"
                  using ts'_def_eval by simp

                have old_ord:
                  "(ts_val <\<^sub>t\<^sub>s t_ts ts_mid pa) = (nid < t_nid ts_mid pa)"
                proof -
                  from inv_mid_pending have
                    "\<forall>p q nid v ts_val.
                        t_pc ts_mid p = ''TE2'' \<and>
                        (nid, v, ts_val) \<in> set (pools ts_mid q) \<and>
                        ts_val \<noteq> TOP \<longrightarrow>
                        (ts_val <\<^sub>t\<^sub>s t_ts ts_mid p) = (nid < t_nid ts_mid p)"
                    unfolding TE2_Pending_Order_def by blast
                  then show ?thesis
                    using hpc_mid mem_mid nz by blast
                qed

                from old_ord tts_eq tnid_eq
                show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
                  by simp
              qed

              show "\<forall>pa q.
                  t_pc ts' pa = ''TE2'' \<and>
                  t_pc ts' q = ''TE2'' \<and>
                  pa \<noteq> q \<longrightarrow>
                  (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
              proof (intro allI impI)
                fix pa q
                assume h:
                  "t_pc ts' pa = ''TE2'' \<and>
                   t_pc ts' q = ''TE2'' \<and>
                   pa \<noteq> q"
                have hpa': "t_pc ts' pa = ''TE2''"
                  using h by blast
                have hq': "t_pc ts' q = ''TE2''"
                  using h by blast
                have neq: "pa \<noteq> q"
                  using h by blast

                have pa_neq: "pa \<noteq> p"
                proof
                  assume eq: "pa = p"
                  from hpa' eq ts'_def_eval show False
                    by simp
                qed

                have q_neq: "q \<noteq> p"
                proof
                  assume eq: "q = p"
                  from hq' eq ts'_def_eval show False
                    by simp
                qed

                have hpa_mid: "t_pc ts_mid pa = ''TE2''"
                  using hpa' pa_neq ts'_def_eval by simp
                have hq_mid: "t_pc ts_mid q = ''TE2''"
                  using hq' q_neq ts'_def_eval by simp
                have tts_pa_eq: "t_ts ts' pa = t_ts ts_mid pa"
                  using ts'_def_eval by simp
                have tts_q_eq: "t_ts ts' q = t_ts ts_mid q"
                  using ts'_def_eval by simp
                have tnid_pa_eq: "t_nid ts' pa = t_nid ts_mid pa"
                  using ts'_def_eval by simp
                have tnid_q_eq: "t_nid ts' q = t_nid ts_mid q"
                  using ts'_def_eval by simp

                have old_ord:
                  "(t_ts ts_mid pa <\<^sub>t\<^sub>s t_ts ts_mid q) = (t_nid ts_mid pa < t_nid ts_mid q)"
                proof -
                  from inv_mid_pending have
                    "\<forall>p q.
                        t_pc ts_mid p = ''TE2'' \<and>
                        t_pc ts_mid q = ''TE2'' \<and>
                        p \<noteq> q \<longrightarrow>
                        (t_ts ts_mid p <\<^sub>t\<^sub>s t_ts ts_mid q) = (t_nid ts_mid p < t_nid ts_mid q)"
                    unfolding TE2_Pending_Order_def by blast
                  then show ?thesis
                    using hpa_mid hq_mid neq by blast
                qed

                from old_ord tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
                show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
                  by simp
              qed
            qed

            from plain_now pending_now show ?thesis
              unfolding TSQ_State_Inv_Plus_def by simp
      qed
qed
qed
qed
  next

    (* ====================================================== *)
    (* Case 9: T_D4                                           *)
    (* Return and clear the local dequeue variables; the pools are unchanged. *)
    (* ====================================================== *)
    assume h: "T_D4 p ts ts'"
    then have pc_rm: "t_pc ts p = ''TD_Remove_Done''"
      unfolding T_D4_def by simp
    from h have ts'_def:
      "ts' =
        ts\<lparr>t_pc := (\<lambda>x. if x = p then ''TL0'' else t_pc ts x),
           t_startTs := (\<lambda>x. if x = p then TOP else t_startTs ts x),
           t_candNid := (\<lambda>x. if x = p then BOT else t_candNid ts x),
           t_candTs := (\<lambda>x. if x = p then TOP else t_candTs ts x),
           t_candPid := (\<lambda>x. if x = p then BOT else t_candPid ts x),
           t_scanned := (\<lambda>x. if x = p then {} else t_scanned ts x),
           t_retV := (\<lambda>x. if x = p then BOT else t_retV ts x)\<rparr>"
      unfolding T_D4_def by simp

    have no_top_p:
      "\<forall>nid v. (nid, v, TOP) \<notin> set (pools ts p)"
    proof (intro allI)
      fix nid v
      show "(nid, v, TOP) \<notin> set (pools ts p)"
      proof
        assume hin: "(nid, v, TOP) \<in> set (pools ts p)"
        then have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts p)"
          by blast
        from inv12 hex have "t_pc ts p = ''TE2'' \<and> nid = t_nid ts p"
          by blast
        then have "t_pc ts p = ''TE2''"
          by simp
        with pc_rm show False
          by simp
      qed
    qed

show ?thesis
  unfolding TSQ_State_Inv_Plus_def
proof
  show "TSQ_State_Inv ts'"
    unfolding TSQ_State_Inv_def
  proof (intro conjI)
      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and> (nid2, v2, ts2) \<in> set (pools ts' q) \<longrightarrow>
          (v1 = v2) = (nid1 = nid2) \<and> (nid1 = nid2 \<longrightarrow> pa = q \<and> ts1 = ts2)"
        using inv1 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val \<noteq> TOP \<longrightarrow>
          ts_val <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv2 ts'_def by simp

      show "\<forall>pa. t_ts ts' pa \<noteq> TOP \<longrightarrow> t_ts ts' pa <\<^sub>t\<^sub>s TS (ts_counter ts')"
        using inv3 ts'_def by simp

      show "\<forall>q.
          t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''} \<longrightarrow>
          t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
      proof (intro allI impI)
        fix q
        assume hpc: "t_pc ts' q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
        show "t_startTs ts' q <\<^sub>t\<^sub>s TS (ts_counter ts')"
        proof (cases "q = p")
          case True
          from hpc True ts'_def show ?thesis
            by simp
        next
          case False
          from False hpc ts'_def have hpc_old:
            "t_pc ts q = ''TD_Line4_Done'' \<or>
             t_pc ts q = ''TD_Loop'' \<or>
             t_pc ts q = ''TD_Remove_Done''"
            by simp
          have old_bd: "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
          proof (cases "t_pc ts q = ''TD_Line4_Done''")
            case True
            with inv4 show ?thesis
              by blast
          next
            case False1: False
            show ?thesis
            proof (cases "t_pc ts q = ''TD_Loop''")
              case True
              with inv4 show ?thesis
                by blast
            next
              case False2: False
              from hpc_old False1 False2 have "t_pc ts q = ''TD_Remove_Done''"
                by blast
              with inv4 show ?thesis
                by blast
            qed
          qed
          from old_bd False ts'_def show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa.
          t_pc ts' pa = ''TE2'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP \<and>
          (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
      proof (intro allI impI)
        fix pa
        assume hpc': "t_pc ts' pa = ''TE2''"
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TL0'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        have hpc: "t_pc ts pa = ''TE2''"
          using hpc' pa_neq ts'_def by simp
        from inv5 hpc have "t_ts ts pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts pa, v, TOP) \<in> set (pools ts pa))"
          by blast
        with pa_neq ts'_def show "t_ts ts' pa \<noteq> TOP \<and> (\<exists>v. (t_nid ts' pa, v, TOP) \<in> set (pools ts' pa))"
          by simp
      qed

      show "\<forall>pa.
          t_pc ts' pa = ''TE3'' \<longrightarrow>
          t_ts ts' pa \<noteq> TOP"
        using inv6 ts'_def by simp

      show "\<forall>pa. t_scanned ts' pa \<subseteq> ProcSet"
        using inv7 ts'_def by simp

      show "\<forall>pa qa nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' qa) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<longrightarrow>
          (ts1 <\<^sub>t\<^sub>s ts2) = (nid1 < nid2)"
        using inv8 ts'_def by simp

      show "BOT < t_V_var ts'"
        using inv9 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          v < t_V_var ts'"
        using inv10 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<longrightarrow>
          nid < nid_counter ts'"
        using inv11 ts'_def by simp

      show "\<forall>pa nid v ts_val.
          (nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP \<longrightarrow>
          t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
      proof (intro allI impI)
        fix pa nid v ts_val
        assume htop:
          "(nid, v, ts_val) \<in> set (pools ts' pa) \<and> ts_val = TOP"
        then have mem': "(nid, v, ts_val) \<in> set (pools ts' pa)"
          by blast
        from htop have ts_top: "ts_val = TOP"
          by blast
        have pools_eq: "pools ts' pa = pools ts pa"
          using ts'_def by simp
        have mem: "(nid, v, ts_val) \<in> set (pools ts pa)"
          using mem' pools_eq by simp
        show "t_pc ts' pa = ''TE2'' \<and> nid = t_nid ts' pa"
        proof (cases "pa = p")
          case True
          from mem ts_top True have "(nid, v, TOP) \<in> set (pools ts p)"
            by simp
          with no_top_p show ?thesis
            by blast
        next
          case False
          have hex: "\<exists>v0. (nid, v0, TOP) \<in> set (pools ts pa)"
          proof -
            from mem ts_top have "(nid, v, TOP) \<in> set (pools ts pa)"
              by simp
            then show ?thesis
              by blast
          qed
          from inv12 hex have "t_pc ts pa = ''TE2'' \<and> nid = t_nid ts pa"
            by blast
          with False ts'_def show ?thesis
            by simp
        qed
      qed

      show "\<forall>pa q nid1 nid2 v1 v2 ts1 ts2.
          (nid1, v1, ts1) \<in> set (pools ts' pa) \<and>
          (nid2, v2, ts2) \<in> set (pools ts' q) \<and>
          ts1 \<noteq> TOP \<and> ts2 \<noteq> TOP \<and> ts1 = ts2 \<longrightarrow>
          nid1 = nid2"
        using inv13 ts'_def by simp

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE2'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<and>
          ts_val \<noteq> TOP \<longrightarrow>
          t_ts ts' pa \<noteq> ts_val"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume h:
          "t_pc ts' pa = ''TE2'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q) \<and>
           ts_val \<noteq> TOP"
        then have hpc': "t_pc ts' pa = ''TE2''"
          and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
          and hneq: "ts_val \<noteq> TOP"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TL0'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        have hpc: "t_pc ts pa = ''TE2''"
          using hpc' pa_neq ts'_def by simp
        have pools_eq: "pools ts' q = pools ts q"
          using ts'_def by simp
        have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
          using hin' pools_eq by simp
        from hpc hin hneq have "t_ts ts pa \<noteq> ts_val"
          using inv14 by blast
        with pa_neq ts'_def show "t_ts ts' pa \<noteq> ts_val"
          by simp
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE2'' \<and>
          t_pc ts' q = ''TE2'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_ts ts' pa \<noteq> t_ts ts' q"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE2'' \<and>
           t_pc ts' q = ''TE2'' \<and>
           pa \<noteq> q"
        then have hpa': "t_pc ts' pa = ''TE2''"
          and hq': "t_pc ts' q = ''TE2''"
          and neq: "pa \<noteq> q"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpa' eq ts'_def have "''TL0'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        have q_neq: "q \<noteq> p"
        proof
          assume eq: "q = p"
          from hq' eq ts'_def have "''TL0'' = ''TE2''"
            by simp
          then show False
            by simp
        qed
        have hpa: "t_pc ts pa = ''TE2''"
          using hpa' pa_neq ts'_def by simp
        have hq: "t_pc ts q = ''TE2''"
          using hq' q_neq ts'_def by simp
        from hpa hq neq have "t_ts ts pa \<noteq> t_ts ts q"
          using inv15 by blast
        with pa_neq q_neq ts'_def show "t_ts ts' pa \<noteq> t_ts ts' q"
          by simp
      qed

      show "\<forall>pa. sorted (map fst (pools ts' pa)) \<and> distinct (map fst (pools ts' pa))"
        using inv16 ts'_def by simp

      show "\<forall>pa.
          t_pc ts' pa = ''TE1'' \<longrightarrow>
          t_v ts' pa \<noteq> BOT \<and> t_v ts' pa < t_V_var ts'"
        using inv17 ts'_def by simp

      show "\<forall>pa q nid v ts_val.
          t_pc ts' pa = ''TE1'' \<and>
          (nid, v, ts_val) \<in> set (pools ts' q) \<longrightarrow>
          t_v ts' pa \<noteq> v"
      proof (intro allI impI)
        fix pa q nid v ts_val
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           (nid, v, ts_val) \<in> set (pools ts' q)"
        then have hpc': "t_pc ts' pa = ''TE1''"
          and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpc' eq ts'_def have "''TL0'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have hpc: "t_pc ts pa = ''TE1''"
          using hpc' pa_neq ts'_def by simp
        have pools_eq: "pools ts' q = pools ts q"
          using ts'_def by simp
        have hin_old: "(nid, v, ts_val) \<in> set (pools ts q)"
          using hin' pools_eq by simp
        have hex: "(\<exists>tsv. (nid, v, tsv) \<in> set (pools ts q))"
        proof
          show "(nid, v, ts_val) \<in> set (pools ts q)"
            using hin_old .
        qed
        from hpc hex have "t_v ts pa \<noteq> v"
          using inv18 by blast
        with pa_neq ts'_def show "t_v ts' pa \<noteq> v"
          by simp
      qed

      show "\<forall>pa q.
          t_pc ts' pa = ''TE1'' \<and>
          t_pc ts' q = ''TE1'' \<and>
          pa \<noteq> q \<longrightarrow>
          t_v ts' pa \<noteq> t_v ts' q"
      proof (intro allI impI)
        fix pa q
        assume h:
          "t_pc ts' pa = ''TE1'' \<and>
           t_pc ts' q = ''TE1'' \<and>
           pa \<noteq> q"
        then have hpa': "t_pc ts' pa = ''TE1''"
          and hq': "t_pc ts' q = ''TE1''"
          and neq: "pa \<noteq> q"
          by simp_all
        have pa_neq: "pa \<noteq> p"
        proof
          assume eq: "pa = p"
          from hpa' eq ts'_def have "''TL0'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have q_neq: "q \<noteq> p"
        proof
          assume eq: "q = p"
          from hq' eq ts'_def have "''TL0'' = ''TE1''"
            by simp
          then show False
            by simp
        qed
        have hpa: "t_pc ts pa = ''TE1''"
          using hpa' pa_neq ts'_def by simp
        have hq: "t_pc ts q = ''TE1''"
          using hq' q_neq ts'_def by simp
        from hpa hq neq have "t_v ts pa \<noteq> t_v ts q"
          using inv19 by blast
        with pa_neq q_neq ts'_def show "t_v ts' pa \<noteq> t_v ts' q"
          by simp
      qed
    qed
(* Final step: reassemble TE2_Pending_Order for the successor state. *)
  show "TE2_Pending_Order ts'"
    unfolding TE2_Pending_Order_def
  proof (intro conjI)
    show "\<forall>pa q nid v ts_val.
        t_pc ts' pa = ''TE2'' \<and>
        (nid, v, ts_val) \<in> set (pools ts' q) \<and>
        ts_val \<noteq> TOP \<longrightarrow>
        (ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
    proof (intro allI impI)
      fix pa q nid v ts_val
      assume h:
        "t_pc ts' pa = ''TE2'' \<and>
         (nid, v, ts_val) \<in> set (pools ts' q) \<and>
         ts_val \<noteq> TOP"
      then have hpc': "t_pc ts' pa = ''TE2''"
        and hin': "(nid, v, ts_val) \<in> set (pools ts' q)"
        and hneq: "ts_val \<noteq> TOP"
        by simp_all

      have pa_neq: "pa \<noteq> p"
      proof
        assume eq: "pa = p"
        from hpc' eq ts'_def have "''TL0'' = ''TE2''"
          by simp
        then show False
          by simp
      qed

      have hpc: "t_pc ts pa = ''TE2''"
        using hpc' pa_neq ts'_def by simp

      have pools_eq: "pools ts' q = pools ts q"
        using ts'_def by simp
      have hin: "(nid, v, ts_val) \<in> set (pools ts q)"
        using hin' pools_eq by simp

      have tts_eq: "t_ts ts' pa = t_ts ts pa"
        using ts'_def by simp
      have tnid_eq: "t_nid ts' pa = t_nid ts pa"
        using ts'_def by simp

      from inv_pending hpc hin hneq
      have "(ts_val <\<^sub>t\<^sub>s t_ts ts pa) = (nid < t_nid ts pa)"
        unfolding TE2_Pending_Order_def by blast
      with tts_eq tnid_eq show "(ts_val <\<^sub>t\<^sub>s t_ts ts' pa) = (nid < t_nid ts' pa)"
        by simp
    qed

    show "\<forall>pa q.
        t_pc ts' pa = ''TE2'' \<and>
        t_pc ts' q = ''TE2'' \<and>
        pa \<noteq> q \<longrightarrow>
        (t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
    proof (intro allI impI)
      fix pa q
      assume h:
        "t_pc ts' pa = ''TE2'' \<and>
         t_pc ts' q = ''TE2'' \<and>
         pa \<noteq> q"
      then have hpa': "t_pc ts' pa = ''TE2''"
        and hq': "t_pc ts' q = ''TE2''"
        and neq: "pa \<noteq> q"
        by simp_all

      have pa_neq: "pa \<noteq> p"
      proof
        assume eq: "pa = p"
        from hpa' eq ts'_def have "''TL0'' = ''TE2''"
          by simp
        then show False
          by simp
      qed

      have q_neq: "q \<noteq> p"
      proof
        assume eq: "q = p"
        from hq' eq ts'_def have "''TL0'' = ''TE2''"
          by simp
        then show False
          by simp
      qed

      have hpa: "t_pc ts pa = ''TE2''"
        using hpa' pa_neq ts'_def by simp
      have hq: "t_pc ts q = ''TE2''"
        using hq' q_neq ts'_def by simp

      have tts_pa_eq: "t_ts ts' pa = t_ts ts pa"
        using ts'_def by simp
      have tts_q_eq: "t_ts ts' q = t_ts ts q"
        using ts'_def by simp
      have tnid_pa_eq: "t_nid ts' pa = t_nid ts pa"
        using ts'_def by simp
      have tnid_q_eq: "t_nid ts' q = t_nid ts q"
        using ts'_def by simp

      from inv_pending hpa hq neq
      have "(t_ts ts pa <\<^sub>t\<^sub>s t_ts ts q) = (t_nid ts pa < t_nid ts q)"
        unfolding TE2_Pending_Order_def by blast
      with tts_pa_eq tts_q_eq tnid_pa_eq tnid_q_eq
      show "(t_ts ts' pa <\<^sub>t\<^sub>s t_ts ts' q) = (t_nid ts' pa < t_nid ts' q)"
        by simp
    qed
  qed
qed

  next

    (* ====================================================== *)
    (* Case 10: Idle                                          *)
    (* ====================================================== *)
    assume h: "ts' = ts"
    have "TSQ_State_Inv_Plus ts'"
      using inv h by simp
    then show ?thesis .
  qed
qed

(* ========================================================== *)
(* Strengthened TSQ invariants over Reachable_T                  *)
(* ========================================================== *)
lemma Reachable_T_TSQ_State_Inv_Plus:
  assumes "Reachable_T ts"
  shows "TSQ_State_Inv_Plus ts"
using assms
proof (induction rule: Reachable_T.induct)
  case (init ts)
  thus ?case
    using TSQ_State_Inv_Plus_Init by blast
next
  case (step ts ts')
  thus ?case
    using TSQ_State_Inv_Plus_Step by blast
qed


end
