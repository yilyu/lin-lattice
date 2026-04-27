theory SimProof
  imports Main 
    TSQModel
    SimLemmas
begin

(* ========================================================== *)
(* 15. Initial-state simulation lemma                            *)
(* ========================================================== *)
lemma Simulation_R_Init:
  assumes "Init s"
      and "T_Init ts"
  shows "Simulation_R s ts"
proof -
  (* Step 0: unpack the system state into the concrete and TSQ components. *)
  obtain cs us where s_eq: "s = (cs, us)" by (cases s)
  
(* Step 1: extract the concrete initial-state facts from Init. *)
  have hwq_pc: "\<forall>p. c_program_counter cs p = ''L0''"
   and hwq_q:  "\<forall>idx. CState.Q_arr cs idx = BOT"
   and hwq_x:  "CState.X_var cs = Suc 0"  (* In Model.thy, the initial value of X_var is 1. *)
   and hwq_V:  "CState.V_var cs = Suc 0"  (* The concrete freshness counter is initialized to 1. *)
   and hwq_his: "his_seq s = []"
    using assms(1) s_eq 
    (* Unfold Model.V_var_def explicitly to expose the initial counter value. *)
    unfolding Init_def his_seq_def Model.X_var_def Model.V_var_def Model.Q_arr_def
    by auto

  (* Step 2: extract the TSQ initial-state facts from T_Init. *)
  have tsq_pc: "\<forall>p. t_pc ts p = ''TL0''"
   and tsq_pool: "\<forall>p. pools ts p = []"
   and tsq_nid: "nid_counter ts = Suc 0"  (* In TSQModel, the initial nid_counter is 1. *)
   and tsq_V: "t_V_var ts = Suc 0"        (* The TSQ-side freshness counter is initialized to 1. *)
    using assms(2) unfolding T_Init_def by auto

  (* Step 3: prove the initial simulation relation. *)
  show ?thesis
    unfolding Simulation_R_def Let_def s_eq fst_conv snd_conv
  proof (intro conjI) (* Split the conjunctions of Simulation_R directly, without eliminating the quantifiers. *)
    
    (* Condition 2: alignment of program counters (eight cases). *)
    show "\<forall>p. c_program_counter cs p = ''L0'' \<longrightarrow> t_pc ts p = ''TL0''" using hwq_pc tsq_pc by simp
    show "\<forall>p. c_program_counter cs p = ''E1'' \<longrightarrow> t_pc ts p = ''TE1''" using hwq_pc by simp
    show "\<forall>p. c_program_counter cs p = ''E2'' \<longrightarrow> t_pc ts p = ''TE2''" using hwq_pc by simp
    show "\<forall>p. c_program_counter cs p = ''E3'' \<longrightarrow> t_pc ts p = ''TE3''" using hwq_pc by simp
    show "\<forall>p. c_program_counter cs p = ''D1'' \<longrightarrow> t_pc ts p = ''TD1''" using hwq_pc by simp
    show "\<forall>p. c_program_counter cs p = ''D2'' \<longrightarrow> t_pc ts p = ''TD_Line4_Done''" using hwq_pc by simp
    show "\<forall>p. c_program_counter cs p = ''D3'' \<longrightarrow> t_pc ts p = ''TD_Loop''" using hwq_pc by simp
    show "\<forall>p. c_program_counter cs p = ''D4'' \<longrightarrow> t_pc ts p = ''TD_Remove_Done''" using hwq_pc by simp

    (* Condition 3: validity of TOP nodes. *)
    show "\<forall>p. \<forall>node\<in>set (pools ts p). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts p = ''TE2'' \<and> t_nid ts p = fst node"
      using tsq_pool by simp

    (* Conditions 5.1 and 5.2: data mapping. *)
   show "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
      using hwq_q by simp
    show "\<forall>u idx. CState.Q_arr cs idx = BOT \<and> c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs u, TOP) \<in> set (pools ts u))"
      using hwq_pc by simp

    (* Condition 6: dequeue scanning coverage. *)
    show "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx<CState.j_var cs q. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts q)"
      using hwq_pc by simp

    (* Condition 7: uniqueness of TOP nodes. *)
    show "\<forall>q. c_program_counter cs q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
      using hwq_pc by simp

    (* Condition 8: startTs guard. *)
    show "\<forall>p. c_program_counter cs p = ''D2'' \<or> c_program_counter cs p = ''D3'' \<longrightarrow> (\<forall>idx<CState.l_var cs p. (CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts p)) \<and> (\<forall>q. CState.Q_arr cs idx = BOT \<and> c_program_counter cs q = ''E2'' \<and> CState.i_var cs q = idx \<longrightarrow> t_ts ts q <\<^sub>t\<^sub>s t_startTs ts p))"
      using hwq_pc by simp

    (* Condition 9: initial candidate values in D3. *)
    show "\<forall>p. c_program_counter cs p = ''D3'' \<longrightarrow> t_candNid ts p = BOT \<and> t_candTs ts p = TOP"
      using hwq_pc by simp

    (* Conditions 10 and 11: basic facts about the pools. *)
    show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
      using tsq_pool by simp
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val"
      using tsq_pool by simp

    (* Condition 12: synchronization of the allocation counters. *)
    show "nid_counter ts = CState.X_var cs" using tsq_nid hwq_x by simp
    show "\<forall>p. c_program_counter cs p \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ts p = CState.i_var cs p"
      using hwq_pc by simp

    (* Conditions 13, 14, and 15: monotonicity constraints. *)
    show "\<forall>q. c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs q)"
      using hwq_pc by simp
    show "\<forall>p q. c_program_counter cs p \<in> {''E2'', ''E3''} \<and> c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ts q) (t_ts ts p) \<longrightarrow> CState.i_var cs p < CState.l_var cs q"
      using hwq_pc by simp
    show "\<forall>u. c_program_counter cs u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs u)"
      using hwq_pc by simp
    show "\<forall>u. c_program_counter cs u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs u)"
      using hwq_pc by simp

       (* Condition 16: ownership bridge. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs, us) u v sn)"
      using tsq_pool by simp

    (* Condition 17: history completeness of the scanned set. *)
    show "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow>
      (\<forall>v. v \<in> t_scanned ts q \<longrightarrow>
        (\<exists>idx < CState.j_var cs q.
          (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
          (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)))"
      using hwq_pc by simp
    (* Conditions 18 and 19: D3-side protection constraints. *)
    show "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> (\<forall>v \<in> t_scanned ts q. \<forall>nid v_val ts_val. (nid, v_val, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q))"
      using hwq_pc by simp
    show "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> (\<forall>u \<in> t_scanned ts q. c_program_counter cs u \<in> {''E2'', ''E3''} \<longrightarrow> CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q))"
      using hwq_pc by simp

    (* ========================================================== *)
    (* Condition 20: synchronization of the value allocator and local snapshots. *)
    (* ========================================================== *)
    show "CState.V_var cs = t_V_var ts" 
      using hwq_V tsq_V by simp
    
    show "\<forall>p. c_program_counter cs p = ''E1'' \<longrightarrow> CState.v_var cs p = t_v ts p" 
      using hwq_pc by simp

  qed
qed


(* ========================================================== *)
(* 16. Simulation lemma for the enqueue call from L0             *)
(* ========================================================== *)
lemma Simulation_R_L0_Enq:
  fixes s s' :: SysState and ts :: TState and p :: nat
  assumes "Simulation_Inv s ts"
      and "Sys_L0 p s s'"
      and "c_program_counter (fst s') p = ''E1''"
  shows "\<exists>ts'. T_Call_Enq p ts ts' \<and> Simulation_R s' ts'"
proof -
  (* Step 0: basic setup. *)
  obtain cs us where s_eq: "s = (cs, us)" by (cases s)
  obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
  have sim_r: "Simulation_R (cs, us) ts" using assms(1) s_eq unfolding Simulation_Inv_def by auto
  
  (* Step 1: extract the concrete-state facts. *)
  have pc_L0: "c_program_counter cs p = ''L0''"
    using assms(2) s_eq unfolding Sys_L0_def C_L0_def by auto
  have cs'_update: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''E1'' else c_program_counter cs x),
                          V_var := CState.V_var cs + 1,
                          v_var := (\<lambda>x. if x = p then CState.V_var cs else CState.v_var cs x) \<rparr>"
  proof -
    from assms(2) s_eq s'_eq have "C_L0 p cs cs'" unfolding Sys_L0_def by auto
    with assms(3) s'_eq show ?thesis unfolding C_L0_def Let_def by auto
  qed

  (* Step 2: derive the history extension facts. *)
  have his_grow: "\<exists>sn. u_his_seq us' = u_his_seq us @ [mk_act enq (CState.V_var cs) p sn call]"
  proof -
    from assms(2,3) s'_eq obtain us_mid where 
      l0: "U_L0_E p us us_mid"
      and e1: "U_E1 p (CState.V_var cs) (s_var (cs, us) p) us_mid us'"
      unfolding Sys_L0_def
      using s_eq
      by (auto simp: s_var_def)

    from l0 have his_mid: "u_his_seq us_mid = u_his_seq us"
      unfolding U_L0_E_def by auto

    from e1 have his_e1:
      "u_his_seq us' = u_his_seq us_mid @ [mk_act enq (CState.V_var cs) p (s_var (cs, us) p) call]"
      unfolding U_E1_def by auto

    have "u_his_seq us' = u_his_seq us @ [mk_act enq (CState.V_var cs) p (s_var (cs, us) p) call]"
      using his_mid his_e1 by simp
    thus ?thesis by blast
  qed

  (* Step 3: construct ts' and prove the corresponding TSQ step. *)
  let ?ts' = "ts\<lparr> t_pc := (\<lambda>x. if x = p then ''TE1'' else t_pc ts x),
                  t_V_var := t_V_var ts + 1,
                  t_v := (\<lambda>x. if x = p then t_V_var ts else t_v ts x) \<rparr>"
  have step_T: "T_Call_Enq p ts ?ts'"
    using sim_r pc_L0 unfolding Simulation_R_def Let_def T_Call_Enq_def by auto

  (* Step 4: re-establish Simulation_R for the successor states. *)
  show ?thesis
  proof (rule exI[where x="?ts'"], rule conjI)
    show "T_Call_Enq p ts ?ts'" using step_T .

    show "Simulation_R s' ?ts'"
      unfolding Simulation_R_def Let_def s'_eq fst_conv snd_conv
    proof (intro conjI)
      
      (* Step 4.1: program-counter alignment (Condition 2). *)
      show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts' q = ''TL0''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts' q = ''TE1''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts' q = ''TE2''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts' q = ''TE3''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts' q = ''TD1''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts' q = ''TD_Line4_Done''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts' q = ''TD_Loop''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts' q = ''TD_Remove_Done''"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.2: pool-side node validity (Condition 3). *)
      show "\<forall>q. \<forall>node\<in>set (pools ?ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
      proof (intro allI ballI)
        fix q node
        assume "node \<in> set (pools ?ts' q)"
        hence in_old: "node \<in> set (pools ts q)" by simp (* The pools are unchanged in this step. *)

        (* Extract Condition 3 from the old state explicitly instead of relying on blind automation. *)
        have old_cond3: "\<forall>q_x. \<forall>node_x\<in>set (pools ts q_x). 
          snd (snd node_x) \<noteq> TOP \<or> snd (snd node_x) = TOP \<and> t_pc ts q_x = ''TE2'' \<and> t_nid ts q_x = fst node_x"
          using sim_r unfolding Simulation_R_def Let_def by simp

        from in_old old_cond3 have old_sat: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
          by blast

        (* Case split on the thread q. *)
        show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
        proof (cases "q = p")
          case True (* Case A: q is the current thread p. *)
          have "t_pc ?ts' p = ''TE1''" by simp
          (* Since p moves from L0 to E1, it is not in E2; any TOP-node obligation must therefore come from the old-state invariant. *)
          (* In fact, a thread in L0/E1 cannot own a TOP node, so the old invariant closes the case immediately. *)
          with old_sat show ?thesis
            using T_Call_Enq_def step_T by force 
        next
          case False (* Case B: q is a different thread. *)
          with old_sat show ?thesis by simp
        qed
      qed

      (* Step 4.2b: data mapping (Condition 5). *)
     show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP)"
       using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u))"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.3: counters and local slot alignment (Condition 12). *)
      show "nid_counter ?ts' = CState.X_var cs'"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts' q = CState.i_var cs' q"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.4: scan-related guards and monotonicity facts. *)

      (* Step 4.4: precision of the scan condition (Condition 6). *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx<CState.j_var cs' q. 
               (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
               (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) 
             \<longrightarrow> v \<in> t_scanned ?ts' q)"
      proof (intro allI impI)
        fix q v
        assume pc_q': "c_program_counter cs' q = ''D3''"
        assume "\<exists>idx<CState.j_var cs' q. 
               (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
               (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
        then obtain idx where idx_lt: "idx < CState.j_var cs' q" and
          cond: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
                 (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
          by blast

        (* Since p is now in E1, it cannot be in D3; therefore q \<noteq> p. *)
        have q_neq_p: "q \<noteq> p" using pc_q' cs'_update by (auto split: if_splits)

        (* Map the unchanged fields of the new state back to the old state. *)
        hence pc_q_old: "c_program_counter cs q = ''D3''" using pc_q' cs'_update by simp
        have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_update by simp
        have arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_update by simp
        have i_eq: "CState.i_var cs' = CState.i_var cs" using cs'_update by simp
        have pools_eq: "pools ?ts' v = pools ts v" by simp   (* The pools field is unchanged in ?ts'. *)
        have scan_eq: "t_scanned ?ts' q = t_scanned ts q" using q_neq_p by simp   (* The t_scanned component is unchanged in ?ts'. *)

        (* Handle the program counter of v; when v = p it changes, but we only use this fact where needed. *)
        have pc_v_old: "v \<noteq> p \<Longrightarrow> c_program_counter cs v = c_program_counter cs' v"
        proof -
          assume "v \<noteq> p"
          then show ?thesis using cs'_update by simp
        qed

        (* Translate the new-state premise into an old-state premise. *)
        have cond_old: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or>  (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
        proof (cases "CState.Q_arr cs' idx = BOT")
          case True
          with cond have "c_program_counter cs' v = ''E2''" and "CState.i_var cs' v = idx" and "idx \<noteq> BOT" by auto
          (* Here v cannot equal p, since c_program_counter cs' p = ''E1''. *)
          have "v \<noteq> p"
          proof
            assume "v = p"
            with `c_program_counter cs' v = ''E2''` and cs'_update show False by simp
          qed
          hence "c_program_counter cs v = ''E2''" using `c_program_counter cs' v = ''E2''` pc_v_old[OF `v \<noteq> p`] by simp
          moreover have "CState.i_var cs v = idx" using `CState.i_var cs' v = idx` i_eq by simp
          ultimately show ?thesis using True arr_eq `idx \<noteq> BOT` by auto
        next
          case False
          with cond obtain nid ts_val where in_new: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v)" and ts_not_top: "ts_val \<noteq> TOP" by blast
          have in_old: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v)" using in_new pools_eq arr_eq by simp
          thus ?thesis using False arr_eq ts_not_top by auto
        qed

        (* Invoke Condition 6 of the old state. *)
        have old_cond6: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx<CState.j_var cs q. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts q)"
          using sim_r unfolding Simulation_R_def Let_def by simp

        from old_cond6[rule_format, OF pc_q_old, of v] idx_lt j_eq cond_old have "v \<in> t_scanned ts q"
          by auto 
        thus "v \<in> t_scanned ?ts' q" using scan_eq by simp
      qed

      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>pa. c_program_counter cs' pa = ''D2'' \<or> c_program_counter cs' pa = ''D3'' \<longrightarrow> (\<forall>idx<CState.l_var cs' pa. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' pa)) \<and> (\<forall>q. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' q = ''E2'' \<and> CState.i_var cs' q = idx \<longrightarrow> t_ts ?ts' q <\<^sub>t\<^sub>s t_startTs ?ts' pa))"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.5: cross-state monotonicity constraints (Conditions 10, 11, 13, 14, and 15). *)
      show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> v \<in> Val"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q r. c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' r \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts' r) (t_ts ?ts' q) \<longrightarrow> CState.i_var cs' q < CState.l_var cs' r"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

     (* Step 4.6: history and ownership constraints (Conditions 16, 17, 18, and 19). *)
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us') u v sn)"
      proof (intro allI impI, elim conjE)
        fix u nid v ts_val 
        assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts' u)" and not_top: "ts_val \<noteq> TOP"
        
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)"
          using in_pool by simp
        
        have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
          using sim_r in_old not_top unfolding Simulation_R_def Let_def by blast
          
        from old_his show "\<exists>sn. EnqCallInHis (cs', us') u v sn"
        proof
          fix sn
          assume h: "EnqCallInHis (cs, us) u v sn"
          have "EnqCallInHis (cs', us') u v sn"
            using h his_grow unfolding EnqCallInHis_def his_seq_def
            by (auto simp: nth_append)
          thus "\<exists>sn. EnqCallInHis (cs', us') u v sn"
            by blast
        qed
      qed

      (* Step 4.6b: scanned-set history completeness (Condition 17). *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow>
        (\<forall>v. v \<in> t_scanned ?ts' q \<longrightarrow>
          (\<exists>idx < CState.j_var cs' q.
            (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
            (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and> InQBack (cs', us') v_val \<and> Idx (cs', us') v_val = idx)))"
      proof (intro allI impI)
        fix q v 
        assume pc_q: "c_program_counter cs' q = ''D3''" 
        assume v_scan: "v \<in> t_scanned ?ts' q"
        
        have q_not_p: "q \<noteq> p"
          using pc_q assms(3) s'_eq by auto
        have pc_q_old: "c_program_counter cs q = ''D3''"
          using pc_q q_not_p cs'_update by simp
        have v_in_old: "v \<in> t_scanned ts q"
          using v_scan q_not_p by simp
        
        have old_fact:
          "\<exists>idx < CState.j_var cs q.
             (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
             (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
          using sim_r pc_q_old v_in_old unfolding Simulation_R_def Let_def
          by auto

        then obtain idx where
          idx_lt: "idx < CState.j_var cs q" and
          branches: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
                     (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
          by blast

               have us'_update: "\<exists>sn. us' = us\<lparr>
          u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter us x),
          u_his_seq := u_his_seq us @ [mk_act enq (CState.V_var cs) p sn call]
        \<rparr>"
      proof -
        from assms(2,3) s'_eq obtain us_mid where
          l0: "U_L0_E p us us_mid"
          and e1: "U_E1 p (CState.V_var cs) (s_var (cs, us) p) us_mid us'"
          unfolding Sys_L0_def
          using s_eq
          by (auto simp: s_var_def)

        from l0 have mid_pc:
          "u_program_counter us_mid = (\<lambda>x. if x = p then ''UE1'' else u_program_counter us x)"
          and mid_his: "u_his_seq us_mid = u_his_seq us"
          unfolding U_L0_E_def by auto

        from e1 have e1_shape:
          "us' = us_mid\<lparr>
            u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter us_mid x),
            u_his_seq := u_his_seq us_mid @ [mk_act enq (CState.V_var cs) p (s_var (cs, us) p) call]
          \<rparr>"
          unfolding U_E1_def by auto

        have mid_eq_full:
          "us_mid = us\<lparr>u_program_counter := (\<lambda>x. if x = p then ''UE1'' else u_program_counter us x)\<rparr>"
          using l0 unfolding U_L0_E_def by auto

        have "us' = us\<lparr>
          u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter us x),
          u_his_seq := u_his_seq us @ [mk_act enq (CState.V_var cs) p (s_var (cs, us) p) call]
        \<rparr>"
        proof -
          from e1_shape have
            "us' = us_mid\<lparr>
              u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter us_mid x),
              u_his_seq := u_his_seq us_mid @ [mk_act enq (CState.V_var cs) p (s_var (cs, us) p) call]
            \<rparr>"
            by simp
          also have "... = us\<lparr>
            u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter us x),
            u_his_seq := u_his_seq us @ [mk_act enq (CState.V_var cs) p (s_var (cs, us) p) call]
          \<rparr>"
          proof -
            have pc_eq:
              "(\<lambda>x. if x = p then ''UE2'' else u_program_counter us_mid x) =
               (\<lambda>x. if x = p then ''UE2'' else u_program_counter us x)"
            proof
              fix x
              show "(if x = p then ''UE2'' else u_program_counter us_mid x) =
                    (if x = p then ''UE2'' else u_program_counter us x)"
                using mid_eq_full by (cases "x = p") auto
            qed
            thus ?thesis
              using mid_eq_full mid_his by simp
          qed
          finally show ?thesis .
        qed
        thus ?thesis by blast
      qed

        show "\<exists>idx < CState.j_var cs' q.
                (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
                (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and> InQBack (cs', us') v_val \<and> Idx (cs', us') v_val = idx)"
        proof (rule exI[where x=idx], intro conjI)
          show "idx < CState.j_var cs' q"
            using idx_lt q_not_p cs'_update by simp
        next
          from branches show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
                              (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and> InQBack (cs', us') v_val \<and> Idx (cs', us') v_val = idx)"
          proof
            assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
            hence "v \<noteq> p"
              using pc_L0 by auto
            thus ?thesis
              using b1 cs'_update by auto
          next
            assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
            then obtain v_val sn where
              h1: "EnqCallInHis (cs, us) v v_val sn" and
              h2: "InQBack (cs, us) v_val" and
              h3: "Idx (cs, us) v_val = idx"
              by blast
            
            have new_h1: "EnqCallInHis (cs', us') v v_val sn"
              using h1 his_grow s_eq s'_eq
              unfolding EnqCallInHis_def his_seq_def
              by (auto simp: nth_append)
            
            have new_h2: "InQBack (cs', us') v_val"
              using h2 cs'_update us'_update s_eq s'_eq
              unfolding InQBack_def Model.Qback_arr_def
              by auto
              
            have new_h3: "Idx (cs', us') v_val = idx"
              using h3 cs'_update us'_update s_eq s'_eq
              unfolding Idx_def AtIdx_def Model.Qback_arr_def
              by auto
              
            from new_h1 new_h2 new_h3 show ?thesis
              by blast
          qed
        qed
      qed

    (* Condition 18: scanned-node boundary constraint. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
            (\<forall>v \<in> t_scanned ?ts' q. \<forall>nid v_val ts_val. 
               (nid, v_val, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
               nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q))"
      proof (intro allI impI ballI, elim conjE) (* Decompose the conjunctions explicitly with elim conjE. *)
        fix q v nid v_val ts_val
        assume pc_q': "c_program_counter cs' q = ''D3''"
        assume v_in_scan: "v \<in> t_scanned ?ts' q"
        assume node: "(nid, v_val, ts_val) \<in> set (pools ?ts' v)" 
        assume ts_not_top: "ts_val \<noteq> TOP"

        (* Since p is now in E1, it cannot be in D3; therefore q \<noteq> p. *)
        have q_neq_p: "q \<noteq> p" using pc_q' assms(3) s'_eq by auto

        (* Map the unchanged fields of the new state back to the old state. *)
        have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q' q_neq_p cs'_update by simp
        have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_update by simp
        have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
        
        (* Derive the old-state premise explicitly. *)
        have scan_q_old: "v \<in> t_scanned ts q" using v_in_scan q_neq_p by simp
        have node_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" using node by simp

        (* Extract Condition 18 from the old state. *)
        have old_cond18: "\<forall>q_x. c_program_counter cs q_x = ''D3'' \<longrightarrow> 
            (\<forall>v_x \<in> t_scanned ts q_x. \<forall>nid_x v_val_x ts_val_x. 
               (nid_x, v_val_x, ts_val_x) \<in> set (pools ts v_x) \<and> ts_val_x \<noteq> TOP \<longrightarrow> 
               nid_x < CState.j_var cs q_x \<or> \<not> ts_less ts_val_x (t_startTs ts q_x))"
          using sim_r unfolding Simulation_R_def Let_def
          by (metis fst_conv) 

        (* Combine the available facts directly with blast. *)
        have "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
          using old_cond18 pc_q_old scan_q_old node_old ts_not_top by blast

        (* Transport the result back to the new state. *)
        thus "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q)" 
          using j_eq startTs_eq by simp
      qed

      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>u \<in> t_scanned ?ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q))"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Condition 20: synchronization of the value allocator and local snapshots. *)
      show "CState.V_var cs' = t_V_var ?ts'" 
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts' q" 
        using sim_r cs'_update unfolding Simulation_R_def Let_def by (auto split: if_splits)

    qed
  qed
qed

(* ========================================================== *)
(* 17. Simulation lemma for the dequeue call from L0             *)
(* ========================================================== *)
lemma Simulation_R_L0_Deq:
  fixes s s' :: SysState and ts :: TState and p :: nat
  assumes "Simulation_Inv s ts"
      and "Sys_L0 p s s'"
      and "c_program_counter (fst s') p = ''D1''"
  shows "\<exists>ts'. T_Call_Deq p ts ts' \<and> Simulation_R s' ts'"
proof -
  (* Step 0: basic setup. *)
  obtain cs us where s_eq: "s = (cs, us)" by (cases s)
  obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
  have sim_r: "Simulation_R (cs, us) ts" using assms(1) s_eq unfolding Simulation_Inv_def by auto
  
  (* Step 1: extract the concrete-state facts. *)
  have pc_L0: "c_program_counter cs p = ''L0''"
    using assms(2) s_eq unfolding Sys_L0_def C_L0_def by auto
    
  (* Unlike enqueue, the dequeue call typically only changes the control state and does not consume a V_var slot. *)
  have cs'_update: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D1'' else c_program_counter cs x) \<rparr>"
  proof -
    from assms(2) s_eq s'_eq have "C_L0 p cs cs'" unfolding Sys_L0_def by auto
    with assms(3) s'_eq show ?thesis unfolding C_L0_def Let_def by (auto split: if_splits)
  qed

    (* Step 2: extend the history with a dequeue call carrying BOT. *)
  have us'_update: "\<exists>sn. us' = us\<lparr>
    u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us x),
    u_his_seq := u_his_seq us @ [mk_act deq BOT p sn call]
  \<rparr>"
  proof -
    from assms(2,3) s'_eq obtain us_mid where 
      l0: "U_L0_D p us us_mid"
      and d1: "U_D1 p (s_var (cs, us) p) us_mid us'"
      unfolding Sys_L0_def
      using s_eq
      by (auto simp: s_var_def)

    have mid_eq_full:
      "us_mid = us\<lparr>u_program_counter := (\<lambda>x. if x = p then ''UD1'' else u_program_counter us x)\<rparr>"
      using l0 unfolding U_L0_D_def by auto

    have d1_shape:
      "us' = us_mid\<lparr>
        u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us_mid x),
        u_his_seq := u_his_seq us_mid @ [mk_act deq BOT p (s_var (cs, us) p) call]
      \<rparr>"
      using d1 unfolding U_D1_def by auto

    have "us' = us\<lparr>
      u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us x),
      u_his_seq := u_his_seq us @ [mk_act deq BOT p (s_var (cs, us) p) call]
    \<rparr>"
    proof -
      from d1_shape have
        "us' = us_mid\<lparr>
          u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us_mid x),
          u_his_seq := u_his_seq us @ [mk_act deq BOT p (s_var (cs, us) p) call]
        \<rparr>"
        using l0 unfolding U_L0_D_def by auto
      also have "... = us\<lparr>
        u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us x),
        u_his_seq := u_his_seq us @ [mk_act deq BOT p (s_var (cs, us) p) call]
      \<rparr>"
      proof -
        have pc_eq:
          "(\<lambda>x. if x = p then ''UD2'' else u_program_counter us_mid x) =
           (\<lambda>x. if x = p then ''UD2'' else u_program_counter us x)"
        proof
          fix x
          show "(if x = p then ''UD2'' else u_program_counter us_mid x) =
                (if x = p then ''UD2'' else u_program_counter us x)"
            using mid_eq_full by (cases "x = p") auto
        qed
        thus ?thesis
          using mid_eq_full by simp
      qed
      finally show ?thesis .
    qed
    thus ?thesis by blast
  qed

  have his_grow: "\<exists>sn. u_his_seq us' = u_his_seq us @ [mk_act deq BOT p sn call]"
  proof -
    from us'_update obtain sn where
      us'_eq: "us' = us\<lparr>
        u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us x),
        u_his_seq := u_his_seq us @ [mk_act deq BOT p sn call]
      \<rparr>"
      by blast
    have "u_his_seq us' = u_his_seq us @ [mk_act deq BOT p sn call]"
      using us'_eq by simp
    thus ?thesis by blast
  qed

  (* Step 3: construct ts' and prove the corresponding TSQ step. *)
  let ?ts' = "ts\<lparr> t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts x) \<rparr>"
  have step_T: "T_Call_Deq p ts ?ts'"
    using sim_r pc_L0 unfolding Simulation_R_def Let_def T_Call_Deq_def by auto

  (* Step 4: re-establish Simulation_R for the successor states. *)
  show ?thesis
  proof (rule exI[where x="?ts'"], rule conjI)
    show "T_Call_Deq p ts ?ts'" using step_T .

    show "Simulation_R s' ?ts'"
      unfolding Simulation_R_def Let_def s'_eq fst_conv snd_conv
    proof (intro conjI)
      
      (* Step 4.1: program-counter alignment (Condition 2). *)
      show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts' q = ''TL0''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts' q = ''TE1''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts' q = ''TE2''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts' q = ''TE3''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts' q = ''TD1''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts' q = ''TD_Line4_Done''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts' q = ''TD_Loop''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts' q = ''TD_Remove_Done''" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.2: pool-side node validity (Condition 3). *)
      show "\<forall>q. \<forall>node\<in>set (pools ?ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
      proof (intro allI ballI)
        fix q node assume "node \<in> set (pools ?ts' q)"
        hence in_old: "node \<in> set (pools ts q)" by simp 
        have old_cond3: "\<forall>q_x. \<forall>node_x\<in>set (pools ts q_x). 
          snd (snd node_x) \<noteq> TOP \<or> snd (snd node_x) = TOP \<and> t_pc ts q_x = ''TE2'' \<and> t_nid ts q_x = fst node_x"
          using sim_r unfolding Simulation_R_def Let_def by simp
        from in_old old_cond3 have old_sat: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node" by blast
        show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
        proof (cases "q = p")
          case True 
          have "t_pc ?ts' p = ''TD1''" by simp
          with old_sat show ?thesis using T_Call_Deq_def step_T by force 
        next
          case False with old_sat show ?thesis by simp
        qed
      qed

      (* Step 4.2b: data mapping (Condition 5). *)
      show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP)"
          using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u))"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.3: counters and local slot alignment (Condition 12). *)
      show "nid_counter ?ts' = CState.X_var cs'" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts' q = CState.i_var cs' q" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.4: precision of the scan condition (Condition 6). *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx<CState.j_var cs' q. 
               (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
               (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) 
             \<longrightarrow> v \<in> t_scanned ?ts' q)"
      proof (intro allI impI)
        fix q v
        assume pc_q': "c_program_counter cs' q = ''D3''"
        assume "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
        then obtain idx where idx_lt: "idx < CState.j_var cs' q" and
          cond: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
                 (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" by blast

        have q_neq_p: "q \<noteq> p" using pc_q' cs'_update by (auto split: if_splits)
        hence pc_q_old: "c_program_counter cs q = ''D3''" using pc_q' cs'_update by simp
        have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_update by simp
        have arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_update by simp
        have pools_eq: "pools ?ts' v = pools ts v" by simp   
        have scan_eq: "t_scanned ?ts' q = t_scanned ts q" using q_neq_p by simp 

        have pc_v_old: "v \<noteq> p \<Longrightarrow> c_program_counter cs v = c_program_counter cs' v"
        proof -
          assume "v \<noteq> p" then show ?thesis using cs'_update by simp
        qed

        have cond_old: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or>  (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
        proof (cases "CState.Q_arr cs' idx = BOT")
          case True
          with cond have "c_program_counter cs' v = ''E2''" and "CState.i_var cs' v = idx" and "idx \<noteq> BOT" by auto
          have "v \<noteq> p"
          proof
            assume "v = p" with `c_program_counter cs' v = ''E2''` and cs'_update show False by simp
          qed
          hence "c_program_counter cs v = ''E2''" using `c_program_counter cs' v = ''E2''` pc_v_old[OF `v \<noteq> p`] by simp
          moreover have "CState.i_var cs v = idx" using `CState.i_var cs' v = idx` cs'_update by simp
          ultimately show ?thesis using True arr_eq `idx \<noteq> BOT` by auto
        next
          case False
          with cond obtain nid ts_val where in_new: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v)" and ts_not_top: "ts_val \<noteq> TOP" by blast
          have in_old: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v)" using in_new pools_eq arr_eq by simp
          thus ?thesis using False arr_eq ts_not_top by auto
        qed

        have old_cond6: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx<CState.j_var cs q. (CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ts q)"
          using sim_r unfolding Simulation_R_def Let_def by simp

        from old_cond6[rule_format, OF pc_q_old, of v] idx_lt j_eq cond_old have "v \<in> t_scanned ts q" by auto 
        thus "v \<in> t_scanned ?ts' q" using scan_eq by simp
      qed

      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>pa. c_program_counter cs' pa = ''D2'' \<or> c_program_counter cs' pa = ''D3'' \<longrightarrow> (\<forall>idx<CState.l_var cs' pa. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' pa)) \<and> (\<forall>q. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' q = ''E2'' \<and> CState.i_var cs' q = idx \<longrightarrow> t_ts ?ts' q <\<^sub>t\<^sub>s t_startTs ?ts' pa))" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Step 4.5: cross-state monotonicity constraints (Conditions 10, 11, 13, 14, and 15). *)
      show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> v \<in> Val" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val \<longrightarrow> nid < CState.l_var cs' q)" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>q r. c_program_counter cs' q \<in> {''E2'', ''E3''} \<and> c_program_counter cs' r \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts' r) (t_ts ?ts' q) \<longrightarrow> CState.i_var cs' q < CState.l_var cs' r" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto
      show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)" using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

          (* Step 4.6: history and ownership constraints (Conditions 16, 17, 18, and 19). *)
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us') u v sn)"
      proof (intro allI impI, elim conjE)
        fix u nid v ts_val 
        assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts' u)" and not_top: "ts_val \<noteq> TOP"
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)"
          using in_pool by simp
        have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
          using sim_r in_old not_top unfolding Simulation_R_def Let_def by blast
        from old_his show "\<exists>sn. EnqCallInHis (cs', us') u v sn"
        proof
          fix sn
          assume h: "EnqCallInHis (cs, us) u v sn"
          have "EnqCallInHis (cs', us') u v sn"
            using h his_grow
            unfolding EnqCallInHis_def his_seq_def
            by (auto simp: nth_append)
          thus "\<exists>sn. EnqCallInHis (cs', us') u v sn"
            by blast
        qed
      qed

      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow>
        (\<forall>v. v \<in> t_scanned ?ts' q \<longrightarrow>
          (\<exists>idx < CState.j_var cs' q.
            (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
            (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and> InQBack (cs', us') v_val \<and> Idx (cs', us') v_val = idx)))"
      proof (intro allI impI)
        fix q v 
        assume pc_q: "c_program_counter cs' q = ''D3''" 
        assume v_scan: "v \<in> t_scanned ?ts' q"
        
        have q_not_p: "q \<noteq> p"
          using pc_q assms(3) s'_eq by auto
        have pc_q_old: "c_program_counter cs q = ''D3''"
          using pc_q q_not_p cs'_update by simp
        have v_in_old: "v \<in> t_scanned ts q"
          using v_scan q_not_p by simp
        
        have old_fact:
          "\<exists>idx < CState.j_var cs q.
             (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
             (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
          using sim_r pc_q_old v_in_old
          unfolding Simulation_R_def Let_def
          by auto

        then obtain idx where idx_lt: "idx < CState.j_var cs q" and 
          branches: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
                     (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
          by blast

        show "\<exists>idx < CState.j_var cs' q.
                (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
                (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and> InQBack (cs', us') v_val \<and> Idx (cs', us') v_val = idx)"
        proof (rule exI[where x=idx], intro conjI)
          show "idx < CState.j_var cs' q"
            using idx_lt q_not_p cs'_update by simp
        next
          from branches show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
                              (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and> InQBack (cs', us') v_val \<and> Idx (cs', us') v_val = idx)"
          proof
            assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
            hence "v \<noteq> p"
              using pc_L0 by auto
            thus ?thesis
              using b1 cs'_update by auto
          next
            assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
            then obtain v_val sn where
              h1: "EnqCallInHis (cs, us) v v_val sn" and
              h2: "InQBack (cs, us) v_val" and
              h3: "Idx (cs, us) v_val = idx"
              by blast
            
            have new_h1: "EnqCallInHis (cs', us') v v_val sn"
              using h1 his_grow
              unfolding EnqCallInHis_def his_seq_def
              by (auto simp: nth_append)
            
            have new_h2: "InQBack (cs', us') v_val"
              using h2 cs'_update us'_update s_eq s'_eq
              unfolding InQBack_def Model.Qback_arr_def
              by auto
              
            have new_h3: "Idx (cs', us') v_val = idx"
              using h3 cs'_update us'_update s_eq s'_eq
              unfolding Idx_def AtIdx_def Model.Qback_arr_def
              by auto
              
            from new_h1 new_h2 new_h3 show ?thesis
              by blast
          qed
        qed
      qed

      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
            (\<forall>v \<in> t_scanned ?ts' q. \<forall>nid v_val ts_val. 
               (nid, v_val, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
               nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q))"
      proof (intro allI impI ballI, elim conjE) 
        fix q v nid v_val ts_val
        assume pc_q': "c_program_counter cs' q = ''D3''"
        assume v_in_scan: "v \<in> t_scanned ?ts' q"
        assume node: "(nid, v_val, ts_val) \<in> set (pools ?ts' v)" 
        assume ts_not_top: "ts_val \<noteq> TOP"

        have q_neq_p: "q \<noteq> p"
          using pc_q' assms(3) s'_eq by auto
        have pc_q_old: "c_program_counter cs q = ''D3''"
          using pc_q' q_neq_p cs'_update by simp
        have j_eq: "CState.j_var cs' q = CState.j_var cs q"
          using q_neq_p cs'_update by simp
        have startTs_eq: "t_startTs ?ts' q = t_startTs ts q"
          using q_neq_p by simp
        
        have scan_q_old: "v \<in> t_scanned ts q"
          using v_in_scan q_neq_p by simp
        have node_old: "(nid, v_val, ts_val) \<in> set (pools ts v)"
          using node by simp

        have old_cond18: "\<forall>q_x. c_program_counter cs q_x = ''D3'' \<longrightarrow> 
            (\<forall>v_x \<in> t_scanned ts q_x. \<forall>nid_x v_val_x ts_val_x. 
               (nid_x, v_val_x, ts_val_x) \<in> set (pools ts v_x) \<and> ts_val_x \<noteq> TOP \<longrightarrow> 
               nid_x < CState.j_var cs q_x \<or> \<not> ts_less ts_val_x (t_startTs ts q_x))"
          using sim_r unfolding Simulation_R_def Let_def by (metis fst_eqD)

        have "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
          using old_cond18 pc_q_old scan_q_old node_old ts_not_top by blast

        thus "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q)" 
          using j_eq startTs_eq by simp
      qed

      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow>
            (\<forall>u \<in> t_scanned ?ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow>
              CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q))"
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      (* Condition 20: synchronization of the value allocator and local snapshots. *)
      show "CState.V_var cs' = t_V_var ?ts'" 
        using sim_r cs'_update unfolding Simulation_R_def Let_def by auto

      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts' q" 
        using sim_r cs'_update unfolding Simulation_R_def Let_def by (auto split: if_splits)

    qed
  qed
qed


(* ========================================================== *)
(* 18. Simulation lemma for the E1 transition                     *)
(* ========================================================== *)
lemma Simulation_R_E1:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes "Simulation_Inv (cs, us) ts"
      and "C_E1 p cs cs'"
      and "CState.v_var cs p = t_v ts p" 
  shows "\<exists>ts'. T_E1 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  (* Step 0: unpack the key state components. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
    using assms(1) unfolding Simulation_Inv_def by auto

  (* Step 1: extract the current-state assumptions. *)
  have pc_E1: "c_program_counter cs p = ''E1''" 
    using `C_E1 p cs cs'` unfolding C_E1_def by auto
  
  have tpc_TE1: "t_pc ts p = ''TE1''"
    using sim_r pc_E1 unfolding Simulation_R_def Let_def by auto
    
  (* Step 2: construct the aligned TSQ successor state ts' explicitly. *)
  let ?new_nid = "nid_counter ts"
  let ?new_ts = "ts_counter ts"
  let ?val = "t_v ts p"
  
  let ?ts' = "ts\<lparr> 
    nid_counter := ?new_nid + 1,
    ts_counter := ?new_ts + 1,
    t_nid := (\<lambda>x. if x = p then ?new_nid else t_nid ts x),
    t_ts := (\<lambda>x. if x = p then TS ?new_ts else t_ts ts x),
    pools := (\<lambda>x. if x = p then pools ts x @ [(?new_nid, ?val, TOP)] else pools ts x),
    t_pc := (\<lambda>x. if x = p then ''TE2'' else t_pc ts x),
    t_scanned := t_scanned ts,
    t_candNid := t_candNid ts,
    t_candTs  := t_candTs ts,
    t_candPid := t_candPid ts,
    t_startTs := t_startTs ts,
    t_retV    := t_retV ts,
    t_V_var   := t_V_var ts
  \<rparr>"
  
  (* Step 3: show that the TSQ side can perform the corresponding step. *)
  have step_T: "T_E1 p ts ?ts'"
    unfolding T_E1_def Let_def using tpc_TE1 by auto
    
  (* Step 4: extract the key index-bound invariant. *)
  have X_bound_j: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> CState.j_var cs q < CState.X_var cs"
    using inv_sys unfolding system_invariant_def sI6_D3_Scan_Pointers_def program_counter_def j_var_def X_var_def by fastforce
    
  have X_bound_l: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> CState.l_var cs q \<le> CState.X_var cs"
    using inv_sys unfolding system_invariant_def sI6_D3_Scan_Pointers_def program_counter_def l_var_def X_var_def by fastforce

  (* Step 5: extract the crucial data-separation invariant. *)
  have v_not_in_Q: "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> CState.Q_arr cs idx \<noteq> CState.v_var cs p"
  proof (intro allI impI)
    fix idx assume "CState.Q_arr cs idx \<noteq> BOT"
    have "hI1_E_Phase_Pending_Enq (cs, us)" using inv_sys unfolding system_invariant_def by simp
    then have p1: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
      using pc_E1 unfolding hI1_E_Phase_Pending_Enq_def program_counter_def v_var_def by auto
      
    have "hI14_Pending_Enq_Qback_Exclusivity (cs, us)" using inv_sys unfolding system_invariant_def by simp
    then have p2: "CState.Qback_arr cs idx \<noteq> CState.v_var cs p"
      using p1 pc_E1 unfolding hI14_Pending_Enq_Qback_Exclusivity_def program_counter_def Qback_arr_def v_var_def by auto
      
    have "sI8_Q_Qback_Sync (cs, us)" using inv_sys unfolding system_invariant_def by simp
    then have p3: "CState.Q_arr cs idx = CState.Qback_arr cs idx"
      using `CState.Q_arr cs idx \<noteq> BOT` unfolding sI8_Q_Qback_Sync_def Q_arr_def Qback_arr_def by fastforce
      
    show "CState.Q_arr cs idx \<noteq> CState.v_var cs p"
      using p2 p3 by simp
  qed
    
  (* Step 6: reassemble Simulation_R for the successor state. *)
  have sim_R_next: "Simulation_R (cs', us) ?ts'"
    (* Add fst_conv and snd_conv so that the projected state simplifies cleanly. *)
    unfolding Simulation_R_def Let_def fst_conv snd_conv
  proof (intro conjI)
    (* Condition 2: alignment of program counters. *)
    show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts' q = ''TL0''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts' q = ''TE1''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts' q = ''TE2''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts' q = ''TE3''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts' q = ''TD1''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts' q = ''TD_Line4_Done''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts' q = ''TD_Loop''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts' q = ''TD_Remove_Done''" using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto

    (* Condition 3: validity of timestamps in the TSQ pools. *)
    show "\<forall>q. \<forall>node\<in>set (pools ?ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
      using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def Let_def by auto

    (* Condition 5.1: mapping for materialized queue elements. *)
    show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP)"
proof (intro allI impI)
  fix idx assume nz': "CState.Q_arr cs' idx \<noteq> BOT"
  have nz_old: "CState.Q_arr cs idx \<noteq> BOT"
    using nz' `C_E1 p cs cs'` unfolding C_E1_def by auto
have sim_data_map:
  "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow>
     (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
        (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
  using sim_r
  unfolding Simulation_R_def Let_def
  by simp

have ex_old:
  "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
      (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP"
  using sim_data_map nz_old
  by blast

then obtain u nid ts_val where u_in: "u \<in> ProcSet"
  and old_in: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)"
  and nz_ts: "ts_val \<noteq> TOP"
  by blast
  have qeq: "CState.Q_arr cs' idx = CState.Q_arr cs idx"
    using `C_E1 p cs cs'` unfolding C_E1_def by auto
  have new_in: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"
  proof (cases "u = p")
    case True
    then show ?thesis
      using old_in qeq by simp
  next
    case False
    then show ?thesis
      using old_in qeq by simp
  qed
  show "\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
    using u_in new_in nz_ts by blast
qed
      
    (* Condition 5.2: mapping for pending elements. *)
    show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u))"
    proof (intro allI impI, elim conjE)
      fix q idx assume "CState.Q_arr cs' idx = BOT" and pc_q: "c_program_counter cs' q = ''E2''" and i_q: "CState.i_var cs' q = idx"
      show "\<exists>nid. (nid, CState.v_var cs' q, TOP) \<in> set (pools ?ts' q)"
      proof (cases "q = p")
        case True
        have "CState.v_var cs' p = t_v ts p" using `C_E1 p cs cs'` `CState.v_var cs p = t_v ts p` unfolding C_E1_def by auto
        then show ?thesis using True by auto
      next
        case False
        have "c_program_counter cs q = ''E2''" using False pc_q `C_E1 p cs cs'` unfolding C_E1_def by auto
        moreover have "CState.Q_arr cs idx = BOT" using `CState.Q_arr cs' idx = BOT` `C_E1 p cs cs'` unfolding C_E1_def by auto
        moreover have "CState.i_var cs q = idx" using False i_q `C_E1 p cs cs'` unfolding C_E1_def by auto
        ultimately have "\<exists>nid. (nid, CState.v_var cs q, TOP) \<in> set (pools ts q)" using sim_r unfolding Simulation_R_def Let_def
          by simp 
        then show ?thesis using False `C_E1 p cs cs'` unfolding C_E1_def by auto
      qed
    qed

    (* Condition 6: precise bidirectional mapping for dequeue scanning. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
            (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
            (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) 
          \<longrightarrow> v \<in> t_scanned ?ts' q)"  (* Use ?ts' explicitly here. *)
    proof (intro allI impI)
      fix q v
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
      
      have q_neq_p: "q \<noteq> p" using pc_q `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      
      from cond obtain idx where idx_less: "idx < CState.j_var cs q" and 
        cond_branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" using j_q_old
        by auto 
      
      have q_arr_eq: "CState.Q_arr cs' idx = CState.Q_arr cs idx" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto

      have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
      proof (cases "v = p")
        case True
        from cond_branch show ?thesis
        proof
          assume left_cond: "CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)"
          from left_cond obtain nid ts_val where in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' p)" and "ts_val \<noteq> TOP" using True by blast
          have "pools ?ts' p = pools ts p @ [(?new_nid, ?val, TOP)]" by simp
          with in_pool `ts_val \<noteq> TOP` have "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ts p)" by auto
          with left_cond q_arr_eq True show ?thesis using `ts_val \<noteq> TOP` by auto 
        next
          assume "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT"
          with True have "CState.i_var cs' p = idx" by simp
          moreover have "CState.i_var cs' p = CState.X_var cs" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
          moreover have "CState.j_var cs q \<le> CState.X_var cs" using inv_sys pc_q_old unfolding system_invariant_def sI6_D3_Scan_Pointers_def program_counter_def j_var_def X_var_def by fastforce
          ultimately have "idx < idx" using idx_less by simp
          then show ?thesis by simp
        qed
      next
        case False
        with cond_branch q_arr_eq `C_E1 p cs cs'` show ?thesis unfolding C_E1_def Let_def by auto
      qed

      have "v \<in> t_scanned ts q" using sim_r pc_q_old idx_less old_cond unfolding Simulation_R_def Let_def
        by (metis fst_eqD)
      (* At the end, simp transports the old-state fact to the new state automatically. *)
      then show "v \<in> t_scanned ?ts' q" by simp
    qed

    (* Condition 7: uniqueness of TOP nodes in the pool of an E2 thread. *)
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''E2''"
      show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1"
      proof (cases "q = p")
        case True
        have new_pool: "pools ?ts' p = pools ts p @ [(?new_nid, ?val, TOP)]" by simp
        have old_no_top: "filter (\<lambda>node. snd (snd node) = TOP) (pools ts p) = []"
        proof -
          have cond3: "\<forall>node\<in>set (pools ts p). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts p = ''TE2'' \<and> t_nid ts p = fst node" using sim_r unfolding Simulation_R_def Let_def by meson 
          { fix node assume "node \<in> set (pools ts p)" with cond3 tpc_TE1 have "snd (snd node) \<noteq> TOP" by auto }
          then show ?thesis by (simp add: filter_empty_conv)
        qed
        show ?thesis using True new_pool old_no_top by simp
      next
        case False
        have pc_q_old: "c_program_counter cs q = ''E2''" using pc_q False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1" using sim_r pc_q_old unfolding Simulation_R_def Let_def
          by auto 
        moreover have "pools ?ts' q = pools ts q" using False by simp
        ultimately show ?thesis by simp
      qed
    qed

    (* Condition 8: startTs timestamp guard. *)
    show "\<forall>p_x. c_program_counter cs' p_x = ''D2'' \<or> c_program_counter cs' p_x = ''D3'' \<longrightarrow> (\<forall>idx<CState.l_var cs' p_x. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' p_x)) \<and> (\<forall>q. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' q = ''E2'' \<and> CState.i_var cs' q = idx \<longrightarrow> t_ts ?ts' q <\<^sub>t\<^sub>s t_startTs ?ts' p_x))"
    proof (rule allI, rule impI, rule allI, rule impI)
      fix q idx assume pc_q: "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''" and idx_less: "idx < CState.l_var cs' q"
      have "q \<noteq> p" using pc_q `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" using pc_q `C_E1 p cs cs'` `q \<noteq> p` unfolding C_E1_def Let_def by auto
      have l_var_eq: "CState.l_var cs' q = CState.l_var cs q" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using `q \<noteq> p` by simp
      show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
      proof (rule conjI)
        show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)"
        proof (intro impI allI)
          fix u nid ts_val
          assume q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT" and in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"
          have old_q_not_bot: "CState.Q_arr cs idx \<noteq> BOT" using q_not_bot `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
          have neq_v: "CState.Q_arr cs idx \<noteq> CState.v_var cs p" using v_not_in_Q old_q_not_bot by simp
          have old_in: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)"
          proof (cases "u = p")
            case True
            have "CState.Q_arr cs' idx = CState.Q_arr cs idx" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
            with in_pool True `CState.v_var cs p = t_v ts p` neq_v show ?thesis by auto
          next
            case False
            have "CState.Q_arr cs' idx = CState.Q_arr cs idx" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
            with in_pool False show ?thesis by auto
          qed
          have "\<forall>idx<CState.l_var cs q. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)" using sim_r pc_q_old unfolding Simulation_R_def Let_def
            by (metis fst_eqD)
          then show "ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q" using old_in old_q_not_bot idx_less l_var_eq startTs_eq by simp 
        qed

        show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q"
        proof (intro allI impI)
          fix u assume "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
          then have q_bot: "CState.Q_arr cs' idx = BOT" and pc_u: "c_program_counter cs' u = ''E2''" and i_u: "CState.i_var cs' u = idx" by auto
          have "u \<noteq> p"
          proof
            assume "u = p"
            hence "CState.i_var cs' p = idx" using i_u by simp
            moreover have "CState.i_var cs' p = CState.X_var cs" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
            ultimately have "idx = CState.X_var cs" by simp
            have "CState.l_var cs q \<le> CState.X_var cs" using inv_sys pc_q_old unfolding system_invariant_def sI5_D2_Local_Bound_def sI6_D3_Scan_Pointers_def program_counter_def l_var_def X_var_def by fastforce
            with idx_less l_var_eq have "idx < CState.X_var cs" by simp
            with `idx = CState.X_var cs` show False by simp
          qed
          have old_pc_u: "c_program_counter cs u = ''E2''" using pc_u `u \<noteq> p` `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
          have old_q_bot: "CState.Q_arr cs idx = BOT" using q_bot `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
          have old_i_u: "CState.i_var cs u = idx" using i_u `u \<noteq> p` `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
          have ts_eq: "t_ts ?ts' u = t_ts ts u" using `u \<noteq> p` by auto
          have "\<forall>u. CState.Q_arr cs idx = BOT \<and> c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q" using sim_r pc_q_old idx_less l_var_eq unfolding Simulation_R_def Let_def
            by (metis fst_conv)
          then show "t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q" using old_q_bot old_pc_u old_i_u ts_eq startTs_eq by auto
        qed
      qed
    qed

    (* Condition 9: initial candidate values in the D3 loop. *)
    show "\<forall>p_x. c_program_counter cs' p_x = ''D3'' \<longrightarrow> t_candNid ?ts' p_x = BOT \<and> t_candTs ?ts' p_x = TOP"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''D3''"
      have "q \<noteq> p" using pc_q `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q `q \<noteq> p` `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      show "t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP" using sim_r pc_q_old unfolding Simulation_R_def Let_def by simp
    qed  

    (* Condition 10: absolute mapping between concrete indices and pools. *)
    show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
    proof (intro allI impI)
      fix u nid v_val n
      assume in_pool: "(nid, v_val, TS n) \<in> set (pools ?ts' u)"
      have old_in_pool: "(nid, v_val, TS n) \<in> set (pools ts u)"
      proof (cases "u = p")
        case True
        have "pools ?ts' p = pools ts p @ [(?new_nid, ?val, TOP)]" by simp
        with in_pool True show ?thesis by auto
      next
        case False
        then show ?thesis using in_pool by simp
      qed
      have old_cond10: "CState.Q_arr cs nid = v_val \<and> nid < CState.X_var cs" using sim_r old_in_pool unfolding Simulation_R_def Let_def
        by (metis fst_conv) 
      have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have x_var_mono: "CState.X_var cs \<le> CState.X_var cs'" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      show "CState.Q_arr cs' nid = v_val \<and> nid < CState.X_var cs'" using old_cond10 q_arr_eq x_var_mono by auto
    qed

    (* Condition 11: value-range safety of the TSQ pools. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> v \<in> Val"
    proof (intro allI impI)
      fix u nid v_val ts_val
      assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)"
      show "v_val \<in> Val"
      proof (cases "u = p")
        case False
        then have "(nid, v_val, ts_val) \<in> set (pools ts u)" using in_pool by simp
        then show ?thesis using sim_r unfolding Simulation_R_def Let_def
          by meson 
      next
        case True
        have "pools ?ts' p = pools ts p @ [(?new_nid, ?val, TOP)]" by simp
        with in_pool True have "(nid, v_val, ts_val) \<in> set (pools ts p) \<or> (nid, v_val, ts_val) = (?new_nid, ?val, TOP)" by auto
        then show ?thesis
        proof
          assume "(nid, v_val, ts_val) \<in> set (pools ts p)"
          then show ?thesis using sim_r unfolding Simulation_R_def Let_def
            by meson 
        next
          assume "(nid, v_val, ts_val) = (?new_nid, ?val, TOP)"
          then have "v_val = t_v ts p" by simp
          have "CState.v_var cs p = t_v ts p" using `CState.v_var cs p = t_v ts p` by simp
          have "CState.v_var cs p \<in> Val"
          proof -
            have ai13: "hI1_E_Phase_Pending_Enq (cs, us)"
              using inv_sys unfolding system_invariant_def by simp
            then have pending: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
              using pc_E1
              unfolding hI1_E_Phase_Pending_Enq_def program_counter_def
              by (simp add: Model.v_var_def)

            from pending have call_in_his: "EnqCallInHis (cs, us) p (CState.v_var cs p) (s_var (cs, us) p)"
              unfolding HasPendingEnq_def Let_def
              by blast

            have hi12: "hI20_Enq_Val_Valid (cs, us)"
              using inv_sys unfolding system_invariant_def by simp

            from hi12 have val_rule:
              "\<forall>k < length (his_seq (cs, us)).
                 act_name (his_seq (cs, us) ! k) = enq \<longrightarrow> act_val (his_seq (cs, us) ! k) \<in> Val"
              unfolding hI20_Enq_Val_Valid_def Let_def by simp

            obtain e where
              e_in: "e \<in> set (his_seq (cs, us))"
              and e_pid: "act_pid e = p"
              and e_ssn: "act_ssn e = s_var (cs, us) p"
              and e_oper: "act_name e = enq"
              and e_cr: "act_cr e = call"
              and e_val: "act_val e = CState.v_var cs p"
              using call_in_his
              unfolding EnqCallInHis_def Let_def
              by blast

              have "\<exists>k < length (his_seq (cs, us)). his_seq (cs, us) ! k = e"
              using e_in
              by (simp add: in_set_conv_nth)
            then obtain k where
              k_lt: "k < length (his_seq (cs, us))"
              and k_e: "his_seq (cs, us) ! k = e"
              by blast

            have k_eq: "his_seq (cs, us) ! k = mk_act enq (CState.v_var cs p) p (s_var (cs, us) p) call"
              using k_e e_pid e_ssn e_oper e_cr e_val
              unfolding mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def
              by (cases e) auto

            have "act_name (his_seq (cs, us) ! k) = enq"
              using k_eq by (simp add: mk_act_def act_name_def)

            hence "act_val (his_seq (cs, us) ! k) \<in> Val"
              using val_rule k_lt by blast

            thus ?thesis
              using k_eq by (simp add: mk_act_def act_val_def)
          qed
          with `CState.v_var cs p = t_v ts p` `v_val = t_v ts p` show ?thesis by simp
        qed
      qed
    qed

    (* Condition 12: synchronization of the allocation counters and local slots. *)
    show "nid_counter ?ts' = CState.X_var cs'"
    proof -
      have old_counter_eq: "nid_counter ts = CState.X_var cs" using sim_r unfolding Simulation_R_def Let_def
        by simp 
      have new_nid_c: "nid_counter ?ts' = nid_counter ts + 1" by simp
      have new_x_var: "CState.X_var cs' = CState.X_var cs + 1" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      show ?thesis using old_counter_eq new_nid_c new_x_var by simp
    qed

    show "\<forall>p_x. c_program_counter cs' p_x \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts' p_x = CState.i_var cs' p_x"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q \<in> {''E2'', ''E3''}"
      show "t_nid ?ts' q = CState.i_var cs' q"
      proof (cases "q = p")
        case True
        have ghost_assign: "t_nid ?ts' p = nid_counter ts" by simp
        have phys_assign: "CState.i_var cs' p = CState.X_var cs" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have old_counter_eq: "nid_counter ts = CState.X_var cs" using sim_r unfolding Simulation_R_def Let_def
          by simp 
        show ?thesis using True ghost_assign phys_assign old_counter_eq by simp
      next
        case False
        have old_pc_q: "c_program_counter cs q \<in> {''E2'', ''E3''}" using pc_q False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have old_align: "t_nid ts q = CState.i_var cs q" using sim_r old_pc_q unfolding Simulation_R_def Let_def
          by (metis fst_conv) 
        have tsq_eq: "t_nid ?ts' q = t_nid ts q" using False by simp
        have phys_eq: "CState.i_var cs' q = CState.i_var cs q" using False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        show ?thesis using old_align tsq_eq phys_eq by simp
      qed
    qed

    (* Condition 13: cross-state monotonicity. *)
    show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
          (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
    proof (intro allI impI)
      fix q u nid v ts_val
      assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val"
      
      have q_neq_p: "q \<noteq> p" using pc_q `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" using pc_q q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have l_eq: "CState.l_var cs' q = CState.l_var cs q" using q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
      
      have in_old_pool: "(nid, v, ts_val) \<in> set (pools ts u)"
      proof (cases "u = p")
        case True
        have "pools ?ts' p = pools ts p @ [(?new_nid, ?val, TOP)]" by simp
        with cond True have "(nid, v, ts_val) \<in> set (pools ts p @ [(?new_nid, ?val, TOP)])" by auto
        then have "(nid, v, ts_val) \<in> set (pools ts p) \<or> (nid, v, ts_val) = (?new_nid, ?val, TOP)" by auto
        with cond have "(nid, v, ts_val) \<in> set (pools ts p)" by auto
        then show ?thesis using True by simp
      next
        case False
        with cond show ?thesis by simp
      qed
      
      have old_cond13: "\<forall>q. c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
         (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val \<longrightarrow> nid < CState.l_var cs q)"
        using sim_r unfolding Simulation_R_def Let_def
        by (metis fst_eqD) 
        
      from in_old_pool cond startTs_eq have exist_witness: "\<exists>v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q) ts_val" by auto
      show "nid < CState.l_var cs' q" using old_cond13 pc_q_old exist_witness l_eq by metis 
    qed

    (* Condition 14: enqueue/dequeue coherence across the two states. *)
    show "\<forall>p_x q_x. c_program_counter cs' p_x \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q_x \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts' q_x) (t_ts ?ts' p_x) \<longrightarrow> CState.i_var cs' p_x < CState.l_var cs' q_x"
    proof (intro allI impI, elim conjE)
      fix q1 q2
      assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
      assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
      assume not_less: "\<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1)"
      
      have q2_neq_p: "q2 \<noteq> p" using pc_q2 `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}" using pc_q2 q2_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have l_q2_eq: "CState.l_var cs' q2 = CState.l_var cs q2" using q2_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have startTs_eq: "t_startTs ?ts' q2 = t_startTs ts q2" using q2_neq_p by simp
      
      show "CState.i_var cs' q1 < CState.l_var cs' q2"
      proof (cases "q1 = p")
        case True
        have ts_p_new: "t_ts ?ts' p = TS (ts_counter ts)" by simp
        have tpc_q2: "t_pc ts q2 \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
          using sim_r pc_q2_old unfolding Simulation_R_def Let_def by auto
          have "t_startTs ts q2 <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using TSQ_State_InvD_startTs_bound[OF inv_tsq tpc_q2] .
        then have "ts_less (t_startTs ts q2) (t_ts ?ts' p)"
          using ts_p_new by simp
        with not_less startTs_eq show ?thesis using True by simp
      next
        case False
        have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}" using pc_q1 False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have i_q1_eq: "CState.i_var cs' q1 = CState.i_var cs q1" using False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)" using not_less False startTs_eq by simp
        
        have "CState.i_var cs q1 < CState.l_var cs q2"
          using sim_r pc_q1_old pc_q2_old not_less_old unfolding Simulation_R_def Let_def
          by simp 
        with i_q1_eq l_q2_eq show ?thesis by simp
      qed
    qed

    (* Condition 15: monotonicity of historical tickets. *)
    show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E2''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      show "nid < CState.i_var cs' u"
      proof (cases "u = p")
        case True
        have i_var_p: "CState.i_var cs' p = CState.X_var cs" using `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have in_old: "(nid, v, ts_val) \<in> set (pools ts p)" using cond True by auto
        
        obtain n where ts_is_n: "ts_val = TS n" using cond by (cases ts_val) auto
        with in_old have in_old_TS: "(nid, v, TS n) \<in> set (pools ts p)" by simp
        
        have "CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
          using sim_r in_old_TS unfolding Simulation_R_def Let_def
          by (metis fst_conv) 
          
        then show ?thesis using True i_var_p by simp
      next
        case False
        have pc_u_old: "c_program_counter cs u = ''E2''" using pc_u False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond False by simp
        have "nid < CState.i_var cs u"
          using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
          by (metis (lifting) fst_conv)
        then show ?thesis using i_u_eq by simp
      qed
    qed

    show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E3''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      have u_neq_p: "u \<noteq> p" using pc_u `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have pc_u_old: "c_program_counter cs u = ''E3''" using pc_u u_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond u_neq_p by simp
      have "nid \<le> CState.i_var cs u"
        using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
        by (metis (lifting) fst_conv) 
      then show "nid \<le> CState.i_var cs' u" using i_u_eq by simp
    qed

       (* Condition 16: ownership bridge. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
    proof (intro allI impI, elim conjE)
      fix u nid v ts_val
      assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts' u)" and not_top: "ts_val \<noteq> TOP"
      have old_in: "(nid, v, ts_val) \<in> set (pools ts u)"
      proof (cases "u = p")
        case True
        then have "(nid, v, ts_val) \<in> set (pools ts p @ [(?new_nid, ?val, TOP)])"
          using in_pool by simp
        with not_top show ?thesis
          by (simp add: True)
      next
        case False
        then show ?thesis
          using in_pool by simp
      qed
      have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
        using sim_r old_in not_top unfolding Simulation_R_def Let_def by blast
      from old_his show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
      proof
        fix sn
        assume his: "EnqCallInHis (cs, us) u v sn"
        have "EnqCallInHis (cs', us) u v sn"
          using his `C_E1 p cs cs'`
          unfolding C_E1_def EnqCallInHis_def his_seq_def
          by auto
        thus "\<exists>sn. EnqCallInHis (cs', us) u v sn"
          by blast
      qed
    qed

    (* Condition 17: history completeness of the scanned set. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ?ts' q \<longrightarrow> 
            (\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
    proof (intro allI impI)
      fix q v
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume v_scan: "v \<in> t_scanned ?ts' q"
      have q_neq_p: "q \<noteq> p"
        using pc_q_new `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''"
        using pc_q_new q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q"
        using q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have scan_eq: "t_scanned ?ts' q = t_scanned ts q"
        by simp
      
      have old_cond17: "\<exists>idx < CState.j_var cs q. 
          (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        using sim_r pc_q_old v_scan scan_eq
        unfolding Simulation_R_def Let_def
        by simp
        
      then obtain idx where idx_lt: "idx < CState.j_var cs q"
        and branches: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
                       (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        by blast
                       
      show "\<exists>idx < CState.j_var cs' q. 
          (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
      proof (rule exI[where x=idx], rule conjI)
        show "idx < CState.j_var cs' q"
          using idx_lt j_q_eq by simp
      next
        from branches show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                            (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (elim disjE)
          assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
          have v_neq_p: "v \<noteq> p"
            using b1 pc_E1 by auto
          thus ?thesis
            using b1 `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        next
          assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
          then obtain v_val sn where
            his: "EnqCallInHis (cs, us) v v_val sn"
            and inq: "InQBack (cs, us) v_val"
            and idx_eq: "Idx (cs, us) v_val = idx"
            by blast
          have his_new: "EnqCallInHis (cs', us) v v_val sn"
            using his `C_E1 p cs cs'`
            unfolding C_E1_def EnqCallInHis_def his_seq_def
            by auto
          have inq_new: "InQBack (cs', us) v_val" 
          proof -
            from inq obtain k_pos where "Qback_arr (cs, us) k_pos = v_val"
              unfolding InQBack_def by blast
            moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
              using `C_E1 p cs cs'` unfolding C_E1_def Qback_arr_def by simp
            ultimately show ?thesis
              unfolding InQBack_def by blast
          qed
          have idx_new: "Idx (cs', us) v_val = idx"
          proof -
            have "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
              using `C_E1 p cs cs'` unfolding C_E1_def AtIdx_def Qback_arr_def by simp
            thus ?thesis
              using idx_eq unfolding Idx_def by presburger
          qed
          show ?thesis
            using his_new inq_new idx_new by blast
        qed
      qed
    qed

(* Condition 18: boundary constraint for scanned nodes in D3. *)
    show "\<forall>p_x. c_program_counter cs' p_x = ''D3'' \<longrightarrow> 
          (\<forall>u \<in> t_scanned ?ts' p_x. \<forall>nid v_val ts_val.
             (nid, v_val, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> 
             nid < CState.j_var cs' p_x \<or> \<not> ts_less ts_val (t_startTs ?ts' p_x))"
    proof (intro allI impI ballI, elim conjE)
      fix q u nid v_val ts_val
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume u_scan: "u \<in> t_scanned ?ts' q"
      assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)"
      assume not_top: "ts_val \<noteq> TOP"
      
      (* Step 1: show that q cannot be the thread p that is currently allocating a node. *)
      have q_neq_p: "q \<noteq> p" using pc_q_new `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      
      (* Step 2: bridge the concrete and TSQ variables. *)
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have j_var_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
      have scan_eq: "t_scanned ?ts' q = t_scanned ts q" by simp
      
      (* Step 3: relate the pool fact for u back to the old state. *)
      have old_in: "(nid, v_val, ts_val) \<in> set (pools ts u)"
      proof (cases "u = p")
        case True
        then have "(nid, v_val, ts_val) \<in> set (pools ts p @ [(?new_nid, ?val, TOP)])" using in_pool by simp
        with not_top show ?thesis
          by (simp add: True) 
      next
        case False
        then show ?thesis using in_pool by simp
      qed
      
      (* Step 4: extract Condition 18 from the old state. *)
      have old_cond18: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> 
        (\<forall>v \<in> t_scanned ts q. \<forall>nid v_val ts_val. 
          (nid, v_val, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
          nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q))"
        using sim_r unfolding Simulation_R_def Let_def by (metis fst_eqD) 
        
      (* Step 5: apply the old constraint and transport it to the new state. *)
      have "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
        using old_cond18 pc_q_old u_scan old_in not_top scan_eq
        by force 
      then show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q)"
        using j_var_eq startTs_eq by simp
    qed

    (* ========================================================================= *)
    (* Condition 19: protection constraint for pending nodes during the D3 scan phase. *)
    (* ========================================================================= *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>u \<in> t_scanned ?ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
        CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q))"
    proof (intro allI impI ballI)
      fix q u
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume u_scan_new: "u \<in> t_scanned ?ts' q"
      assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"

      (* Step 1: q cannot be the thread p that is taking the E1 -> E2 transition. *)
      have q_neq_p: "q \<noteq> p" using pc_q_new `C_E1 p cs cs'` unfolding C_E1_def Let_def by force
      
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have j_var_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
      have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
      have u_scan_old: "u \<in> t_scanned ts q" using u_scan_new by simp

      show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q)"
      proof (cases "u = p")
        case True
        (* The critical subcase is when u is exactly the thread p that just obtained a fresh ticket. *)
        (* Since p just obtained a fresh ticket, ?new_ts is strictly newer than the old startTs recorded by q. *)
        
        (* Step 1: p obtains a fresh timestamp. *)
        have ts_p_new: "t_ts ?ts' p = TS (ts_counter ts)" using True by simp
        
        (* Step 2: since q is in D3 in the old state, TSQ_State_Inv yields that its startTs is below the current global counter. *)
        have "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
          using inv_tsq pc_q_old sim_r unfolding TSQ_State_Inv_def Simulation_R_def Let_def by force
          
        (* Step 3: therefore the claim that p's fresh ticket is smaller than q's old startTs is impossible. *)
        hence "\<not> ts_less (TS (ts_counter ts)) (t_startTs ts q)"
          using ts_less.elims(2) by fastforce
          
        (* Step 4: discharge the right-hand disjunct via \<not> ts_less. *)
        hence "\<not> ts_less (t_ts ?ts' p) (t_startTs ?ts' q)"
          using ts_p_new startTs_eq by simp
          
        thus ?thesis using True by simp
      next
        case False
        (* Proof note. *)
        have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}"
          using pc_u_new False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
          
        have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
          using sim_r pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def
          by (metis fst_eqD) 
          
        have i_eq: "CState.i_var cs' u = CState.i_var cs u" using False `C_E1 p cs cs'` unfolding C_E1_def Let_def by auto
        have ts_u_eq: "t_ts ?ts' u = t_ts ts u" using False by simp
        
        show ?thesis using old_cond19 j_var_eq i_eq startTs_eq ts_u_eq by simp
      qed
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "CState.V_var cs' = t_V_var ?ts'" 
      using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def by auto

    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts' q" 
      using sim_r `C_E1 p cs cs'` unfolding Simulation_R_def Let_def C_E1_def by (auto split: if_splits)

  qed

  show ?thesis using step_T sim_R_next by blast
qed


(* ========================================================== *)
(* Simulation Step for E2 *)
(* ========================================================== *)

lemma Simulation_R_E2:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes "Simulation_Inv (cs, us) ts"
      and "C_E2 p cs cs'"
      and "t_ts ts p \<noteq> TOP"
      and "p \<in> ProcSet"
  shows "\<exists>ts'. T_E2 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  (* Proof note. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
    using assms(1) unfolding Simulation_Inv_def by auto

  (* Step 1: extract the current-state assumptions. *)
  have pc_E2: "c_program_counter cs p = ''E2''" 
    using `C_E2 p cs cs'` unfolding C_E2_def by auto
  
  have tpc_TE2: "t_pc ts p = ''TE2''"
    using sim_r pc_E2 unfolding Simulation_R_def Let_def by auto
    
  (* Proof note. *)
  let ?ts' = "ts\<lparr> 
    pools := (\<lambda>x. if x = p then pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p) else pools ts x),
    t_pc := (\<lambda>x. if x = p then ''TE3'' else t_pc ts x),
    nid_counter := nid_counter ts,
    ts_counter  := ts_counter ts,
    t_nid       := t_nid ts,
    t_ts        := t_ts ts,
    t_scanned   := t_scanned ts,
    t_candNid   := t_candNid ts,
    t_candTs    := t_candTs ts,
    t_candPid   := t_candPid ts,
    t_startTs   := t_startTs ts,
    t_retV      := t_retV ts,
    t_V_var     := t_V_var ts
  \<rparr>"
  
  (* Proof step. *)
  have step_T: "T_E2 p ts ?ts'"
    unfolding T_E2_def Let_def using tpc_TE2 by auto
    
  (* Proof note. *)
  have Q_update: "CState.Q_arr cs' = (CState.Q_arr cs)(CState.i_var cs p := CState.v_var cs p)"
    using `C_E2 p cs cs'` unfolding C_E2_def Let_def fun_upd_def by auto

  (* Key proof idea. *)
  have sim_R_next: "Simulation_R (cs', us) ?ts'"
    (* Add fst_conv and snd_conv so that the projected state simplifies cleanly. *)
    unfolding Simulation_R_def Let_def fst_conv snd_conv
  proof (intro conjI)
    (* Condition 2. *)
    show "\<forall>p. c_program_counter cs' p = ''L0'' \<longrightarrow> t_pc ?ts' p = ''TL0''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto
    show "\<forall>p. c_program_counter cs' p = ''E1'' \<longrightarrow> t_pc ?ts' p = ''TE1''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto
    show "\<forall>p. c_program_counter cs' p = ''E2'' \<longrightarrow> t_pc ?ts' p = ''TE2''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto
    show "\<forall>p. c_program_counter cs' p = ''E3'' \<longrightarrow> t_pc ?ts' p = ''TE3''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto
    show "\<forall>p. c_program_counter cs' p = ''D1'' \<longrightarrow> t_pc ?ts' p = ''TD1''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto
    show "\<forall>p. c_program_counter cs' p = ''D2'' \<longrightarrow> t_pc ?ts' p = ''TD_Line4_Done''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto
    show "\<forall>p. c_program_counter cs' p = ''D3'' \<longrightarrow> t_pc ?ts' p = ''TD_Loop''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto
    show "\<forall>p. c_program_counter cs' p = ''D4'' \<longrightarrow> t_pc ?ts' p = ''TD_Remove_Done''" using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def Let_def by auto

    (* Condition 3: validity of timestamps in the TSQ pools. *)
    show "\<forall>q. \<forall>node\<in>set (pools ?ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
    proof (intro allI ballI)
      fix q node assume node_in: "node \<in> set (pools ?ts' q)"
      show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
      proof (cases "q = p")
        case True
        have "node \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
          using node_in True by simp
        have "snd (snd node) \<noteq> TOP"
        proof
          assume is_top: "snd (snd node) = TOP"
          have neq_nid: "fst node \<noteq> t_nid ts p"
            using `node \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))` is_top `t_ts ts p \<noteq> TOP` pool_setTs_clears_TOP by fastforce
          have "node \<in> set (pools ts p)"
            using `node \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))` is_top `t_ts ts p \<noteq> TOP` pool_setTs_miss by fastforce
          have "fst node = t_nid ts p"
            using sim_r `node \<in> set (pools ts p)` is_top unfolding Simulation_R_def Let_def by fastforce
          with neq_nid show False by simp
        qed
        then show ?thesis by simp
      next
        case False
        have "node \<in> set (pools ts q)" using node_in False by simp
        have old_cond: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
          using sim_r `node \<in> set (pools ts q)` unfolding Simulation_R_def Let_def by meson 
        have "t_pc ?ts' q = t_pc ts q" using False by simp
        have "t_nid ?ts' q = t_nid ts q" by simp
        with old_cond show ?thesis using False `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      qed
    qed

   (* Condition 5.1: mapping for materialized queue elements. *)
show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP)"
proof (intro allI impI)
  fix idx assume nz': "CState.Q_arr cs' idx \<noteq> BOT"
  show "\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
  proof (cases "idx = CState.i_var cs p")
    case True
    have qeq_new: "CState.Q_arr cs' idx = CState.v_var cs p"
      using True `C_E2 p cs cs'` unfolding C_E2_def by (simp add: Q_update)
have p_in: "p \<in> ProcSet"
  using assms(4) .
    have slot_empty: "CState.Q_arr cs (CState.i_var cs p) = BOT"
      using inv_sys pc_E2
      unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def
      by fastforce
    have top_exists: "\<exists>nid. (nid, CState.v_var cs p, TOP) \<in> set (pools ts p)"
      using sim_r pc_E2 True slot_empty
      unfolding Simulation_R_def Let_def
      by auto
    then obtain nid where old_node: "(nid, CState.v_var cs p, TOP) \<in> set (pools ts p)"
      by blast
    have nid_is_target: "nid = t_nid ts p"
      using sim_r old_node pc_E2
      unfolding Simulation_R_def Let_def
      by fastforce
    have new_in: "(nid, CState.v_var cs p, t_ts ts p) \<in> set (pools ?ts' p)"
      using old_node `t_ts ts p \<noteq> TOP` nid_is_target by auto
        show ?thesis
        proof (intro bexI exI conjI)
          show "p \<in> ProcSet"
            using p_in .
          show "(nid, CState.Q_arr cs' idx, t_ts ts p) \<in> set (pools ?ts' p)"
            using new_in qeq_new by simp
          show "t_ts ts p \<noteq> TOP"
            using `t_ts ts p \<noteq> TOP` .
        qed
  next
    case False
    have qeq_old: "CState.Q_arr cs' idx = CState.Q_arr cs idx"
      using False `C_E2 p cs cs'` unfolding C_E2_def using Q_update by fastforce
    have nz_old: "CState.Q_arr cs idx \<noteq> BOT"
      using nz' qeq_old by simp

    have sim_data_map:
      "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow>
         (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
            (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
      using sim_r
      unfolding Simulation_R_def Let_def
      by simp

    have ex_old:
      "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
          (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP"
      using sim_data_map nz_old
      by blast

    then obtain u nid ts_val where u_in: "u \<in> ProcSet"
      and old_in: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)"
      and not_top: "ts_val \<noteq> TOP"
      by blast

    have new_in: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"
    proof (cases "u = p")
      case True
      have "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p))"
        using old_in True not_top by auto
      then show ?thesis
        using True qeq_old by simp
    next
      case False
      then show ?thesis
        using old_in qeq_old by simp
    qed

    show ?thesis
      using u_in new_in not_top by blast
  qed
qed
      
    (* Condition 5.2: mapping for pending elements. *)
    show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u))"
    proof (intro allI impI, elim conjE)
      fix u idx
      assume "CState.Q_arr cs' idx = BOT" and pc_u: "c_program_counter cs' u = ''E2''" and i_u: "CState.i_var cs' u = idx"
      have pc_p_next: "c_program_counter cs' p = ''E3''" 
        using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have "u \<noteq> p" using pc_u pc_p_next by force

      have old_pc_u: "c_program_counter cs u = ''E2''" 
        using pc_u `u \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have old_i_u: "CState.i_var cs u = idx" 
        using i_u `u \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto

      have "CState.i_var cs u \<noteq> CState.i_var cs p"
        using inv_sys pc_E2 old_pc_u `u \<noteq> p`
        unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def by fastforce
      then have "idx \<noteq> CState.i_var cs p" using old_i_u by simp

      have old_q_bot: "CState.Q_arr cs idx = BOT"
        using `CState.Q_arr cs' idx = BOT` `idx \<noteq> CState.i_var cs p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto

      have "\<exists>nid. (nid, CState.v_var cs u, TOP) \<in> set (pools ts u)"
        using sim_r old_q_bot old_pc_u old_i_u unfolding Simulation_R_def Let_def
        by auto 
      then show "\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u)"
        using `u \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by simp
    qed

    (* Proof note. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
            (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
            (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) 
          \<longrightarrow> v \<in> t_scanned ?ts' q)"
    proof (intro allI impI)
      fix q v
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
      
      have q_not_p: "q \<noteq> p" using pc_q `C_E2 p cs cs'` unfolding C_E2_def Let_def by force

      show "v \<in> t_scanned ?ts' q"
      proof -
        from cond obtain idx where idx_less: "idx < CState.j_var cs' q" and 
          cond_branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" by blast
          
        show ?thesis
        proof (cases "idx = CState.i_var cs p")
          case True
          have v_not_bot: "CState.v_var cs p \<noteq> BOT"
proof -
  have pc_s: "program_counter (cs, us) p = ''E2''"
    using pc_E2 unfolding program_counter_def by simp

  have pending: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
    using E2_implies_HasPendingEnq[OF inv_sys pc_s]
    unfolding v_var_def by simp

  from pending have call_in_his:
    "EnqCallInHis (cs, us) p (CState.v_var cs p) (s_var (cs, us) p)"
    unfolding HasPendingEnq_def Let_def by blast

  from call_in_his obtain e where
    e_in: "e \<in> set (his_seq (cs, us))"
    and e_pid: "act_pid e = p"
    and e_ssn: "act_ssn e = s_var (cs, us) p"
    and e_oper: "act_name e = enq"
    and e_cr: "act_cr e = call"
    and e_val: "act_val e = CState.v_var cs p"
    unfolding EnqCallInHis_def Let_def by blast

  have "\<exists>tc < length (his_seq (cs, us)). his_seq (cs, us) ! tc = e"
    using e_in by (simp add: in_set_conv_nth)
  then obtain tc where
    tc_lt: "tc < length (his_seq (cs, us))"
    and tc_eq: "his_seq (cs, us) ! tc = e"
    by blast

  have tc_oper: "act_name (his_seq (cs, us) ! tc) = enq"
    using tc_eq e_oper by simp
  have tc_val: "act_val (his_seq (cs, us) ! tc) = CState.v_var cs p"
    using tc_eq e_val by simp

  have hi12: "hI20_Enq_Val_Valid (cs, us)"
    using inv_sys unfolding system_invariant_def by simp

  have "CState.v_var cs p \<in> Val"
    using hi12 tc_lt tc_oper tc_val
    unfolding hI20_Enq_Val_Valid_def by auto

  then show ?thesis
    unfolding Val_def BOT_def by auto
qed

          have q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT" 
            using True `C_E2 p cs cs'` v_not_bot unfolding C_E2_def Let_def by (simp add: Q_update)
            
          have v_is_p: "v = p"
          proof (rule ccontr)
            assume "v \<noteq> p"
            from cond_branch consider (d_case) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP" 
                              | (e_case) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' v = ''E2''" "CState.i_var cs' v = idx" "idx \<noteq> BOT" by blast
            then show False
            proof cases
              case d_case
              then obtain nid ts_val where "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v)" and "ts_val \<noteq> TOP" by blast
              then have in_old: "(nid, CState.v_var cs p, ts_val) \<in> set (pools ts v)"
                using `v \<noteq> p` True `C_E2 p cs cs'` unfolding C_E2_def Let_def by (simp add: Q_update)
                
              have old_q_bot: "CState.Q_arr cs idx = BOT"
                using inv_sys pc_E2 True unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def by fastforce
              
              have "CState.v_var cs p \<notin> {CState.Q_arr cs k | k. CState.Q_arr cs k \<noteq> BOT}"
              proof
                assume "CState.v_var cs p \<in> {CState.Q_arr cs k | k. CState.Q_arr cs k \<noteq> BOT}"
                then obtain k where "CState.Q_arr cs k = CState.v_var cs p" and "CState.Q_arr cs k \<noteq> BOT"
                  by auto 
                
                (* Proof step. *)
                have "hI1_E_Phase_Pending_Enq (cs, us)" using inv_sys unfolding system_invariant_def by simp
                then have pending: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
                  using pc_E2 unfolding hI1_E_Phase_Pending_Enq_def program_counter_def v_var_def by auto
                  
                (* Proof step. *)
                have "hI14_Pending_Enq_Qback_Exclusivity (cs, us)" using inv_sys unfolding system_invariant_def by simp
                then have qback_neq: "CState.Qback_arr cs k \<noteq> CState.v_var cs p"
                proof -
                  (* Pool/array correspondence note. *)
                  have "k \<noteq> CState.i_var cs p"
                  proof
                    assume "k = CState.i_var cs p"
                    have "sI3_E2_Slot_Exclusive (cs, us)" using inv_sys unfolding system_invariant_def by simp
                    then have "CState.Q_arr cs k = BOT" 
                      using pc_E2 `k = CState.i_var cs p` unfolding sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def by auto
                    thus False using `CState.Q_arr cs k \<noteq> BOT` by simp
                  qed
                  
                  (* Pool/array correspondence note. *)
                  with `hI14_Pending_Enq_Qback_Exclusivity (cs, us)` pending pc_E2 show ?thesis
                    unfolding hI14_Pending_Enq_Qback_Exclusivity_def program_counter_def Qback_arr_def v_var_def
                    using Model.i_var_def by force
                qed
                
                (* Proof step. *)
                have "sI8_Q_Qback_Sync (cs, us)" using inv_sys unfolding system_invariant_def by simp
                then have "CState.Q_arr cs k = CState.Qback_arr cs k"
                  using `CState.Q_arr cs k \<noteq> BOT` unfolding sI8_Q_Qback_Sync_def Q_arr_def Qback_arr_def by fastforce
                  
                (* Proof step. *)
                with `CState.Q_arr cs k = CState.v_var cs p` qback_neq show False by simp
              qed   

              (* Proof note. *)
              show False 
              proof -
                (* Proof step. *)
                from \<open>ts_val \<noteq> TOP\<close> obtain n where ts_eq: "ts_val = TS n" by (cases ts_val) auto
                
                (* Proof step. *)
                have "CState.Q_arr cs nid = CState.v_var cs p"
                  using sim_r in_old ts_eq unfolding Simulation_R_def Let_def
                  using inv_sys node_in_pool_implies_Q_nonempty sim_r by auto 
                  
                (* Proof step. *)
                moreover have "CState.v_var cs p \<in> Val"
                  using sim_r in_old unfolding Simulation_R_def Let_def
                  by meson 
                hence "CState.v_var cs p \<noteq> BOT" unfolding Val_def BOT_def by auto
                
                (* Proof step. *)
                ultimately have "CState.Q_arr cs nid \<noteq> BOT" by simp
                
                (* Proof step. *)
                hence "CState.v_var cs p \<in> {CState.Q_arr cs k | k. CState.Q_arr cs k \<noteq> BOT}"
                  using \<open>CState.Q_arr cs nid = CState.v_var cs p\<close>
                  by (metis (mono_tags, lifting) mem_Collect_eq)
                  
                (* Proof note. *)
                with \<open>CState.v_var cs p \<notin> {CState.Q_arr cs k | k. CState.Q_arr cs k \<noteq> BOT}\<close> 
                show ?thesis
                  by auto 
              qed
            next
              case e_case
              with q_not_bot show False by simp
            qed
          qed
          
          have "p \<in> t_scanned ts q"
          proof -
            have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_not_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
            have idx_less_old: "idx < CState.j_var cs q" using idx_less q_not_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
            have old_q_bot: "CState.Q_arr cs idx = BOT" using inv_sys pc_E2 True unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def by fastforce
            have old_i_p: "CState.i_var cs p = idx" using True by simp
            have old_pc_p: "c_program_counter cs p = ''E2''" using pc_E2 by simp
            
            have idx_not_bot: "idx \<noteq> BOT" 
            proof -
              have "CState.i_var cs p \<in> Val" 
                using inv_sys pc_E2 unfolding system_invariant_def sI3_E2_Slot_Exclusive_def
                using Model.i_var_def program_counter_def by auto 
              then show ?thesis using True unfolding Val_def BOT_def by auto
            qed
            
            have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts p) \<and> ts_val \<noteq> TOP)) \<or> 
                            (CState.Q_arr cs idx = BOT \<and> c_program_counter cs p = ''E2'' \<and> CState.i_var cs p = idx \<and> idx \<noteq> BOT)" 
              using old_q_bot old_pc_p old_i_p idx_not_bot by simp
            show "p \<in> t_scanned ts q"
              using sim_r pc_q_old idx_less_old old_cond unfolding Simulation_R_def Let_def
              by (metis fst_conv)
          qed
          then show ?thesis using v_is_p by simp
        next
          case False
          have old_q_arr: "CState.Q_arr cs' idx = CState.Q_arr cs idx" 
            using False `C_E2 p cs cs'` unfolding C_E2_def Let_def by fastforce
          have old_i_var: "CState.i_var cs' v = CState.i_var cs v"
            using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
          
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_not_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
          have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using q_not_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
          have idx_less_old: "idx < CState.j_var cs q" using idx_less j_q_old by simp

          have old_cond: "((CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                           (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT))"
          proof -
            from cond_branch consider (d_case) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP" 
                              | (e_case) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' v = ''E2''" "CState.i_var cs' v = idx" "idx \<noteq> BOT" by blast
            then show ?thesis
            proof cases
              case e_case
              have v_neq_p: "v \<noteq> p" using e_case(2) `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
              have pc_v_old: "c_program_counter cs v = ''E2''" using e_case(2) v_neq_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
              show ?thesis using old_q_arr old_i_var e_case pc_v_old by auto
            next
              case d_case
              then obtain nid ts_val where node: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ?ts' v)" and not_top: "ts_val \<noteq> TOP" 
                using old_q_arr by auto
              
              have "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v)"
              proof (cases "v = p")
                case True
                have val_neq: "CState.Q_arr cs idx \<noteq> CState.v_var cs p"
                proof -
                  have pc_s: "program_counter (cs, us) p = ''E2''" using pc_E2 unfolding program_counter_def by simp
                  have p1: "HasPendingEnq (cs, us) p (CState.v_var cs p)" using E2_implies_HasPendingEnq[OF inv_sys pc_s] unfolding v_var_def by simp
                  have "hI14_Pending_Enq_Qback_Exclusivity (cs, us)" using inv_sys unfolding system_invariant_def by simp
                  then have p2: "CState.Qback_arr cs idx \<noteq> CState.v_var cs p"
                    using p1 pc_s unfolding hI14_Pending_Enq_Qback_Exclusivity_def program_counter_def Qback_arr_def v_var_def
                    using False Model.i_var_def by fastforce 
                  have "sI8_Q_Qback_Sync (cs, us)" using inv_sys unfolding system_invariant_def by simp
                  then have p3: "CState.Q_arr cs idx = CState.Qback_arr cs idx"
                    using d_case old_q_arr unfolding sI8_Q_Qback_Sync_def Q_arr_def Qback_arr_def by fastforce
                  show ?thesis using p2 p3 by simp
                qed
                
                have in_new_p: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ?ts' p)" 
                  using True node by blast 
                
                have "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts p) \<or> 
                      (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p))"
                  using in_set_pool_setTs[of nid "CState.Q_arr cs idx" ts_val "pools ts p" "t_nid ts p" "t_ts ts p"] node True
                  by simp
                then show ?thesis
                proof
                  assume "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts p)"
                  then show ?thesis by (simp add: True) 
                next
                  assume "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p)"
                  then have "(nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p)" by auto 
                  have "CState.Q_arr cs idx = CState.v_var cs p"
                    using pool_node_value_is_v_var[OF assms(1) `(nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p)`] pc_E2 by blast
                  with val_neq show ?thesis by simp
                qed
              next
                case False_v: False
                then show ?thesis using node by simp
              qed
              then show ?thesis using d_case old_q_arr not_top by auto 
            qed
          qed
          
          have "v \<in> t_scanned ts q"
            using sim_r pc_q_old idx_less_old old_cond unfolding Simulation_R_def Let_def
            by (metis fst_eqD) 
            
          then show ?thesis by simp
        qed
      qed
    qed

    (* pending *)
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''E2''"
      have "q \<noteq> p"
      proof
        assume "q = p"
        with pc_q have "c_program_counter cs' p = ''E2''" by simp
        moreover have "c_program_counter cs' p = ''E3''" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        ultimately show False by simp
      qed
      have old_pc: "c_program_counter cs q = ''E2''" using pc_q `q \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have "pools ?ts' q = pools ts q" using `q \<noteq> p` by simp
      moreover have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
        using sim_r old_pc unfolding Simulation_R_def Let_def
        by auto 
      ultimately show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1" by simp
    qed

    (* This fact is shared by the D2 and D3 cases. *)
    show "\<forall>p_x. c_program_counter cs' p_x = ''D2'' \<or> c_program_counter cs' p_x = ''D3'' \<longrightarrow> 
          (\<forall>idx<CState.l_var cs' p_x. 
            (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' p_x)) \<and> 
            (\<forall>q. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' q = ''E2'' \<and> CState.i_var cs' q = idx \<longrightarrow> t_ts ?ts' q <\<^sub>t\<^sub>s t_startTs ?ts' p_x))"
    proof (rule allI, rule impI, rule allI, rule impI)
      fix q idx assume pc_q: "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''" and idx_less: "idx < CState.l_var cs' q"
      have q_not_p: "q \<noteq> p" using pc_q `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" using pc_q `C_E2 p cs cs'` `q \<noteq> p` unfolding C_E2_def Let_def by auto
      have l_var_eq: "CState.l_var cs' q = CState.l_var cs q" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using q_not_p by simp

      show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
      proof (rule conjI)
        
        show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)"
        proof (intro impI allI)
          fix u nid ts_val
          assume q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT"
          assume in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"
          
          show "ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q"
          proof (cases "idx = CState.i_var cs p")
            case True
            have old_pc_p: "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def by auto
            have old_i_p: "CState.i_var cs p = idx" using True by simp
            have old_Q_bot: "CState.Q_arr cs idx = BOT" using inv_sys old_pc_p old_i_p unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def by fastforce
            
            have idx_less_old: "idx < CState.l_var cs q" using idx_less l_var_eq by simp
            
            have ts_p_less: "t_ts ts p <\<^sub>t\<^sub>s t_startTs ts q"
              using sim_r pc_q_old idx_less_old old_Q_bot old_pc_p old_i_p 
              unfolding Simulation_R_def Let_def
              by (metis fst_conv)
              
            have "CState.Q_arr cs' idx = CState.v_var cs p" using True `C_E2 p cs cs'` unfolding C_E2_def Let_def by (simp add: Q_update)
            with in_pool have pool_has_v: "(nid, CState.v_var cs p, ts_val) \<in> set (pools ?ts' u)" by simp
            
            have "u = p"
            proof (rule ccontr)
              assume "u \<noteq> p"
              then have "pools ?ts' u = pools ts u" by simp
              with pool_has_v have in_u: "(nid, CState.v_var cs p, ts_val) \<in> set (pools ts u)" by simp
              have "\<exists>nid_p. (nid_p, CState.v_var cs p, TOP) \<in> set (pools ts p)"
                using sim_r old_Q_bot old_pc_p old_i_p unfolding Simulation_R_def Let_def
                by auto
              then obtain nid_p where in_p: "(nid_p, CState.v_var cs p, TOP) \<in> set (pools ts p)" by blast
              show False using inv_tsq in_u in_p `u \<noteq> p` unfolding TSQ_State_Inv_def
                by metis
            qed
            
            have "ts_val = t_ts ts p"
            proof (rule ccontr)
              assume "ts_val \<noteq> t_ts ts p"
              have in_p_new: "(nid, CState.v_var cs p, ts_val) \<in> set (pools ?ts' p)" using pool_has_v `u = p` by simp
              have in_p_old: "(nid, CState.v_var cs p, ts_val) \<in> set (pools ts p)"
                using in_set_pool_setTs[of nid "CState.v_var cs p" ts_val "pools ts p" "t_nid ts p" "t_ts ts p"] in_p_new `ts_val \<noteq> t_ts ts p`
                `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
              have "\<exists>nid_p. (nid_p, CState.v_var cs p, TOP) \<in> set (pools ts p)"
                using sim_r old_Q_bot old_pc_p old_i_p unfolding Simulation_R_def Let_def
                by auto 
              then obtain nid_p where in_p_top: "(nid_p, CState.v_var cs p, TOP) \<in> set (pools ts p)" by blast
              have "ts_val = TOP"
                using inv_tsq in_p_old in_p_top unfolding TSQ_State_Inv_def
                by metis 
              have "(nid, CState.v_var cs p, TOP) \<in> set (pools ?ts' p)" using in_p_new `ts_val = TOP` by simp
              have "nid = t_nid ts p"
                using sim_r in_p_old `ts_val = TOP` unfolding Simulation_R_def Let_def by force
              have "(t_nid ts p, CState.v_var cs p, TOP) \<notin> set (pools ?ts' p)"
                using pool_setTs_clears_TOP `C_E2 p cs cs'` `t_ts ts p \<noteq> TOP` unfolding C_E2_def Let_def by fastforce
              show False using `(nid, CState.v_var cs p, TOP) \<in> set (pools ?ts' p)` `nid = t_nid ts p` `(t_nid ts p, CState.v_var cs p, TOP) \<notin> set (pools ?ts' p)` by simp
            qed
            
            then show ?thesis using ts_p_less startTs_eq by auto
          next
            case False
            have "CState.Q_arr cs' idx = CState.Q_arr cs idx"
              using False `C_E2 p cs cs'` unfolding C_E2_def Let_def by (simp add: Q_update)
            have old_q_not_bot: "CState.Q_arr cs idx \<noteq> BOT" using q_not_bot `CState.Q_arr cs' idx = CState.Q_arr cs idx` by simp
            
            have in_old_pool: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)"
            proof (cases "u = p")
              case True
              have val_neq: "CState.Q_arr cs idx \<noteq> CState.v_var cs p"
              proof -
                have pc_s: "program_counter (cs, us) p = ''E2''" using pc_E2 unfolding program_counter_def by simp
                have p1: "HasPendingEnq (cs, us) p (CState.v_var cs p)" using E2_implies_HasPendingEnq[OF inv_sys pc_s] unfolding v_var_def by simp
                have "hI14_Pending_Enq_Qback_Exclusivity (cs, us)" using inv_sys unfolding system_invariant_def by simp
                then have p2: "CState.Qback_arr cs idx \<noteq> CState.v_var cs p"
                  using p1 pc_s unfolding hI14_Pending_Enq_Qback_Exclusivity_def program_counter_def Qback_arr_def v_var_def
                  using False Model.i_var_def by fastforce 
                have "sI8_Q_Qback_Sync (cs, us)" using inv_sys unfolding system_invariant_def by simp
                then have p3: "CState.Q_arr cs idx = CState.Qback_arr cs idx"
                  using old_q_not_bot unfolding sI8_Q_Qback_Sync_def Q_arr_def Qback_arr_def by fastforce
                show ?thesis using p2 p3 by simp
              qed
              
              have in_new_p: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ?ts' p)" 
                using in_pool True `CState.Q_arr cs' idx = CState.Q_arr cs idx` by simp
              
              have "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts p) \<or> 
                     (nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p))"
                using in_set_pool_setTs[of nid "CState.Q_arr cs idx" ts_val "pools ts p" "t_nid ts p" "t_ts ts p"] in_new_p
                `C_E2 p cs cs'` unfolding C_E2_def Let_def by simp
              then show ?thesis
              proof
                assume "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts p)"
                then show ?thesis by (simp add: True) 
              next
                assume "nid = t_nid ts p \<and> ts_val = t_ts ts p \<and> (nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p)"
                then have "(nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p)" by auto 
                have pc_E2_local: "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def by auto
                have "CState.Q_arr cs idx = CState.v_var cs p"
                  using pool_node_value_is_v_var[OF assms(1) `(nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts p)`] pc_E2_local by blast
                with val_neq show ?thesis by simp
              qed
            next
              case False
              then show ?thesis using in_pool `CState.Q_arr cs' idx = CState.Q_arr cs idx` `C_E2 p cs cs'` unfolding C_E2_def Let_def by simp
            qed
            
            have idx_less_old: "idx < CState.l_var cs q" using idx_less l_var_eq by simp
            have "ts_val <\<^sub>t\<^sub>s t_startTs ts q"
              using sim_r pc_q_old idx_less_old old_q_not_bot in_old_pool unfolding Simulation_R_def Let_def
              by (metis split_pairs2) 
              
            then show ?thesis using startTs_eq by simp
          qed
        qed

        show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q"
        proof (intro allI impI)
          fix u assume cond: "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
          
          have "u \<noteq> p" using cond `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
          
          have old_pc_u: "c_program_counter cs u = ''E2''" 
            using cond `u \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
          have old_i_u: "CState.i_var cs u = idx" 
            using cond `u \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
            
          have pc_p_cs: "c_program_counter cs p = ''E2''"
            using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
            
          have "CState.i_var cs u \<noteq> CState.i_var cs p"
            using inv_sys old_pc_u pc_p_cs `u \<noteq> p`
            unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def by fastforce
            
          then have idx_not_p: "idx \<noteq> CState.i_var cs p" 
            using old_i_u by simp
          
          have old_q_bot: "CState.Q_arr cs idx = BOT" 
            using cond idx_not_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
            
          have idx_less_old: "idx < CState.l_var cs q" 
            using idx_less l_var_eq by simp
            
          have ts_eq: "t_ts ?ts' u = t_ts ts u" using `u \<noteq> p` by simp
          
          have "t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q"
            using sim_r pc_q_old idx_less_old old_q_bot old_pc_u old_i_u unfolding Simulation_R_def Let_def
            by (metis fst_conv)
            
          then show "t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q" 
            using ts_eq startTs_eq by simp
        qed
      qed
    qed

    (* Condition 9: initial candidate values in the D3 loop. *)
    show "\<forall>p_x. c_program_counter cs' p_x = ''D3'' \<longrightarrow> t_candNid ?ts' p_x = BOT \<and> t_candTs ?ts' p_x = TOP"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''D3''"
      have "q \<noteq> p" using pc_q `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q `q \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      show "t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP" using sim_r pc_q_old unfolding Simulation_R_def Let_def by simp
    qed

    (* Nid-related proof note. *)
    show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
    proof (intro allI impI)
      fix u nid v_val n
      assume in_pool: "(nid, v_val, TS n) \<in> set (pools ?ts' u)"
      have x_var_eq: "CState.X_var cs' = CState.X_var cs" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      show "CState.Q_arr cs' nid = v_val \<and> nid < CState.X_var cs'"
      proof (cases "u = p")
        case True
        have p_E2: "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have "((nid, v_val, TS n) \<in> set (pools ts p)) \<or> (TS n = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p)"
        proof -
          have "pools ?ts' p = pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p)" by simp
          with in_pool show ?thesis using pool_setTs_set_cases by (simp add: True) 
        qed
        then show ?thesis
        proof
          assume old_node: "(nid, v_val, TS n) \<in> set (pools ts p)"
          have old_cond10: "CState.Q_arr cs nid = v_val \<and> nid < CState.X_var cs" using sim_r old_node unfolding Simulation_R_def Let_def
            by (metis fst_eqD)
          have "nid \<noteq> CState.i_var cs p" 
          proof
            assume "nid = CState.i_var cs p"
            have "CState.Q_arr cs nid = BOT" using inv_sys p_E2 `nid = CState.i_var cs p` unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def by fastforce
            with old_cond10 have "v_val = BOT" by simp
            have "v_val \<noteq> BOT"
            proof -
              have "v_val \<in> Val" using sim_r old_node unfolding Simulation_R_def Let_def
                by meson 
              then show ?thesis unfolding Val_def BOT_def by auto
            qed
            with `v_val = BOT` show False by simp
          qed
          have "CState.Q_arr cs' nid = CState.Q_arr cs nid" using `C_E2 p cs cs'` `nid \<noteq> CState.i_var cs p` unfolding C_E2_def Let_def by auto
          with old_cond10 x_var_eq show ?thesis by simp
        next
          assume new_upd: "TS n = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p"
          have nid_eq_ivar: "nid = CState.i_var cs p"
          proof -
            have ghost_nid: "nid = t_nid ts p" using new_upd by simp
            have phys_nid: "t_nid ts p = CState.i_var cs p" using sim_r p_E2 unfolding Simulation_R_def Let_def
              by simp 
            show ?thesis using ghost_nid phys_nid by simp
          qed
          have v_eq_vvar: "v_val = CState.v_var cs p"
            using sim_r p_E2 new_upd unfolding Simulation_R_def Let_def by (metis assms(1) insertCI pool_node_value_is_v_var)
          have q_arr_eq: "CState.Q_arr cs' nid = CState.v_var cs p" 
            using `C_E2 p cs cs'` nid_eq_ivar unfolding C_E2_def Let_def by auto
          have part1: "CState.Q_arr cs' nid = v_val" using q_arr_eq v_eq_vvar by simp
          have part2: "nid < CState.X_var cs'"
            using inv_sys p_E2 nid_eq_ivar x_var_eq unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def X_var_def by fastforce
          show ?thesis using part1 part2 by simp
        qed
      next
        case False
        have old_in_pool: "(nid, v_val, TS n) \<in> set (pools ts u)"
          using in_pool False `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have old_cond10: "CState.Q_arr cs nid = v_val \<and> nid < CState.X_var cs"
          using sim_r old_in_pool unfolding Simulation_R_def Let_def
          by (metis fst_eqD) 
        have p_E2: "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have "nid \<noteq> CState.i_var cs p"
        proof
          assume "nid = CState.i_var cs p"
          have "CState.Q_arr cs nid = BOT" using inv_sys p_E2 `nid = CState.i_var cs p` unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def by fastforce
          with old_cond10 have "v_val = BOT" by simp
          have "v_val \<in> Val" using sim_r old_in_pool unfolding Simulation_R_def Let_def
            by meson 
          moreover have "BOT \<notin> Val" unfolding Val_def BOT_def by auto
          ultimately show False using `v_val = BOT` by blast
        qed
        have "CState.Q_arr cs' nid = CState.Q_arr cs nid" using `C_E2 p cs cs'` `nid \<noteq> CState.i_var cs p` unfolding C_E2_def Let_def by auto
        with old_cond10 x_var_eq show ?thesis by simp
      qed
    qed

    (* Condition 11: value-range safety of the TSQ pools. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> v \<in> Val"
    proof (intro allI impI)
      fix u nid v_val ts_val
      assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)"
      show "v_val \<in> Val"
      proof (cases "u = p")
        case True
        have "pools ?ts' p = pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p)" by simp
        with in_pool True have "((nid, v_val, ts_val) \<in> set (pools ts p)) \<or> (ts_val = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p)"
          using pool_setTs_set_cases by simp 
        then show ?thesis
        proof                                                                                  
          assume "(nid, v_val, ts_val) \<in> set (pools ts p)"
          then show ?thesis using sim_r unfolding Simulation_R_def Let_def
            by meson
        next
          assume "ts_val = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p"
          then have "(nid, v_val, TOP) \<in> set (pools ts p)" by auto 
          then show ?thesis using sim_r unfolding Simulation_R_def Let_def
            by meson 
        qed
      next
        case False
        have "(nid, v_val, ts_val) \<in> set (pools ts u)" 
          using in_pool False `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        then show ?thesis using sim_r unfolding Simulation_R_def Let_def
          by meson 
      qed
    qed

    (* Condition 12: synchronization of the allocation counters and local slots. *)
    show "nid_counter ?ts' = CState.X_var cs'"
    proof -
      have old_eq: "nid_counter ts = CState.X_var cs" 
        using sim_r unfolding Simulation_R_def Let_def
        by auto 
      have "nid_counter ?ts' = nid_counter ts" by simp
      moreover have "CState.X_var cs' = CState.X_var cs" 
        using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      ultimately show ?thesis using old_eq by simp
    qed

    show "\<forall>p_x. c_program_counter cs' p_x \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts' p_x = CState.i_var cs' p_x"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q \<in> {''E2'', ''E3''}"
      have nid_unchanged: "t_nid ?ts' q = t_nid ts q" by simp
      have ivar_unchanged: "CState.i_var cs' q = CState.i_var cs q" 
        using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      show "t_nid ?ts' q = CState.i_var cs' q"
      proof (cases "q = p")
        case True
        have old_pc_p: "c_program_counter cs p = ''E2''" 
          using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        then have "c_program_counter cs p \<in> {''E2'', ''E3''}" by simp
        with sim_r have "t_nid ts p = CState.i_var cs p" 
          unfolding Simulation_R_def Let_def
          by (metis fst_conv) 
        with nid_unchanged ivar_unchanged True show ?thesis by simp
      next
        case False
        have old_pc_q: "c_program_counter cs q \<in> {''E2'', ''E3''}"
          using pc_q False `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        with sim_r have "t_nid ts q = CState.i_var cs q" 
          unfolding Simulation_R_def Let_def
          by (metis fst_eqD) 
        with nid_unchanged ivar_unchanged show ?thesis by simp
      qed
    qed

    (* Proof note. *)
    show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
         (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
    proof (intro allI impI allI impI)
      fix q u nid v_val ts_val
      assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
      assume prems: "(nid, v_val, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val"
      
      have in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)" 
        and not_top: "ts_val \<noteq> TOP" 
        and not_less: "\<not> ts_less (t_startTs ?ts' q) ts_val" using prems by auto
        
      have q_ne_p: "q \<noteq> p" using pc_q `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
      have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" 
        using pc_q q_ne_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" 
        using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have start_eq: "t_startTs ?ts' q = t_startTs ts q" by simp
      
      show "nid < CState.l_var cs' q"
      proof (cases "u = p")
        case False
        have in_old_pool: "(nid, v_val, ts_val) \<in> set (pools ts u)" 
          using in_pool False `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        show ?thesis using sim_r pc_q_old in_old_pool not_top not_less start_eq l_q_eq unfolding Simulation_R_def Let_def
          by (metis (lifting) fst_eqD)
      next
        case True
        have p_E2: "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have pool_eq: "pools ?ts' p = pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p)" by simp
        with in_pool True have cases: "((nid, v_val, ts_val) \<in> set (pools ts p)) \<or> (ts_val = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p)"
          using pool_setTs_set_cases by simp 
        then show ?thesis
        proof (elim disjE)
          assume old_node: "(nid, v_val, ts_val) \<in> set (pools ts p)"
          then show ?thesis using sim_r pc_q_old old_node not_top not_less start_eq l_q_eq unfolding Simulation_R_def Let_def
            by (metis (lifting) fst_conv)
        next
          assume new_upd: "ts_val = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p"
          have ts_eq: "ts_val = t_ts ts p" using new_upd by simp
          have tpc_q: "t_pc ts q \<in> {''TD_Line4_Done'', ''TD_Loop'', ''TD_Remove_Done''}"
            using sim_r pc_q_old unfolding Simulation_R_def Let_def by auto
          have "t_startTs ts q <\<^sub>t\<^sub>s TS (ts_counter ts)"
            using TSQ_State_InvD_startTs_bound[OF inv_tsq tpc_q] .
          have not_less_p: "\<not> ts_less (t_startTs ts q) (t_ts ts p)"
            using not_less ts_eq start_eq by simp
          have "CState.i_var cs p < CState.l_var cs q"
            using sim_r p_E2 pc_q_old not_less_p unfolding Simulation_R_def Let_def
            by simp 
          have nid_eq: "nid = CState.i_var cs p" 
          proof -
            have ghost_nid: "nid = t_nid ts p" using new_upd by simp
            have phys_nid: "t_nid ts p = CState.i_var cs p" using sim_r p_E2 unfolding Simulation_R_def Let_def
              by auto 
            show ?thesis using ghost_nid phys_nid by simp
          qed
          with `CState.i_var cs p < CState.l_var cs q` l_q_eq show ?thesis by simp
        qed
      qed
    qed

    (* Proof note. *)
    show "\<forall>p_x q_x. c_program_counter cs' p_x \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q_x \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts' q_x) (t_ts ?ts' p_x) \<longrightarrow> CState.i_var cs' p_x < CState.l_var cs' q_x"
    proof (intro allI impI, elim conjE)
      fix q1 q2
      assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
      assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
      assume not_less: "\<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1)"
      
      have q2_neq_p: "q2 \<noteq> p" using pc_q2 `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
      have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}"
      proof (cases "q1 = p")
        case True
        have "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        then show ?thesis using True by simp
      next
        case False
        then have "c_program_counter cs q1 = c_program_counter cs' q1" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        with pc_q1 show ?thesis by simp
      qed

      have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}"
        using pc_q2 q2_neq_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto

      have start_eq: "t_startTs ?ts' q2 = t_startTs ts q2" using q2_neq_p by simp
      have ts_eq: "t_ts ?ts' q1 = t_ts ts q1" by simp 
      have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)"
        using not_less start_eq ts_eq by simp
        
      have i_var_eq: "CState.i_var cs' q1 = CState.i_var cs q1"
        using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have l_var_eq: "CState.l_var cs' q2 = CState.l_var cs q2"
        using q2_neq_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        
      have "CState.i_var cs q1 < CState.l_var cs q2"
        using sim_r pc_q1_old pc_q2_old not_less_old unfolding Simulation_R_def Let_def
        by simp 
        
      with i_var_eq l_var_eq show "CState.i_var cs' q1 < CState.l_var cs' q2" by simp
    qed

    (* Condition 15: monotonicity of historical tickets. *)
    show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E2''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      have "u \<noteq> p" using pc_u `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
      have pc_u_old: "c_program_counter cs u = ''E2''" using pc_u `u \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using `u \<noteq> p` `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond `u \<noteq> p` by simp
      
      have "nid < CState.i_var cs u"
        using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
        by (metis (lifting) fst_eqD) 
      then show "nid < CState.i_var cs' u" using i_u_eq by simp
    qed

    show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E3''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      show "nid \<le> CState.i_var cs' u"
      proof (cases "u = p")
        case True
        have i_var_eq: "CState.i_var cs' p = CState.i_var cs p" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have p_E2: "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have pool_upd: "pools ?ts' p = pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p)" by simp
        with cond True have "((nid, v, ts_val) \<in> set (pools ts p)) \<or> (ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p)"
          using pool_setTs_set_cases by simp
        then show ?thesis
        proof
          assume old_node: "(nid, v, ts_val) \<in> set (pools ts p)"
          have "nid < CState.i_var cs p"
            using sim_r p_E2 old_node cond unfolding Simulation_R_def Let_def
            by (metis (no_types, lifting) fst_eqD) 
          then show ?thesis using i_var_eq by (simp add: True) 
        next
          assume new_node: "ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p"
          have ghost_phys_align: "t_nid ts p = CState.i_var cs p"
            using sim_r p_E2 unfolding Simulation_R_def Let_def
            by simp 
          have "nid = CState.i_var cs p" using new_node ghost_phys_align by simp
          then show ?thesis using i_var_eq by (simp add: True) 
        qed
      next
        case False
        have pc_u_old: "c_program_counter cs u = ''E3''" using pc_u False `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using False `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond False by simp
        have "nid \<le> CState.i_var cs u"
          using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
          by (metis (lifting) fst_eqD)
        then show ?thesis using i_u_eq by simp
      qed
    qed

         (* Condition 16. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
    proof (intro allI impI, elim conjE)
      fix u nid v ts_val
      assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts' u)"
      assume not_top: "ts_val \<noteq> TOP"

      have old_or_top:
        "(nid, v, ts_val) \<in> set (pools ts u) \<or> (u = p \<and> ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p)"
      proof (cases "u = p")
        case True
        then have "((nid, v, ts_val) \<in> set (pools ts p)) \<or>
                   (ts_val = t_ts ts p \<and> (nid, v, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p)"
          using pool_setTs_set_cases in_pool by auto
        then show ?thesis
          using True by blast
      next
        case False
        then have "(nid, v, ts_val) \<in> set (pools ts u)"
          using in_pool by simp
        then show ?thesis
          by blast
      qed

      have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
      proof (cases "(nid, v, ts_val) \<in> set (pools ts u)")
        case True
        then show ?thesis
          using sim_r not_top
          unfolding Simulation_R_def Let_def
          by blast
      next
        case False
        from old_or_top False obtain
          u_eq_p: "u = p" and
          ts_eq: "ts_val = t_ts ts p" and
          top_old: "(nid, v, TOP) \<in> set (pools ts p)" and
          nid_eq: "nid = t_nid ts p"
          by blast

        have pc_p: "c_program_counter cs p = ''E2''"
          using `C_E2 p cs cs'`
          unfolding C_E2_def
          by simp

        have ai13: "hI1_E_Phase_Pending_Enq (cs, us)"
          using inv_sys
          unfolding system_invariant_def
          by simp

        have pending: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
          using ai13 pc_p
          unfolding hI1_E_Phase_Pending_Enq_def program_counter_def
          by (auto simp: Model.v_var_def)

        have v_eq: "v = CState.v_var cs p"
          using pool_node_value_is_v_var[OF assms(1) top_old] pc_p u_eq_p
          by simp

        have "\<exists>sn. EnqCallInHis (cs, us) p (CState.v_var cs p) sn"
          using pending
          unfolding HasPendingEnq_def Let_def
          by blast
        then show ?thesis
          using u_eq_p v_eq by simp
      qed

      show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
      proof -
        from old_his obtain sn where
          his_old: "EnqCallInHis (cs, us) u v sn"
          by blast
        have "EnqCallInHis (cs', us) u v sn"
          using his_old `C_E2 p cs cs'`
          unfolding C_E2_def EnqCallInHis_def his_seq_def
          by auto
        thus ?thesis
          by blast
      qed
    qed

    (* Condition 17. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ?ts' q \<longrightarrow> 
            (\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
    proof (intro allI impI)
      fix q v
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume v_scan: "v \<in> t_scanned ?ts' q"

      have q_neq_p: "q \<noteq> p"
        using pc_q_new `C_E2 p cs cs'`
        unfolding C_E2_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''"
        using pc_q_new q_neq_p `C_E2 p cs cs'`
        unfolding C_E2_def Let_def by auto
      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q"
        using q_neq_p `C_E2 p cs cs'`
        unfolding C_E2_def Let_def by auto
      have scan_old: "v \<in> t_scanned ts q"
        using v_scan by simp

      have old_cond17: "\<exists>idx < CState.j_var cs q. 
          (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
      proof -
        have "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ts q \<longrightarrow> 
            (\<exists>idx < CState.j_var cs q. 
              (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)))"
          using sim_r
          unfolding Simulation_R_def Let_def fst_conv snd_conv prod.collapse by blast
        thus ?thesis
          using pc_q_old scan_old by blast
      qed
        
      then obtain idx where idx_lt: "idx < CState.j_var cs q"
        and branches:
          "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
           (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        by blast
                       
      show "\<exists>idx < CState.j_var cs' q. 
          (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
      proof (rule exI[where x=idx], rule conjI)
        show "idx < CState.j_var cs' q"
          using idx_lt j_q_eq by simp
      next
        from branches show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                            (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (elim disjE)
          assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
          have pc_v_new: "c_program_counter cs' v = (if v = p then ''E3'' else ''E2'')"
            using b1 `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
          show ?thesis
          proof (cases "v = p")
            case True
            have his_p: "\<exists>sn. EnqCallInHis (cs', us) p (CState.v_var cs p) sn"
            proof -
              have pc_E2: "c_program_counter cs p = ''E2''"
                using `C_E2 p cs cs'` unfolding C_E2_def by simp
              have ai13: "hI1_E_Phase_Pending_Enq (cs, us)"
                using inv_sys unfolding system_invariant_def by simp
              then have pending: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
                using pc_E2 unfolding hI1_E_Phase_Pending_Enq_def program_counter_def
                by (auto simp: Model.v_var_def)
              from pending show ?thesis
                unfolding HasPendingEnq_def Let_def C_E2_def EnqCallInHis_def his_seq_def
                using `C_E2 p cs cs'`
                by auto
            qed
            
            have inq_p: "InQBack (cs', us) (CState.v_var cs p)"
            proof -
              have "CState.Qback_arr cs' (CState.i_var cs p) = CState.v_var cs p"
                using `C_E2 p cs cs'`
                unfolding C_E2_def Qback_arr_def Let_def fun_upd_def by auto
              then show ?thesis
                unfolding InQBack_def Qback_arr_def by auto
            qed
            
            have idx_p: "Idx (cs', us) (CState.v_var cs p) = idx"
            proof -
              have at_idx: "AtIdx (cs', us) (CState.v_var cs p) (CState.i_var cs p)"
                using `C_E2 p cs cs'`
                unfolding C_E2_def AtIdx_def Qback_arr_def Let_def fun_upd_def by auto
               
              have unique_idx: "\<And>k. AtIdx (cs', us) (CState.v_var cs p) k \<Longrightarrow> k = CState.i_var cs p"
              proof -
                fix k
                assume atk: "AtIdx (cs', us) (CState.v_var cs p) k"
                hence k_val_new: "CState.Qback_arr cs' k = CState.v_var cs p"
                  unfolding AtIdx_def Model.Qback_arr_def by auto
                show "k = CState.i_var cs p"
                proof (rule ccontr)
                  assume k_neq: "k \<noteq> CState.i_var cs p"
                  hence "CState.Qback_arr cs' k = CState.Qback_arr cs k"
                    using `C_E2 p cs cs'`
                    unfolding C_E2_def Qback_arr_def Let_def by auto
                  with k_val_new have k_val_old: "CState.Qback_arr cs k = CState.v_var cs p"
                    by simp
                   
                  have pc_E2: "c_program_counter cs p = ''E2''"
                    using `C_E2 p cs cs'` unfolding C_E2_def by simp
                  have ai13: "hI1_E_Phase_Pending_Enq (cs, us)"
                    using inv_sys unfolding system_invariant_def by simp
                  hence pending: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
                    using pc_E2 unfolding hI1_E_Phase_Pending_Enq_def program_counter_def v_var_def by auto
                     
                  have hi6: "hI14_Pending_Enq_Qback_Exclusivity (cs, us)"
                    using inv_sys unfolding system_invariant_def by simp
                  hence "\<nexists>k. CState.Qback_arr cs k = CState.v_var cs p \<and> k \<noteq> CState.i_var cs p"
                    using pending pc_E2
                    unfolding hI14_Pending_Enq_Qback_Exclusivity_def program_counter_def Qback_arr_def v_var_def Model.i_var_def by auto
                     
                  thus False
                    using k_val_old k_neq by blast
                qed
              qed
               
              have "Idx (cs', us) (CState.v_var cs p) = CState.i_var cs p"
                unfolding Idx_def
                using some_equality[of "AtIdx (cs', us) (CState.v_var cs p)" "CState.i_var cs p"]
                using at_idx unique_idx by blast
              thus ?thesis
                using b1 True by simp
            qed
            
            from his_p obtain sn where his_p_sn: "EnqCallInHis (cs', us) p (CState.v_var cs p) sn"
              by blast
            show ?thesis
              using his_p_sn inq_p idx_p True by blast
          next
            case False
            then have "c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx"
              using b1 `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
            then show ?thesis
              by blast
          qed
        next
          assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
          then obtain v_val sn where
            his: "EnqCallInHis (cs, us) v v_val sn"
            and inq: "InQBack (cs, us) v_val"
            and idx_eq: "Idx (cs, us) v_val = idx"
            by blast
                              
          have his_new: "EnqCallInHis (cs', us) v v_val sn"
            using his `C_E2 p cs cs'`
            unfolding C_E2_def EnqCallInHis_def his_seq_def by auto
            
                  have hi12: "hI20_Enq_Val_Valid (cs, us)"
            using inv_sys unfolding system_invariant_def by simp

          obtain e where
            e_in: "e \<in> set (his_seq (cs, us))"
            and e_pid: "act_pid e = v"
            and e_ssn: "act_ssn e = sn"
            and e_oper: "act_name e = enq"
            and e_cr: "act_cr e = call"
            and e_val: "act_val e = v_val"
            using his unfolding EnqCallInHis_def Let_def by blast

          have "\<exists>k < length (his_seq (cs, us)). his_seq (cs, us) ! k = e"
            using e_in by (simp add: in_set_conv_nth)
          then obtain k where
            k_lt: "k < length (his_seq (cs, us))"
            and k_eq: "his_seq (cs, us) ! k = e"
            by blast

          have k_oper: "act_name (his_seq (cs, us) ! k) = enq"
            using k_eq e_oper by simp
          have k_val: "act_val (his_seq (cs, us) ! k) = v_val"
            using k_eq e_val by simp

          have "v_val \<in> Val"
            using hi12 k_lt k_oper k_val
            unfolding hI20_Enq_Val_Valid_def by auto
          hence "v_val \<noteq> BOT"
            unfolding Val_def BOT_def by auto

          have inq_new: "InQBack (cs', us) v_val"
          proof (cases "v_val = CState.v_var cs p")
            case True
            have qback_hit: "CState.Qback_arr cs' (CState.i_var cs p) = CState.v_var cs p"
              using `C_E2 p cs cs'`
              unfolding C_E2_def Qback_arr_def Let_def fun_upd_def by auto
            have "Qback_arr (cs', us) (CState.i_var cs p) = v_val"
              using qback_hit True
              unfolding Model.Qback_arr_def by simp
            thus ?thesis
              unfolding InQBack_def by blast
                   next
            case False
            from inq obtain k_pos where
              k_pos_wrap: "Qback_arr (cs, us) k_pos = v_val"
              unfolding InQBack_def by blast

            have k_pos_eq: "CState.Qback_arr cs k_pos = v_val"
              using k_pos_wrap unfolding Model.Qback_arr_def by simp

            have pc_E2: "c_program_counter cs p = ''E2''"
              using `C_E2 p cs cs'` unfolding C_E2_def by simp
                       have sI3_E2_Slot_Exclusive: "sI3_E2_Slot_Exclusive (cs, us)"
              using inv_sys unfolding system_invariant_def by simp
            have qarr_bot: "CState.Q_arr cs (CState.i_var cs p) = BOT"
              using sI3_E2_Slot_Exclusive pc_E2
              unfolding sI3_E2_Slot_Exclusive_def program_counter_def Model.i_var_def Model.Q_arr_def
              by auto
            have qback_bot: "CState.Qback_arr cs (CState.i_var cs p) = BOT"
              using sI3_E2_Slot_Exclusive pc_E2
              unfolding sI3_E2_Slot_Exclusive_def program_counter_def Model.i_var_def Model.Qback_arr_def
              by auto

            have v_val_nonbot: "v_val \<noteq> BOT"
            proof -
              have hi2: "hI10_Enq_Call_Existence (cs, us)"
                using inv_sys unfolding system_invariant_def by simp
              have hi12: "hI20_Enq_Val_Valid (cs, us)"
                using inv_sys unfolding system_invariant_def by simp
              from inq obtain k where
                k_inq: "Qback_arr (cs, us) k = v_val"
                unfolding InQBack_def by blast
              from hi2 k_inq obtain q0 sn0 where
                call_in_his: "EnqCallInHis (cs, us) q0 v_val sn0"
                unfolding hI10_Enq_Call_Existence_def by blast
              then obtain e where
                e_in: "e \<in> set (his_seq (cs, us))"
                and e_op: "act_name e = enq"
                and e_val: "act_val e = v_val"
                unfolding EnqCallInHis_def by blast
              have "\<exists>k < length (his_seq (cs, us)). his_seq (cs, us) ! k = e"
                using e_in by (simp add: in_set_conv_nth)
              then obtain k where
                k_lt: "k < length (his_seq (cs, us))"
                and k_eq: "his_seq (cs, us) ! k = e"
                by blast
              have "v_val \<in> Val"
                using hi12 k_lt e_op k_eq e_val
                unfolding hI20_Enq_Val_Valid_def by auto
              thus ?thesis
                unfolding Val_def BOT_def by auto
            qed

            have k_pos_neq: "k_pos \<noteq> CState.i_var cs p"
            proof
              assume hit: "k_pos = CState.i_var cs p"
              from k_pos_eq hit have "CState.Qback_arr cs (CState.i_var cs p) = v_val"
                by simp
              with qback_bot have "v_val = BOT"
                by simp
              with v_val_nonbot show False
                by simp
            qed

            have k_pos_neq: "k_pos \<noteq> CState.i_var cs p"
            proof
              assume hit: "k_pos = CState.i_var cs p"
              from k_pos_eq hit have "CState.Qback_arr cs (CState.i_var cs p) = v_val"
                by simp
              with qback_bot have "v_val = BOT"
                by simp
              with v_val_nonbot show False
                by simp
            qed

            have qback_same: "CState.Qback_arr cs' k_pos = CState.Qback_arr cs k_pos"
              using `C_E2 p cs cs'` k_pos_neq
              unfolding C_E2_def Qback_arr_def Let_def fun_upd_def by auto

            have "Qback_arr (cs', us) k_pos = v_val"
              using qback_same k_pos_eq unfolding Model.Qback_arr_def by simp
            thus ?thesis
              unfolding InQBack_def by blast
          qed

          have idx_new: "Idx (cs', us) v_val = idx"
          proof (cases "v_val = CState.v_var cs p")
            case True
            have pc_E2: "c_program_counter cs p = ''E2''"
              using `C_E2 p cs cs'` unfolding C_E2_def by simp
            have pending: "HasPendingEnq (cs, us) p (CState.v_var cs p)"
              using pc_E2 inv_sys
              unfolding system_invariant_def hI1_E_Phase_Pending_Enq_def program_counter_def v_var_def by force
            have hi6: "hI14_Pending_Enq_Qback_Exclusivity (cs, us)"
              using inv_sys unfolding system_invariant_def by simp

            from inq obtain k_pos where
              k_pos_wrap: "Qback_arr (cs, us) k_pos = v_val"
              unfolding InQBack_def by blast
            have k_pos_eq: "CState.Qback_arr cs k_pos = v_val"
              using k_pos_wrap unfolding Model.Qback_arr_def by simp
            with True have k_pos_val: "CState.Qback_arr cs k_pos = CState.v_var cs p"
              by simp

            have uniq_old: "\<And>k. CState.Qback_arr cs k = CState.v_var cs p \<Longrightarrow> k = CState.i_var cs p"
              using hi6 pending pc_E2
              unfolding hI14_Pending_Enq_Qback_Exclusivity_def program_counter_def Qback_arr_def v_var_def Model.i_var_def
              by auto

            have k_pos_hit: "k_pos = CState.i_var cs p"
              using uniq_old k_pos_val by blast

            have at_old: "AtIdx (cs, us) v_val (CState.i_var cs p)"
              using k_pos_eq k_pos_hit
              unfolding AtIdx_def Qback_arr_def True by simp

            have uniq_at_old: "\<And>k. AtIdx (cs, us) v_val k \<Longrightarrow> k = CState.i_var cs p"
            proof -
              fix k
              assume atk: "AtIdx (cs, us) v_val k"
              hence "CState.Qback_arr cs k = v_val"
                unfolding AtIdx_def Qback_arr_def by simp
              with True have "CState.Qback_arr cs k = CState.v_var cs p"
                by simp
              thus "k = CState.i_var cs p"
                using uniq_old by blast
            qed

            have idx_old_hit: "Idx (cs, us) v_val = CState.i_var cs p"
              unfolding Idx_def
              using some_equality[of "AtIdx (cs, us) v_val" "CState.i_var cs p"]
              using at_old uniq_at_old by blast

            have at_new: "AtIdx (cs', us) v_val (CState.i_var cs p)"
              using `C_E2 p cs cs'` True
              unfolding AtIdx_def C_E2_def Qback_arr_def Let_def fun_upd_def
              by auto

            have uniq_at_new: "\<And>k. AtIdx (cs', us) v_val k \<Longrightarrow> k = CState.i_var cs p"
            proof -
              fix k
              assume atk: "AtIdx (cs', us) v_val k"
              have k_val_new: "CState.Qback_arr cs' k = v_val"
                using atk unfolding AtIdx_def Qback_arr_def by simp
              show "k = CState.i_var cs p"
              proof (rule ccontr)
                assume k_neq: "k \<noteq> CState.i_var cs p"
                hence "CState.Qback_arr cs' k = CState.Qback_arr cs k"
                  using `C_E2 p cs cs'`
                  unfolding C_E2_def Qback_arr_def Let_def fun_upd_def by auto
                with k_val_new True have "CState.Qback_arr cs k = CState.v_var cs p"
                  by simp
                thus False
                  using uniq_old k_neq by blast
              qed
            qed

            have idx_new_hit: "Idx (cs', us) v_val = CState.i_var cs p"
              unfolding Idx_def
              using some_equality[of "AtIdx (cs', us) v_val" "CState.i_var cs p"]
              using at_new uniq_at_new by blast

            show ?thesis
              using idx_eq idx_old_hit idx_new_hit by simp
                   next
            case False
            have vneq: "v_val \<noteq> CState.v_var cs p"
              using False by simp

            have ext_eq: "\<And>kk. AtIdx (cs', us) v_val kk = AtIdx (cs, us) v_val kk"
            proof -
              fix kk
              show "AtIdx (cs', us) v_val kk = AtIdx (cs, us) v_val kk"
              proof (cases "kk = CState.i_var cs p")
                case True
                have qback_hit: "CState.Qback_arr cs' kk = CState.v_var cs p"
                  using True `C_E2 p cs cs'`
                  unfolding C_E2_def Qback_arr_def Let_def fun_upd_def by auto

                have qback_neq: "CState.Qback_arr cs' kk \<noteq> v_val"
                proof
                  assume hit: "CState.Qback_arr cs' kk = v_val"
                  from qback_hit hit have "v_val = CState.v_var cs p"
                    by simp
                  with vneq show False
                    by simp
                qed

                have left_not: "\<not> AtIdx (cs', us) v_val kk"
                proof
                  assume atk: "AtIdx (cs', us) v_val kk"
                  then have "CState.Qback_arr cs' kk = v_val"
                    unfolding AtIdx_def Qback_arr_def by simp
                  with qback_neq show False
                    by simp
                qed
                have left_false: "AtIdx (cs', us) v_val kk = False"
                  using left_not by simp

                have right_not: "\<not> AtIdx (cs, us) v_val kk"
                proof
                  assume atk: "AtIdx (cs, us) v_val kk"

                  have pc_E2: "c_program_counter cs p = ''E2''"
                    using `C_E2 p cs cs'`
                    unfolding C_E2_def by simp
                  have sI3_E2_Slot_Exclusive: "sI3_E2_Slot_Exclusive (cs, us)"
                    using inv_sys unfolding system_invariant_def by simp
                  have qback_bot: "CState.Qback_arr cs (CState.i_var cs p) = BOT"
                    using sI3_E2_Slot_Exclusive pc_E2
                    unfolding sI3_E2_Slot_Exclusive_def program_counter_def Model.i_var_def Model.Qback_arr_def
                    by auto

                  have hi2: "hI10_Enq_Call_Existence (cs, us)"
                    using inv_sys unfolding system_invariant_def by simp
                  have hi12: "hI20_Enq_Val_Valid (cs, us)"
                    using inv_sys unfolding system_invariant_def by simp
                  from inq obtain k0 where
                    k0_inq: "Qback_arr (cs, us) k0 = v_val"
                    unfolding InQBack_def by blast
                  from hi2 k0_inq obtain q0 sn0 where
                    call_in_his: "EnqCallInHis (cs, us) q0 v_val sn0"
                    unfolding hI10_Enq_Call_Existence_def by blast
                  then obtain e where
                    e_in: "e \<in> set (his_seq (cs, us))"
                    and e_op: "act_name e = enq"
                    and e_val2: "act_val e = v_val"
                    unfolding EnqCallInHis_def by blast
                  have "\<exists>k < length (his_seq (cs, us)). his_seq (cs, us) ! k = e"
                    using e_in by (simp add: in_set_conv_nth)
                  then obtain k where
                    k_lt: "k < length (his_seq (cs, us))"
                    and k_eq: "his_seq (cs, us) ! k = e"
                    by blast
                  have "v_val \<in> Val"
                    using hi12 k_lt e_op k_eq e_val2
                    unfolding hI20_Enq_Val_Valid_def by auto
                  hence v_val_nonbot: "v_val \<noteq> BOT"
                    unfolding Val_def BOT_def by auto

                  from atk True have hit_old: "CState.Qback_arr cs (CState.i_var cs p) = v_val"
                    unfolding AtIdx_def Qback_arr_def by simp
                  from hit_old qback_bot have "v_val = BOT"
                    by simp
                  with v_val_nonbot show False
                    by simp
                qed
                have right_false: "AtIdx (cs, us) v_val kk = False"
                  using right_not by simp

                show ?thesis
                  using left_false right_false by simp
              next
                case False
                have "CState.Qback_arr cs' kk = CState.Qback_arr cs kk"
                  using False `C_E2 p cs cs'`
                  unfolding C_E2_def Qback_arr_def Let_def fun_upd_def by auto
                thus ?thesis
                  unfolding AtIdx_def Qback_arr_def by simp
              qed
            qed

            show ?thesis
              using idx_eq ext_eq unfolding Idx_def by presburger
          qed

          show ?thesis
            using his_new inq_new idx_new by blast
        qed
      qed
    qed

    (* NEW *)
    show "\<forall>p_x. c_program_counter cs' p_x = ''D3'' \<longrightarrow> 
          (\<forall>u \<in> t_scanned ?ts' p_x. \<forall>nid v_val ts_val. 
             (nid, v_val, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> 
             nid < CState.j_var cs' p_x \<or> \<not> ts_less ts_val (t_startTs ?ts' p_x))"
    proof (intro allI impI ballI, elim conjE)
      fix q u nid v_val ts_val
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume u_scan: "u \<in> t_scanned ?ts' q"
      assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)"
      assume not_top: "ts_val \<noteq> TOP"
      
      have q_neq_p: "q \<noteq> p" using pc_q_new `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
      
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have j_var_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
      have scan_eq: "t_scanned ?ts' q = t_scanned ts q" by simp
      
      show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q)"
      proof (cases "u = p")
        case True
        have "pools ?ts' p = pool_setTs (pools ts p) (t_nid ts p) (t_ts ts p)" by simp
        with in_pool True have "((nid, v_val, ts_val) \<in> set (pools ts p)) \<or> (ts_val = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p)"
          using pool_setTs_set_cases by simp
        then show ?thesis
        proof
          assume old_node: "(nid, v_val, ts_val) \<in> set (pools ts p)"
          have p_scan_old: "p \<in> t_scanned ts q" using u_scan scan_eq True by simp
          have old_cond18: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> 
            (\<forall>v \<in> t_scanned ts q. \<forall>nid_x v_x ts_x. 
               (nid_x, v_x, ts_x) \<in> set (pools ts v) \<and> ts_x \<noteq> TOP \<longrightarrow> 
               nid_x < CState.j_var cs q \<or> \<not> ts_less ts_x (t_startTs ts q))"
            using sim_r unfolding Simulation_R_def Let_def by (metis fst_eqD)
          have "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
            using old_cond18 pc_q_old p_scan_old old_node not_top by blast
          thus ?thesis using j_var_eq startTs_eq by simp
        next
          assume new_node: "ts_val = t_ts ts p \<and> (nid, v_val, TOP) \<in> set (pools ts p) \<and> nid = t_nid ts p"
          have nid_eq: "nid = CState.i_var cs p" 
            using sim_r pc_E2 new_node unfolding Simulation_R_def Let_def by auto
            
          have p_scan_old: "p \<in> t_scanned ts q" using u_scan scan_eq True by simp
          
          (* Condition 19. *)
          have old_cond19: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> 
            (\<forall>u \<in> t_scanned ts q. c_program_counter cs u \<in> {''E2'', ''E3''} \<longrightarrow> 
              CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q))"
            using sim_r unfolding Simulation_R_def Let_def by (metis fst_eqD)
            
          have "CState.i_var cs p < CState.j_var cs q \<or> \<not> ts_less (t_ts ts p) (t_startTs ts q)"
            using old_cond19 pc_q_old p_scan_old pc_E2 by blast
            
          thus ?thesis using nid_eq j_var_eq startTs_eq new_node by simp
        qed
      next
        case False
        have old_in: "(nid, v_val, ts_val) \<in> set (pools ts u)" using in_pool False by simp
        have u_scan_old: "u \<in> t_scanned ts q" using u_scan scan_eq by simp
        
        have old_cond18: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> 
          (\<forall>v \<in> t_scanned ts q. \<forall>nid v_val ts_val. 
             (nid, v_val, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
             nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q))"
          using sim_r unfolding Simulation_R_def Let_def by (metis fst_eqD) 
          
        have "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
          using old_cond18 pc_q_old u_scan_old old_in not_top by blast
          
        thus ?thesis using j_var_eq startTs_eq by simp
      qed
    qed

    (* Pending Node Lapping Shield *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>u \<in> t_scanned ?ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
        CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q))"
    proof (intro allI impI ballI)
      fix q u
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume u_scan: "u \<in> t_scanned ?ts' q"
      assume pc_u: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
      
      have q_neq_p: "q \<noteq> p" using pc_q `C_E2 p cs cs'` unfolding C_E2_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_neq_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have u_scan_old: "u \<in> t_scanned ts q" using u_scan by simp
      
      have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}"
      proof (cases "u = p")
        case True
        have "c_program_counter cs p = ''E2''" using `C_E2 p cs cs'` unfolding C_E2_def by auto
        thus ?thesis
          using True by blast 
      next
        case False
        thus ?thesis using pc_u `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      qed
      
      have old_cond19: "\<forall>q. c_program_counter cs q = ''D3'' \<longrightarrow> 
        (\<forall>u \<in> t_scanned ts q. c_program_counter cs u \<in> {''E2'', ''E3''} \<longrightarrow> 
          CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q))"
        using sim_r unfolding Simulation_R_def Let_def by (metis fst_eqD)
        
      have "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
        using old_cond19 pc_q_old u_scan_old pc_u_old by blast
        
      have i_var_eq: "CState.i_var cs' u = CState.i_var cs u" using `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have j_var_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_E2 p cs cs'` unfolding C_E2_def Let_def by auto
      have ts_eq: "t_ts ?ts' u = t_ts ts u" by simp
      have startTs_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
      
      show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q)"
        using `CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)` i_var_eq j_var_eq ts_eq startTs_eq by simp
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "CState.V_var cs' = t_V_var ?ts'" 
      using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def by auto

    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts' q" 
      using sim_r `C_E2 p cs cs'` unfolding Simulation_R_def Let_def C_E2_def by (auto split: if_splits)

  qed

  have "T_E2 p ts ?ts' \<and> Simulation_R (cs', us) ?ts'"
    using step_T sim_R_next by simp
    
  then show ?thesis 
    by (rule exI)
qed


(* ========================================================== *)
(* Simulation Step for E3 *)
(* ========================================================== *)
lemma Simulation_R_E3:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes "Simulation_Inv (cs, us) ts"
      and "C_E3 p cs cs'"
  shows "\<exists>ts'. T_E3 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  (* Proof note. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
    using assms(1) unfolding Simulation_Inv_def by auto

  (* Step 1: extract the current-state assumptions. *)
  have pc_E3: "c_program_counter cs p = ''E3''" 
    using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
  
  have tpc_TE3: "t_pc ts p = ''TE3''"
    using sim_r pc_E3 unfolding Simulation_R_def Let_def by auto
    
  (* ========================================================== *)
  (* Proof step. *)
  (* Pool/array correspondence note. *)
  (* ========================================================== *)
  let ?ts' = "ts\<lparr> 
    t_pc := (\<lambda>x. if x = p then ''TL0'' else t_pc ts x),
    t_v := (\<lambda>x. if x = p then BOT else t_v ts x),
    t_nid := (\<lambda>x. if x = p then BOT else t_nid ts x),
    t_ts := (\<lambda>x. if x = p then TOP else t_ts ts x) 
  \<rparr>"
  
  (* Proof step. *)
  have step_T: "T_E3 p ts ?ts'"
    unfolding T_E3_def Let_def using tpc_TE3 by auto

  (* Key proof idea. *)
  have sim_R_next: "Simulation_R (cs', us) ?ts'"
    unfolding Simulation_R_def Let_def fst_conv snd_conv
  proof (intro conjI)
    (* Condition 2. *)
    show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts' q = ''TL0''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts' q = ''TE1''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts' q = ''TE2''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts' q = ''TE3''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts' q = ''TD1''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts' q = ''TD_Line4_Done''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts' q = ''TD_Loop''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts' q = ''TD_Remove_Done''"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto

    (* Condition 3: validity of timestamps in the TSQ pools. *)
    show "\<forall>q. \<forall>node\<in>set (pools ?ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
    proof (intro allI ballI)
      fix q node assume node_in: "node \<in> set (pools ?ts' q)"
      have "node \<in> set (pools ts q)" using node_in by simp
      have old_cond: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
        using sim_r `node \<in> set (pools ts q)` unfolding Simulation_R_def Let_def by meson 
        
      show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
      proof (cases "snd (snd node) = TOP")
        case True
        with old_cond have "t_pc ts q = ''TE2''" by simp
        have "q \<noteq> p"
        proof
          assume "q = p"
          with `t_pc ts q = ''TE2''` tpc_TE3 show False by simp
        qed
        with old_cond True show ?thesis by simp
      next
        case False 
        then show ?thesis by simp
      qed
    qed

    (* Condition 5.1. *)
    show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP)"
      using sim_r `C_E3 p cs cs'`
      unfolding Simulation_R_def Let_def C_E3_def
      by auto
      
    (* Condition 5.2. *)
    show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u))"
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def Let_def by auto

    (* Compact proof branch. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
            (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
            (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) 
          \<longrightarrow> v \<in> t_scanned ?ts' q)"
    proof (intro allI impI)
      fix q v
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
      
      have q_not_p: "q \<noteq> p" using pc_q `C_E3 p cs cs'` unfolding C_E3_def Let_def by force

      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_not_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using q_not_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto

      from cond obtain idx where idx_less: "idx < CState.j_var cs' q" and 
        cond_branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" by blast

      have idx_less_old: "idx < CState.j_var cs q" using idx_less j_q_old by simp
      have q_arr_eq: "CState.Q_arr cs' idx = CState.Q_arr cs idx" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      
      show "v \<in> t_scanned ?ts' q"
      proof (cases "v = p")
        case False
        have i_v_eq: "CState.i_var cs' v = CState.i_var cs v" using False `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
        have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using False `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
        
        have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                        (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
          using cond_branch q_arr_eq i_v_eq pc_v_eq by simp
          
        have "v \<in> t_scanned ts q"
          using sim_r pc_q_old idx_less_old old_cond unfolding Simulation_R_def Let_def
          by (metis fst_eqD)
        then show ?thesis by simp
      next
        case True
        from cond_branch consider (d_case) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' p) \<and> ts_val \<noteq> TOP"  
                          | (e_case) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' p = ''E2''" "CState.i_var cs' p = idx" "idx \<noteq> BOT" using True by blast 
        then show ?thesis
        proof cases
          case d_case
          have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts p) \<and> ts_val \<noteq> TOP)) \<or> 
                          (CState.Q_arr cs idx = BOT \<and> c_program_counter cs p = ''E2'' \<and> CState.i_var cs p = idx \<and> idx \<noteq> BOT)"
            using d_case q_arr_eq by simp
          have "p \<in> t_scanned ts q"
            using sim_r pc_q_old idx_less_old old_cond unfolding Simulation_R_def Let_def
            by (metis fst_eqD) 
          then show ?thesis using True by simp
        next
          case e_case
          have "c_program_counter cs' p = ''L0''" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
          with e_case(2) show ?thesis by simp
        qed
      qed
    qed

    (* TOP-sensitive branch. *)
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''E2''"
      have p_is_L0: "c_program_counter cs' p = ''L0''" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have "q \<noteq> p" using pc_q p_is_L0 by force
      
      have old_pc: "c_program_counter cs q = ''E2''" using pc_q `q \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have "pools ?ts' q = pools ts q" using `q \<noteq> p` by simp
      
      moreover have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
        using sim_r old_pc unfolding Simulation_R_def Let_def
        by auto
        
      ultimately show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1" by simp
    qed

    (* This fact is shared by the D2 and D3 cases. *)
    show "\<forall>q. c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>idx<CState.l_var cs' q. 
        (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> 
        (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q))"
    proof (rule allI, rule impI) 
      fix q
      assume pc_q: "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''"
      have q_not_p: "q \<noteq> p" using pc_q `C_E3 p cs cs'` unfolding C_E3_def Let_def by force
      
      show "\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
      proof (rule allI, rule impI) 
        fix idx
        assume idx_less: "idx < CState.l_var cs' q"
        
        have pc_q_old: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" using pc_q q_not_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
        have l_q_old: "CState.l_var cs q = CState.l_var cs' q" using q_not_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
        have idx_less_old: "idx < CState.l_var cs q" using idx_less l_q_old by simp
        have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
        have start_eq: "t_startTs ?ts' q = t_startTs ts q" using q_not_p by auto

        show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
        proof (rule conjI)
          
          show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)"
          proof (intro impI allI)
            fix u nid ts_val
            assume q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT"
            assume in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"
            
            have old_q_not_bot: "CState.Q_arr cs idx \<noteq> BOT" using q_not_bot q_arr_eq by simp
            have in_old_pool: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" using in_pool q_arr_eq by simp
            
            have "ts_val <\<^sub>t\<^sub>s t_startTs ts q"
              using sim_r pc_q_old idx_less_old old_q_not_bot in_old_pool
              unfolding Simulation_R_def Let_def
              by (metis split_pairs2) 
              
            then show "ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q" using start_eq by simp
          qed
          
          show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q"
          proof (intro allI impI)
            fix u
            assume cond: "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
            
            have "u \<noteq> p" using cond `C_E3 p cs cs'` unfolding C_E3_def Let_def by force
            
            have pc_u_old: "c_program_counter cs u = ''E2''" using cond `u \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
            have i_u_old: "CState.i_var cs u = idx" using cond `u \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
            have q_bot_old: "CState.Q_arr cs idx = BOT" using cond q_arr_eq by simp
            have ts_u_eq: "t_ts ?ts' u = t_ts ts u" using `u \<noteq> p` by simp
            
            have "t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q"
              using sim_r pc_q_old idx_less_old q_bot_old pc_u_old i_u_old unfolding Simulation_R_def Let_def
              by (metis fst_conv) 
              
            then show "t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q" using ts_u_eq start_eq by simp
          qed
        qed
      qed
    qed

    (* Condition 9: initial candidate values in the D3 loop. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''D3''"
      have "q \<noteq> p" using pc_q `C_E3 p cs cs'` unfolding C_E3_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''"
        using pc_q `q \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have old_cand: "t_candNid ts q = BOT \<and> t_candTs ts q = TOP"
        using sim_r pc_q_old unfolding Simulation_R_def Let_def
        by simp 
      have "t_candNid ?ts' q = t_candNid ts q" by simp
      have "t_candTs ?ts' q = t_candTs ts q" by simp
      then show "t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP" using old_cand by simp
    qed

    (* Condition 10: absolute mapping between concrete indices and pools. *)
    show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
    proof (intro allI impI)
      fix u nid v n 
      assume "(nid, v, TS n) \<in> set (pools ?ts' u)"
      then have old_pool: "(nid, v, TS n) \<in> set (pools ts u)" by simp 
      have q_eq: "CState.Q_arr cs' = CState.Q_arr cs" 
        using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have x_eq: "CState.X_var cs' = CState.X_var cs" 
        using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      show "CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
        using sim_r old_pool q_eq x_eq unfolding Simulation_R_def Let_def
        by (metis fst_conv)
    qed

    (* Condition 11: value-range safety of the TSQ pools. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> v \<in> Val"
    proof (intro allI impI)
      fix u nid v ts_val 
      assume "(nid, v, ts_val) \<in> set (pools ?ts' u)"
      then have "(nid, v, ts_val) \<in> set (pools ts u)" by simp
      then show "v \<in> Val" using sim_r unfolding Simulation_R_def Let_def
        by meson 
    qed

    (* Condition 12. *)
    show "nid_counter ?ts' = CState.X_var cs'"
    proof -
      have "nid_counter ?ts' = nid_counter ts" by simp
      moreover have "CState.X_var cs' = CState.X_var cs" 
        using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      ultimately show ?thesis 
        using sim_r unfolding Simulation_R_def Let_def
        by auto 
    qed

    show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts' q = CState.i_var cs' q"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q \<in> {''E2'', ''E3''}"
      have p_is_L0: "c_program_counter cs' p = ''L0''" 
        using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have "q \<noteq> p" using pc_q p_is_L0 by auto
      have old_pc_q: "c_program_counter cs q \<in> {''E2'', ''E3''}"
        using pc_q `q \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have old_align: "t_nid ts q = CState.i_var cs q"
        using sim_r old_pc_q unfolding Simulation_R_def Let_def
        by (metis fst_eqD) 
      have tsq_eq: "t_nid ?ts' q = t_nid ts q" using `q \<noteq> p` by simp
      have phys_eq: "CState.i_var cs' q = CState.i_var cs q" 
        using `q \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      show "t_nid ?ts' q = CState.i_var cs' q" 
        using old_align tsq_eq phys_eq by simp
    qed

    (* Condition 13: cross-state monotonicity. *)
    show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
          (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val \<longrightarrow> 
           nid < CState.l_var cs' q)"
    proof (intro allI impI allI allI allI impI) 
      fix q u nid v_val ts_val 
      assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
      assume prems: "(nid, v_val, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val"

      have in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)"
        and not_top: "ts_val \<noteq> TOP"
        and not_less: "\<not> ts_less (t_startTs ?ts' q) ts_val"
        using prems by auto

      have p_is_L0: "c_program_counter cs' p = ''L0''" 
        using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have q_ne_p: "q \<noteq> p" using pc_q p_is_L0 by force

      have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" 
        using pc_q q_ne_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" 
        using q_ne_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have start_eq: "t_startTs ?ts' q = t_startTs ts q" using q_ne_p by simp

      have in_old_pool: "(nid, v_val, ts_val) \<in> set (pools ts u)" 
        using in_pool by simp
        
      show "nid < CState.l_var cs' q"
        using sim_r pc_q_old in_old_pool not_top not_less start_eq l_q_eq
        unfolding Simulation_R_def Let_def
        by (metis (no_types, lifting) fst_eqD) 
    qed


    (* Condition 14: enqueue/dequeue coherence across the two states. *)
    show "\<forall>q1 q2. c_program_counter cs' q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1) \<longrightarrow> CState.i_var cs' q1 < CState.l_var cs' q2"
    proof (intro allI impI, elim conjE)
      fix q1 q2
      assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
      assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
      assume not_less: "\<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1)"
      
      have p_is_L0: "c_program_counter cs' p = ''L0''" 
        using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have "q1 \<noteq> p" using pc_q1 p_is_L0 by force
      have "q2 \<noteq> p" using pc_q2 p_is_L0 by force
      
      have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}"
        using pc_q1 `q1 \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}"
        using pc_q2 `q2 \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
        
      have start_eq: "t_startTs ?ts' q2 = t_startTs ts q2" using `q2 \<noteq> p` by simp
      have ts_eq: "t_ts ?ts' q1 = t_ts ts q1" using `q1 \<noteq> p` by simp
      have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)"
        using not_less start_eq ts_eq by simp
        
      have i_var_eq: "CState.i_var cs' q1 = CState.i_var cs q1"
        using `q1 \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have l_var_eq: "CState.l_var cs' q2 = CState.l_var cs q2"
        using `q2 \<noteq> p` `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
        
      have "CState.i_var cs q1 < CState.l_var cs q2"
        using sim_r pc_q1_old pc_q2_old not_less_old unfolding Simulation_R_def Let_def
        by simp 
        
      with i_var_eq l_var_eq show "CState.i_var cs' q1 < CState.l_var cs' q2" by simp
    qed

    (* Condition 15. *)
    show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E2''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      have p_is_L0: "c_program_counter cs' p = ''L0''" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have u_neq_p: "u \<noteq> p" using pc_u p_is_L0 by force
      
      have pc_u_old: "c_program_counter cs u = ''E2''" using pc_u u_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond by simp
      
      have "nid < CState.i_var cs u"
        using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
        by (metis (lifting) fst_eqD)
      then show "nid < CState.i_var cs' u" using i_u_eq by simp
    qed

    show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E3''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      have p_is_L0: "c_program_counter cs' p = ''L0''" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have u_neq_p: "u \<noteq> p" using pc_u p_is_L0 by force
      
      have pc_u_old: "c_program_counter cs u = ''E3''" using pc_u u_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond by simp
      
      have "nid \<le> CState.i_var cs u"
        using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
        by (metis (no_types, lifting) fst_eqD)
      then show "nid \<le> CState.i_var cs' u" using i_u_eq by simp
    qed

       (* Condition 16: ownership bridge. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
    proof (intro allI impI, elim conjE)
      fix u nid v ts_val
      assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts' u)"
      assume not_top: "ts_val \<noteq> TOP"

      have in_old_pool: "(nid, v, ts_val) \<in> set (pools ts u)"
        using in_pool by simp

      have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
        using sim_r in_old_pool not_top
        unfolding Simulation_R_def Let_def
        by blast

      then obtain sn where his_old: "EnqCallInHis (cs, us) u v sn"
        by blast

      have his_new: "EnqCallInHis (cs', us) u v sn"
        using his_old `C_E3 p cs cs'`
        unfolding C_E3_def EnqCallInHis_def his_seq_def
        by auto

      show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
        using his_new by blast
    qed

    (* Condition 17: history completeness of the scanned set. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ?ts' q \<longrightarrow> 
            (\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
    proof (intro allI impI)
      fix q v
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume v_scan: "v \<in> t_scanned ?ts' q"

      have p_is_L0: "c_program_counter cs' p = ''L0''"
        using `C_E3 p cs cs'`
        unfolding C_E3_def Let_def by auto

      have q_neq_p: "q \<noteq> p"
        using pc_q_new p_is_L0 by force

      have pc_q_old: "c_program_counter cs q = ''D3''"
        using pc_q_new q_neq_p `C_E3 p cs cs'`
        unfolding C_E3_def Let_def by auto

      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q"
        using q_neq_p `C_E3 p cs cs'`
        unfolding C_E3_def Let_def by auto

      have scan_old: "v \<in> t_scanned ts q"
        using v_scan by simp

      have old_cond17:
        "\<exists>idx < CState.j_var cs q. 
          (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        using sim_r pc_q_old scan_old
        unfolding Simulation_R_def Let_def
        by simp

      then obtain idx where
        idx_lt: "idx < CState.j_var cs q"
        and branches:
          "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
           (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        by blast

      show "\<exists>idx < CState.j_var cs' q. 
          (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
      proof (rule exI[where x=idx], rule conjI)
        show "idx < CState.j_var cs' q"
          using idx_lt j_q_eq by simp
      next
        from branches show
          "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
           (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (elim disjE)
          assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"

          have v_neq_p: "v \<noteq> p"
            using b1 `c_program_counter cs p = ''E3''` by force

          have pc_v_new: "c_program_counter cs' v = ''E2''"
            using b1 v_neq_p `C_E3 p cs cs'`
            unfolding C_E3_def Let_def by auto

          have i_v_new: "CState.i_var cs' v = idx"
            using b1 v_neq_p `C_E3 p cs cs'`
            unfolding C_E3_def Let_def by auto

          thus ?thesis
            using pc_v_new by auto
        next
          assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"

          then obtain v_val sn where
            his: "EnqCallInHis (cs, us) v v_val sn"
            and inq: "InQBack (cs, us) v_val"
            and idx_eq: "Idx (cs, us) v_val = idx"
            by blast

          have his_new: "EnqCallInHis (cs', us) v v_val sn"
            using his `C_E3 p cs cs'`
            unfolding C_E3_def EnqCallInHis_def his_seq_def
            by auto

          have inq_new: "InQBack (cs', us) v_val"
          proof -
            from inq obtain k_pos where
              k_pos_eq: "Qback_arr (cs, us) k_pos = v_val"
              unfolding InQBack_def by blast
            moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
              using `C_E3 p cs cs'`
              unfolding C_E3_def Qback_arr_def Let_def
              by auto
            ultimately show ?thesis
              unfolding InQBack_def by blast
          qed

          have idx_new: "Idx (cs', us) v_val = idx"
          proof -
            have ext_eq: "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
              using `C_E3 p cs cs'`
              unfolding C_E3_def AtIdx_def Qback_arr_def Let_def
              by auto
            show ?thesis
              using idx_eq ext_eq
              unfolding Idx_def by presburger
          qed

          show ?thesis
            using his_new inq_new idx_new by blast
        qed
      qed
    qed

    (* Condition 18. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>v \<in> t_scanned ?ts' q. \<forall>nid v_val ts_val.
         (nid, v_val, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
         nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q))"
    proof (intro allI impI ballI, elim conjE)
      fix q v nid v_val ts_val
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
         and v_scan: "v \<in> t_scanned ?ts' q"
         and in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' v)"
         and not_top: "ts_val \<noteq> TOP"

      have p_is_L0: "c_program_counter cs' p = ''L0''" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have q_neq_p: "q \<noteq> p" using pc_q_new p_is_L0 by force

      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have v_scan_old: "v \<in> t_scanned ts q" using v_scan by simp
      have in_pool_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" using in_pool by simp

      have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
        using sim_r pc_q_old v_scan_old in_pool_old not_top unfolding Simulation_R_def Let_def by (metis fst_eqD) 

      have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have start_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp

      show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q)"
        using old_cond18 j_eq start_eq by simp
    qed

    (* Condition 19. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>u \<in> t_scanned ?ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
        CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q))"
    proof (intro allI impI ballI)
      fix q u
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume u_scan: "u \<in> t_scanned ?ts' q"
      assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"

      have p_is_L0: "c_program_counter cs' p = ''L0''" using `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have q_neq_p: "q \<noteq> p" using pc_q p_is_L0 by force
      have u_neq_p: "u \<noteq> p" using pc_u_new p_is_L0 by force
      
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new u_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have u_scan_old: "u \<in> t_scanned ts q" using u_scan by simp
      
      have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
        using sim_r pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def by (metis fst_eqD)
        
      have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have i_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p `C_E3 p cs cs'` unfolding C_E3_def Let_def by auto
      have start_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
      have ts_eq: "t_ts ?ts' u = t_ts ts u" using u_neq_p by simp
      
      show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q)"
        using old_cond19 j_eq i_eq start_eq ts_eq by simp
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "CState.V_var cs' = t_V_var ?ts'" 
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def by auto

    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts' q" 
      using sim_r `C_E3 p cs cs'` unfolding Simulation_R_def Let_def C_E3_def by (auto split: if_splits)

  qed
    
  (* Proof note. *)
  have "T_E3 p ts ?ts' \<and> Simulation_R (cs', us) ?ts'"
    using step_T sim_R_next by simp
  then show ?thesis 
    by (rule exI)
qed


(* ========================================================== *)
(* Simulation Step for D1 *)
(* ========================================================== *)
lemma Simulation_R_D1:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes "Simulation_Inv (cs, us) ts"
      and "C_D1 p cs cs'"
  shows "\<exists>ts'. T_D1 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  (* Proof note. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
    using assms(1) unfolding Simulation_Inv_def by auto

  (* Step 1: extract the current-state assumptions. *)
  have pc_D1: "c_program_counter cs p = ''D1''" 
    using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
    
  have tpc_TD1: "t_pc ts p = ''TD1''"
    using sim_r pc_D1 unfolding Simulation_R_def Let_def by auto

  (* ========================================================== *)
  (* Proof step. *)
  (* Proof note. *)
  (* ========================================================== *)
  let ?ts' = "ts\<lparr> 
    ts_counter := ts_counter ts + 1,
    t_startTs := (\<lambda>x. if x = p then TS (ts_counter ts) else t_startTs ts x),
    t_candNid := (\<lambda>x. if x = p then BOT else t_candNid ts x),
    t_candTs := (\<lambda>x. if x = p then TOP else t_candTs ts x),
    t_candPid := (\<lambda>x. if x = p then BOT else t_candPid ts x),
    t_scanned := (\<lambda>x. if x = p then {} else t_scanned ts x),
    t_pc := (\<lambda>x. if x = p then ''TD_Line4_Done'' else t_pc ts x) 
  \<rparr>"
  
  (* Proof step. *)
  have step_T: "T_D1 p ts ?ts'"
    using tpc_TD1 unfolding T_D1_def Let_def by simp

  (* Key proof idea. *)
  have sim_R_next: "Simulation_R (cs', us) ?ts'"
    unfolding Simulation_R_def Let_def fst_conv snd_conv
  proof (intro conjI)
    (* Condition 2. *)
    show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts' q = ''TL0''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts' q = ''TE1''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts' q = ''TE2''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts' q = ''TE3''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts' q = ''TD1''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto

    show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts' q = ''TD_Line4_Done''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto

    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts' q = ''TD_Loop''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts' q = ''TD_Remove_Done''"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto

    (* Condition 3: validity of timestamps in the TSQ pools. *)
    show "\<forall>q. \<forall>node\<in>set (pools ?ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
    proof (intro allI ballI)
      fix q node assume "node \<in> set (pools ?ts' q)"
      then have in_old: "node \<in> set (pools ts q)" by simp
      have old_cond: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
        using sim_r in_old unfolding Simulation_R_def Let_def by meson 
      show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
      proof (cases "q = p")
        case True
        with old_cond have "snd (snd node) \<noteq> TOP" using tpc_TD1 by auto
        then show ?thesis by simp
      next
        case False
        with old_cond show ?thesis by auto
      qed
    qed

    (* Condition 5. *)
   show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP)"
      using sim_r `C_D1 p cs cs'`
      unfolding Simulation_R_def Let_def C_D1_def
      by auto
      
    show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u))"
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def Let_def by auto

    (* Condition 6. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. (\<exists>idx < CState.j_var cs' q. 
            (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> 
            (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) 
          \<longrightarrow> v \<in> t_scanned ?ts' q)"
    proof (intro allI impI)
      fix q v
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
      
      have q_not_p: "q \<noteq> p" using pc_q `C_D1 p cs cs'` unfolding C_D1_def Let_def by force

      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_not_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using q_not_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto

      from cond obtain idx where idx_less: "idx < CState.j_var cs' q" and 
        cond_branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" by blast

      have idx_less_old: "idx < CState.j_var cs q" using idx_less j_q_old by simp
      have q_arr_eq: "CState.Q_arr cs' idx = CState.Q_arr cs idx" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      
      show "v \<in> t_scanned ?ts' q"
      proof (cases "v = p")
        case False
        have i_v_eq: "CState.i_var cs' v = CState.i_var cs v" using False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        have pc_v_eq: "c_program_counter cs' v = c_program_counter cs v" using False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        
        have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                        (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
          using cond_branch q_arr_eq i_v_eq pc_v_eq by simp
          
        have "v \<in> t_scanned ts q"
          using sim_r pc_q_old idx_less_old old_cond unfolding Simulation_R_def Let_def by (metis fst_eqD)
        then show ?thesis using q_not_p by simp
      next
        case True
        from cond_branch consider (d_case) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' p) \<and> ts_val \<noteq> TOP"  
                          | (e_case) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' p = ''E2''" "CState.i_var cs' p = idx" "idx \<noteq> BOT" using True by blast 
        then show ?thesis
        proof cases
          case d_case
          have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts p) \<and> ts_val \<noteq> TOP)) \<or> 
                          (CState.Q_arr cs idx = BOT \<and> c_program_counter cs p = ''E2'' \<and> CState.i_var cs p = idx \<and> idx \<noteq> BOT)"
            using d_case q_arr_eq by simp
          have "p \<in> t_scanned ts q"
            using sim_r pc_q_old idx_less_old old_cond unfolding Simulation_R_def Let_def by (metis fst_eqD) 
          then show ?thesis using True q_not_p by simp
        next
          case e_case
          have "c_program_counter cs' p = ''D2''" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
          with e_case(2) show ?thesis by simp
        qed
      qed
    qed

    (* Condition 7. *)
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''E2''"
      have p_is_D2: "c_program_counter cs' p = ''D2''" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have "q \<noteq> p" using pc_q p_is_D2 by force
      
      have old_pc: "c_program_counter cs q = ''E2''" using pc_q `q \<noteq> p` `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have "pools ?ts' q = pools ts q" using `q \<noteq> p` by simp
      
      (* Key proof idea. *)
      moreover have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
        using sim_r old_pc unfolding Simulation_R_def Let_def by (metis fst_conv) 
        
      ultimately show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1" by simp
    qed

    (* Condition 8: startTs timestamp guard. *)
    show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> (\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q))"
    proof (rule allI, rule impI)
      fix q assume pc_q: "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''"
      show "\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
      proof (rule allI, rule impI)
        fix idx assume idx_less: "idx < CState.l_var cs' q"

        show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
        proof (cases "q = p")
          case True
          have l_p_eq: "CState.l_var cs' p = CState.X_var cs" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
          have startTs_p: "t_startTs ?ts' p = TS (ts_counter ts)" by simp
          
          show ?thesis
          proof (rule conjI)
            show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)"
            proof (intro impI allI)
              fix u nid ts_val
              assume q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT"
              assume in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"
              
              have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
              have old_q_not_bot: "CState.Q_arr cs idx \<noteq> BOT" using q_not_bot q_arr_eq by simp
              have in_old_pool: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" using in_pool q_arr_eq by simp
              
              have ts_val_less_counter: "ts_val <\<^sub>t\<^sub>s TS (ts_counter ts)"
              proof -
                have "ts_val \<noteq> TOP"
                proof
                  assume "ts_val = TOP"
                  with in_old_pool have top_in_pool: "(nid, CState.Q_arr cs idx, TOP) \<in> set (pools ts u)" by simp
                  
                  (* Key proof idea. *)
                  have cond3_all: "\<forall>p. \<forall>node\<in>set (pools ts p). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts p = ''TE2'' \<and> t_nid ts p = fst node"
                    using sim_r unfolding Simulation_R_def Let_def by simp
                  hence "snd (snd (nid, CState.Q_arr cs idx, TOP)) \<noteq> TOP \<or> 
                         (snd (snd (nid, CState.Q_arr cs idx, TOP)) = TOP \<and> t_pc ts u = ''TE2'' \<and> t_nid ts u = fst (nid, CState.Q_arr cs idx, TOP))"
                    using top_in_pool by blast
                  hence tpc_E2: "t_pc ts u = ''TE2''" and nid_eq: "nid = t_nid ts u" by auto

                  (* Key proof idea. *)
                  have cond2_L0: "c_program_counter cs u = ''L0'' \<longrightarrow> t_pc ts u = ''TL0''" using sim_r unfolding Simulation_R_def Let_def by simp
                  have cond2_E1: "c_program_counter cs u = ''E1'' \<longrightarrow> t_pc ts u = ''TE1''" using sim_r unfolding Simulation_R_def Let_def by simp
                  have cond2_E3: "c_program_counter cs u = ''E3'' \<longrightarrow> t_pc ts u = ''TE3''" using sim_r unfolding Simulation_R_def Let_def by simp
                  have cond2_D1: "c_program_counter cs u = ''D1'' \<longrightarrow> t_pc ts u = ''TD1''" using sim_r unfolding Simulation_R_def Let_def by simp
                  have cond2_D2: "c_program_counter cs u = ''D2'' \<longrightarrow> t_pc ts u = ''TD_Line4_Done''" using sim_r unfolding Simulation_R_def Let_def by simp
                  have cond2_D3: "c_program_counter cs u = ''D3'' \<longrightarrow> t_pc ts u = ''TD_Loop''" using sim_r unfolding Simulation_R_def Let_def by simp
                  have cond2_D4: "c_program_counter cs u = ''D4'' \<longrightarrow> t_pc ts u = ''TD_Remove_Done''" using sim_r unfolding Simulation_R_def Let_def by simp

                  have ai1: "c_program_counter cs u \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}"
                    using inv_sys TypeOK_def  unfolding system_invariant_def sI2_X_var_Upper_Bound_def program_counter_def by auto

                  have "c_program_counter cs u = ''E2''"
                  proof (rule ccontr)
                    assume "c_program_counter cs u \<noteq> ''E2''"
                    with ai1 have "c_program_counter cs u \<in> {''L0'', ''E1'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}" by auto
                    then show False using tpc_E2 cond2_L0 cond2_E1 cond2_E3 cond2_D1 cond2_D2 cond2_D3 cond2_D4 by auto
                  qed
                  
                  (* Proof note. *)
                  then have "CState.Q_arr cs (CState.i_var cs u) = BOT" 
                    using inv_sys unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def Q_arr_def by fastforce
                  have "CState.Q_arr cs idx = CState.v_var cs u" 
                    using pool_node_value_is_v_var[OF assms(1) top_in_pool] `c_program_counter cs u = ''E2''` by simp
                  have "CState.Qback_arr cs idx \<noteq> CState.v_var cs u"
                    using inv_sys `c_program_counter cs u = ''E2''` E2_implies_HasPendingEnq unfolding system_invariant_def hI14_Pending_Enq_Qback_Exclusivity_def program_counter_def Qback_arr_def v_var_def
                    using Model.i_var_def
                    by (metis \<open>CState.Q_arr cs (CState.i_var cs u) = BOT\<close> fst_conv insert_iff old_q_not_bot) 
                  have "CState.Q_arr cs idx = CState.Qback_arr cs idx"
                    using inv_sys old_q_not_bot unfolding system_invariant_def sI8_Q_Qback_Sync_def Q_arr_def Qback_arr_def by fastforce
                  with `CState.Q_arr cs idx = CState.v_var cs u` `CState.Qback_arr cs idx \<noteq> CState.v_var cs u` show False by simp
                qed
                then show ?thesis using inv_tsq in_old_pool unfolding TSQ_State_Inv_def by fastforce
              qed
              
              then show "ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q" using startTs_p True by simp
            qed

            show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q"
            proof (intro allI impI)
              fix u assume cond: "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
              have "u \<noteq> p" using cond True pc_q `C_D1 p cs cs'` unfolding C_D1_def Let_def by force
              
              have pc_u_old: "c_program_counter cs u = ''E2''" using cond `u \<noteq> p` `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
              have i_u_old: "CState.i_var cs u = idx" using cond `u \<noteq> p` `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
              have ts_eq: "t_ts ?ts' u = t_ts ts u" using `u \<noteq> p` by simp
              
              have "t_pc ts u = ''TE2''" 
                using sim_r pc_u_old unfolding Simulation_R_def Let_def
                by auto 
                
            have pc_u_te2: "t_pc ts u = ''TE2''"
              using \<open>t_pc ts u = ''TE2''\<close> .
            
            have "t_ts ts u \<noteq> TOP"
              using TSQ_State_InvD_TE2_not_top[OF inv_tsq pc_u_te2] .
            
            have "t_ts ts u <\<^sub>t\<^sub>s TS (ts_counter ts)"
              using TSQ_State_InvD_tts_bound[OF inv_tsq \<open>t_ts ts u \<noteq> TOP\<close>] .
                
              then show "t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q" using ts_eq startTs_p True by simp
            qed
          qed
          
        next
          case False
          have pc_q_old: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" 
            using pc_q False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
          have l_q_old: "CState.l_var cs q = CState.l_var cs' q" 
            using False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
          have start_eq: "t_startTs ?ts' q = t_startTs ts q" 
            using False by auto
          have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" 
            using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
          have idx_less_old: "idx < CState.l_var cs q" 
            using idx_less l_q_old by simp

          show ?thesis
          proof (rule conjI)
            show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)"
            proof (intro impI allI)
              fix u nid ts_val
              assume q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT"
              assume in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"

              have old_q_not_bot: "CState.Q_arr cs idx \<noteq> BOT" using q_not_bot q_arr_eq by simp
              have in_old_pool: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" 
                using in_pool q_arr_eq by simp

              have "ts_val <\<^sub>t\<^sub>s t_startTs ts q"
                using sim_r pc_q_old idx_less_old old_q_not_bot in_old_pool unfolding Simulation_R_def Let_def
                by (metis fst_eqD)
              then show "ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q" using start_eq by simp
            qed

            show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q"
            proof (intro allI impI)
              fix u assume cond: "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
              have "u \<noteq> p" using cond `C_D1 p cs cs'` unfolding C_D1_def Let_def by force

              have pc_u_old: "c_program_counter cs u = ''E2''" using cond `u \<noteq> p` `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
              have i_u_old: "CState.i_var cs u = idx" using cond `u \<noteq> p` `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
              have q_bot_old: "CState.Q_arr cs idx = BOT" using cond q_arr_eq by simp

              have "t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q"
                using sim_r pc_q_old idx_less_old q_bot_old pc_u_old i_u_old unfolding Simulation_R_def Let_def
                by (metis fst_conv)
              moreover have "t_ts ?ts' u = t_ts ts u" using `u \<noteq> p` by simp
              ultimately show "t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q" using start_eq by simp
            qed
          qed
        qed
      qed
    qed

    (* Condition 9. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''D3''"
      have "q \<noteq> p" using pc_q `C_D1 p cs cs'` unfolding C_D1_def Let_def by force
      have pc_q_old: "c_program_counter cs q = ''D3''"
        using pc_q `q \<noteq> p` `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have old_cand: "t_candNid ts q = BOT \<and> t_candTs ts q = TOP"
        using sim_r pc_q_old unfolding Simulation_R_def Let_def
        by auto 
      have "t_candNid ?ts' q = t_candNid ts q" using `q \<noteq> p` by simp
      have "t_candTs ?ts' q = t_candTs ts q" using `q \<noteq> p` by simp
      then show "t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP" using old_cand by simp
    qed

    (* Condition 10: absolute mapping between concrete indices and pools. *)
    show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
    proof (intro allI impI)
      fix u nid v_val n
      assume in_pool: "(nid, v_val, TS n) \<in> set (pools ?ts' u)"
      have "pools ?ts' u = pools ts u" by simp
      with in_pool have in_old: "(nid, v_val, TS n) \<in> set (pools ts u)" by simp
      from sim_r have cond10: "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
        unfolding Simulation_R_def Let_def
        by auto 
      with in_old have "CState.Q_arr cs nid = v_val \<and> nid < CState.X_var cs" by blast
      moreover have "CState.Q_arr cs' = CState.Q_arr cs" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      moreover have "CState.X_var cs' = CState.X_var cs" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      ultimately show "CState.Q_arr cs' nid = v_val \<and> nid < CState.X_var cs'" by simp
    qed

    (* Condition 11: value-range safety of the TSQ pools. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> v \<in> Val"
    proof (intro allI impI)
      fix u nid v_val ts_val
      assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)"
      have "pools ?ts' u = pools ts u" by simp
      with in_pool have in_old: "(nid, v_val, ts_val) \<in> set (pools ts u)" by simp
      from sim_r have cond11: "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val"
        unfolding Simulation_R_def Let_def
        by argo 
      with in_old show "v_val \<in> Val" by blast
    qed

    (* Condition 12.1. *)
    show "nid_counter ?ts' = CState.X_var cs'"
    proof -
      have "nid_counter ?ts' = nid_counter ts" by simp
      moreover have "CState.X_var cs' = CState.X_var cs" 
        using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      ultimately show ?thesis 
        using sim_r unfolding Simulation_R_def Let_def
        by auto 
    qed

    (* Condition 12.2. *)
    show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts' q = CState.i_var cs' q"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q \<in> {''E2'', ''E3''}"
      have nid_unchanged: "t_nid ?ts' q = t_nid ts q" by simp
      have ivar_unchanged: "CState.i_var cs' q = CState.i_var cs q" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      show "t_nid ?ts' q = CState.i_var cs' q"
      proof (cases "q = p")
        case True
        have "c_program_counter cs' p = ''D2''" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        with pc_q True show ?thesis by simp
      next
        case False
        have pc_q_old: "c_program_counter cs q \<in> {''E2'', ''E3''}"
          using pc_q False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        from sim_r have "t_nid ts q = CState.i_var cs q" using pc_q_old unfolding Simulation_R_def Let_def
          by (metis fst_conv)
        with nid_unchanged ivar_unchanged show ?thesis by simp
      qed
    qed

    (* Condition 13: cross-state monotonicity. *)
    show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
         (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
    proof (intro allI impI allI allI allI impI)
      fix q u nid v_val ts_val 
      assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
      assume prems: "(nid, v_val, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val"

      have in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' u)"
        and not_top: "ts_val \<noteq> TOP"
        and not_less: "\<not> ts_less (t_startTs ?ts' q) ts_val"
        using prems by auto

      have pool_eq: "pools ?ts' u = pools ts u" by simp
      with in_pool have in_old_pool: "(nid, v_val, ts_val) \<in> set (pools ts u)" by simp

      show "nid < CState.l_var cs' q"
      proof (cases "q = p")
        case False
        have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" 
          using pc_q False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" 
          using False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        have start_eq: "t_startTs ?ts' q = t_startTs ts q" 
          using False by simp
          
        have not_less_old: "\<not> ts_less (t_startTs ts q) ts_val"
          using not_less start_eq by simp
          
        show ?thesis
          using sim_r pc_q_old in_old_pool not_top not_less_old l_q_eq
          unfolding Simulation_R_def Let_def
          by (metis fst_conv)
          
      next
        case True
        have l_p_eq: "CState.l_var cs' p = CState.X_var cs" 
          using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        
        obtain n where ts_eq: "ts_val = TS n"
        proof (cases ts_val)
          case (TS n)
          then show ?thesis using that by simp
        next
          case TOP
          with not_top show ?thesis by simp
        qed
        
        have cond10_old: "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> nid < CState.X_var cs"
          using sim_r unfolding Simulation_R_def Let_def
          by simp
          
        have "nid < CState.X_var cs"
          using cond10_old in_old_pool ts_eq by blast
          
        with l_p_eq True show ?thesis by simp
      qed
    qed

    (* Condition 14: enqueue/dequeue coherence across the two states. *)
    show "\<forall>q1 q2. c_program_counter cs' q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1) \<longrightarrow> CState.i_var cs' q1 < CState.l_var cs' q2"
    proof (intro allI impI, elim conjE)
      fix q1 q2
      assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
      assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
      assume not_less: "\<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1)"
      
      have p_is_D2: "c_program_counter cs' p = ''D2''" 
        using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have q1_neq_p: "q1 \<noteq> p" using pc_q1 p_is_D2 by force
      
      have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}"
        using pc_q1 q1_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      
      have ts_q1_eq: "t_ts ?ts' q1 = t_ts ts q1" using q1_neq_p by simp
      have i_q1_eq: "CState.i_var cs' q1 = CState.i_var cs q1" 
        using q1_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto

      show "CState.i_var cs' q1 < CState.l_var cs' q2"
      proof (cases "q2 = p")
        case False
        have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}"
          using pc_q2 False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
        have start_q2_eq: "t_startTs ?ts' q2 = t_startTs ts q2" using False by simp
        have l_q2_eq: "CState.l_var cs' q2 = CState.l_var cs q2" 
          using False `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
          
        have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)"
          using not_less start_q2_eq ts_q1_eq by simp
          
        show ?thesis
          using sim_r pc_q1_old pc_q2_old not_less_old i_q1_eq l_q2_eq unfolding Simulation_R_def Let_def
          by simp

          
      next
        case True
        have start_p_new: "t_startTs ?ts' p = TS (ts_counter ts)" by simp
        have l_p_new: "CState.l_var cs' p = CState.X_var cs" 
          using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
            
        have "t_ts ts q1 \<noteq> TOP"
          using inv_tsq pc_q1_old unfolding TSQ_State_Inv_def
          by (metis True local.not_less start_p_new ts_less.simps(2) ts_q1_eq) 
          
        have "t_ts ts q1 <\<^sub>t\<^sub>s TS (ts_counter ts)"
          using inv_tsq `t_ts ts q1 \<noteq> TOP` unfolding TSQ_State_Inv_def by fastforce
          
        then have "ts_less (t_ts ?ts' q1) (t_startTs ?ts' p)"
          using ts_q1_eq start_p_new by simp
          
        have "CState.i_var cs q1 < CState.X_var cs"
        proof (cases "c_program_counter cs q1 = ''E2''")
          case True
          then show ?thesis 
            using inv_sys unfolding system_invariant_def sI3_E2_Slot_Exclusive_def program_counter_def i_var_def X_var_def by fastforce
        next
          case False
          with pc_q1_old have "c_program_counter cs q1 = ''E3''" by simp
          then show ?thesis
            using inv_sys unfolding system_invariant_def sI4_E3_Qback_Written_def program_counter_def i_var_def X_var_def by fastforce
        qed   

        with i_q1_eq l_p_new True show ?thesis by simp
      qed
    qed

    (* Condition 15. *)
    show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E2''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      have p_is_D2: "c_program_counter cs' p = ''D2''" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have u_neq_p: "u \<noteq> p" using pc_u p_is_D2 by force
      
      have pc_u_old: "c_program_counter cs u = ''E2''" using pc_u u_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond u_neq_p by simp
      
      have "nid < CState.i_var cs u"
        using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
        by (metis (lifting) fst_conv) 
      then show "nid < CState.i_var cs' u" using i_u_eq by simp
    qed

    show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E3''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      have p_is_D2: "c_program_counter cs' p = ''D2''" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have u_neq_p: "u \<noteq> p" using pc_u p_is_D2 by force
      
      have pc_u_old: "c_program_counter cs u = ''E3''" using pc_u u_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond by simp
      
      have "nid \<le> CState.i_var cs u"
        using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
        by (metis (lifting) fst_eqD) 
      then show "nid \<le> CState.i_var cs' u" using i_u_eq by simp
    qed

    (* Condition 16: ownership bridge. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
    proof (intro allI impI, elim conjE)
      fix u nid v ts_val
      assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts' u)"
      assume not_top: "ts_val \<noteq> TOP"

      have in_old_pool: "(nid, v, ts_val) \<in> set (pools ts u)"
        using in_pool by simp

      have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
        using sim_r in_old_pool not_top
        unfolding Simulation_R_def Let_def
        by blast

      then obtain sn where his_old: "EnqCallInHis (cs, us) u v sn"
        by blast

      have his_new: "EnqCallInHis (cs', us) u v sn"
        using his_old `C_D1 p cs cs'`
        unfolding C_D1_def EnqCallInHis_def his_seq_def
        by auto

      show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
        using his_new by blast
    qed

    (* Condition 17: history completeness of the scanned set. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. v \<in> t_scanned ?ts' q \<longrightarrow> 
            (\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
    proof (intro allI impI)
      fix q v
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume v_scan: "v \<in> t_scanned ?ts' q"

      have p_is_D2: "c_program_counter cs' p = ''D2''"
        using `C_D1 p cs cs'`
        unfolding C_D1_def Let_def by auto

      have q_neq_p: "q \<noteq> p"
        using pc_q_new p_is_D2 by force

      have pc_q_old: "c_program_counter cs q = ''D3''"
        using pc_q_new q_neq_p `C_D1 p cs cs'`
        unfolding C_D1_def Let_def by auto

      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q"
        using q_neq_p `C_D1 p cs cs'`
        unfolding C_D1_def Let_def by auto

      have scan_old: "v \<in> t_scanned ts q"
        using v_scan q_neq_p by simp

      have old_cond17:
        "\<exists>idx < CState.j_var cs q. 
          (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        using sim_r pc_q_old scan_old
        unfolding Simulation_R_def Let_def
        by simp

      then obtain idx where
        idx_lt: "idx < CState.j_var cs q"
        and branches:
          "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> 
           (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        by blast

      show "\<exists>idx < CState.j_var cs' q. 
          (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
          (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
      proof (rule exI[where x=idx], rule conjI)
        show "idx < CState.j_var cs' q"
          using idx_lt j_q_eq by simp
      next
        from branches show
          "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
           (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (elim disjE)
          assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"

          have v_neq_p: "v \<noteq> p"
            using b1 `c_program_counter cs p = ''D1''` by force

          have pc_v_new: "c_program_counter cs' v = ''E2''"
            using b1 v_neq_p `C_D1 p cs cs'`
            unfolding C_D1_def Let_def by auto

          have i_v_new: "CState.i_var cs' v = idx"
            using b1 v_neq_p `C_D1 p cs cs'`
            unfolding C_D1_def Let_def by auto

          thus ?thesis
            using pc_v_new by auto
        next
          assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"

          then obtain v_val sn where
            his: "EnqCallInHis (cs, us) v v_val sn"
            and inq: "InQBack (cs, us) v_val"
            and idx_eq: "Idx (cs, us) v_val = idx"
            by blast

          have his_new: "EnqCallInHis (cs', us) v v_val sn"
            using his `C_D1 p cs cs'`
            unfolding C_D1_def EnqCallInHis_def his_seq_def
            by auto

          have inq_new: "InQBack (cs', us) v_val"
          proof -
            from inq obtain k_pos where
              k_pos_eq: "Qback_arr (cs, us) k_pos = v_val"
              unfolding InQBack_def by blast
            moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
              using `C_D1 p cs cs'`
              unfolding C_D1_def Qback_arr_def Let_def
              by auto
            ultimately show ?thesis
              unfolding InQBack_def by blast
          qed

          have idx_new: "Idx (cs', us) v_val = idx"
          proof -
            have ext_eq: "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
              using `C_D1 p cs cs'`
              unfolding C_D1_def AtIdx_def Qback_arr_def Let_def
              by auto
            show ?thesis
              using idx_eq ext_eq
              unfolding Idx_def by presburger
          qed

          show ?thesis
            using his_new inq_new idx_new by blast
        qed
      qed
    qed

    (* Condition 18. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>v \<in> t_scanned ?ts' q. \<forall>nid v_val ts_val.
         (nid, v_val, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP \<longrightarrow> 
         nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q))"
    proof (intro allI impI ballI, elim conjE)
      fix q v nid v_val ts_val
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
         and v_scan: "v \<in> t_scanned ?ts' q"
         and in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' v)"
         and not_top: "ts_val \<noteq> TOP"

      have p_is_D2: "c_program_counter cs' p = ''D2''" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have q_neq_p: "q \<noteq> p" using pc_q_new p_is_D2 by force

      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have v_scan_old: "v \<in> t_scanned ts q" using v_scan q_neq_p by simp
      have in_pool_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" using in_pool by simp

      have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
        using sim_r pc_q_old v_scan_old in_pool_old not_top unfolding Simulation_R_def Let_def by (metis fst_eqD) 

      have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have start_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp

      show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q)"
        using old_cond18 j_eq start_eq by simp
    qed

    (* Condition 19. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
      (\<forall>u \<in> t_scanned ?ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> 
        CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q))"
    proof (intro allI impI ballI)
      fix q u
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume u_scan: "u \<in> t_scanned ?ts' q"
      assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"

      have p_is_D2: "c_program_counter cs' p = ''D2''" using `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have q_neq_p: "q \<noteq> p" using pc_q p_is_D2 by force
      have u_neq_p: "u \<noteq> p" using pc_u_new p_is_D2 by force
      
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new u_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have u_scan_old: "u \<in> t_scanned ts q" using u_scan q_neq_p by simp
      
      have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
        using sim_r pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def by (metis fst_eqD)
        
      have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have i_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p `C_D1 p cs cs'` unfolding C_D1_def Let_def by auto
      have start_eq: "t_startTs ?ts' q = t_startTs ts q" using q_neq_p by simp
      have ts_eq: "t_ts ?ts' u = t_ts ts u" using u_neq_p by simp
      
      show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q)"
        using old_cond19 j_eq i_eq start_eq ts_eq by simp
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "CState.V_var cs' = t_V_var ?ts'" 
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def by auto

    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts' q" 
      using sim_r `C_D1 p cs cs'` unfolding Simulation_R_def Let_def C_D1_def by (auto split: if_splits)

  qed
    
  (* Proof note. *)
  have "T_D1 p ts ?ts' \<and> Simulation_R (cs', us) ?ts'"
    using step_T sim_R_next by simp
  then show ?thesis 
    by (rule exI)
qed


(* ========================================================== *)
(* Simulation Step for D2 *)
(* ========================================================== *)
lemma Simulation_R_D2:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes "Simulation_Inv (cs, us) ts"
      and "C_D2 p cs cs'"
  shows "\<exists>ts'. T_D2 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  (* Proof note. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
    using assms(1) unfolding Simulation_Inv_def by auto

  have step_facts [simp]:
    "CState.Q_arr cs' = CState.Q_arr cs"
    "CState.i_var cs' = CState.i_var cs"
    "CState.l_var cs' = CState.l_var cs"
    "CState.x_var cs' = CState.x_var cs"
    "CState.V_var cs' = CState.V_var cs"
  proof -
    show "CState.Q_arr cs' = CState.Q_arr cs"
      using assms(2) unfolding C_D2_def Let_def by (auto split: if_splits)
    show "CState.i_var cs' = CState.i_var cs"
      using assms(2) unfolding C_D2_def Let_def by (auto split: if_splits)
    show "CState.l_var cs' = CState.l_var cs"
      using assms(2) unfolding C_D2_def Let_def by (auto split: if_splits)
    show "CState.x_var cs' = CState.x_var cs"
      using assms(2) unfolding C_D2_def Let_def by (auto split: if_splits)
    show "CState.V_var cs' = CState.V_var cs"
      using assms(2) unfolding C_D2_def Let_def by (auto split: if_splits)
  qed

  (* Proof step. *)
  have pc_D2: "c_program_counter cs p = ''D2''" 
    using `C_D2 p cs cs'` unfolding C_D2_def Let_def by auto
  have Q_eq: "CState.Q_arr cs' = CState.Q_arr cs"
    using `C_D2 p cs cs'` unfolding C_D2_def Let_def
    by simp
    
  let ?lp = "CState.l_var cs p"

  (* ========================================================== *)
  (* Key proof idea. *)
  (* ========================================================== *)
  show ?thesis
  proof (cases "?lp = 1")
    case True
    (* Proof note. *)
    have cs'_eq: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D1'' else c_program_counter cs x) \<rparr>"
      using True `C_D2 p cs cs'` unfolding C_D2_def Let_def by auto
      
    (* Proof note. *)
    let ?ts'_T = "ts\<lparr> t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts x) \<rparr>"
    
    have step_T: "T_D2 p ts ?ts'_T"
      using sim_r pc_D2 unfolding T_D2_def T_D2_BackToD1_def Simulation_R_def Let_def by auto
      
    have sim_R_next: "Simulation_R (cs', us) ?ts'_T"
      unfolding Simulation_R_def Let_def fst_conv snd_conv
    proof (intro conjI)
      (* Condition 2. *)
      show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts'_T q = ''TL0''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts'_T q = ''TE1''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts'_T q = ''TE2''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts'_T q = ''TE3''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts'_T q = ''TD1''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts'_T q = ''TD_Line4_Done''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts'_T q = ''TD_Loop''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts'_T q = ''TD_Remove_Done''"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto

      (* Condition 3. *)
      show "\<forall>q. \<forall>node\<in>set (pools ?ts'_T q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts'_T q = ''TE2'' \<and> t_nid ?ts'_T q = fst node"
        using sim_r cs'_eq True pc_D2 unfolding Simulation_R_def Let_def by auto
     show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow>
        (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
           (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP)"
        proof (intro allI impI)
          fix idx
          assume nz': "CState.Q_arr cs' idx \<noteq> BOT"
        
          have qeq: "CState.Q_arr cs' idx = CState.Q_arr cs idx"
            using Q_eq by simp
        
          have sim_data_map:
            "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow>
               (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                  (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
            using sim_r
            unfolding Simulation_R_def Let_def
            by simp
        
          have ex_old:
            "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP"
            using sim_data_map nz' qeq
            by auto
        
          then obtain u nid ts_val where
            u_in: "u \<in> ProcSet" and
            old_in: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" and
            nz_ts: "ts_val \<noteq> TOP"
            by blast
        
          have new_in:
            "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T u)"
            using old_in qeq by simp
        
          show "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                  (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP"
            using u_in new_in nz_ts by blast
        qed
      show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts'_T u))"
        using sim_r cs'_eq True Q_eq pc_D2 unfolding Simulation_R_def Let_def by auto

      (* Compact proof branch. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx < CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ?ts'_T q)"
      proof (intro allI impI)
        fix q v
        assume pc_q: "c_program_counter cs' q = ''D3''"
        assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
        have q_not_p: "q \<noteq> p" using pc_q cs'_eq by force
        have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_not_p cs'_eq by auto
        have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using q_not_p cs'_eq by auto
        
        from cond obtain idx where idx_less: "idx < CState.j_var cs q" and 
          cond_branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" using j_q_old
          by auto 

        have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
                        (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
        proof (cases "v = p")
          case True
          from cond_branch consider (d_case) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T p) \<and> ts_val \<noteq> TOP"  
                            | (e_case) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' p = ''E2''" "CState.i_var cs' p = idx" "idx \<noteq> BOT" using True by blast 
          then show ?thesis
          proof cases
            case d_case
            thus ?thesis using Q_eq True by auto
          next
            case e_case
            have "c_program_counter cs' p = ''D1''" using cs'_eq by simp
            with e_case(2) show ?thesis by simp
          qed
        next
          case False
          thus ?thesis using cond_branch cs'_eq Q_eq by auto
        qed

        (* Key proof idea. *)
        have cond6_rule: "\<And>q_x v_x. c_program_counter cs q_x = ''D3'' \<Longrightarrow> 
          (\<exists>idx_x < CState.j_var cs q_x. 
            (CState.Q_arr cs idx_x \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx_x, ts_val) \<in> set (pools ts v_x) \<and> ts_val \<noteq> TOP)) \<or> 
            (CState.Q_arr cs idx_x = BOT \<and> c_program_counter cs v_x = ''E2'' \<and> CState.i_var cs v_x = idx_x \<and> idx_x \<noteq> BOT)) 
          \<Longrightarrow> v_x \<in> t_scanned ts q_x"
          using sim_r unfolding Simulation_R_def Let_def by simp

        (* Proof note. *)
        have existential_prems: "\<exists>idx_x < CState.j_var cs q. 
            (CState.Q_arr cs idx_x \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx_x, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
            (CState.Q_arr cs idx_x = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx_x \<and> idx_x \<noteq> BOT)"
          using idx_less old_cond by auto

        (* Proof note. *)
        have "v \<in> t_scanned ts q"
          using cond6_rule[OF pc_q_old existential_prems] .
          
        then show "v \<in> t_scanned ?ts'_T q" by simp
      qed
        
      (* TOP-sensitive branch. *)
      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts'_T q)) = 1"
      proof (intro allI impI)
        fix q assume pc_q: "c_program_counter cs' q = ''E2''"
        have "q \<noteq> p" using pc_q cs'_eq pc_D2 by force
        have old_pc: "c_program_counter cs q = ''E2''" using pc_q `q \<noteq> p` cs'_eq by auto
        have "pools ?ts'_T q = pools ts q" using `q \<noteq> p` by simp
        moreover have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
          using sim_r old_pc unfolding Simulation_R_def Let_def by simp
        ultimately show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts'_T q)) = 1" by simp
      qed
        
      (* Condition 8: startTs timestamp guard. *)
      show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> (\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_T u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts'_T q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts'_T u <\<^sub>t\<^sub>s t_startTs ?ts'_T q))"
        using sim_r cs'_eq True Q_eq pc_D2 unfolding Simulation_R_def Let_def by auto

      (* Condition 9. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts'_T q = BOT \<and> t_candTs ?ts'_T q = TOP"
      proof (intro allI impI)
        fix q assume pc_q: "c_program_counter cs' q = ''D3''"
        have "q \<noteq> p" using pc_q cs'_eq by force
        have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q `q \<noteq> p` cs'_eq by auto
        have old_cand: "t_candNid ts q = BOT \<and> t_candTs ts q = TOP" using sim_r pc_q_old unfolding Simulation_R_def Let_def
          by auto
        have "t_candNid ?ts'_T q = t_candNid ts q" and "t_candTs ?ts'_T q = t_candTs ts q" by simp_all
        then show "t_candNid ?ts'_T q = BOT \<and> t_candTs ?ts'_T q = TOP" using old_cand by simp
      qed

      (* Condition 10. *)
      show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts'_T u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
      proof (intro allI impI)
        fix u nid v_val n
        assume in_pool: "(nid, v_val, TS n) \<in> set (pools ?ts'_T u)"
        have "pools ?ts'_T u = pools ts u" by simp
        with in_pool have in_old: "(nid, v_val, TS n) \<in> set (pools ts u)" by simp
        from sim_r have "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
          unfolding Simulation_R_def Let_def
          by simp 
        with in_old have "CState.Q_arr cs nid = v_val \<and> nid < CState.X_var cs" by blast
        moreover have "CState.Q_arr cs' = CState.Q_arr cs" using Q_eq by simp
        moreover have "CState.X_var cs' = CState.X_var cs" using cs'_eq by simp
        ultimately show "CState.Q_arr cs' nid = v_val \<and> nid < CState.X_var cs'" by simp
      qed

      (* Condition 11: value-range safety of the TSQ pools. *)
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_T u) \<longrightarrow> v \<in> Val"
      proof (intro allI impI)
        fix u nid v_val ts_val
        assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts'_T u)"
        have "pools ?ts'_T u = pools ts u" by simp
        with in_pool have in_old: "(nid, v_val, ts_val) \<in> set (pools ts u)" by simp
        from sim_r have "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val"
          unfolding Simulation_R_def Let_def
          by argo 
        with in_old show "v_val \<in> Val" by blast
      qed

      (* Condition 12.1. *)
      show "nid_counter ?ts'_T = CState.X_var cs'"
      proof -
        have "nid_counter ?ts'_T = nid_counter ts" by simp
        moreover have "CState.X_var cs' = CState.X_var cs" using cs'_eq by simp
        ultimately show ?thesis using sim_r unfolding Simulation_R_def Let_def
          by simp
      qed

      (* Condition 12.2. *)
      show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts'_T q = CState.i_var cs' q"
      proof (intro allI impI)
        fix q assume pc_q: "c_program_counter cs' q \<in> {''E2'', ''E3''}"
        have nid_unchanged: "t_nid ?ts'_T q = t_nid ts q" by simp
        have ivar_unchanged: "CState.i_var cs' q = CState.i_var cs q" using cs'_eq by simp
        show "t_nid ?ts'_T q = CState.i_var cs' q"
        proof (cases "q = p")
          case True
          have "c_program_counter cs' p = ''D1''" using cs'_eq by simp
          with pc_q True show ?thesis by simp
        next
          case False
          have pc_q_old: "c_program_counter cs q \<in> {''E2'', ''E3''}"
            using pc_q False cs'_eq by auto
          from sim_r have "t_nid ts q = CState.i_var cs q" using pc_q_old unfolding Simulation_R_def Let_def
            by (metis fst_eqD)
          with nid_unchanged ivar_unchanged show ?thesis by simp
        qed
      qed

      (* Proof note. *)
      show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
           (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts'_T q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
      proof (intro allI impI allI allI allI impI) 
        fix q u nid v_val ts_val 
        assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
        assume prems: "(nid, v_val, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts'_T q) ts_val"
        
        have in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts'_T u)"
          and not_top: "ts_val \<noteq> TOP"
          and not_less: "\<not> ts_less (t_startTs ?ts'_T q) ts_val"
          using prems by auto

        have q_ne_p: "q \<noteq> p" using pc_q cs'_eq by force
        
        have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" 
          using pc_q q_ne_p cs'_eq by auto
        have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" 
          using q_ne_p cs'_eq by auto
        have start_eq: "t_startTs ?ts'_T q = t_startTs ts q" by simp

        have in_old_pool: "(nid, v_val, ts_val) \<in> set (pools ts u)" 
          using in_pool by simp
        have not_less_old: "\<not> ts_less (t_startTs ts q) ts_val"
          using not_less start_eq by simp

        show "nid < CState.l_var cs' q"
          using sim_r pc_q_old in_old_pool not_top not_less_old l_q_eq
          unfolding Simulation_R_def Let_def
          by (metis fst_eqD)
      qed

      (* Condition 14: enqueue/dequeue coherence across the two states. *)
      show "\<forall>q1 q2. c_program_counter cs' q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts'_T q2) (t_ts ?ts'_T q1) \<longrightarrow> CState.i_var cs' q1 < CState.l_var cs' q2"
      proof (intro allI impI, elim conjE)
        fix q1 q2
        assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
        assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
        assume not_less: "\<not> ts_less (t_startTs ?ts'_T q2) (t_ts ?ts'_T q1)"
        
        have "q1 \<noteq> p" using pc_q1 cs'_eq by force
        have "q2 \<noteq> p" using pc_q2 cs'_eq by force
        
        have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}"
          using pc_q1 `q1 \<noteq> p` cs'_eq by auto
        have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}"
          using pc_q2 `q2 \<noteq> p` cs'_eq by auto
          
        have start_eq: "t_startTs ?ts'_T q2 = t_startTs ts q2" by simp
        have ts_eq: "t_ts ?ts'_T q1 = t_ts ts q1" by simp
        have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)"
          using not_less start_eq ts_eq by simp
          
        have i_var_eq: "CState.i_var cs' q1 = CState.i_var cs q1" using cs'_eq by auto
        have l_var_eq: "CState.l_var cs' q2 = CState.l_var cs q2" using cs'_eq by auto
          
        show "CState.i_var cs' q1 < CState.l_var cs' q2"
          using sim_r pc_q1_old pc_q2_old not_less_old i_var_eq l_var_eq unfolding Simulation_R_def Let_def
          by (metis fst_conv)
      qed

      (* Condition 15. *)
      show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
      proof (intro allI impI)
        fix u nid v ts_val
        assume pc_u: "c_program_counter cs' u = ''E2''"
        assume cond: "(nid, v, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP"

        have u_neq_p: "u \<noteq> p"
          using pc_u cs'_eq by force
        have pc_u_old: "c_program_counter cs u = ''E2''"
          using pc_u u_neq_p cs'_eq by auto
        have i_u_eq: "CState.i_var cs' u = CState.i_var cs u"
          using u_neq_p cs'_eq by auto
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)"
          using cond by simp

        have "nid < CState.i_var cs u"
          using sim_r pc_u_old in_old cond
          unfolding Simulation_R_def Let_def
          by (metis fst_conv)
        then show "nid < CState.i_var cs' u"
          using i_u_eq by simp
      qed

      show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
      proof (intro allI impI)
        fix u nid v ts_val
        assume pc_u: "c_program_counter cs' u = ''E3''"
        assume cond: "(nid, v, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP"

        have u_neq_p: "u \<noteq> p"
          using pc_u cs'_eq by force
        have pc_u_old: "c_program_counter cs u = ''E3''"
          using pc_u u_neq_p cs'_eq by auto
        have i_u_eq: "CState.i_var cs' u = CState.i_var cs u"
          using u_neq_p cs'_eq by auto
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)"
          using cond by simp

        have "nid \<le> CState.i_var cs u"
          using sim_r pc_u_old in_old cond
          unfolding Simulation_R_def Let_def
          by (metis fst_conv)
        then show "nid \<le> CState.i_var cs' u"
          using i_u_eq by simp
      qed



          (* Condition 16: ownership bridge. *)
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_T u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
      proof (intro allI impI, elim conjE)
        fix u nid v ts_val
        assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts'_T u)"
        assume not_top: "ts_val \<noteq> TOP"

        have in_old_pool: "(nid, v, ts_val) \<in> set (pools ts u)"
          using in_pool by simp

        have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
          using sim_r in_old_pool not_top
          unfolding Simulation_R_def Let_def
          by blast

        then obtain sn where his_old: "EnqCallInHis (cs, us) u v sn"
          by blast

        have his_new: "EnqCallInHis (cs', us) u v sn"
          using his_old cs'_eq
          unfolding EnqCallInHis_def his_seq_def
          by auto

        show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
          using his_new by blast
      qed

      (* Condition 17: history completeness of the scanned set. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
            (\<forall>v. v \<in> t_scanned ?ts'_T q \<longrightarrow> 
              (\<exists>idx < CState.j_var cs' q. 
                (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
      proof (intro allI impI)
        fix q v
        assume pc_q_new: "c_program_counter cs' q = ''D3''"
        assume v_scan: "v \<in> t_scanned ?ts'_T q"

        have q_neq_p: "q \<noteq> p"
          using pc_q_new cs'_eq by auto

        have pc_q_old: "c_program_counter cs q = ''D3''"
          using pc_q_new q_neq_p cs'_eq by auto

        have scan_old: "v \<in> t_scanned ts q"
          using v_scan q_neq_p by simp

        have old_cond17:
          "\<exists>idx < CState.j_var cs q.
            (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
            (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
          using sim_r pc_q_old scan_old
          unfolding Simulation_R_def Let_def
          by simp

        then obtain idx where
          idx_lt: "idx < CState.j_var cs q"
          and branches:
            "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
             (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
          by blast

        show "\<exists>idx < CState.j_var cs' q.
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (rule exI[where x=idx], rule conjI)
          show "idx < CState.j_var cs' q"
            using idx_lt q_neq_p cs'_eq by simp
        next
          from branches show
            "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
             (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
          proof (elim disjE)
            assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
            have v_neq_p: "v \<noteq> p"
              using b1 `c_program_counter cs p = ''D2''` pc_D2 by force
            thus ?thesis
              using b1 cs'_eq by auto
          next
            assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
            then obtain v_val sn where
              his: "EnqCallInHis (cs, us) v v_val sn"
              and inq: "InQBack (cs, us) v_val"
              and idx_eq: "Idx (cs, us) v_val = idx"
              by blast

            have his_new: "EnqCallInHis (cs', us) v v_val sn"
              using his cs'_eq
              unfolding EnqCallInHis_def his_seq_def by simp

            have inq_new: "InQBack (cs', us) v_val"
            proof -
              from inq obtain k_pos where
                k_pos_eq: "Qback_arr (cs, us) k_pos = v_val"
                unfolding InQBack_def by blast
              moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
                using cs'_eq unfolding Qback_arr_def by simp
              ultimately show ?thesis
                unfolding InQBack_def by blast
            qed

            have idx_new: "Idx (cs', us) v_val = idx"
            proof -
              have ext_eq: "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
                using cs'_eq unfolding AtIdx_def Qback_arr_def by simp
              show ?thesis
                using idx_eq ext_eq unfolding Idx_def by presburger
            qed

            show ?thesis
              using his_new inq_new idx_new by blast
          qed
        qed
      qed

      (* Condition 18. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v \<in> t_scanned ?ts'_T q. \<forall>nid v_val ts_val. (nid, v_val, ts_val) \<in> set (pools ?ts'_T v) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts'_T q))"
      proof (intro allI impI ballI, elim conjE)
        fix q v nid v_val ts_val
        assume pc_q_new: "c_program_counter cs' q = ''D3''"
        assume v_scan: "v \<in> t_scanned ?ts'_T q"
        assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts'_T v)"
        assume not_top: "ts_val \<noteq> TOP"
        have q_neq_p: "q \<noteq> p" using pc_q_new cs'_eq by auto
        have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p cs'_eq by auto
        have j_var_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_eq by simp
        have startTs_eq: "t_startTs ?ts'_T q = t_startTs ts q" using q_neq_p by simp
        have in_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" using in_pool by simp
        have v_scan_old: "v \<in> t_scanned ts q" using v_scan by simp
        have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
          using sim_r pc_q_old v_scan_old in_old not_top unfolding Simulation_R_def Let_def by (metis fst_conv)
        show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts'_T q)"
          using old_cond18 j_var_eq startTs_eq by simp
      qed

      (* Condition 19. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>u \<in> t_scanned ?ts'_T q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts'_T u) (t_startTs ?ts'_T q))"
      proof (intro allI impI ballI)
        fix q u
        assume pc_q: "c_program_counter cs' q = ''D3''"
        assume u_scan: "u \<in> t_scanned ?ts'_T q"
        assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
        have q_neq_p: "q \<noteq> p" using pc_q cs'_eq by auto
        have u_neq_p: "u \<noteq> p" using pc_u_new cs'_eq `c_program_counter cs p = ''D2''` pc_D2 by force
        have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_neq_p cs'_eq by auto
        have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new u_neq_p cs'_eq by auto
        have u_scan_old: "u \<in> t_scanned ts q" using u_scan by simp
        have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
          using sim_r pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def by (metis fst_conv)
        have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_eq by simp
        have i_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p cs'_eq by simp
        have start_eq: "t_startTs ?ts'_T q = t_startTs ts q" using q_neq_p by simp
        have ts_eq: "t_ts ?ts'_T u = t_ts ts u" using u_neq_p by simp
        show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts'_T u) (t_startTs ?ts'_T q)"
          using old_cond19 j_eq i_eq start_eq ts_eq by simp
      qed

      (* ========================================================================= *)
      (* NEW *)
      (* ========================================================================= *)
      have vvar_cs_unchanged: "CState.V_var cs' = CState.V_var cs"
  using cs'_eq by simp

have vvar_ts_unchanged: "t_V_var ?ts'_T = t_V_var ts"
  using step_T unfolding T_D2_def Let_def by auto

show "CState.V_var cs' = t_V_var ?ts'_T"
  using sim_r vvar_cs_unchanged vvar_ts_unchanged
  unfolding Simulation_R_def Let_def
  by simp

show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts'_T q"
proof (intro allI impI)
  fix q
  assume hE1: "c_program_counter cs' q = ''E1''"

 have q_ne_p: "q \<noteq> p"
proof
  assume "q = p"
  with hE1 cs'_eq show False
    by simp
qed

  have pc_old: "c_program_counter cs q = ''E1''"
    using hE1 cs'_eq q_ne_p by simp

have sim_e1_sync:
  "\<forall>r. c_program_counter cs r = ''E1'' \<longrightarrow> CState.v_var cs r = t_v ts r"
  using sim_r
  unfolding Simulation_R_def Let_def
  by simp

have sim_old: "CState.v_var cs q = t_v ts q"
  using sim_e1_sync pc_old
  by blast

  have v_cs_unchanged: "CState.v_var cs' q = CState.v_var cs q"
    using cs'_eq q_ne_p by simp

  have v_ts_unchanged: "t_v ?ts'_T q = t_v ts q"
    using step_T q_ne_p unfolding T_D2_def Let_def by auto

  show "CState.v_var cs' q = t_v ?ts'_T q"
    using sim_old v_cs_unchanged v_ts_unchanged by simp
qed
qed
    
    then show ?thesis using step_T by blast

  next
    case False
    (* Proof note. *)
    have cs'_eq: "cs' = cs\<lparr> j_var := (\<lambda>x. if x = p then 1 else CState.j_var cs x), c_program_counter := (\<lambda>x. if x = p then ''D3'' else c_program_counter cs x) \<rparr>"
      using False `C_D2 p cs cs'` unfolding C_D2_def Let_def by auto
      
    (* Proof note. *)
    let ?ts'_F = "ts\<lparr> 
      t_pc := (\<lambda>x. if x = p then ''TD_Loop'' else t_pc ts x),
      t_scanned := (\<lambda>x. if x = p then {} else t_scanned ts x),
      t_candNid := (\<lambda>x. if x = p then BOT else t_candNid ts x),
      t_candPid := (\<lambda>x. if x = p then BOT else t_candPid ts x),
      t_candTs  := (\<lambda>x. if x = p then TOP else t_candTs ts x)
    \<rparr>"
    
    have step_F: "T_D2 p ts ?ts'_F"
      using sim_r pc_D2 unfolding T_D2_def T_D2_EnterLoop_def Simulation_R_def Let_def by auto

    have sim_R_next: "Simulation_R (cs', us) ?ts'_F"
      unfolding Simulation_R_def Let_def fst_conv snd_conv
    proof (intro conjI)
      (* Condition 2. *)
      show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts'_F q = ''TL0''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts'_F q = ''TE1''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts'_F q = ''TE2''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts'_F q = ''TE3''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts'_F q = ''TD1''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts'_F q = ''TD_Line4_Done''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts'_F q = ''TD_Loop''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
      show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts'_F q = ''TD_Remove_Done''"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto

      show "\<forall>q. \<forall>node\<in>set (pools ?ts'_F q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts'_F q = ''TE2'' \<and> t_nid ?ts'_F q = fst node"
        using sim_r cs'_eq False pc_D2 unfolding Simulation_R_def Let_def by auto
    show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow>
        (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
           (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP)"
        proof (intro allI impI)
          fix idx
          assume nz': "CState.Q_arr cs' idx \<noteq> BOT"
        
          have qeq: "CState.Q_arr cs' idx = CState.Q_arr cs idx"
            using Q_eq by simp
        
          have sim_data_map:
            "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow>
               (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                  (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
            using sim_r
            unfolding Simulation_R_def Let_def
            by simp
        
          have ex_old:
            "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP"
            using sim_data_map nz' qeq
            by auto
        
          then obtain u nid ts_val where
            u_in: "u \<in> ProcSet" and
            old_in: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" and
            nz_ts: "ts_val \<noteq> TOP"
            by blast
        
          have new_in:
            "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u)"
            using old_in qeq by simp
        
          show "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                  (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP"
            using u_in new_in nz_ts by blast
        qed
      show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts'_F u))"
        using sim_r cs'_eq False Q_eq pc_D2 unfolding Simulation_R_def Let_def by auto

      (* Compact proof branch. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx < CState.j_var cs' q. ((CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT))) \<longrightarrow> v \<in> t_scanned ?ts'_F q)"
      proof (intro allI impI)
        fix q v
        assume pc_q: "c_program_counter cs' q = ''D3''"
        assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
        
        show "v \<in> t_scanned ?ts'_F q"
        proof (cases "q = p")
          case True
          (* Proof note. *)
          have "CState.j_var cs' p = 1" using cs'_eq by simp
          with True cond obtain idx where "idx < 1" and 
            branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
            by simp 
          then have "idx = 0" by simp
          then have idx_bot: "idx = BOT" unfolding BOT_def by simp
          
          from branch consider (left) "CState.Q_arr cs' idx \<noteq> BOT" | (right) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' v = ''E2''" "CState.i_var cs' v = idx" "idx \<noteq> BOT" by blast
          then show ?thesis
          proof cases
            case left
            have "CState.Q_arr cs' BOT = BOT"
            proof -
              have "CState.Q_arr cs' BOT = CState.Q_arr cs BOT" using Q_eq by simp
              moreover have "CState.Q_arr cs BOT = BOT" 
                using inv_sys unfolding system_invariant_def sI1_Zero_Index_BOT_def BOT_def Q_arr_def by fastforce
              ultimately show ?thesis by simp
            qed
            with left idx_bot show ?thesis by simp
          next
            case right
            with idx_bot show ?thesis by simp
          qed
        next
          case False
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q False cs'_eq pc_D2 by auto
          have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using False cs'_eq by auto
          have scan_eq: "t_scanned ?ts'_F q = t_scanned ts q" using False by simp
          
          from cond obtain idx where idx_less_old: "idx < CState.j_var cs q" and 
            branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" using j_q_old
            by force

          have old_cond: "((CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT))"
          proof -
            from branch consider (left_c) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F v) \<and> ts_val \<noteq> TOP" 
                             | (right_c) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' v = ''E2''" "CState.i_var cs' v = idx" "idx \<noteq> BOT" by blast
            then show ?thesis
            proof cases
              case left_c
              then show ?thesis using Q_eq by auto
            next
              case right_c
              have "v \<noteq> p" using right_c(2) cs'_eq by force
              then have "c_program_counter cs v = ''E2''" and "CState.i_var cs v = idx"
                using right_c cs'_eq by auto
              with right_c(1) right_c(4) Q_eq show ?thesis by auto
            qed
          qed
            
          have "v \<in> t_scanned ts q"
            using sim_r pc_q_old idx_less_old old_cond unfolding Simulation_R_def Let_def
            by (metis fst_conv) 
          then show ?thesis using scan_eq by simp
        qed
      qed

      (* TOP-sensitive branch. *)
      show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts'_F q)) = 1"
      proof (intro allI impI)
        fix q assume pc_q: "c_program_counter cs' q = ''E2''"
        have "q \<noteq> p" using pc_q cs'_eq pc_D2 by force
        have old_pc: "c_program_counter cs q = ''E2''" using pc_q `q \<noteq> p` cs'_eq by auto
        have "pools ?ts'_F q = pools ts q" using `q \<noteq> p` by simp
        
        (* Key proof idea. *)
        moreover have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
          using sim_r old_pc unfolding Simulation_R_def Let_def by (metis fst_conv)
          
        ultimately show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts'_F q)) = 1" by simp
      qed

      (* This fact is shared by the D2 and D3 cases. *)
      show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> (\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts'_F q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts'_F u <\<^sub>t\<^sub>s t_startTs ?ts'_F q))"
      proof (rule allI, rule impI)
        fix q assume pc_q: "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''"
        show "\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts'_F q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts'_F u <\<^sub>t\<^sub>s t_startTs ?ts'_F q)"
        proof (rule allI, rule impI) 
          fix idx assume idx_less: "idx < CState.l_var cs' q"
          
          have old_pc_q: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''"
          proof (cases "q = p")
            case True
            then have "c_program_counter cs q = ''D2''" using pc_D2 by simp
            then show ?thesis by simp
          next
            case False
            then have "c_program_counter cs q = c_program_counter cs' q" using cs'_eq by auto
            with pc_q show ?thesis by auto
          qed
          have l_eq: "CState.l_var cs' q = CState.l_var cs q" using cs'_eq by auto
          have idx_less_old: "idx < CState.l_var cs q" using idx_less l_eq by simp
          have start_eq: "t_startTs ?ts'_F q = t_startTs ts q" by simp
          
          show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts'_F q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts'_F u <\<^sub>t\<^sub>s t_startTs ?ts'_F q)"
          proof (rule conjI)
            show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts'_F q)"
            proof (intro impI allI)
              fix u nid ts_val
              assume q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT"
              assume in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_F u)"
              have in_old_pool: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" using in_pool Q_eq by simp
              have "ts_val <\<^sub>t\<^sub>s t_startTs ts q"
                using sim_r old_pc_q idx_less_old Q_eq q_not_bot in_old_pool unfolding Simulation_R_def Let_def
                by (metis (lifting) fst_conv) 
              thus "ts_val <\<^sub>t\<^sub>s t_startTs ?ts'_F q" using start_eq by simp
            qed
            
            show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts'_F u <\<^sub>t\<^sub>s t_startTs ?ts'_F q"
            proof (intro allI impI)
              fix u assume cond: "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
              have "u \<noteq> p" using cond cs'_eq pc_D2 by force
              have old_pc_u: "c_program_counter cs u = ''E2''" using cond `u \<noteq> p` cs'_eq by auto
              have old_i_u: "CState.i_var cs u = idx" using cond `u \<noteq> p` cs'_eq by auto
              have ts_u_eq: "t_ts ?ts'_F u = t_ts ts u" using `u \<noteq> p` by simp
              
              have "t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q"
                using sim_r old_pc_q idx_less_old Q_eq cond old_pc_u old_i_u unfolding Simulation_R_def Let_def
                by (metis fst_conv)
              then show "t_ts ?ts'_F u <\<^sub>t\<^sub>s t_startTs ?ts'_F q" using ts_u_eq start_eq by simp
            qed
          qed
        qed
      qed

      (* Proof note. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts'_F q = BOT \<and> t_candTs ?ts'_F q = TOP"
      proof (intro allI impI)
        fix q assume pc_q: "c_program_counter cs' q = ''D3''"
        show "t_candNid ?ts'_F q = BOT \<and> t_candTs ?ts'_F q = TOP"
        proof (cases "q = p")
          case True
          then show ?thesis by simp
        next
          case False
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q False cs'_eq by auto
          have old_cand: "t_candNid ts q = BOT \<and> t_candTs ts q = TOP" using sim_r pc_q_old unfolding Simulation_R_def Let_def
            by auto
          have "t_candNid ?ts'_F q = t_candNid ts q" and "t_candTs ?ts'_F q = t_candTs ts q" using False by simp_all
          then show ?thesis using old_cand by simp
        qed
      qed

      (* Condition 10. *)
      show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts'_F u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
      proof (intro allI impI)
        fix u nid v_val n
        assume in_pool: "(nid, v_val, TS n) \<in> set (pools ?ts'_F u)"
        have "pools ?ts'_F u = pools ts u" by simp
        with in_pool have in_old: "(nid, v_val, TS n) \<in> set (pools ts u)" by simp
        from sim_r have "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ts u) \<longrightarrow> CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
          unfolding Simulation_R_def Let_def
          by simp
        with in_old have "CState.Q_arr cs nid = v_val \<and> nid < CState.X_var cs" by blast
        moreover have "CState.Q_arr cs' = CState.Q_arr cs" using Q_eq by simp
        moreover have "CState.X_var cs' = CState.X_var cs" using cs'_eq by simp
        ultimately show "CState.Q_arr cs' nid = v_val \<and> nid < CState.X_var cs'" by simp
      qed

      (* Condition 11: value-range safety of the TSQ pools. *)
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_F u) \<longrightarrow> v \<in> Val"
      proof (intro allI impI)
        fix u nid v_val ts_val
        assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts'_F u)"
        have "pools ?ts'_F u = pools ts u" by simp
        with in_pool have in_old: "(nid, v_val, ts_val) \<in> set (pools ts u)" by simp
        from sim_r have "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ts u) \<longrightarrow> v \<in> Val"
          unfolding Simulation_R_def Let_def
          by argo 
        with in_old show "v_val \<in> Val" by blast
      qed

      (* Condition 12.1. *)
      show "nid_counter ?ts'_F = CState.X_var cs'"
      proof -
        have "nid_counter ?ts'_F = nid_counter ts" by simp
        moreover have "CState.X_var cs' = CState.X_var cs" using cs'_eq by simp
        ultimately show ?thesis using sim_r unfolding Simulation_R_def Let_def
          by (metis fst_conv) 
      qed

      (* Condition 12.2. *)
      show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts'_F q = CState.i_var cs' q"
      proof (intro allI impI)
        fix q assume pc_q: "c_program_counter cs' q \<in> {''E2'', ''E3''}"
        have nid_unchanged: "t_nid ?ts'_F q = t_nid ts q" by simp
        have ivar_unchanged: "CState.i_var cs' q = CState.i_var cs q" using cs'_eq by simp
        show "t_nid ?ts'_F q = CState.i_var cs' q"
        proof (cases "q = p")
          case True
          (* Proof note. *)
          have "c_program_counter cs' p = ''D3''" using cs'_eq by simp
          with pc_q True show ?thesis by simp
        next
          case False
          have pc_q_old: "c_program_counter cs q \<in> {''E2'', ''E3''}"
            using pc_q False cs'_eq by auto
          from sim_r have "t_nid ts q = CState.i_var cs q" using pc_q_old unfolding Simulation_R_def Let_def
            by (metis fst_eqD)
          with nid_unchanged ivar_unchanged show ?thesis by simp
        qed
      qed

      (* Proof note. *)
      show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
           (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts'_F q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
      proof (intro allI impI allI allI allI impI)
        fix q u nid v_val ts_val
        assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
        assume prems: "(nid, v_val, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts'_F q) ts_val"

        have in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts'_F u)"
          and not_top: "ts_val \<noteq> TOP"
          and not_less: "\<not> ts_less (t_startTs ?ts'_F q) ts_val"
          using prems by auto

        have in_old_pool: "(nid, v_val, ts_val) \<in> set (pools ts u)" 
          using in_pool by simp

        show "nid < CState.l_var cs' q"
        proof (cases "q = p")
          case True
          have pc_q_old: "c_program_counter cs q = ''D2''" using True pc_D2 by simp
          have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" using cs'_eq by auto
          have start_eq: "t_startTs ?ts'_F q = t_startTs ts q" by simp
          
          have not_less_old: "\<not> ts_less (t_startTs ts q) ts_val"
            using not_less start_eq by simp
            
          show ?thesis
            using sim_r pc_q_old in_old_pool not_top not_less_old l_q_eq
            unfolding Simulation_R_def Let_def
            by (metis fst_eqD insertI1)
        next
          case False
          have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" 
            using pc_q False cs'_eq by auto
          have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" 
            using False cs'_eq by auto
          have start_eq: "t_startTs ?ts'_F q = t_startTs ts q" by simp
          
          have not_less_old: "\<not> ts_less (t_startTs ts q) ts_val"
            using not_less start_eq by simp
            
          show ?thesis
            using sim_r pc_q_old in_old_pool not_top not_less_old l_q_eq
            unfolding Simulation_R_def Let_def
            by (metis fst_conv)
        qed
      qed

      (* Proof note. *)
      show "\<forall>q1 q2. c_program_counter cs' q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts'_F q2) (t_ts ?ts'_F q1) \<longrightarrow> CState.i_var cs' q1 < CState.l_var cs' q2"
      proof (intro allI impI, elim conjE)
        fix q1 q2
        assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
        assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
        assume not_less: "\<not> ts_less (t_startTs ?ts'_F q2) (t_ts ?ts'_F q1)"
        
        have "q1 \<noteq> p" using pc_q1 cs'_eq by force
        
        have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}"
          using pc_q1 `q1 \<noteq> p` cs'_eq by auto
          
        have ts_eq: "t_ts ?ts'_F q1 = t_ts ts q1" using `q1 \<noteq> p` by simp
        have i_var_eq: "CState.i_var cs' q1 = CState.i_var cs q1" using cs'_eq by auto

        show "CState.i_var cs' q1 < CState.l_var cs' q2"
        proof (cases "q2 = p")
          case True
          have pc_q2_old: "c_program_counter cs q2 = ''D2''" using True pc_D2 by simp
          have start_eq: "t_startTs ?ts'_F q2 = t_startTs ts q2" by simp
          have l_var_eq: "CState.l_var cs' q2 = CState.l_var cs q2" using cs'_eq by auto
          
          have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)"
            using not_less start_eq ts_eq by simp
            
          show ?thesis
            using sim_r pc_q1_old pc_q2_old not_less_old i_var_eq l_var_eq unfolding Simulation_R_def Let_def
            by auto
        next
          case False
          have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}"
            using pc_q2 False cs'_eq by auto
          have start_eq: "t_startTs ?ts'_F q2 = t_startTs ts q2" by simp
          have l_var_eq: "CState.l_var cs' q2 = CState.l_var cs q2" using cs'_eq by auto
          
          have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)"
            using not_less start_eq ts_eq by simp
            
          show ?thesis
            using sim_r pc_q1_old pc_q2_old not_less_old i_var_eq l_var_eq unfolding Simulation_R_def Let_def
            by (metis fst_conv)
        qed
      qed

      (* Condition 15. *)
      show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
      proof (intro allI impI)
        fix u nid v ts_val
        assume pc_u: "c_program_counter cs' u = ''E2''"
        assume cond: "(nid, v, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP"
        
        have u_neq_p: "u \<noteq> p" using pc_u cs'_eq pc_D2 by force
        have pc_u_old: "c_program_counter cs u = ''E2''" using pc_u u_neq_p cs'_eq by auto
        have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p cs'_eq by auto
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond u_neq_p by simp
        
        have "nid < CState.i_var cs u"
          using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def by (metis fst_conv)
        then show "nid < CState.i_var cs' u" using i_u_eq by simp
      qed

      show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
      proof (intro allI impI)
        fix u nid v ts_val
        assume pc_u: "c_program_counter cs' u = ''E3''"
        assume cond: "(nid, v, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP"
        
        have u_neq_p: "u \<noteq> p" using pc_u cs'_eq pc_D2 by force
        have pc_u_old: "c_program_counter cs u = ''E3''" using pc_u u_neq_p cs'_eq by auto
        have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p cs'_eq by auto
        have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond u_neq_p by simp
        
        have "nid \<le> CState.i_var cs u"
          using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def by (metis fst_conv)
        then show "nid \<le> CState.i_var cs' u" using i_u_eq by simp
      qed

          (* Condition 16: ownership bridge. *)
      show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_F u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
      proof (intro allI impI, elim conjE)
        fix u nid v ts_val
        assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts'_F u)"
        assume not_top: "ts_val \<noteq> TOP"

        have in_old_pool: "(nid, v, ts_val) \<in> set (pools ts u)"
          using in_pool by simp

        have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
          using sim_r in_old_pool not_top
          unfolding Simulation_R_def Let_def
          by blast

        then obtain sn where his: "EnqCallInHis (cs, us) u v sn"
          by blast

        have his_new: "EnqCallInHis (cs', us) u v sn"
          using his cs'_eq
          unfolding EnqCallInHis_def his_seq_def
          by auto

        show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
          using his_new by blast
      qed

      (* Condition 17: history completeness of the scanned set. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
            (\<forall>v. v \<in> t_scanned ?ts'_F q \<longrightarrow> 
              (\<exists>idx < CState.j_var cs' q. 
                (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
                (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
      proof (intro allI impI)
        fix q v
        assume pc_q_new: "c_program_counter cs' q = ''D3''"
        assume v_scan: "v \<in> t_scanned ?ts'_F q"

        show "\<exists>idx < CState.j_var cs' q. 
              (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> 
              (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (cases "q = p")
          case True
          have "v \<in> {}"
            using v_scan True by simp
          thus ?thesis
            by simp
        next
          case False
          have pc_q_old: "c_program_counter cs q = ''D3''"
            using pc_q_new False cs'_eq by auto

          have scan_old: "v \<in> t_scanned ts q"
            using v_scan False by simp

          have old_cond17:
            "\<exists>idx < CState.j_var cs q.
              (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
              (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            using sim_r pc_q_old scan_old
            unfolding Simulation_R_def Let_def
            by simp

          then obtain idx where
            idx_lt: "idx < CState.j_var cs q"
            and branches:
              "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
               (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            by blast

          show ?thesis
          proof (rule exI[where x=idx], rule conjI)
            show "idx < CState.j_var cs' q"
              using idx_lt False cs'_eq by simp
          next
            from branches show
              "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
               (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
            proof (elim disjE)
              assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
              have v_neq_p: "v \<noteq> p"
                using b1 `c_program_counter cs p = ''D2''` pc_D2 by force
              thus ?thesis
                using b1 cs'_eq by auto
            next
              assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"

              then obtain v_val sn where
                his: "EnqCallInHis (cs, us) v v_val sn"
                and inq: "InQBack (cs, us) v_val"
                and idx_eq: "Idx (cs, us) v_val = idx"
                by blast

              have his_new: "EnqCallInHis (cs', us) v v_val sn"
                using his cs'_eq
                unfolding EnqCallInHis_def his_seq_def by simp

              have inq_new: "InQBack (cs', us) v_val"
              proof -
                from inq obtain k_pos where
                  k_pos_eq: "Qback_arr (cs, us) k_pos = v_val"
                  unfolding InQBack_def by blast
                moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
                  using cs'_eq unfolding Qback_arr_def by simp
                ultimately show ?thesis
                  unfolding InQBack_def by blast
              qed

              have idx_new: "Idx (cs', us) v_val = idx"
              proof -
                have ext_eq: "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
                  using cs'_eq unfolding AtIdx_def Qback_arr_def by simp
                show ?thesis
                  using idx_eq ext_eq unfolding Idx_def by presburger
              qed

              show ?thesis
                using his_new inq_new idx_new by blast
            qed
          qed
        qed
      qed

      (* Condition 18. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v \<in> t_scanned ?ts'_F q. \<forall>nid v_val ts_val. (nid, v_val, ts_val) \<in> set (pools ?ts'_F v) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts'_F q))"
      proof (intro allI impI ballI, elim conjE)
        fix q v nid v_val ts_val
        assume pc_q_new: "c_program_counter cs' q = ''D3''"
        assume v_scan: "v \<in> t_scanned ?ts'_F q"
        assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts'_F v)"
        assume not_top: "ts_val \<noteq> TOP"
        show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts'_F q)"
        proof (cases "q = p")
          case True
          have "v \<in> {}" using v_scan True by simp
          thus ?thesis by simp
        next
          case False
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new False cs'_eq by auto
          have j_var_eq: "CState.j_var cs' q = CState.j_var cs q" using False cs'_eq by simp
          have startTs_eq: "t_startTs ?ts'_F q = t_startTs ts q" using False by simp
          have in_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" using in_pool by simp
          have v_scan_old: "v \<in> t_scanned ts q" using v_scan False by simp
          have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
            using sim_r pc_q_old v_scan_old in_old not_top unfolding Simulation_R_def Let_def by (metis fst_conv)
          show ?thesis using old_cond18 j_var_eq startTs_eq by simp
        qed
      qed

      (* Condition 19. *)
      show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>u \<in> t_scanned ?ts'_F q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts'_F u) (t_startTs ?ts'_F q))"
      proof (intro allI impI ballI)
        fix q u
        assume pc_q: "c_program_counter cs' q = ''D3''"
        assume u_scan: "u \<in> t_scanned ?ts'_F q"
        assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
        show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts'_F u) (t_startTs ?ts'_F q)"
        proof (cases "q = p")
          case True
          have "u \<in> {}" using u_scan True by simp
          thus ?thesis by simp
        next
          case False
          have u_neq_p: "u \<noteq> p" using pc_u_new cs'_eq `c_program_counter cs p = ''D2''` pc_D2 by force
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q False cs'_eq by auto
          have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new u_neq_p cs'_eq by auto
          have u_scan_old: "u \<in> t_scanned ts q" using u_scan False by simp
          have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
            using sim_r pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def by (metis fst_conv)
          have j_eq: "CState.j_var cs' q = CState.j_var cs q" using False cs'_eq by simp
          have i_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p cs'_eq by simp
          have start_eq: "t_startTs ?ts'_F q = t_startTs ts q" using False by simp
          have ts_eq: "t_ts ?ts'_F u = t_ts ts u" using u_neq_p by simp
          show ?thesis using old_cond19 j_eq i_eq start_eq ts_eq by simp
        qed
      qed

      (* ========================================================================= *)
      (* NEW *)
      (* ========================================================================= *)
      show "CState.V_var cs' = t_V_var ?ts'_F" 
        using sim_r cs'_eq unfolding Simulation_R_def Let_def by auto

      show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts'_F q" 
        using sim_r cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)

    qed
    then show ?thesis using step_F by blast
  qed
qed

(* ==================================================================== *)
(* ========================================================== *)
(* ==================================================================== *)
lemma Simulation_R_D3:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes sim_inv: "Simulation_Inv (cs, us) ts"
      and c_step: "C_D3 p cs cs'"
      and E2_in_ProcSet: "\<forall>q. c_program_counter cs q = ''E2'' \<longrightarrow> q \<in> ProcSet"
  shows "\<exists>ts'. T_D3 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  (* Proof note. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
   using sim_inv unfolding Simulation_Inv_def by auto

  (* Proof step. *)
  have pc_D3: "c_program_counter cs p = ''D3''" 
    using c_step unfolding C_D3_def Let_def by auto
    
  let ?jp = "CState.j_var cs p"
  let ?lp = "CState.l_var cs p"
  let ?q_val = "CState.Q_arr cs ?jp"

  show ?thesis
  proof (cases "?q_val = BOT")
    case True
    (* ========================================================== *)
    (* q_val = BOT *)
    (* ========================================================== *)
    
    (* Proof note. *)
    have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs"
      using True `C_D3 p cs cs'` unfolding C_D3_def Let_def by force

    show ?thesis
    proof (cases "?jp = ?lp - 1")
      case True
      (* -------------------------------------------------------- *)
      (* Proof note. *)
      (* -------------------------------------------------------- *)
      
      have q_upd: "(\<lambda>x. if x = CState.j_var cs p then BOT else CState.Q_arr cs x) = CState.Q_arr cs"
        using `?q_val = BOT` by fastforce 
      have j_upd: "(\<lambda>x. if x = p then CState.j_var cs p else CState.j_var cs x) = CState.j_var cs"
        by auto
      have x_upd: "(\<lambda>x. if x = p then CState.Q_arr cs (CState.j_var cs p) else CState.x_var cs x) = (\<lambda>x. if x = p then BOT else CState.x_var cs x)"
        using `?q_val = BOT` by auto
        
      have cs'_eq: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D1'' else c_program_counter cs x),
                              x_var := (\<lambda>x. if x = p then BOT else CState.x_var cs x) \<rparr>"
        using `?q_val = BOT` True `C_D3 p cs cs'` q_upd j_upd x_upd unfolding C_D3_def Let_def by auto

      have fast_forward_cond: "\<forall>k \<in> ProcSet - t_scanned ts p. 
             fst (pool_getOldest (pools ts k)) = BOT \<or> 
             \<not> ts_less (snd (pool_getOldest (pools ts k))) (t_candTs ts p) \<or> 
             ts_less (t_startTs ts p) (snd (pool_getOldest (pools ts k)))"
      proof (intro ballI)
        fix k assume k_in: "k \<in> ProcSet - t_scanned ts p"
        show "fst (pool_getOldest (pools ts k)) = BOT \<or> 
              \<not> ts_less (snd (pool_getOldest (pools ts k))) (t_candTs ts p) \<or> 
              ts_less (t_startTs ts p) (snd (pool_getOldest (pools ts k)))"
        proof (cases "fst (pool_getOldest (pools ts k)) = BOT")
          case True then show ?thesis by simp
        next
          case False
          obtain nid tstamp where old_k: "pool_getOldest (pools ts k) = (nid, tstamp)" by fastforce
          from False old_k have "nid \<noteq> BOT" by auto
          
          have q_bot: "CState.Q_arr cs (CState.j_var cs p) = BOT" using `?q_val = BOT` by simp
          have j_eq: "CState.j_var cs p = CState.l_var cs p - 1" using True by simp
          
          have "ts_less (t_startTs ts p) tstamp"
            using unscanned_node_ts_gt_startTs[OF inv_sys inv_tsq sim_r pc_D3 j_eq q_bot k_in old_k `nid \<noteq> BOT`] .
            
          with old_k show ?thesis by simp
        qed
      qed

      have pc_loop: "t_pc ts p = ''TD_Loop''" using sim_r pc_D3 unfolding Simulation_R_def Let_def by auto
      from Ghost_Fast_Forward[OF pc_loop fast_forward_cond]
      obtain ts_mid where step_star: "T_D3_Scan_Star p ts ts_mid" 
                      and scanned_all: "ProcSet \<subseteq> t_scanned ts_mid p" 
                      and cand_eq: "t_candNid ts_mid p = t_candNid ts p" by blast

      (* Proof note. *)
      have preserve: "pools ts_mid = pools ts \<and> t_ts ts_mid = t_ts ts \<and> 
                      t_startTs ts_mid = t_startTs ts \<and> nid_counter ts_mid = nid_counter ts \<and> 
                      t_nid ts_mid = t_nid ts \<and> (\<forall>q. t_pc ts_mid q = t_pc ts q) \<and> 
                      (\<forall>q. q \<noteq> p \<longrightarrow> t_scanned ts_mid q = t_scanned ts q) \<and>
                      (\<forall>q. q \<noteq> p \<longrightarrow> t_candNid ts_mid q = t_candNid ts q) \<and>
                      (\<forall>q. q \<noteq> p \<longrightarrow> t_candTs ts_mid q = t_candTs ts q) \<and>
                      t_V_var ts_mid = t_V_var ts \<and> t_v ts_mid = t_v ts" (* Proof note. *)
        using step_star
      proof (induction rule: T_D3_Scan_Star.induct)
        case refl then show ?case by simp
      next
        case (step ts1 k ts2 ts3)
        then show ?case unfolding T_D3_Scan_def Let_def by auto
      qed

      let ?ts'_Fail = "ts_mid\<lparr> t_pc := (\<lambda>x. if x = p then ''TD1'' else t_pc ts_mid x) \<rparr>"

      have step_EvalFail: "T_D3_Eval p ts_mid ?ts'_Fail"
      proof -
        have "t_pc ts_mid p = ''TD_Loop''" using preserve pc_loop by simp
        moreover have "t_candNid ts p = BOT" using sim_r pc_D3 unfolding Simulation_R_def Let_def
          by auto 
        with cand_eq have "t_candNid ts_mid p = BOT" by simp
        moreover have "t_scanned ts_mid p = ProcSet" 
        proof -
        have "t_scanned ts p \<subseteq> ProcSet"
          using TSQ_State_InvD_scanned_subset[OF inv_tsq] .
          then have "t_scanned ts_mid p \<subseteq> ProcSet" 
            using T_D3_Scan_Star_scanned_subset[OF step_star] by simp
          with scanned_all show ?thesis by blast
        qed
        ultimately show ?thesis unfolding T_D3_Eval_def Let_def by auto
      qed

      have sim_R_Fail: "Simulation_R (cs', us) ?ts'_Fail"
        unfolding Simulation_R_def Let_def fst_conv snd_conv
      proof (intro conjI)
        (* Proof note. *)
        show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts'_Fail q = ''TL0''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto
        show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts'_Fail q = ''TE1''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto
        show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts'_Fail q = ''TE2''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto
        show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts'_Fail q = ''TE3''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto
        show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts'_Fail q = ''TD1''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto
        show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts'_Fail q = ''TD_Line4_Done''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts'_Fail q = ''TD_Loop''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto
        show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts'_Fail q = ''TD_Remove_Done''" using sim_r cs'_eq pc_D3 preserve unfolding Simulation_R_def Let_def by auto

        (* Condition 3: validity of timestamps in the TSQ pools. *)
        show "\<forall>q. \<forall>node\<in>set (pools ?ts'_Fail q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts'_Fail q = ''TE2'' \<and> t_nid ?ts'_Fail q = fst node"
        proof (intro allI ballI)
          fix q node assume "node \<in> set (pools ?ts'_Fail q)"
          then have in_old: "node \<in> set (pools ts q)" using preserve by simp
          have old_cond: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
            using sim_r in_old unfolding Simulation_R_def Let_def by meson 
          show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts'_Fail q = ''TE2'' \<and> t_nid ?ts'_Fail q = fst node"
          proof (cases "q = p")
            case True
            have "t_pc ts p \<noteq> ''TE2''" using sim_r pc_D3 unfolding Simulation_R_def Let_def by fastforce
            with old_cond True have "snd (snd node) \<noteq> TOP" by blast
            then show ?thesis by simp
          next
            case False
            with old_cond preserve show ?thesis by auto
          qed
        qed

        (* Condition 5.1. *)
       show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow>
        (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
           (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP)"
        proof (intro allI impI)
          fix idx
          assume nz': "CState.Q_arr cs' idx \<noteq> BOT"
        
          have qeq: "CState.Q_arr cs' idx = CState.Q_arr cs idx"
            using cs'_eq by simp
        
have sim_data_map_old:
  "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow>
     (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
        (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<and> ts_val \<noteq> TOP)"
  using sim_r
  unfolding Simulation_R_def Let_def
  by simp

have sim_data_map:
  "\<forall>idx. CState.Q_arr cs idx \<noteq> BOT \<longrightarrow>
     (\<exists>u\<in>ProcSet. \<exists>nid ts_val.
        (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts_mid u) \<and> ts_val \<noteq> TOP)"
  using sim_data_map_old preserve
  by simp
        
          have ex_old:
            "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts_mid u) \<and> ts_val \<noteq> TOP"
            using sim_data_map nz' qeq
            by auto
        
          then obtain u nid ts_val where
            u_in: "u \<in> ProcSet" and
            old_in: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts_mid u)" and
            nz_ts: "ts_val \<noteq> TOP"
            by blast
        
          have new_in:
            "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail u)"
            using old_in qeq by simp
        
          show "\<exists>u\<in>ProcSet. \<exists>nid ts_val.
                  (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP"
            using u_in new_in nz_ts by blast
        qed
        (* Condition 5.2: mapping for pending elements. *)
        show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts'_Fail u))"
        proof (intro allI impI, elim conjE)
          fix u idx
          assume q_bot: "CState.Q_arr cs' idx = BOT"
          assume pc_u: "c_program_counter cs' u = ''E2''"
          assume i_u: "CState.i_var cs' u = idx"

          have "u \<noteq> p" using pc_u cs'_eq by force
          
          have old_pc_u: "c_program_counter cs u = ''E2''" using pc_u `u \<noteq> p` cs'_eq by auto
          have old_q_bot: "CState.Q_arr cs idx = BOT" using q_bot cs'_eq by simp
          have old_i_u: "CState.i_var cs u = idx" using i_u `u \<noteq> p` cs'_eq by auto
          
          have "\<exists>nid. (nid, CState.v_var cs u, TOP) \<in> set (pools ts u)"
            using sim_r old_q_bot old_pc_u old_i_u unfolding Simulation_R_def Let_def
            by auto 
          then obtain nid where "(nid, CState.v_var cs u, TOP) \<in> set (pools ts u)" by blast
          
          moreover have "pools ?ts'_Fail u = pools ts u" using preserve by simp
          moreover have "CState.v_var cs' u = CState.v_var cs u" using cs'_eq by auto
          ultimately show "\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts'_Fail u)" by metis
        qed

        (* Condition 6. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v. (\<exists>idx < CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ?ts'_Fail q)"
        proof (intro allI impI)
          fix q v
          assume pc_q: "c_program_counter cs' q = ''D3''"
          assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
          
          have q_not_p: "q \<noteq> p" using pc_q cs'_eq by force
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_not_p cs'_eq by auto
          have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using q_not_p cs'_eq by auto
          
          from cond obtain idx where idx_less_old: "idx < CState.j_var cs q" and 
            branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" using j_q_old
            by auto 
          
          have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by auto
          have pools_eq: "pools ?ts'_Fail v = pools ts v" using preserve by simp
          have scan_eq: "t_scanned ?ts'_Fail q = t_scanned ts q" using q_not_p preserve by simp
          
          have old_cond: "(CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT)"
          proof -
            from branch consider (left_c) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail v) \<and> ts_val \<noteq> TOP" 
                             | (right_c) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' v = ''E2''" "CState.i_var cs' v = idx" "idx \<noteq> BOT" by blast
            then show ?thesis
            proof cases
              case left_c
              then show ?thesis using q_arr_eq pools_eq by auto
            next
              case right_c
              have "v \<noteq> p" using right_c(2) cs'_eq by force
              then have "c_program_counter cs v = ''E2''" and "CState.i_var cs v = idx" using right_c cs'_eq by auto
              with right_c(1) right_c(4) q_arr_eq show ?thesis by auto
            qed
          qed
          
          have cond6_rule: "\<And>q_x v_x. c_program_counter cs q_x = ''D3'' \<Longrightarrow> 
            (\<exists>idx_x < CState.j_var cs q_x. 
              (CState.Q_arr cs idx_x \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx_x, ts_val) \<in> set (pools ts v_x) \<and> ts_val \<noteq> TOP)) \<or> 
              (CState.Q_arr cs idx_x = BOT \<and> c_program_counter cs v_x = ''E2'' \<and> CState.i_var cs v_x = idx_x \<and> idx_x \<noteq> BOT)) 
            \<Longrightarrow> v_x \<in> t_scanned ts q_x"
            using sim_r unfolding Simulation_R_def Let_def by simp

          have existential_prems: "\<exists>idx_x < CState.j_var cs q. 
              (CState.Q_arr cs idx_x \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx_x, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
              (CState.Q_arr cs idx_x = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx_x \<and> idx_x \<noteq> BOT)"
            using idx_less_old old_cond by blast

          have "v \<in> t_scanned ts q"
            using cond6_rule[OF pc_q_old existential_prems] .
            
          then show "v \<in> t_scanned ?ts'_Fail q" using scan_eq by simp
        qed

        (* TOP-sensitive branch. *)
        show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts'_Fail q)) = 1"
        proof (intro allI impI)
          fix q assume pc_q: "c_program_counter cs' q = ''E2''"
          have "q \<noteq> p" using pc_q cs'_eq by force
          have old_pc: "c_program_counter cs q = ''E2''" using pc_q `q \<noteq> p` cs'_eq by auto
          have "pools ?ts'_Fail q = pools ts q" using `q \<noteq> p` preserve by simp
          moreover have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
            using sim_r old_pc unfolding Simulation_R_def Let_def by (metis fst_conv)
          ultimately show "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts'_Fail q)) = 1" by simp
        qed

        (* Condition 8. *)
        show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> (\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts'_Fail u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts'_Fail q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts'_Fail u <\<^sub>t\<^sub>s t_startTs ?ts'_Fail q))"
          using sim_r cs'_eq preserve unfolding Simulation_R_def Let_def by auto

        (* Condition 9. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts'_Fail q = BOT \<and> t_candTs ?ts'_Fail q = TOP"
        proof (intro allI impI)
          fix q assume pc_q_new: "c_program_counter cs' q = ''D3''"
          have q_neq_p: "q \<noteq> p" using pc_q_new cs'_eq by force
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p cs'_eq by auto
          
          have old_cand: "t_candNid ts q = BOT \<and> t_candTs ts q = TOP"
            using sim_r pc_q_old unfolding Simulation_R_def Let_def
            by simp
            
          have "t_candNid ts_mid q = t_candNid ts q" using preserve q_neq_p by simp
          moreover have "t_candTs ts_mid q = t_candTs ts q" using preserve q_neq_p by simp
          ultimately show "t_candNid ?ts'_Fail q = BOT \<and> t_candTs ?ts'_Fail q = TOP" 
            using old_cand by simp
        qed

        (* Condition 10. *)
        show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts'_Fail u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
        proof (intro allI impI)
          fix u nid v n
          assume "(nid, v, TS n) \<in> set (pools ?ts'_Fail u)"
          then have in_old_pool: "(nid, v, TS n) \<in> set (pools ts u)" using preserve by simp
          have old_cond: "CState.Q_arr cs nid = v \<and> nid < CState.X_var cs"
            using sim_r in_old_pool unfolding Simulation_R_def Let_def
            by (metis fst_eqD) 
          have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using cs'_eq by simp
          have x_var_eq: "CState.X_var cs' = CState.X_var cs" using cs'_eq by simp
          show "CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
            using old_cond q_arr_eq x_var_eq by simp
        qed

        (* Condition 11: value-range safety of the TSQ pools. *)
        show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<longrightarrow> v \<in> Val"
        proof (intro allI impI)
          fix u nid v_val ts_val
          assume "(nid, v_val, ts_val) \<in> set (pools ?ts'_Fail u)"
          then have "(nid, v_val, ts_val) \<in> set (pools ts u)" using preserve by simp
          then show "v_val \<in> Val" using sim_r unfolding Simulation_R_def Let_def
            by meson 
        qed

        (* Condition 12.1. *)
        show "nid_counter ?ts'_Fail = CState.X_var cs'"
        proof -
          have ghost_eq: "nid_counter ?ts'_Fail = nid_counter ts" using preserve by simp
          have phys_eq: "CState.X_var cs' = CState.X_var cs" using cs'_eq by simp
          have old_cond: "nid_counter ts = CState.X_var cs"
            using sim_r unfolding Simulation_R_def Let_def
            by simp 
          show ?thesis using ghost_eq phys_eq old_cond by simp
        qed

        (* [Condition 12.2] *)
        show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts'_Fail q = CState.i_var cs' q"
          using sim_r cs'_eq preserve unfolding Simulation_R_def Let_def by auto

        (* Condition 13. *)
        show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
              (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts'_Fail q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
        proof (intro allI impI allI allI allI impI)
          fix q u nid v ts_val
          assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
          assume conds: "(nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts'_Fail q) ts_val"
          
          have q_not_p: "q \<noteq> p" using pc_q cs'_eq by force
          
          have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using conds preserve by simp
          have not_top: "ts_val \<noteq> TOP" using conds by simp
          have not_less_old: "\<not> ts_less (t_startTs ts q) ts_val" using conds `q \<noteq> p` preserve by simp
          have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" using pc_q `q \<noteq> p` cs'_eq by auto
          
          have "nid < CState.l_var cs q"
            using sim_r pc_q_old in_old not_top not_less_old unfolding Simulation_R_def Let_def
            by (metis fst_eqD) 
            
          then show "nid < CState.l_var cs' q" using `q \<noteq> p` cs'_eq by simp
        qed

        (* Condition 14. *)
        show "\<forall>q1 q2. c_program_counter cs' q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts'_Fail q2) (t_ts ?ts'_Fail q1) \<longrightarrow> CState.i_var cs' q1 < CState.l_var cs' q2"
        proof (intro allI impI, elim conjE)
          fix q1 q2
          assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
          assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
          assume not_less: "\<not> ts_less (t_startTs ?ts'_Fail q2) (t_ts ?ts'_Fail q1)"
          
          have q1_neq: "q1 \<noteq> p" using pc_q1 cs'_eq by force
          have q2_neq: "q2 \<noteq> p" using pc_q2 cs'_eq by force
          
          have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}" using pc_q1 q1_neq cs'_eq by auto
          have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}" using pc_q2 q2_neq cs'_eq by auto
          have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)" using not_less q1_neq q2_neq preserve by simp
          
          have "CState.i_var cs q1 < CState.l_var cs q2"
            using sim_r pc_q1_old pc_q2_old not_less_old unfolding Simulation_R_def Let_def
            by auto 
            
          then show "CState.i_var cs' q1 < CState.l_var cs' q2" using q1_neq q2_neq cs'_eq by simp
        qed

        (* Condition 15. *)
        show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
        proof (intro allI impI)
          fix u nid v ts_val
          assume pc_u: "c_program_counter cs' u = ''E2''"
          assume cond: "(nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP"
          
          have u_neq_p: "u \<noteq> p" using pc_u cs'_eq by force
          have pc_u_old: "c_program_counter cs u = ''E2''" using pc_u u_neq_p cs'_eq by auto
          have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p cs'_eq by auto
          have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond u_neq_p preserve by simp
          
          have "nid < CState.i_var cs u" using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
            by (metis (lifting) split_pairs2) 
          then show "nid < CState.i_var cs' u" using i_u_eq by simp
        qed

        show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
        proof (intro allI impI)
          fix u nid v ts_val
          assume pc_u: "c_program_counter cs' u = ''E3''"
          assume cond: "(nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP"
          
          have u_neq_p: "u \<noteq> p" using pc_u cs'_eq by force
          have pc_u_old: "c_program_counter cs u = ''E3''" using pc_u u_neq_p cs'_eq by auto
          have i_u_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p cs'_eq by auto
          have in_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond u_neq_p preserve by simp
          
          have "nid \<le> CState.i_var cs u" using sim_r pc_u_old in_old cond unfolding Simulation_R_def Let_def
            by (metis (lifting) fst_conv)
          then show "nid \<le> CState.i_var cs' u" using i_u_eq by simp
        qed

        (* Condition 16: ownership bridge. *)
        show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts'_Fail u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
        proof (intro allI impI, elim conjE)
          fix u nid v ts_val
          assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts'_Fail u)"
          assume not_top: "ts_val \<noteq> TOP"

          have in_old: "(nid, v, ts_val) \<in> set (pools ts u)"
            using in_pool preserve by simp

          have old_his: "\<exists>sn. EnqCallInHis (cs, us) u v sn"
            using sim_r in_old not_top
            unfolding Simulation_R_def Let_def by blast

          then obtain sn where his: "EnqCallInHis (cs, us) u v sn"
            by blast

          have his_new: "EnqCallInHis (cs', us) u v sn"
            using his cs'_eq
            unfolding EnqCallInHis_def his_seq_def by simp

          show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
            using his_new by blast
        qed

        (* Condition 17. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow>
              (\<forall>v. v \<in> t_scanned ?ts'_Fail q \<longrightarrow>
                (\<exists>idx < CState.j_var cs' q.
                  (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
                  (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
        proof (intro allI impI)
          fix q v
          assume pc_q: "c_program_counter cs' q = ''D3''"
          assume v_scan: "v \<in> t_scanned ?ts'_Fail q"

          have q_neq_p: "q \<noteq> p"
            using pc_q cs'_eq by force
          have pc_q_old: "c_program_counter cs q = ''D3''"
            using pc_q q_neq_p cs'_eq by auto
          have j_q_eq: "CState.j_var cs' q = CState.j_var cs q"
            using q_neq_p cs'_eq by auto
          have scan_old: "v \<in> t_scanned ts q"
            using v_scan q_neq_p preserve by simp

          have old_cond17:
            "\<exists>idx < CState.j_var cs q.
              (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
              (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            using sim_r pc_q_old scan_old
            unfolding Simulation_R_def Let_def by simp

          then obtain idx where
            idx_lt: "idx < CState.j_var cs q"
            and branches:
              "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or>
               (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
            by blast

          show "\<exists>idx < CState.j_var cs' q.
                  (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
                  (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
          proof (rule exI[where x=idx], rule conjI)
            show "idx < CState.j_var cs' q"
              using idx_lt j_q_eq by simp
          next
            from branches show
              "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or>
               (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
            proof (elim disjE)
              assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
              have v_neq_p: "v \<noteq> p"
                using b1 `c_program_counter cs p = ''D3''` pc_D3 by force
              thus ?thesis
                using b1 cs'_eq by auto
            next
              assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
              then obtain v_val sn where
                his: "EnqCallInHis (cs, us) v v_val sn"
                and inq: "InQBack (cs, us) v_val"
                and idx_eq: "Idx (cs, us) v_val = idx"
                by blast

              have his_new: "EnqCallInHis (cs', us) v v_val sn"
                using his cs'_eq
                unfolding EnqCallInHis_def his_seq_def by simp

              have inq_new: "InQBack (cs', us) v_val"
              proof -
                from inq obtain k_pos where
                  k_pos_eq: "Qback_arr (cs, us) k_pos = v_val"
                  unfolding InQBack_def by blast
                moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
                  using cs'_eq unfolding Qback_arr_def by simp
                ultimately show ?thesis
                  unfolding InQBack_def by blast
              qed

              have idx_new: "Idx (cs', us) v_val = idx"
              proof -
                have ext_eq: "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
                  using cs'_eq unfolding AtIdx_def Qback_arr_def by simp
                show ?thesis
                  using idx_eq ext_eq unfolding Idx_def by presburger
              qed

              show ?thesis
                using his_new inq_new idx_new by blast
            qed
          qed
        qed

        (* Condition 18. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v \<in> t_scanned ?ts'_Fail q. \<forall>nid v_val ts_val. (nid, v_val, ts_val) \<in> set (pools ?ts'_Fail v) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts'_Fail q))"
        proof (intro allI impI ballI, elim conjE)
          fix q v nid v_val ts_val
          assume pc_q_new: "c_program_counter cs' q = ''D3''"
          assume v_scan: "v \<in> t_scanned ?ts'_Fail q"
          assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts'_Fail v)"
          assume not_top: "ts_val \<noteq> TOP"
          
          have q_neq_p: "q \<noteq> p" using pc_q_new cs'_eq by force
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new q_neq_p cs'_eq by auto
          have j_var_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_eq by simp
          have startTs_eq: "t_startTs ?ts'_Fail q = t_startTs ts q" using q_neq_p preserve by simp
          have in_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" using in_pool preserve by simp
          have v_scan_old: "v \<in> t_scanned ts q" using v_scan q_neq_p preserve by simp
          
          have old_cond18: "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
            using sim_r pc_q_old v_scan_old in_old not_top unfolding Simulation_R_def Let_def by (metis fst_conv)
          show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts'_Fail q)"
            using old_cond18 j_var_eq startTs_eq by simp
        qed

        (* Condition 19. *)
        show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>u \<in> t_scanned ?ts'_Fail q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts'_Fail u) (t_startTs ?ts'_Fail q))"
        proof (intro allI impI ballI)
          fix q u
          assume pc_q: "c_program_counter cs' q = ''D3''"
          assume u_scan: "u \<in> t_scanned ?ts'_Fail q"
          assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
          
          have q_neq_p: "q \<noteq> p" using pc_q cs'_eq by force
          have u_neq_p: "u \<noteq> p" using pc_u_new cs'_eq by force
          
          have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_neq_p cs'_eq by auto
          have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new u_neq_p cs'_eq by auto
          have u_scan_old: "u \<in> t_scanned ts q" using u_scan q_neq_p preserve by simp
          
          have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
            using sim_r pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def by (metis fst_conv)
            
          have j_eq: "CState.j_var cs' q = CState.j_var cs q" using q_neq_p cs'_eq by simp
          have i_eq: "CState.i_var cs' u = CState.i_var cs u" using u_neq_p cs'_eq by simp
          have start_eq: "t_startTs ?ts'_Fail q = t_startTs ts q" using q_neq_p preserve by simp
          have ts_eq: "t_ts ?ts'_Fail u = t_ts ts u" using u_neq_p preserve by simp
          
          show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts'_Fail u) (t_startTs ?ts'_Fail q)"
            using old_cond19 j_eq i_eq start_eq ts_eq by simp
        qed

        (* ========================================================================= *)
        (* NEW *)
        (* ========================================================================= *)
        show "CState.V_var cs' = t_V_var ?ts'_Fail" 
          using sim_r cs'_eq preserve unfolding Simulation_R_def Let_def by auto

        show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts'_Fail q" 
          using sim_r cs'_eq preserve unfolding Simulation_R_def Let_def by (auto split: if_splits)

      qed
      
        have pc_loop: "t_pc ts p = ''TD_Loop''"
          using sim_r pc_D3 unfolding Simulation_R_def Let_def by auto
        
        have scanned_full: "t_scanned ts_mid p = ProcSet"
          using step_EvalFail unfolding T_D3_Eval_def by auto
        
        have "T_D3 p ts ?ts'_Fail"
          unfolding T_D3_def
          using pc_loop step_star scanned_full step_EvalFail
          by blast
      then show ?thesis using sim_R_Fail by blast

    next
      case False
      (* -------------------------------------------------------- *)
      (* Key proof idea. *)
      (* -------------------------------------------------------- *)
      
      have q_upd: "(\<lambda>x. if x = CState.j_var cs p then BOT else CState.Q_arr cs x) = CState.Q_arr cs"
        using `?q_val = BOT` by auto

      have x_upd: "(\<lambda>x. if x = p then CState.Q_arr cs (CState.j_var cs p) else CState.x_var cs x) = (\<lambda>x. if x = p then BOT else CState.x_var cs x)"
        using `?q_val = BOT` by auto

      have cs'_eq: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D3'' else c_program_counter cs x),
                              j_var := (\<lambda>x. if x = p then ?jp + 1 else CState.j_var cs x),
                              x_var := (\<lambda>x. if x = p then BOT else CState.x_var cs x) \<rparr>"
        using `?q_val = BOT` False `C_D3 p cs cs'` q_upd x_upd unfolding C_D3_def Let_def by auto

      (* Proof note. *)
      have jp_less: "CState.j_var cs p < CState.l_var cs p - 1"
      proof -
        have "CState.j_var cs p < CState.l_var cs p" 
          using inv_sys pc_D3 unfolding system_invariant_def sI6_D3_Scan_Pointers_def program_counter_def j_var_def l_var_def by fastforce
        with False show ?thesis by simp
      qed

      (* Proof note. *)
have "\<exists>ts'. T_D3 p ts ts' \<and> Simulation_R (cs', us) ts'"
  using D3_Scan_Empty_Slot_Helper[OF inv_sys inv_tsq sim_r pc_D3 E2_in_ProcSet `?q_val = BOT` jp_less cs'_eq] .
        
      then show ?thesis by blast
    qed

  next
    case False
    (* ========================================================== *)
    (* q_val \<noteq> BOT *)
    (* ========================================================== *)
    
    (* Key proof idea. *)
    have j_upd: "(\<lambda>x. if x = p then CState.j_var cs p else CState.j_var cs x) = CState.j_var cs"
      by (rule ext, simp)
      
    have cs'_eq: "cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D4'' else c_program_counter cs x),
                            Q_arr := (\<lambda>x. if x = ?jp then BOT else CState.Q_arr cs x),
                            j_var := CState.j_var cs,
                            x_var := (\<lambda>x. if x = p then ?q_val else CState.x_var cs x) \<rparr>"
      using False `C_D3 p cs cs'` j_upd unfolding C_D3_def Let_def by auto

    (* Proof note. *)
    have "\<exists>ts'. T_D3 p ts ts' \<and> Simulation_R (cs', us) ts'"
      using D3_Eval_Success_Helper[OF inv_sys inv_tsq sim_r pc_D3 False cs'_eq] .
    then show ?thesis by blast
  qed
qed


(* ========================================================== *)
(* Simulation Step for D4 *)
(* ========================================================== *)
lemma Simulation_R_D4:
  fixes cs :: CState and us :: UState and ts :: TState
  assumes "Simulation_Inv (cs, us) ts"
      and "C_D4 p cs cs'"
  shows "\<exists>ts'. T_D4 p ts ts' \<and> Simulation_R (cs', us) ts'"
proof -
  (* Proof note. *)
  have inv_sys: "system_invariant (cs, us)" 
   and inv_tsq: "TSQ_State_Inv ts" 
   and sim_r: "Simulation_R (cs, us) ts"
    using assms(1) unfolding Simulation_Inv_def by auto

  (* Proof note. *)
  have pc_D4: "c_program_counter cs p = ''D4''" 
    using `C_D4 p cs cs'` unfolding C_D4_def Let_def by auto
    
  have tpc_TD4: "t_pc ts p = ''TD_Remove_Done''"
    using sim_r pc_D4 unfolding Simulation_R_def Let_def by auto

   have step_facts [simp]:
    "c_program_counter cs' p = ''L0''"
    "CState.j_var cs' p = BOT"
    "CState.l_var cs' p = BOT"
    "CState.x_var cs' p = BOT"
    "(\<And>q. q \<noteq> p \<Longrightarrow> c_program_counter cs' q = c_program_counter cs q)"
    "(\<And>q. q \<noteq> p \<Longrightarrow> CState.j_var cs' q = CState.j_var cs q)"
    "(\<And>q. q \<noteq> p \<Longrightarrow> CState.l_var cs' q = CState.l_var cs q)"
    "(\<And>q. q \<noteq> p \<Longrightarrow> CState.x_var cs' q = CState.x_var cs q)"
  proof -
    show "c_program_counter cs' p = ''L0''"
      using assms(2) unfolding C_D4_def Let_def by auto
    show "CState.j_var cs' p = BOT"
      using assms(2) unfolding C_D4_def Let_def by auto
    show "CState.l_var cs' p = BOT"
      using assms(2) unfolding C_D4_def Let_def by auto
    show "CState.x_var cs' p = BOT"
      using assms(2) unfolding C_D4_def Let_def by auto
    fix q assume "q \<noteq> p"
    then show "c_program_counter cs' q = c_program_counter cs q"
      using assms(2) unfolding C_D4_def Let_def by auto
    show "CState.j_var cs' q = CState.j_var cs q"
      using assms(2) `q \<noteq> p` unfolding C_D4_def Let_def by auto
    show "CState.l_var cs' q = CState.l_var cs q"
      using assms(2) `q \<noteq> p` unfolding C_D4_def Let_def by auto
    show "CState.x_var cs' q = CState.x_var cs q"
      using assms(2) `q \<noteq> p` unfolding C_D4_def Let_def by auto
  qed

  (* ========================================================== *)
  (* Proof note. *)
  (* ========================================================== *)
  let ?ts' = "ts\<lparr> 
    t_pc := (\<lambda>x. if x = p then ''TL0'' else t_pc ts x),
    t_startTs := (\<lambda>x. if x = p then TOP else t_startTs ts x),
    t_candNid := (\<lambda>x. if x = p then BOT else t_candNid ts x),
    t_candTs := (\<lambda>x. if x = p then TOP else t_candTs ts x),
    t_candPid := (\<lambda>x. if x = p then BOT else t_candPid ts x),
    t_scanned := (\<lambda>x. if x = p then {} else t_scanned ts x),
    t_retV := (\<lambda>x. if x = p then BOT else t_retV ts x)
  \<rparr>"
  
  (* Proof step. *)
  have step_T: "T_D4 p ts ?ts'"
    using tpc_TD4 unfolding T_D4_def Let_def by simp

  have cs'_eq: "cs' = cs\<lparr> 
    c_program_counter := (\<lambda>x. if x = p then ''L0'' else c_program_counter cs x),
    j_var := (\<lambda>x. if x = p then BOT else CState.j_var cs x),
    l_var := (\<lambda>x. if x = p then BOT else CState.l_var cs x),
    x_var := (\<lambda>x. if x = p then BOT else CState.x_var cs x)
  \<rparr>"
    using assms(2)
    unfolding C_D4_def Let_def
    by auto

  have pc_new_p: "c_program_counter cs' p = ''L0''" using cs'_eq by simp
  have q_arr_eq: "CState.Q_arr cs' = CState.Q_arr cs" using `C_D4 p cs cs'` unfolding C_D4_def Let_def by auto
  have x_var_eq: "CState.X_var cs' = CState.X_var cs" using `C_D4 p cs cs'` unfolding C_D4_def Let_def by auto
  have i_var_eq: "CState.i_var cs' = CState.i_var cs" using `C_D4 p cs cs'` unfolding C_D4_def Let_def by auto
  have v_var_eq: "CState.v_var cs' = CState.v_var cs" using `C_D4 p cs cs'` unfolding C_D4_def Let_def by auto

  (* Key proof idea. *)
  have sim_R_next: "Simulation_R (cs', us) ?ts'"
    unfolding Simulation_R_def Let_def fst_conv snd_conv
  proof (intro conjI)
    (* Condition 2. *)
    show "\<forall>q. c_program_counter cs' q = ''L0'' \<longrightarrow> t_pc ?ts' q = ''TL0''"
    proof (intro allI impI)
      fix q assume "c_program_counter cs' q = ''L0''"
      then show "t_pc ?ts' q = ''TL0''"
        using sim_r `C_D4 p cs cs'` pc_D4 unfolding C_D4_def Let_def Simulation_R_def Let_def
        by (cases "q = p") auto
    qed
    
    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> t_pc ?ts' q = ''TE1''"
      using sim_r cs'_eq pc_D4 unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> t_pc ?ts' q = ''TE2''"
      using sim_r cs'_eq pc_D4 unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''E3'' \<longrightarrow> t_pc ?ts' q = ''TE3''"
      using sim_r cs'_eq pc_D4 unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D1'' \<longrightarrow> t_pc ?ts' q = ''TD1''"
      using sim_r cs'_eq pc_D4 unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D2'' \<longrightarrow> t_pc ?ts' q = ''TD_Line4_Done''"
      using sim_r cs'_eq pc_D4 unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_pc ?ts' q = ''TD_Loop''"
      using sim_r cs'_eq pc_D4 unfolding Simulation_R_def Let_def by auto
    show "\<forall>q. c_program_counter cs' q = ''D4'' \<longrightarrow> t_pc ?ts' q = ''TD_Remove_Done''"
      using sim_r cs'_eq pc_D4 unfolding Simulation_R_def Let_def by auto

    (* Condition 3: validity of timestamps in the TSQ pools. *)
    show "\<forall>q. \<forall>node\<in>set (pools ?ts' q). snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
    proof (intro allI ballI)
      fix q node assume "node \<in> set (pools ?ts' q)"
      then have in_old: "node \<in> set (pools ts q)" by simp
      have old_cond: "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ts q = ''TE2'' \<and> t_nid ts q = fst node"
        using sim_r in_old unfolding Simulation_R_def Let_def by meson 
      show "snd (snd node) \<noteq> TOP \<or> snd (snd node) = TOP \<and> t_pc ?ts' q = ''TE2'' \<and> t_nid ?ts' q = fst node"
      proof (cases "q = p")
        case True
        have "t_pc ts p \<noteq> ''TE2''" using tpc_TD4 by simp
        with old_cond True show ?thesis by simp
      next
        case False
        with old_cond show ?thesis by auto
      qed
    qed

    (* Condition 5.1. *)
show "\<forall>idx. CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<exists>u\<in>ProcSet. \<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP)"
  using sim_r q_arr_eq unfolding Simulation_R_def Let_def by auto
      
    show "\<forall>u idx. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> (\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u))"
    proof (intro allI impI, elim conjE)
      fix u idx
      assume cond: "CState.Q_arr cs' idx = BOT" "c_program_counter cs' u = ''E2''" "CState.i_var cs' u = idx"
      have "u \<noteq> p" using cond(2) pc_new_p by force
      have pc_u_old: "c_program_counter cs u = ''E2''" using cond(2) `u \<noteq> p` cs'_eq by auto
      have "\<exists>nid. (nid, CState.v_var cs u, TOP) \<in> set (pools ts u)"
        using sim_r cond(1) cond(3) pc_u_old q_arr_eq i_var_eq unfolding Simulation_R_def Let_def
        by auto
      then show "\<exists>nid. (nid, CState.v_var cs' u, TOP) \<in> set (pools ?ts' u)"
        using `u \<noteq> p` v_var_eq by simp
    qed

    (* Condition 6. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> 
          (\<forall>v. (\<exists>idx < CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)) \<longrightarrow> v \<in> t_scanned ?ts' q)"
    proof (intro allI impI)
      fix q v
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume cond: "\<exists>idx<CState.j_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)"
      
      have q_not_p: "q \<noteq> p" using pc_q pc_new_p by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q q_not_p cs'_eq by auto
      
      (* Key proof idea. *)
      have j_q_old: "CState.j_var cs q = CState.j_var cs' q" using q_not_p cs'_eq by simp

      from cond obtain idx where idx_less_old: "idx < CState.j_var cs q" and 
        branch: "(CState.Q_arr cs' idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP)) \<or> (CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx \<and> idx \<noteq> BOT)" using j_q_old
        by auto 
        
      have old_cond: "CState.Q_arr cs idx \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP) \<or> CState.Q_arr cs idx = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx \<and> idx \<noteq> BOT"
      proof -
        from branch consider (left_c) "CState.Q_arr cs' idx \<noteq> BOT" "\<exists>nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP" 
                         | (right_c) "CState.Q_arr cs' idx = BOT" "c_program_counter cs' v = ''E2''" "CState.i_var cs' v = idx" "idx \<noteq> BOT" by blast
        then show ?thesis
        proof cases
          case left_c
          then show ?thesis using q_arr_eq by auto
        next
          case right_c
          have "v \<noteq> p" using right_c(2) pc_new_p by force
          then have "c_program_counter cs v = ''E2''" using right_c(2) cs'_eq by auto
          with right_c q_arr_eq i_var_eq show ?thesis by auto
        qed
      qed

      have cond6_rule: "\<And>q_x v_x. c_program_counter cs q_x = ''D3'' \<Longrightarrow> 
        (\<exists>idx_x < CState.j_var cs q_x. 
          (CState.Q_arr cs idx_x \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx_x, ts_val) \<in> set (pools ts v_x) \<and> ts_val \<noteq> TOP)) \<or> 
          (CState.Q_arr cs idx_x = BOT \<and> c_program_counter cs v_x = ''E2'' \<and> CState.i_var cs v_x = idx_x \<and> idx_x \<noteq> BOT)) 
        \<Longrightarrow> v_x \<in> t_scanned ts q_x"
        using sim_r unfolding Simulation_R_def Let_def by simp

      have existential_prems: "\<exists>idx_x < CState.j_var cs q. 
          (CState.Q_arr cs idx_x \<noteq> BOT \<and> (\<exists>nid ts_val. (nid, CState.Q_arr cs idx_x, ts_val) \<in> set (pools ts v) \<and> ts_val \<noteq> TOP)) \<or> 
          (CState.Q_arr cs idx_x = BOT \<and> c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx_x \<and> idx_x \<noteq> BOT)"
        using idx_less_old old_cond by blast

      have "v \<in> t_scanned ts q" using cond6_rule[OF pc_q_old existential_prems] .
      then show "v \<in> t_scanned ?ts' q" using q_not_p by simp
    qed

    (* Condition 7. *)
    show "\<forall>q. c_program_counter cs' q = ''E2'' \<longrightarrow> length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''E2''"
      have "q \<noteq> p" using pc_q pc_new_p by force
      have old_pc: "c_program_counter cs q = ''E2''" using pc_q `q \<noteq> p` cs'_eq by auto
      have "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ts q)) = 1"
        using sim_r old_pc unfolding Simulation_R_def Let_def by (metis fst_conv)
      thus "length (filter (\<lambda>node. snd (snd node) = TOP) (pools ?ts' q)) = 1" using `q \<noteq> p` by simp
    qed

    (* Condition 8. *)
    show "\<forall>q. (c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3'') \<longrightarrow> (\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q))"
    proof (rule allI, rule impI)
      fix q assume pc_q: "c_program_counter cs' q = ''D2'' \<or> c_program_counter cs' q = ''D3''"
      have "q \<noteq> p" using pc_q pc_new_p by force
      have old_pc_q: "c_program_counter cs q = ''D2'' \<or> c_program_counter cs q = ''D3''" using pc_q `q \<noteq> p` cs'_eq by auto
      have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" using `q \<noteq> p` cs'_eq by simp
      have start_eq: "t_startTs ?ts' q = t_startTs ts q" using `q \<noteq> p` by simp
      
      show "\<forall>idx<CState.l_var cs' q. (CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
      proof (rule allI, rule impI)
        fix idx assume idx_less: "idx < CState.l_var cs' q"
        have idx_less_old: "idx < CState.l_var cs q" using idx_less l_q_eq by simp
        
        (* Key proof idea. *)
        have old_cond8: "(CState.Q_arr cs idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ts q)) \<and> 
                         (\<forall>u. CState.Q_arr cs idx = BOT \<and> c_program_counter cs u = ''E2'' \<and> CState.i_var cs u = idx \<longrightarrow> t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q)"
          using sim_r old_pc_q idx_less_old unfolding Simulation_R_def Let_def
          by (metis fst_eqD) 
          
        show "(CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)) \<and> (\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q)"
        proof (rule conjI)
          (* Proof note. *)
          show "CState.Q_arr cs' idx \<noteq> BOT \<longrightarrow> (\<forall>u nid ts_val. (nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q)"
          proof (intro impI allI)
            fix u nid ts_val
            assume q_not_bot: "CState.Q_arr cs' idx \<noteq> BOT"
            assume in_pool: "(nid, CState.Q_arr cs' idx, ts_val) \<in> set (pools ?ts' u)"
            
            have old_q_not_bot: "CState.Q_arr cs idx \<noteq> BOT" using q_not_bot q_arr_eq by simp
            have in_old_pool: "(nid, CState.Q_arr cs idx, ts_val) \<in> set (pools ts u)" using in_pool q_arr_eq by simp
            
            have "ts_val <\<^sub>t\<^sub>s t_startTs ts q" using old_cond8 old_q_not_bot in_old_pool by blast
            then show "ts_val <\<^sub>t\<^sub>s t_startTs ?ts' q" using start_eq by simp
          qed
          
          (* Proof note. *)
          show "\<forall>u. CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx \<longrightarrow> t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q"
          proof (intro allI impI)
            fix u assume cond: "CState.Q_arr cs' idx = BOT \<and> c_program_counter cs' u = ''E2'' \<and> CState.i_var cs' u = idx"
            have "u \<noteq> p" using cond pc_new_p by force
            have pc_u_old: "c_program_counter cs u = ''E2''" using cond `u \<noteq> p` cs'_eq by auto
            have i_u_old: "CState.i_var cs u = idx" using cond `u \<noteq> p` i_var_eq by auto
            have q_bot_old: "CState.Q_arr cs idx = BOT" using cond q_arr_eq by simp
            have ts_u_eq: "t_ts ?ts' u = t_ts ts u" using `u \<noteq> p` by simp
            
            have "t_ts ts u <\<^sub>t\<^sub>s t_startTs ts q" using old_cond8 q_bot_old pc_u_old i_u_old by blast
            thus "t_ts ?ts' u <\<^sub>t\<^sub>s t_startTs ?ts' q" using ts_u_eq start_eq by simp
          qed
        qed
      qed
    qed

    (* Condition 9. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q = ''D3''"
      have "q \<noteq> p" using pc_q pc_new_p by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q `q \<noteq> p` cs'_eq by auto
      have "t_candNid ts q = BOT \<and> t_candTs ts q = TOP" using sim_r pc_q_old unfolding Simulation_R_def Let_def
        by simp
      thus "t_candNid ?ts' q = BOT \<and> t_candTs ?ts' q = TOP" using `q \<noteq> p` by simp
    qed

    (* Condition 10. *)
    show "\<forall>u nid v n. (nid, v, TS n) \<in> set (pools ?ts' u) \<longrightarrow> CState.Q_arr cs' nid = v \<and> nid < CState.X_var cs'"
      using sim_r q_arr_eq x_var_eq unfolding Simulation_R_def Let_def
      by simp 

    (* Condition 11: value-range safety of the TSQ pools. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<longrightarrow> v \<in> Val"
      using sim_r unfolding Simulation_R_def Let_def
      by simp 

    (* Condition 12.1. *)
    show "nid_counter ?ts' = CState.X_var cs'"
      using sim_r x_var_eq unfolding Simulation_R_def Let_def by simp

    (* [Condition 12.2] *)
    show "\<forall>q. c_program_counter cs' q \<in> {''E2'', ''E3''} \<longrightarrow> t_nid ?ts' q = CState.i_var cs' q"
    proof (intro allI impI)
      fix q assume pc_q: "c_program_counter cs' q \<in> {''E2'', ''E3''}"
      have "q \<noteq> p" using pc_q pc_new_p by force
      have pc_q_old: "c_program_counter cs q \<in> {''E2'', ''E3''}" using pc_q `q \<noteq> p` cs'_eq by auto
      have "t_nid ts q = CState.i_var cs q" using sim_r pc_q_old unfolding Simulation_R_def Let_def
        by (metis fst_conv) 
      thus "t_nid ?ts' q = CState.i_var cs' q" using `q \<noteq> p` i_var_eq by simp
    qed

    (* Condition 13. *)
    show "\<forall>q. c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
          (\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val \<longrightarrow> nid < CState.l_var cs' q)"
    proof (intro allI impI allI allI allI impI)
      fix q u nid v ts_val
      assume pc_q: "c_program_counter cs' q \<in> {''D2'', ''D3'', ''D4''}"
      assume conds: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<and> \<not> ts_less (t_startTs ?ts' q) ts_val"
      
      have "q \<noteq> p" using pc_q pc_new_p by force
      have pc_q_old: "c_program_counter cs q \<in> {''D2'', ''D3'', ''D4''}" using pc_q `q \<noteq> p` cs'_eq by auto
      have not_less_old: "\<not> ts_less (t_startTs ts q) ts_val" using conds `q \<noteq> p` by simp
      have in_pool_old: "(nid, v, ts_val) \<in> set (pools ts u)" using conds by simp
      have not_top: "ts_val \<noteq> TOP" using conds by simp

      (* Key proof idea. *)
      have l_q_eq: "CState.l_var cs' q = CState.l_var cs q" using `q \<noteq> p` cs'_eq by simp
      
      (* Key proof idea. *)
      have old_cond13: "\<forall>q_x. c_program_counter cs q_x \<in> {''D2'', ''D3'', ''D4''} \<longrightarrow> 
           (\<forall>u_x nid_x v_x ts_x. (nid_x, v_x, ts_x) \<in> set (pools ts u_x) \<and> ts_x \<noteq> TOP \<and> \<not> ts_less (t_startTs ts q_x) ts_x \<longrightarrow> nid_x < CState.l_var cs q_x)"
        using sim_r unfolding Simulation_R_def Let_def by simp
        
      have "nid < CState.l_var cs q"
        using old_cond13 pc_q_old in_pool_old not_top not_less_old by blast
        
      (* Proof note. *)
      then show "nid < CState.l_var cs' q" using l_q_eq by simp
    qed

    (* Condition 14. *)
    show "\<forall>q1 q2. c_program_counter cs' q1 \<in> {''E2'', ''E3''} \<and> c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''} \<and> \<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1) \<longrightarrow> CState.i_var cs' q1 < CState.l_var cs' q2"
    proof (intro allI impI, elim conjE)
      fix q1 q2
      assume pc_q1: "c_program_counter cs' q1 \<in> {''E2'', ''E3''}"
      assume pc_q2: "c_program_counter cs' q2 \<in> {''D2'', ''D3'', ''D4''}"
      assume not_less: "\<not> ts_less (t_startTs ?ts' q2) (t_ts ?ts' q1)"
      
      have "q1 \<noteq> p" using pc_q1 pc_new_p by force
      have "q2 \<noteq> p" using pc_q2 pc_new_p by force
      
      have pc_q1_old: "c_program_counter cs q1 \<in> {''E2'', ''E3''}" using pc_q1 `q1 \<noteq> p` cs'_eq by auto
      have pc_q2_old: "c_program_counter cs q2 \<in> {''D2'', ''D3'', ''D4''}" using pc_q2 `q2 \<noteq> p` cs'_eq by auto
      have not_less_old: "\<not> ts_less (t_startTs ts q2) (t_ts ts q1)" using not_less `q1 \<noteq> p` `q2 \<noteq> p` by simp
      
      (* Key proof idea. *)
      have l_q2_eq: "CState.l_var cs' q2 = CState.l_var cs q2" using `q2 \<noteq> p` cs'_eq by simp
      
      have "CState.i_var cs q1 < CState.l_var cs q2"
        using sim_r pc_q1_old pc_q2_old not_less_old unfolding Simulation_R_def Let_def
        by auto 
      then show "CState.i_var cs' q1 < CState.l_var cs' q2" using i_var_eq l_q2_eq by simp
    qed

    (* Condition 15. *)
    show "\<forall>u. c_program_counter cs' u = ''E2'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E2''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      have "u \<noteq> p" using pc_u pc_new_p by force
      have pc_u_old: "c_program_counter cs u = ''E2''" using pc_u `u \<noteq> p` `C_D4 p cs cs'` unfolding C_D4_def Let_def by auto
      
      have in_pool_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond by simp
      have not_top: "ts_val \<noteq> TOP" using cond by simp
      
      (* Key proof idea. *)
      have old_cond15_E2: "\<forall>u_x. c_program_counter cs u_x = ''E2'' \<longrightarrow> (\<forall>nid_x v_x ts_x. (nid_x, v_x, ts_x) \<in> set (pools ts u_x) \<and> ts_x \<noteq> TOP \<longrightarrow> nid_x < CState.i_var cs u_x)"
        using sim_r unfolding Simulation_R_def Let_def by simp
        
      have "nid < CState.i_var cs u" using old_cond15_E2 pc_u_old in_pool_old not_top by blast
      then show "nid < CState.i_var cs' u" using i_var_eq by simp
    qed

    show "\<forall>u. c_program_counter cs' u = ''E3'' \<longrightarrow> (\<forall>nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> nid \<le> CState.i_var cs' u)"
    proof (intro allI impI)
      fix u nid v ts_val
      assume pc_u: "c_program_counter cs' u = ''E3''"
      assume cond: "(nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP"
      
      have "u \<noteq> p" using pc_u pc_new_p by force
      have pc_u_old: "c_program_counter cs u = ''E3''" using pc_u `u \<noteq> p` `C_D4 p cs cs'` unfolding C_D4_def Let_def by auto
      
      have in_pool_old: "(nid, v, ts_val) \<in> set (pools ts u)" using cond by simp
      have not_top: "ts_val \<noteq> TOP" using cond by simp
      
      (* Key proof idea. *)
      have old_cond15_E3: "\<forall>u_x. c_program_counter cs u_x = ''E3'' \<longrightarrow> (\<forall>nid_x v_x ts_x. (nid_x, v_x, ts_x) \<in> set (pools ts u_x) \<and> ts_x \<noteq> TOP \<longrightarrow> nid_x \<le> CState.i_var cs u_x)"
        using sim_r unfolding Simulation_R_def Let_def by simp

      have "nid \<le> CState.i_var cs u" using old_cond15_E3 pc_u_old in_pool_old not_top by blast
      then show "nid \<le> CState.i_var cs' u" using i_var_eq by simp
    qed

    (* Condition 16: ownership bridge. *)
    show "\<forall>u nid v ts_val. (nid, v, ts_val) \<in> set (pools ?ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs', us) u v sn)"
    proof (intro allI impI, elim conjE)
      fix u nid v ts_val 
      assume in_pool: "(nid, v, ts_val) \<in> set (pools ?ts' u)" 
      assume not_top: "ts_val \<noteq> TOP"
      
      have in_old_pool: "(nid, v, ts_val) \<in> set (pools ts u)"
        using in_pool by simp
      
      have old_cond16: "\<forall>u_x nid_x v_x ts_x. (nid_x, v_x, ts_x) \<in> set (pools ts u_x) \<and> ts_x \<noteq> TOP \<longrightarrow> (\<exists>sn. EnqCallInHis (cs, us) u_x v_x sn)"
        using sim_r unfolding Simulation_R_def Let_def by simp
        
      have "\<exists>sn. EnqCallInHis (cs, us) u v sn" 
        using old_cond16 in_old_pool not_top by blast
        
      then obtain sn where his_old: "EnqCallInHis (cs, us) u v sn"
        by blast
        
      have his_new: "EnqCallInHis (cs', us) u v sn" 
        using his_old `C_D4 p cs cs'`
        unfolding C_D4_def EnqCallInHis_def his_seq_def by simp
        
      show "\<exists>sn. EnqCallInHis (cs', us) u v sn"
        using his_new by blast
    qed

    (* Condition 17. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v. v \<in> t_scanned ?ts' q \<longrightarrow> (\<exists>idx < CState.j_var cs' q. (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)))"
    proof (intro allI impI)
      fix q v
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume v_scan: "v \<in> t_scanned ?ts' q"

      have q_neq_p: "q \<noteq> p"
        using pc_q pc_new_p by force
      have pc_q_old: "c_program_counter cs q = ''D3''"
        using pc_q q_neq_p cs'_eq by auto
      have scan_old: "v \<in> t_scanned ts q"
        using v_scan q_neq_p by simp
      
      have j_q_old: "CState.j_var cs q = CState.j_var cs' q"
        using q_neq_p cs'_eq by simp
      
      have old_cond17: "\<exists>idx < CState.j_var cs q. (c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        using sim_r pc_q_old scan_old
        unfolding Simulation_R_def Let_def by simp
        
      then obtain idx where
        idx_lt: "idx < CState.j_var cs q"
        and branches: "(c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx) \<or> (\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx)"
        by blast
      
      show "\<exists>idx < CState.j_var cs' q. (c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
      proof (rule exI[where x=idx], rule conjI)
        show "idx < CState.j_var cs' q"
          using idx_lt j_q_old by simp
      next
        from branches show "(c_program_counter cs' v = ''E2'' \<and> CState.i_var cs' v = idx) \<or> (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and> InQBack (cs', us) v_val \<and> Idx (cs', us) v_val = idx)"
        proof (elim disjE)
          assume b1: "c_program_counter cs v = ''E2'' \<and> CState.i_var cs v = idx"
          have v_neq_p: "v \<noteq> p"
            using b1 pc_D4 by force
          have pc_v_new: "c_program_counter cs' v = ''E2''"
            using b1 v_neq_p cs'_eq by auto
          thus ?thesis
            using i_var_eq b1 by auto
        next
          assume b2: "\<exists>v_val sn. EnqCallInHis (cs, us) v v_val sn \<and> InQBack (cs, us) v_val \<and> Idx (cs, us) v_val = idx"
          then obtain v_val sn where
            his: "EnqCallInHis (cs, us) v v_val sn"
            and inq: "InQBack (cs, us) v_val"
            and idx_eq: "Idx (cs, us) v_val = idx"
            by blast

          have his_new: "EnqCallInHis (cs', us) v v_val sn"
            using his cs'_eq
            unfolding EnqCallInHis_def his_seq_def by simp

          have inq_new: "InQBack (cs', us) v_val" 
          proof -
            from inq obtain k_pos where
              k_pos_eq: "Qback_arr (cs, us) k_pos = v_val"
              unfolding InQBack_def by blast
            moreover have "Qback_arr (cs', us) k_pos = Qback_arr (cs, us) k_pos"
              using cs'_eq unfolding Qback_arr_def Let_def by auto
            ultimately show ?thesis
              unfolding InQBack_def by blast
          qed

          have idx_new: "Idx (cs', us) v_val = idx"
          proof -
            have ext_eq: "\<And>k_pos. AtIdx (cs', us) v_val k_pos = AtIdx (cs, us) v_val k_pos"
              using cs'_eq unfolding AtIdx_def Qback_arr_def Let_def by auto
            show ?thesis
              using idx_eq ext_eq unfolding Idx_def by presburger
          qed

          show ?thesis
            using his_new inq_new idx_new by blast
        qed
      qed
    qed

    (* Condition 18. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>v \<in> t_scanned ?ts' q. \<forall>nid v_val ts_val. (nid, v_val, ts_val) \<in> set (pools ?ts' v) \<and> ts_val \<noteq> TOP \<longrightarrow> nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q))"
    proof (intro allI impI ballI, elim conjE)
      fix q v nid v_val ts_val
      assume pc_q_new: "c_program_counter cs' q = ''D3''"
      assume v_scan: "v \<in> t_scanned ?ts' q"
      assume in_pool: "(nid, v_val, ts_val) \<in> set (pools ?ts' v)"
      assume not_top: "ts_val \<noteq> TOP"
      
      have "q \<noteq> p" using pc_q_new pc_new_p by force
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q_new `q \<noteq> p` cs'_eq by auto
      have v_scan_old: "v \<in> t_scanned ts q" using v_scan `q \<noteq> p` by simp
      
      have in_pool_old: "(nid, v_val, ts_val) \<in> set (pools ts v)" using in_pool by simp
      
      (* Key proof idea. *)
      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q" using `q \<noteq> p` cs'_eq by simp
      
      (* Key proof idea. *)
      have old_cond18: "\<forall>q_x. c_program_counter cs q_x = ''D3'' \<longrightarrow> 
        (\<forall>v_x \<in> t_scanned ts q_x. \<forall>nid_x v_val_x ts_val_x. 
          (nid_x, v_val_x, ts_val_x) \<in> set (pools ts v_x) \<and> ts_val_x \<noteq> TOP \<longrightarrow> 
          nid_x < CState.j_var cs q_x \<or> \<not> ts_less ts_val_x (t_startTs ts q_x))"
        using sim_r unfolding Simulation_R_def Let_def
        by (metis fst_eqD)

      have "nid < CState.j_var cs q \<or> \<not> ts_less ts_val (t_startTs ts q)"
        using old_cond18 pc_q_old v_scan_old in_pool_old not_top by blast
        
      (* Proof note. *)
      then show "nid < CState.j_var cs' q \<or> \<not> ts_less ts_val (t_startTs ?ts' q)"
        using j_q_eq `q \<noteq> p` by simp
    qed

    (* Condition 19. *)
    show "\<forall>q. c_program_counter cs' q = ''D3'' \<longrightarrow> (\<forall>u \<in> t_scanned ?ts' q. c_program_counter cs' u \<in> {''E2'', ''E3''} \<longrightarrow> CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q))"
    proof (intro allI impI ballI)
      fix q u
      assume pc_q: "c_program_counter cs' q = ''D3''"
      assume u_scan: "u \<in> t_scanned ?ts' q"
      assume pc_u_new: "c_program_counter cs' u \<in> {''E2'', ''E3''}"
      
      have "q \<noteq> p" using pc_q pc_new_p by force
      have "u \<noteq> p" using pc_u_new pc_new_p by force
      
      have pc_q_old: "c_program_counter cs q = ''D3''" using pc_q `q \<noteq> p` cs'_eq by auto
      have pc_u_old: "c_program_counter cs u \<in> {''E2'', ''E3''}" using pc_u_new `u \<noteq> p` cs'_eq by auto
      have u_scan_old: "u \<in> t_scanned ts q" using u_scan `q \<noteq> p` by simp
      
      (* Key proof idea. *)
      have j_q_eq: "CState.j_var cs' q = CState.j_var cs q" using `q \<noteq> p` cs'_eq by simp
      
      have old_cond19: "CState.i_var cs u < CState.j_var cs q \<or> \<not> ts_less (t_ts ts u) (t_startTs ts q)"
        using sim_r pc_q_old u_scan_old pc_u_old unfolding Simulation_R_def Let_def by (metis fst_conv)
        
      show "CState.i_var cs' u < CState.j_var cs' q \<or> \<not> ts_less (t_ts ?ts' u) (t_startTs ?ts' q)"
        using old_cond19 j_q_eq i_var_eq `q \<noteq> p` `u \<noteq> p` by simp
    qed

    (* ========================================================================= *)
    (* NEW *)
    (* ========================================================================= *)
    show "CState.V_var cs' = t_V_var ?ts'" 
      using sim_r cs'_eq unfolding Simulation_R_def Let_def by simp

    show "\<forall>q. c_program_counter cs' q = ''E1'' \<longrightarrow> CState.v_var cs' q = t_v ?ts' q" 
      using sim_r cs'_eq unfolding Simulation_R_def Let_def by (auto split: if_splits)
  qed
  
  then show ?thesis using step_T by blast
qed

(* ========================================================== *)
(* Global Step Simulation Theorem *)
(* ========================================================== *)
theorem Global_Simulation_Step:
  fixes s s' :: SysState and ts :: TState
  assumes sim_inv: "Simulation_Inv s ts"
      and next_step: "Next s s'"
      and E2_in_ProcSet_s: "\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet"
  shows "\<exists>ts'. T_Next ts ts' \<and> Simulation_R s' ts'"
proof -
  (* Proof note. *)
  from assms(2) obtain p where p_in: "p \<in> ProcSet" and
    sys_step: "Sys_L0 p s s' \<or> Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_E3 p s s' \<or>
               Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s' \<or> Sys_D4 p s s'"
    unfolding Next_def by blast

  (* Proof note. *)
  from sys_step show ?thesis
  proof (elim disjE)
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
    assume step: "Sys_L0 p s s'"
    (* Proof note. *)
    have "c_program_counter (fst s') p = ''E1'' \<or> c_program_counter (fst s') p = ''D1''"
      using step unfolding Sys_L0_def C_L0_def Let_def by (auto split: if_splits)
    thus ?thesis
    proof (elim disjE)
      assume "c_program_counter (fst s') p = ''E1''"
      with assms(1) step Simulation_R_L0_Enq obtain ts' where "T_Call_Enq p ts ts' \<and> Simulation_R s' ts'" by blast
      thus ?thesis using p_in unfolding T_Next_def by blast
    next
      assume "c_program_counter (fst s') p = ''D1''"
      with assms(1) step Simulation_R_L0_Deq obtain ts' where "T_Call_Deq p ts ts' \<and> Simulation_R s' ts'" by blast
      thus ?thesis using p_in unfolding T_Next_def by blast
    qed

   next
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
    assume step: "Sys_E1 p s s'"
    
    (* Proof step. *)
    obtain cs us where s_eq: "s = (cs, us)" by (cases s)
    obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
    
    (* Proof step. *)
    have inv: "Simulation_Inv (cs, us) ts" using assms(1) s_eq by simp
    have c_step: "C_E1 p cs cs'" using step s_eq s'_eq unfolding Sys_E1_def by auto
    have v_eq: "CState.v_var cs p = t_v ts p" 
      using assms(1) s_eq step
      unfolding Simulation_Inv_def Simulation_R_def Let_def Sys_E1_def C_E1_def
      by auto
      
    (* Proof step. *)
    from Simulation_R_E1[OF inv c_step v_eq] obtain ts' where 
      t_step: "T_E1 p ts ts'" and sim_mid: "Simulation_R (cs', us) ts'" by blast
      
       (* Proof step. *)
    have us'_eq_upd: "us' = us\<lparr> 
      u_program_counter := (\<lambda>x. if x = p then ''UE3'' else u_program_counter us x),
      u_lin_seq := u_lin_seq us @ [mk_op enq (CState.v_var cs p) p (s_var (cs, us) p)] \<rparr>"
    proof -
      have us'_raw:
        "us' = us\<lparr> 
          u_program_counter := (\<lambda>x. if x = p then ''UE3'' else u_program_counter (snd (cs, us)) x),
          u_lin_seq := u_lin_seq us @ [mk_op enq (CState.v_var cs p) p (s_var (cs, us) p)] \<rparr>"
        using step s_eq s'_eq
        unfolding Sys_E1_def U_E2_def
        by (auto simp: s_var_def)

      have pc_fun_eq:
        "(\<lambda>x. if x = p then ''UE3'' else u_program_counter (snd (cs, us)) x) =
         (\<lambda>x. if x = p then ''UE3'' else u_program_counter us x)"
      proof
        fix x
        show "(if x = p then ''UE3'' else u_program_counter (snd (cs, us)) x) =
              (if x = p then ''UE3'' else u_program_counter us x)"
          by simp
      qed

      from us'_raw show ?thesis
        using pc_fun_eq
        by simp
    qed

       (* Proof note. *)
    have "Simulation_R s' ts'" 
    proof -
      have us'_eq_upd: "us' = us\<lparr> 
        u_program_counter := (\<lambda>x. if x = p then ''UE3'' else u_program_counter us x),
        u_lin_seq := u_lin_seq us @ [mk_op enq (CState.v_var cs p) p (s_var (cs, us) p)] \<rparr>"
      proof -
        have us'_raw:
          "us' = us\<lparr> 
            u_program_counter := (\<lambda>x. if x = p then ''UE3'' else u_program_counter (snd (cs, us)) x),
            u_lin_seq := u_lin_seq us @ [mk_op enq (CState.v_var cs p) p (s_var (cs, us) p)] \<rparr>"
          using step s_eq s'_eq
          unfolding Sys_E1_def U_E2_def
          by (auto simp: s_var_def)

        have pc_fun_eq:
          "(\<lambda>x. if x = p then ''UE3'' else u_program_counter (snd (cs, us)) x) =
           (\<lambda>x. if x = p then ''UE3'' else u_program_counter us x)"
        proof
          fix x
          show "(if x = p then ''UE3'' else u_program_counter (snd (cs, us)) x) =
                (if x = p then ''UE3'' else u_program_counter us x)"
            by simp
        qed

        from us'_raw show ?thesis
          using pc_fun_eq
          by simp
      qed
        
      have sim_eq:
        "Simulation_R (cs', us') ts' = Simulation_R (cs', us) ts'"
        unfolding Simulation_R_def Let_def EnqCallInHis_def his_seq_def InQBack_def Idx_def AtIdx_def Model.Qback_arr_def s_var_def
        using us'_eq_upd
        by simp
        
      thus ?thesis
        using sim_mid s'_eq
        by simp
    qed
    thus ?thesis
      using t_step p_in
      unfolding T_Next_def
      by blast

  next
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
    assume step: "Sys_E2 p s s'"
    obtain cs us where s_eq: "s = (cs, us)" by (cases s)
    obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
    
    have inv: "Simulation_Inv (cs, us) ts" using assms(1) s_eq by simp
    have c_step: "C_E2 p cs cs'" using step s_eq s'_eq unfolding Sys_E2_def by auto
    
    (* Proof note. *)
    have ts_not_top: "t_ts ts p \<noteq> TOP" 
    proof -
      (* Proof step. *)
      have "t_pc ts p = ''TE2''" 
        using inv c_step unfolding Simulation_Inv_def Simulation_R_def Let_def C_E2_def by auto
      
      (* Proof step. *)
      moreover have "TSQ_State_Inv ts" 
        using inv unfolding Simulation_Inv_def by simp
        
      (* Proof step. *)
      ultimately show ?thesis 
        unfolding TSQ_State_Inv_def by auto
    qed
      
    from Simulation_R_E2[OF inv c_step ts_not_top p_in] obtain ts' where 
      t_step: "T_E2 p ts ts'" and sim_mid: "Simulation_R (cs', us) ts'" by blast
      
    (* Proof step. *)
    have "Simulation_R s' ts'" 
    proof -
      have "us' = us"
        using step s_eq s'_eq unfolding Sys_E2_def by auto
      thus ?thesis using sim_mid s'_eq by simp
    qed
    thus ?thesis using t_step p_in unfolding T_Next_def by blast

  next
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
    assume step: "Sys_E3 p s s'"
    obtain cs us where s_eq: "s = (cs, us)" by (cases s)
    obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
    
    have inv: "Simulation_Inv (cs, us) ts" using assms(1) s_eq by simp
    have c_step: "C_E3 p cs cs'" using step s_eq s'_eq unfolding Sys_E3_def by auto

     (* Proof note. *)
    from step s_eq s'_eq have "\<exists>us_mid. U_E3 p (CState.v_var cs p) (s_var (cs, us) p) us us_mid \<and> U_E4 p us_mid us'"
      unfolding Sys_E3_def
      by (auto simp: s_var_def)
    then obtain us_mid where 
      u3: "U_E3 p (CState.v_var cs p) (s_var (cs, us) p) us us_mid" and 
      u4: "U_E4 p us_mid us'"
      by blast

    (* Proof step. *)
    from Simulation_R_E3[OF inv c_step] obtain ts' where 
      t_step: "T_E3 p ts ts'" and sim_mid: "Simulation_R (cs', us) ts'" by blast
      
    (* Proof step. *)
    have us'_eq_upd: "us' = us\<lparr> 
        u_program_counter := (\<lambda>x. if x = p then ''UL0'' else u_program_counter us x),
        u_his_seq := u_his_seq us @ [mk_act enq (CState.v_var cs p) p (s_var (cs, us) p) ret],
        S_var := (\<lambda>x. if x = p then s_var (cs, us) p + 1 else S_var us x) \<rparr>"
    proof -
      let ?v = "CState.v_var cs p"

      have us_mid_eq: "us_mid = us\<lparr> 
          u_program_counter := (\<lambda>x. if x = p then ''UE4'' else u_program_counter us x),
          u_his_seq := u_his_seq us @ [mk_act enq ?v p (s_var (cs, us) p) ret] \<rparr>"
        using u3
        unfolding U_E3_def
        by (simp add: fun_eq_iff s_var_def split: if_splits)

      have us'_eq: "us' = us_mid\<lparr> 
          u_program_counter := (\<lambda>x. if x = p then ''UL0'' else u_program_counter us_mid x),
          S_var := (\<lambda>x. if x = p then S_var us_mid p + 1 else S_var us_mid x) \<rparr>"
        using u4
        unfolding U_E4_def
        by (simp add: fun_eq_iff split: if_splits)

      from us'_eq us_mid_eq show ?thesis
        by (simp add: fun_eq_iff s_var_def)
    qed

    (* Simulation_R s' ts' *)
    have "Simulation_R s' ts'"
    proof -
      have his_grow:
        "u_his_seq us' = u_his_seq us @ [mk_act enq (CState.v_var cs p) p (s_var (cs, us) p) ret]"
        using us'_eq_upd by simp

      have preserve_his:
        "\<And>u v sn. EnqCallInHis (cs', us) u v sn \<Longrightarrow> EnqCallInHis (cs', us') u v sn"
      proof -
        fix u v sn
        assume h: "EnqCallInHis (cs', us) u v sn"
        then obtain e where
          e_in: "e \<in> set (u_his_seq us)" and
          e_pid: "act_pid e = u" and
          e_ssn: "act_ssn e = sn" and
          e_oper: "act_name e = enq" and
          e_cr: "act_cr e = call" and
          e_val: "act_val e = v"
          unfolding EnqCallInHis_def his_seq_def
          by auto
        have "e \<in> set (u_his_seq us')"
          using e_in his_grow by auto
        then show "EnqCallInHis (cs', us') u v sn"
          unfolding EnqCallInHis_def his_seq_def
          using e_pid e_ssn e_oper e_cr e_val
          by auto
      qed

  have cond16_new:
    "\<forall>u nid v ts_val.
       (nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow>
       (\<exists>sn. EnqCallInHis (cs', us') u v sn)"
  proof (intro allI impI)
    fix u nid v ts_val
    assume h: "(nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP"

    have old_his_ex: "Ex (EnqCallInHis (cs', us) u v)"
      using sim_mid h
      unfolding Simulation_R_def Let_def
      by blast

    then obtain sn where
      old_his: "EnqCallInHis (cs', us) u v sn"
      by blast

    have new_his: "EnqCallInHis (cs', us') u v sn"
      using old_his preserve_his by blast

    show "\<exists>sn. EnqCallInHis (cs', us') u v sn"
      using new_his by blast
  qed

  have cond17_new:
    "\<forall>q. c_program_counter (fst (cs', us')) q = ''D3'' \<longrightarrow>
      (\<forall>v. v \<in> t_scanned ts' q \<longrightarrow>
        (\<exists>idx < CState.j_var (fst (cs', us')) q.
          (c_program_counter (fst (cs', us')) v = ''E2'' \<and> CState.i_var (fst (cs', us')) v = idx) \<or>
          (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and>
                   InQBack (fst (cs', us'), snd (cs', us')) v_val \<and>
                   Idx (fst (cs', us'), snd (cs', us')) v_val = idx)))"
  proof (intro allI impI)
    fix q v
    assume q_pc: "c_program_counter (fst (cs', us')) q = ''D3''"
    assume v_scan: "v \<in> t_scanned ts' q"

    have q_pc_old: "c_program_counter (fst (cs', us)) q = ''D3''"
      using q_pc by simp

    have q_pc_old: "c_program_counter (fst (cs', us)) q = ''D3''"
      using q_pc by simp

    have scan_rule:
      "\<forall>q. c_program_counter (fst (fst (cs', us), snd (cs', us))) q = ''D3'' \<longrightarrow>
         (\<forall>v. v \<in> t_scanned ts' q \<longrightarrow>
           (\<exists>idx<CState.j_var (fst (fst (cs', us), snd (cs', us))) q.
              (c_program_counter (fst (fst (cs', us), snd (cs', us))) v = ''E2'' \<and>
               CState.i_var (fst (fst (cs', us), snd (cs', us))) v = idx) \<or>
              (\<exists>v_val sn. EnqCallInHis (fst (cs', us), snd (cs', us)) v v_val sn \<and>
                       InQBack (fst (fst (cs', us), snd (cs', us)), snd (fst (cs', us), snd (cs', us))) v_val \<and>
                       Idx (fst (fst (cs', us), snd (cs', us)), snd (fst (cs', us), snd (cs', us))) v_val = idx)))"
      using sim_mid
      unfolding Simulation_R_def Let_def
      by auto

    have old_scan_ex:
      "\<exists>idx < CState.j_var (fst (cs', us)) q.
         (c_program_counter (fst (cs', us)) v = ''E2'' \<and> CState.i_var (fst (cs', us)) v = idx) \<or>
         (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and>
                  InQBack (fst (cs', us), snd (cs', us)) v_val \<and>
                  Idx (fst (cs', us), snd (cs', us)) v_val = idx)"
      using scan_rule q_pc_old v_scan
      by simp

    then obtain idx where
      idx_lt: "idx < CState.j_var (fst (cs', us)) q" and
      old_cases:
        "(c_program_counter (fst (cs', us)) v = ''E2'' \<and> CState.i_var (fst (cs', us)) v = idx) \<or>
         (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and>
                  InQBack (fst (cs', us), snd (cs', us)) v_val \<and>
                  Idx (fst (cs', us), snd (cs', us)) v_val = idx)"
      by blast

    show "\<exists>idx < CState.j_var (fst (cs', us')) q.
            (c_program_counter (fst (cs', us')) v = ''E2'' \<and> CState.i_var (fst (cs', us')) v = idx) \<or>
            (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and>
                     InQBack (fst (cs', us'), snd (cs', us')) v_val \<and>
                     Idx (fst (cs', us'), snd (cs', us')) v_val = idx)"
    proof (rule exI[where x = idx], intro conjI)
      show "idx < CState.j_var (fst (cs', us')) q"
        using idx_lt by simp
    next
      from old_cases show
        "(c_program_counter (fst (cs', us')) v = ''E2'' \<and> CState.i_var (fst (cs', us')) v = idx) \<or>
         (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and>
                  InQBack (fst (cs', us'), snd (cs', us')) v_val \<and>
                  Idx (fst (cs', us'), snd (cs', us')) v_val = idx)"
      proof
        assume h1: "c_program_counter (fst (cs', us)) v = ''E2'' \<and> CState.i_var (fst (cs', us)) v = idx"
        thus ?thesis by simp
      next
        assume h2: "\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and>
                             InQBack (fst (cs', us), snd (cs', us)) v_val \<and>
                             Idx (fst (cs', us), snd (cs', us)) v_val = idx"
        then obtain v_val sn where
          h_his: "EnqCallInHis (cs', us) v v_val sn" and
          h_inq: "InQBack (fst (cs', us), snd (cs', us)) v_val" and
          h_idx: "Idx (fst (cs', us), snd (cs', us)) v_val = idx"
          by blast

        have h_his': "EnqCallInHis (cs', us') v v_val sn"
          using h_his preserve_his by blast

        have h_inq': "InQBack (fst (cs', us'), snd (cs', us')) v_val"
          using h_inq
          unfolding InQBack_def Qback_arr_def
          by simp

        have h_idx': "Idx (fst (cs', us'), snd (cs', us')) v_val = idx"
          using h_idx
          unfolding Idx_def AtIdx_def Qback_arr_def
          by simp

        show ?thesis
          using h_his' h_inq' h_idx' by blast
      qed
    qed
  qed

  have sim_new: "Simulation_R (cs', us') ts'"
    using sim_mid cond16_new cond17_new
    unfolding Simulation_R_def Let_def
    apply simp
    by blast

  thus ?thesis
    using s'_eq by simp
qed


thus ?thesis
  using t_step p_in unfolding T_Next_def by blast

  next
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
    assume step: "Sys_D1 p s s'"
    obtain cs us where s_eq: "s = (cs, us)" by (cases s)
    obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
    
    have inv: "Simulation_Inv (cs, us) ts" using assms(1) s_eq by simp
    have c_step: "C_D1 p cs cs'" using step s_eq s'_eq unfolding Sys_D1_def by auto
    
    from Simulation_R_D1[OF inv c_step] obtain ts' where 
      t_step: "T_D1 p ts ts'" and sim_mid: "Simulation_R (cs', us) ts'" by blast
      
    have "Simulation_R s' ts'" 
    proof -
      have "us' = us"
        using step s_eq s'_eq unfolding Sys_D1_def by auto
      thus ?thesis 
        using sim_mid s'_eq by simp
    qed
    
    thus ?thesis using t_step p_in unfolding T_Next_def by blast

  next
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
    assume step: "Sys_D2 p s s'"
    obtain cs us where s_eq: "s = (cs, us)" by (cases s)
    obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
    
    have inv: "Simulation_Inv (cs, us) ts" using assms(1) s_eq by simp
    have c_step: "C_D2 p cs cs'" using step s_eq s'_eq unfolding Sys_D2_def by auto
    
    from Simulation_R_D2[OF inv c_step] obtain ts' where 
      t_step: "T_D2 p ts ts'" and sim_mid: "Simulation_R (cs', us) ts'" by blast
      
    have "Simulation_R s' ts'" 
    proof -
      have us'_eq_upd: "us' = us"
        using step s_eq s'_eq unfolding Sys_D2_def by auto
      thus ?thesis using sim_mid s'_eq by simp
    qed
    thus ?thesis using t_step p_in unfolding T_Next_def by blast

  next
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
    assume step: "Sys_D3 p s s'"
    obtain cs us where s_eq: "s = (cs, us)" by (cases s)
    obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
    
have inv: "Simulation_Inv (cs, us) ts" using assms(1) s_eq by simp
have c_step: "C_D3 p cs cs'" using step s_eq s'_eq unfolding Sys_D3_def by auto
have E2_in_ProcSet_cs: "\<forall>q. c_program_counter cs q = ''E2'' \<longrightarrow> q \<in> ProcSet"
  using assms(3) s_eq by simp

from Simulation_R_D3[OF inv c_step E2_in_ProcSet_cs] obtain ts' where 
  t_step: "T_D3 p ts ts'" and sim_mid: "Simulation_R (cs', us) ts'" by blast
      
    have "Simulation_R s' ts'" 
    proof -
      have his_eq: "his_seq (cs', us') = his_seq (cs', us)"
      proof (cases "CState.Q_arr cs (CState.j_var cs p) = BOT")
        case True
        from step s_eq s'_eq have "snd s' = snd s"
          unfolding Sys_D3_def Let_def
          using True
          by auto
        hence "us' = us"
          using s_eq s'_eq by simp
        thus ?thesis
          unfolding his_seq_def by simp
           next
        case False
        from step s_eq s'_eq have u2_step:
          "U_D2 p (CState.Q_arr cs (CState.j_var cs p)) (s_var (cs, us) p) us us'"
          unfolding Sys_D3_def Let_def
          using False
          by (auto simp: s_var_def)

        have "u_his_seq us' = u_his_seq us"
          using u2_step
          unfolding U_D2_def Let_def
          by auto
        thus ?thesis
          unfolding his_seq_def by simp
      qed

      have enq_eq: "\<And>u v sn. EnqCallInHis (cs', us') u v sn = EnqCallInHis (cs', us) u v sn"
        unfolding EnqCallInHis_def using his_eq by simp
      have enq_eq: "\<And>u v. EnqCallInHis (cs', us') u v = EnqCallInHis (cs', us) u v"
        unfolding EnqCallInHis_def using his_eq by simp

      have qback_eq: "\<And>k. Model.Qback_arr (cs', us') k = Model.Qback_arr (cs', us) k"
        unfolding Model.Qback_arr_def by simp

      show ?thesis
        using sim_mid unfolding s'_eq Simulation_R_def Let_def InQBack_def Idx_def AtIdx_def
        apply (simp add: his_eq enq_eq qback_eq)
        by blast
    qed
    thus ?thesis using t_step p_in unfolding T_Next_def by blast

    next
    (* ====================================================== *)
    (* Proof note. *)
    (* ====================================================== *)
       assume step: "Sys_D4 p s s'"
    obtain cs us where s_eq: "s = (cs, us)" by (cases s)
    obtain cs' us' where s'_eq: "s' = (cs', us')" by (cases s')
    
    have inv: "Simulation_Inv (cs, us) ts" using assms(1) s_eq by simp
    have c_step: "C_D4 p cs cs'" using step s_eq s'_eq unfolding Sys_D4_def by auto

    from step s_eq s'_eq obtain us_mid where 
      u3: "U_D3 p (CState.x_var cs p) (s_var (cs, us) p) us us_mid" and 
      u4: "U_D4 p us_mid us'"
      unfolding Sys_D4_def by (auto simp: s_var_def)

    from Simulation_R_D4[OF inv c_step] obtain ts' where 
      t_step: "T_D4 p ts ts'" and sim_mid: "Simulation_R (cs', us) ts'" by blast
      
    have us'_eq_upd: "us' = us\<lparr> 
        u_program_counter := (\<lambda>x. if x = p then ''UL0'' else u_program_counter us x),
        u_his_seq := u_his_seq us @ [mk_act deq (CState.x_var cs p) p (s_var (cs, us) p) ret],
        S_var := (\<lambda>x. if x = p then s_var (cs, us) p + 1 else S_var us x) \<rparr>"
    proof -
      have us_mid_eq: "us_mid = us\<lparr> 
          u_program_counter := (\<lambda>x. if x = p then ''UD4'' else u_program_counter us x),
          u_his_seq := u_his_seq us @ [mk_act deq (CState.x_var cs p) p (s_var (cs, us) p) ret] \<rparr>"
        using u3
        unfolding U_D3_def
        by (simp add: fun_eq_iff s_var_def split: if_splits)

      have us'_eq: "us' = us_mid\<lparr> 
          u_program_counter := (\<lambda>x. if x = p then ''UL0'' else u_program_counter us_mid x),
          S_var := (\<lambda>x. if x = p then S_var us_mid p + 1 else S_var us_mid x) \<rparr>"
        using u4
        unfolding U_D4_def
        by (simp add: fun_eq_iff split: if_splits)

      have pc_mid_neq: "\<And>x. x \<noteq> p \<Longrightarrow> u_program_counter us_mid x = u_program_counter us x"
        using us_mid_eq by simp

      show ?thesis
        using us'_eq us_mid_eq pc_mid_neq
        by (simp add: fun_eq_iff s_var_def)
    qed

    have "Simulation_R s' ts'"
    proof -
      have his_grow:
        "u_his_seq us' = u_his_seq us @ [mk_act deq (CState.x_var cs p) p (s_var (cs, us) p) ret]"
        using us'_eq_upd by simp

      have enq_eq:
        "\<And>u v sn. EnqCallInHis (cs', us') u v sn = EnqCallInHis (cs', us) u v sn"
      proof -
        fix u v sn
        have deq_not_enq:
          "act_name (mk_act deq (CState.x_var cs p) p (s_var (cs, us) p) ret) \<noteq> enq"
          by (simp add: mk_act_def act_name_def)
        show "EnqCallInHis (cs', us') u v sn = EnqCallInHis (cs', us) u v sn"
          unfolding EnqCallInHis_def his_seq_def
          using his_grow deq_not_enq
          by auto
      qed

      have qback_eq:
        "\<And>k. Model.Qback_arr (cs', us') k = Model.Qback_arr (cs', us) k"
        unfolding Model.Qback_arr_def
        by simp

      have idx_eq:
        "\<And>v_val. Idx (cs', us') v_val = Idx (cs', us) v_val"
        unfolding Idx_def AtIdx_def
        using qback_eq
        by simp

      have cond16_new:
        "\<forall>u nid v ts_val.
           (nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP \<longrightarrow>
           (\<exists>sn. EnqCallInHis (cs', us') u v sn)"
      proof (intro allI impI)
        fix u nid v ts_val
        assume h: "(nid, v, ts_val) \<in> set (pools ts' u) \<and> ts_val \<noteq> TOP"
        have old_his_ex: "Ex (EnqCallInHis (cs', us) u v)"
          using sim_mid h
          unfolding Simulation_R_def Let_def
          by blast
        then show "\<exists>sn. EnqCallInHis (cs', us') u v sn"
          using enq_eq by blast
      qed

      have cond17_new:
        "\<forall>q. c_program_counter (fst (cs', us')) q = ''D3'' \<longrightarrow>
          (\<forall>v. v \<in> t_scanned ts' q \<longrightarrow>
            (\<exists>idx < CState.j_var (fst (cs', us')) q.
              (c_program_counter (fst (cs', us')) v = ''E2'' \<and> CState.i_var (fst (cs', us')) v = idx) \<or>
              (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and>
                       InQBack (fst (cs', us'), snd (cs', us')) v_val \<and>
                       Idx (fst (cs', us'), snd (cs', us')) v_val = idx)))"
      proof (intro allI impI)
        fix q v
        assume q_pc: "c_program_counter (fst (cs', us')) q = ''D3''"
        assume v_scan: "v \<in> t_scanned ts' q"

        have q_pc_old: "c_program_counter (fst (cs', us)) q = ''D3''"
          using q_pc by simp

        have scan_rule:
          "\<forall>q. c_program_counter (fst (fst (cs', us), snd (cs', us))) q = ''D3'' \<longrightarrow>
             (\<forall>v. v \<in> t_scanned ts' q \<longrightarrow>
               (\<exists>idx<CState.j_var (fst (fst (cs', us), snd (cs', us))) q.
                  (c_program_counter (fst (fst (cs', us), snd (cs', us))) v = ''E2'' \<and>
                   CState.i_var (fst (fst (cs', us), snd (cs', us))) v = idx) \<or>
                  (\<exists>v_val sn. EnqCallInHis (fst (cs', us), snd (cs', us)) v v_val sn \<and>
                           InQBack (fst (fst (cs', us), snd (cs', us)), snd (fst (cs', us), snd (cs', us))) v_val \<and>
                           Idx (fst (fst (cs', us), snd (cs', us)), snd (fst (cs', us), snd (cs', us))) v_val = idx)))"
          using sim_mid
          unfolding Simulation_R_def Let_def
          by auto

        have old_scan_ex:
          "\<exists>idx < CState.j_var (fst (cs', us)) q.
             (c_program_counter (fst (cs', us)) v = ''E2'' \<and> CState.i_var (fst (cs', us)) v = idx) \<or>
             (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and>
                      InQBack (fst (cs', us), snd (cs', us)) v_val \<and>
                      Idx (fst (cs', us), snd (cs', us)) v_val = idx)"
          using scan_rule q_pc_old v_scan
          by simp

        then obtain idx where
          idx_lt: "idx < CState.j_var (fst (cs', us)) q" and
          old_cases:
            "(c_program_counter (fst (cs', us)) v = ''E2'' \<and> CState.i_var (fst (cs', us)) v = idx) \<or>
             (\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and>
                      InQBack (fst (cs', us), snd (cs', us)) v_val \<and>
                      Idx (fst (cs', us), snd (cs', us)) v_val = idx)"
          by blast

        show "\<exists>idx < CState.j_var (fst (cs', us')) q.
                (c_program_counter (fst (cs', us')) v = ''E2'' \<and> CState.i_var (fst (cs', us')) v = idx) \<or>
                (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and>
                         InQBack (fst (cs', us'), snd (cs', us')) v_val \<and>
                         Idx (fst (cs', us'), snd (cs', us')) v_val = idx)"
        proof (rule exI[where x = idx], intro conjI)
          show "idx < CState.j_var (fst (cs', us')) q"
            using idx_lt by simp
        next
          from old_cases show
            "(c_program_counter (fst (cs', us')) v = ''E2'' \<and> CState.i_var (fst (cs', us')) v = idx) \<or>
             (\<exists>v_val sn. EnqCallInHis (cs', us') v v_val sn \<and>
                      InQBack (fst (cs', us'), snd (cs', us')) v_val \<and>
                      Idx (fst (cs', us'), snd (cs', us')) v_val = idx)"
          proof
            assume h1: "c_program_counter (fst (cs', us)) v = ''E2'' \<and> CState.i_var (fst (cs', us)) v = idx"
            thus ?thesis by simp
          next
            assume h2: "\<exists>v_val sn. EnqCallInHis (cs', us) v v_val sn \<and>
                                 InQBack (fst (cs', us), snd (cs', us)) v_val \<and>
                                 Idx (fst (cs', us), snd (cs', us)) v_val = idx"
            then obtain v_val sn where
              h_his: "EnqCallInHis (cs', us) v v_val sn" and
              h_inq: "InQBack (fst (cs', us), snd (cs', us)) v_val" and
              h_idx: "Idx (fst (cs', us), snd (cs', us)) v_val = idx"
              by blast

            have h_his': "EnqCallInHis (cs', us') v v_val sn"
              using h_his enq_eq by simp

            have h_inq': "InQBack (fst (cs', us'), snd (cs', us')) v_val"
              using h_inq
              unfolding InQBack_def Qback_arr_def
              by simp

            have h_idx': "Idx (fst (cs', us'), snd (cs', us')) v_val = idx"
              using h_idx idx_eq by simp

            show ?thesis
              using h_his' h_inq' h_idx' by blast
          qed
        qed
      qed

      have sim_new: "Simulation_R (cs', us') ts'"
        using sim_mid cond16_new cond17_new
        unfolding Simulation_R_def Let_def
        apply simp
        by blast

      show ?thesis
        using sim_new
        unfolding s'_eq
        by simp
    qed
    thus ?thesis using t_step p_in unfolding T_Next_def by blast
qed
qed

end