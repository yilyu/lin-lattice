theory TraceProof
  imports TraceInv
begin

(* ========================================================== *)
(* Global simulation construction for initial states            *)
(* ========================================================== *)
theorem Global_Simulation_Init:
  assumes "Init s"
  shows "\<exists>ts. T_Init ts \<and> Simulation_Inv s ts"
proof -
  let ?ts_init = "\<lparr>
    t_pc = (\<lambda>p. ''TL0''),
    pools = (\<lambda>p. []),
    ts_counter = 1,
    nid_counter = 1,
    t_V_var = 1,
    t_v = (\<lambda>p. BOT),
    t_nid = (\<lambda>p. BOT),
    t_ts = (\<lambda>p. TOP),
    t_startTs = (\<lambda>p. TOP),
    t_candNid = (\<lambda>p. BOT),
    t_candTs = (\<lambda>p. TOP),
    t_candPid = (\<lambda>p. BOT),
    t_retV = (\<lambda>p. BOT),
    t_scanned = (\<lambda>p. {})
  \<rparr>"

  have t_init_def: "T_Init ?ts_init"
    unfolding T_Init_def by simp

  have inv_sys: "system_invariant s"
    using system_invariant_Init assms by blast

  have inv_tsq: "TSQ_State_Inv ?ts_init"
    using TSQ_State_Inv_Init t_init_def by blast

  have sim_r: "Simulation_R s ?ts_init"
    using Simulation_R_Init assms t_init_def by blast

  have "Simulation_Inv s ?ts_init"
    unfolding Simulation_Inv_def
    using inv_sys inv_tsq sim_r by blast
  thus ?thesis
    using t_init_def by blast
qed

(* ========================================================== *)
(* Simulation relation wrapper                                  *)
(* ========================================================== *)
definition SimRel :: "SysState \<Rightarrow> TState \<Rightarrow> bool" where
  "SimRel s ts \<equiv> Reachable_T ts \<and> Simulation_Inv s ts"

lemma SimRel_Init:
  assumes "Init s"
  shows "\<exists>ts. T_Init ts \<and> SimRel s ts"
proof -
  from Global_Simulation_Init[OF assms]
  obtain ts where t_init: "T_Init ts" and sim_inv: "Simulation_Inv s ts"
    by blast
  moreover have "Reachable_T ts"
    using Reachable_T.init[OF t_init] .
  ultimately show ?thesis
    unfolding SimRel_def by blast
qed

lemma SimRel_Step:
  assumes rel: "SimRel s ts"
      and step: "Next s s'"
      and E2_in_ProcSet_s: "\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet"
  shows "\<exists>ts'. T_Next ts ts' \<and> SimRel s' ts'"
proof -
  have ts_reach: "Reachable_T ts"
    using rel unfolding SimRel_def by blast
  have sim_inv: "Simulation_Inv s ts"
    using rel unfolding SimRel_def by blast

from Global_Simulation_Step[OF sim_inv step E2_in_ProcSet_s]
obtain ts' where t_next: "T_Next ts ts'" and sim_r: "Simulation_R s' ts'"
  by blast

  have inv_sys_s': "system_invariant s'"
    using sim_inv step Sys_Inv_Step
    unfolding Simulation_Inv_def by blast

  have inv_tsq_plus_ts: "TSQ_State_Inv_Plus ts"
    using Reachable_T_TSQ_State_Inv_Plus ts_reach by blast

  have inv_tsq_plus_ts': "TSQ_State_Inv_Plus ts'"
    using TSQ_State_Inv_Plus_Step[OF inv_tsq_plus_ts t_next] .

  have inv_tsq_ts': "TSQ_State_Inv ts'"
    using TSQ_State_Inv_PlusD_plain[OF inv_tsq_plus_ts'] .

  have sim_inv_s': "Simulation_Inv s' ts'"
    unfolding Simulation_Inv_def
    using inv_sys_s' inv_tsq_ts' sim_r by blast

  have ts_reach': "Reachable_T ts'"
    using Reachable_T.step[OF ts_reach t_next] .

  show ?thesis
    using t_next ts_reach' sim_inv_s'
    unfolding SimRel_def by blast
qed

(* ========================================================== *)
(* Main theorem: TSQ forward/weakly simulates HWQ               *)
(* ========================================================== *)
theorem HWQ_is_weakly_simulated_by_TSQ:
  shows
    "(\<forall>s0. Init s0 \<longrightarrow> (\<exists>ts0. T_Init ts0 \<and> SimRel s0 ts0)) \<and>
     (\<forall>s ts s'. SimRel s ts \<and> Next s s' \<and>
        (\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet)
        \<longrightarrow> (\<exists>ts'. T_Next ts ts' \<and> SimRel s' ts'))"
proof (intro conjI allI impI)
  fix s0
  assume "Init s0"
  thus "\<exists>ts0. T_Init ts0 \<and> SimRel s0 ts0"
    using SimRel_Init by blast
next
  fix s ts s'
  assume "SimRel s ts \<and> Next s s' \<and>
          (\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet)"
  thus "\<exists>ts'. T_Next ts ts' \<and> SimRel s' ts'"
    using SimRel_Step by blast
qed






(* ========================================================== *)
(* Trace-refinement theorem as a corollary of weak simulation   *)
(* ========================================================== *)
theorem Trace_Refinement:
  assumes "Reachable_Sys s"
  shows "\<exists>ts. Reachable_T ts \<and> Simulation_Inv s ts"
proof -
  have init_part:
    "\<forall>s0. Init s0 \<longrightarrow> (\<exists>ts0. T_Init ts0 \<and> SimRel s0 ts0)"
    using HWQ_is_weakly_simulated_by_TSQ by blast

  have stronger:
    "\<forall>s. Reachable_Sys s \<longrightarrow>
        (\<exists>ts. Reachable_T ts \<and> Simulation_Inv s ts) \<and>
        (\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet)"
  proof (intro allI impI)
    fix s
    assume reach: "Reachable_Sys s"
    then show "(\<exists>ts. Reachable_T ts \<and> Simulation_Inv s ts) \<and>
               (\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet)"
    proof (induction rule: Reachable_Sys.induct)
      case (init s)
      from init_part init
      obtain ts where "T_Init ts" and rel: "SimRel s ts"
        by blast
      have ex_part: "\<exists>ts. Reachable_T ts \<and> Simulation_Inv s ts"
        using `T_Init ts` rel unfolding SimRel_def by blast
      have proc_part: "\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet"
        using init unfolding Init_def by auto
      show ?case
        using ex_part proc_part by blast
    next
      case (step s s')
      have ex_prev: "\<exists>ts. Reachable_T ts \<and> Simulation_Inv s ts"
        using step.IH by blast
      then obtain ts where ts_reach: "Reachable_T ts" and sim_inv: "Simulation_Inv s ts"
        by blast
      have proc_prev: "\<forall>q. c_program_counter (fst s) q = ''E2'' \<longrightarrow> q \<in> ProcSet"
        using step.IH by blast
      have rel: "SimRel s ts"
        using ts_reach sim_inv unfolding SimRel_def by blast
      from SimRel_Step[OF rel step.hyps(2) proc_prev]
      obtain ts' where t_next: "T_Next ts ts'" and rel': "SimRel s' ts'"
        by blast
      have ex_part: "\<exists>ts. Reachable_T ts \<and> Simulation_Inv s' ts"
        using rel' unfolding SimRel_def by blast

      from step.hyps(2)
      obtain p where p_in: "p \<in> ProcSet" and
        step_cases:
          "Sys_L0 p s s' \<or> Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_E3 p s s' \<or>
           Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s' \<or> Sys_D4 p s s'"
        unfolding Next_def by blast

      have proc_part: "\<forall>q. c_program_counter (fst s') q = ''E2'' \<longrightarrow> q \<in> ProcSet"
      proof (intro allI impI)
        fix q
        assume pcq: "c_program_counter (fst s') q = ''E2''"
        show "q \<in> ProcSet"
        proof (cases "q = p")
          case True
          then show ?thesis
            using p_in by simp
        next
          case False
            have pc_unchanged: "c_program_counter (fst s') q = c_program_counter (fst s) q"
              using step_cases False
              unfolding Sys_L0_def Sys_E1_def Sys_E2_def Sys_E3_def
                        Sys_D1_def Sys_D2_def Sys_D3_def Sys_D4_def
                        C_L0_def C_E1_def C_E2_def C_E3_def
                        C_D1_def C_D2_def C_D3_def C_D4_def Let_def
              by (auto split: if_splits)
          then have "c_program_counter (fst s) q = ''E2''"
            using pcq by simp
          then show ?thesis
            using proc_prev by blast
        qed
      qed

      show ?case
        using ex_part proc_part by blast
    qed
  qed

  from stronger assms show ?thesis
    by blast
qed

end
