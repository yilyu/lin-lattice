theory NotSimLemmas
  imports TraceInv
    "../HWQ-U/ULinProof"
begin

text \<open>
  A call/return-preserving weak forward-simulation framework for the corrected
  2-process counterexample showing that HWQ does not simulate TSQ.
  Compared with the earlier "strong-simulation" proof, this theory no longer
  bakes concrete-state correspondence into the simulation relation.
  Instead we:

    (1) model both systems as labelled transition systems with observable
        call/return events and internal Tau steps;
    (2) define a standard weak forward simulation FW_Sim_CR;
    (3) make the three critical witness traces explicit:
          * e1_labels  : the common prefix reaching conf_k,
          * e2_labels  : the branch where the old pending deq returns a1,
          * e3_labels  : the branch where a fresh deq returns a1 and the old
                     
        pending deq later returns a3;
    (4) isolate the remaining proof obligations into:
          * TSQ-side witness paths for e1 / e2 / e3, and
          * HWQ-side semantic impossibility lemmas extracted from the matched
            prefix point.
  In the Scheme-A version below, the concrete-side prefix extraction no longer
  claims that the weakly matched endpoint sk itself is the common-prefix state.
  Instead, it extracts an earlier concrete state sk0 with the desired HWQ shape,
  together with a trailing C_Tau_Star sk0 sk.
  This aligns the theorem statement
  with the semantics of weak matching.
\<close>

subsection \<open>Observations\<close>

type_synonym CRObs = "mname \<times> nat \<times> nat \<times> cr_type"

definition mk_obs :: "mname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cr_type \<Rightarrow> CRObs" where
  "mk_obs m v p c = (m, v, p, c)"

fun visible_proj :: "CRObs option list \<Rightarrow> CRObs list" where
  "visible_proj [] = []"
|
"visible_proj (None # xs) = visible_proj xs"
| "visible_proj (Some a # xs) = a # visible_proj xs"

abbreviation P1 :: nat where "P1 \<equiv> 0"
abbreviation P2 :: nat where "P2 \<equiv> 1"
abbreviation A1 :: nat where "A1 \<equiv> 1"
abbreviation A2 :: nat where "A2 \<equiv> 2"
abbreviation A3 :: nat where "A3 \<equiv> 3"

subsection \<open>Explicit witness traces\<close>

text \<open>
  The intended observable reading is:

    e1_labels :
      P1 enq(a1) call/ret;
      P2 enq(a2) call;
      P1 enq(a3) call/ret;
      P1 deq() call;
      then P2 enq(a2) completes/returns after P1 has already scanned P2 once.
  e2_labels :
      from conf_k, the old pending deq of P1 returns a1;
      then P1 performs two fresh dequeues returning a2 and a3.
  e3_labels :
      from conf_k, a fresh deq of P2 returns a1;
      then the old pending deq of P1 returns a3.
\<close>

definition e1_labels :: "CRObs option list" where
  "e1_labels = [
      Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
      Some (mk_obs enq A2 P2 call), None,
      Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret),
      Some (mk_obs deq BOT P1 call), None, None, None,
      None, Some (mk_obs enq A2 P2 ret)
    ]"

(* Revised e2_labels: A2 fresh deq 5 None *)
definition e2_labels ::  "CRObs option list" where
"e2_labels = [
  None, None, Some (mk_obs deq A1 P1 ret),
  Some (mk_obs deq BOT P1 call), None, None, None, None, None,
  Some (mk_obs deq A2 P1 ret),
  Some (mk_obs deq BOT P1 call), None, None, None, None, None,
  Some (mk_obs deq A3 P1 ret)
]"

(* Revised e3_labels: P2 A1 fresh deq 5 None *)
definition e3_labels ::  "CRObs option list" where
"e3_labels = [
  Some (mk_obs deq BOT P2 call), None, None, None, None, None,
  Some (mk_obs deq A1 P2 ret),
  None, None,
  Some (mk_obs deq A3 P1 ret)
]"

definition e1_pre_labels :: "CRObs option list" where
  "e1_pre_labels = butlast e1_labels"

lemma e1_labels_split:
  "e1_labels = e1_pre_labels @ [Some (mk_obs enq A2 P2 ret)]"
  unfolding e1_pre_labels_def e1_labels_def by simp

lemma visible_e1_labels:
  "visible_proj e1_labels = [
      mk_obs enq A1 P1 call,
      mk_obs enq A1 P1 ret,
      mk_obs enq 
A2 P2 call,
      mk_obs enq A3 P1 call,
      mk_obs enq A3 P1 ret,
      mk_obs deq BOT P1 call,
      mk_obs enq A2 P2 ret
    ]"
  unfolding e1_labels_def mk_obs_def by simp

lemma visible_e2_labels:
  "visible_proj e2_labels = [
      mk_obs deq A1 P1 ret,
      mk_obs deq BOT P1 call,
      mk_obs deq A2 P1 ret,
      mk_obs deq BOT P1 call,
  
      mk_obs deq A3 P1 ret
    ]"
  unfolding e2_labels_def mk_obs_def by simp

lemma visible_e3_labels:
  "visible_proj e3_labels = [
      mk_obs deq BOT P2 call,
      mk_obs deq A1 P2 ret,
      mk_obs deq A3 P1 ret
    ]"
  unfolding e3_labels_def mk_obs_def by simp

subsection \<open>Labelled TSQ steps (single-scan semantics)\<close>

inductive T_StepCR :: "TState \<Rightarrow> CRObs option \<Rightarrow> TState \<Rightarrow> bool" where
  T_Call_Enq_vis:
    "\<lbrakk> p \<in> ProcSet;
     T_Call_Enq p ts ts' \<rbrakk> \<Longrightarrow>
     T_StepCR ts (Some (mk_obs enq (t_V_var ts) p call)) ts'"
| T_E1_tau:
    "\<lbrakk> p \<in> ProcSet;
     T_E1 p ts ts' \<rbrakk> \<Longrightarrow> T_StepCR ts None ts'"
| T_E2_tau:
    "\<lbrakk> p \<in> ProcSet;
     T_E2 p ts ts' \<rbrakk> \<Longrightarrow> T_StepCR ts None ts'"
| T_E3_vis:
    "\<lbrakk> p \<in> ProcSet;
     T_E3 p ts ts' \<rbrakk> \<Longrightarrow>
     T_StepCR ts (Some (mk_obs enq (t_v ts p) p ret)) ts'"
| T_Call_Deq_vis:
    "\<lbrakk> p \<in> ProcSet;
     T_Call_Deq p ts ts' \<rbrakk> \<Longrightarrow>
     T_StepCR ts (Some (mk_obs deq BOT p call)) ts'"
| T_D1_tau:
    "\<lbrakk> p \<in> ProcSet;
     T_D1 p ts ts' \<rbrakk> \<Longrightarrow> T_StepCR ts None ts'"
| T_D2_tau:
    "\<lbrakk> p \<in> ProcSet;
     T_D2 p ts ts' \<rbrakk> \<Longrightarrow> T_StepCR ts None ts'"
| T_D3_tau:
    "\<lbrakk> p \<in> ProcSet;
     T_D3' p ts ts' \<rbrakk> \<Longrightarrow> T_StepCR ts None ts'"
| T_D4_vis:
    "\<lbrakk> p \<in> ProcSet;
     T_D4 p ts ts' \<rbrakk> \<Longrightarrow>
     T_StepCR ts (Some (mk_obs deq (t_retV ts p) p ret)) ts'"

subsection \<open>Labelled HWQ steps\<close>

inductive C_StepCR :: "SysState \<Rightarrow> CRObs option \<Rightarrow> SysState \<Rightarrow> bool" where
  C_Sys_L0_enq_vis:
    "\<lbrakk> p \<in> ProcSet;
     Sys_L0 p s s'; program_counter s' p = ''E1'' \<rbrakk> \<Longrightarrow>
     C_StepCR s (Some (mk_obs enq (V_var s) p call)) s'"
| C_Sys_L0_deq_vis:
    "\<lbrakk> p \<in> ProcSet;
     Sys_L0 p s s'; program_counter s' p = ''D1'' \<rbrakk> \<Longrightarrow>
     C_StepCR s (Some (mk_obs deq BOT p call)) s'"
| C_Sys_E1_tau:
    "\<lbrakk> p \<in> ProcSet;
     Sys_E1 p s s' \<rbrakk> \<Longrightarrow> C_StepCR s None s'"
| C_Sys_E2_tau:
    "\<lbrakk> p \<in> ProcSet;
     Sys_E2 p s s' \<rbrakk> \<Longrightarrow> C_StepCR s None s'"
| C_Sys_E3_vis:
    "\<lbrakk> p \<in> ProcSet;
     Sys_E3 p s s' \<rbrakk> \<Longrightarrow>
     C_StepCR s (Some (mk_obs enq (v_var s p) p ret)) s'"
| C_Sys_D1_tau:
    "\<lbrakk> p \<in> ProcSet;
     Sys_D1 p s s' \<rbrakk> \<Longrightarrow> C_StepCR s None s'"
| C_Sys_D2_tau:
    "\<lbrakk> p \<in> ProcSet;
     Sys_D2 p s s' \<rbrakk> \<Longrightarrow> C_StepCR s None s'"
| C_Sys_D3_tau:
    "\<lbrakk> p \<in> ProcSet;
     Sys_D3 p s s' \<rbrakk> \<Longrightarrow> C_StepCR s None s'"
| C_Sys_D4_vis:
    "\<lbrakk> p \<in> ProcSet;
     Sys_D4 p s s' \<rbrakk> \<Longrightarrow>
     C_StepCR s (Some (mk_obs deq (x_var s p) p ret)) s'"

lemma C_StepCR_into_Next:
  assumes "C_StepCR s l s'"
  shows "Next s s'"
  using assms
  unfolding Next_def
  by (cases rule: C_StepCR.cases; blast)

subsection \<open>Concrete weak matching segments\<close>

definition C_Tau :: "SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "C_Tau s s' \<longleftrightarrow> C_StepCR s None s'"

inductive C_Tau_Star :: "SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  refl: "C_Tau_Star s s"
| step: "C_Tau s s1 \<Longrightarrow> C_Tau_Star s1 s2 \<Longrightarrow> C_Tau_Star s s2"

lemma C_Tau_Star_trans:
  assumes "C_Tau_Star s s1" "C_Tau_Star s1 s2"
 
  shows "C_Tau_Star s s2"
  using assms
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s t u)
  then show ?case by (meson C_Tau_Star.step)
qed

lemma C_Tau_Star_reachable:
  assumes RS: "Reachable_Sys s"
      and TS: "C_Tau_Star s s'"
  shows "Reachable_Sys s'"
  using TS RS
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case .
next
  case (step s s1 s2)
  from step.prems have "Reachable_Sys s" .
  moreover from step.hyps(1) have "Next s s1"
    unfolding C_Tau_def using C_StepCR_into_Next by blast
  ultimately have "Reachable_Sys s1"
    by (rule Reachable_Sys.step)
  thus ?case using step.IH by blast
qed

inductive C_Match :: "SysState \<Rightarrow> CRObs option \<Rightarrow> SysState \<Rightarrow> bool" where
  match_tau:
    "C_Tau_Star s s' \<Longrightarrow> C_Match s None s'"
|
  match_vis:
    "C_Tau_Star s u \<Longrightarrow>
     C_StepCR u (Some a) v \<Longrightarrow>
     C_Tau_Star v s' \<Longrightarrow>
     C_Match s (Some a) s'"

lemma C_Match_reachable:
  assumes RS: "Reachable_Sys s"
      and M:  "C_Match s l s'"
  shows "Reachable_Sys s'"
  using M
proof (cases rule: C_Match.cases)
  case match_tau
  (* Step 1. *)
  (* match_tau(1) l = None, match_tau(2) C_Tau_Star s s' *)
  then show ?thesis 
    using RS C_Tau_Star_reachable by blast
next
  
  case (match_vis u a v)
  (* Branch 2. *)  
  (* match_vis(1) l = Some a *)
  (* match_vis(2) C_Tau_Star s u *)
  (* Step 3. *)
  (* match_vis(4) C_Tau_Star v s' *)
  
  from C_Tau_Star_reachable[OF RS match_vis(2)] 
  have RU: "Reachable_Sys u" .
  from C_StepCR_into_Next[OF match_vis(3)] 
  have UV: "Next u v" .
  have RV: "Reachable_Sys v" 
    using RU UV by (rule Reachable_Sys.step)
    
  from C_Tau_Star_reachable[OF RV match_vis(4)] 
  show ?thesis .
qed

subsection \<open>Abstract paths and concrete matched paths\<close>

inductive T_Path :: "TState \<Rightarrow> CRObs option list \<Rightarrow> TState \<Rightarrow> bool" where
  nil:  "T_Path ts [] ts"
|
  cons: "T_StepCR ts l ts1 \<Longrightarrow> T_Path ts1 ls ts2 \<Longrightarrow> T_Path ts (l # ls) ts2"

lemma T_StepCR_into_T_Next:
  assumes "T_StepCR ts l ts'"
  shows "T_Next ts ts'"
  using assms
  unfolding T_Next_def
  by (cases rule: T_StepCR.cases; blast intro: T_D3'_into_T_D3)

lemma T_Path_reachable:
  assumes INIT: "T_Init t0"
      and P: "T_Path t0 ls t"
  shows "Reachable_T t"
  using P Reachable_T.init[OF INIT]
proof (induction rule: T_Path.induct)
  case nil
  then show ?case by simp
next
  case (cons s l s1 ls s2)
  from T_StepCR_into_T_Next[OF cons.hyps(1)] have "T_Next s s1" .
  then have RS1: "Reachable_T s1" using cons.prems
    using Reachable_T.step by auto
  from cons.IH[OF RS1] show ?case .
qed

lemma T_Path_TSQ_State_Inv_Plus:
  assumes INIT: "T_Init t0"
      and P: "T_Path t0 ls t"
  shows "TSQ_State_Inv_Plus t"
  using Reachable_T_TSQ_State_Inv_Plus[OF T_Path_reachable[OF INIT P]] .
  inductive C_Path :: "SysState \<Rightarrow> CRObs option list \<Rightarrow> SysState \<Rightarrow> bool" where
  nil:  "C_Path s [] s"
|
  cons: "C_Match s l s1 \<Longrightarrow> C_Path s1 ls s2 \<Longrightarrow> C_Path s (l # ls) s2"

lemma T_Path_append:
  assumes "T_Path s xs t" "T_Path t ys u"
  shows "T_Path s (xs @ ys) u"
  using assms
proof (induction rule: T_Path.induct)
  case nil
  then show ?case by simp
next
  case (cons s l s1 ls t)
  then show ?case by (simp add: T_Path.cons)
qed

lemma C_Path_append:
  assumes "C_Path s xs t" "C_Path t ys u"
  shows "C_Path s (xs @ ys) u"
  using assms
proof (induction rule: C_Path.induct)
  case nil
  then show ?case by 
simp
next
  case (cons s l s1 ls t)
  then show ?case by (simp add: C_Path.cons)
qed

lemma C_Path_reachable:
  assumes RS: "Reachable_Sys s"
      and P:  "C_Path s ls s'"
  shows "Reachable_Sys s'"
  using P RS
proof (induction rule: C_Path.induct)
  case nil
  then show ?case .
next
  case (cons s l s1 ls s2)
  from C_Match_reachable[OF cons.prems cons.hyps(1)] have RS1: "Reachable_Sys s1" .
  from cons.IH[OF RS1] show ?case .
qed

lemma Reachable_Sys_system_invariant:
  assumes "Reachable_Sys s"
  shows "system_invariant s"
  using Reachable_Sys_in_SimRel_U[OF assms] .
  subsection \<open>General call/return-preserving forward simulation\<close>

definition FW_Sim_CR :: "(TState \<Rightarrow> SysState \<Rightarrow> bool) \<Rightarrow> bool" where
  "FW_Sim_CR R \<longleftrightarrow>
     (\<forall>t0. T_Init t0 \<longrightarrow> (\<exists>s0. Init s0 \<and> R t0 s0)) \<and>
     (\<forall>t l t' s. R t s \<and> T_StepCR t l t' \<longrightarrow> (\<exists>s'. C_Match s l s' \<and> R t' s'))"

lemma FW_Sim_CR_path:
  assumes SIM: "FW_Sim_CR R"
      and REL: "R t s"
      and PATH: "T_Path t ls t'"
  shows "\<exists>s'. C_Path s ls s' \<and> R t' s'"
  
  using PATH REL
proof (induction arbitrary: s rule: T_Path.induct)
  case nil
  then show ?case
    using C_Path.nil by blast 
next
  case (cons t l t1 ls t2)
  from SIM cons.prems cons.hyps(1)
  obtain s1 where M1: "C_Match s l s1" and R1: "R t1 s1"
    unfolding FW_Sim_CR_def by blast
  from cons.IH[OF R1] obtain s2 where P2: "C_Path s1 ls s2" and R2: "R t2 s2"
    by blast
  from M1 P2 have "C_Path s (l # ls) s2"
    by (rule C_Path.cons)
  with 
  R2 show 
  ?case by blast
qed

lemma FW_Sim_CR_from_init:
  assumes SIM: "FW_Sim_CR R"
      and INIT: "T_Init t0"
      and PATH: "T_Path t0 ls t'"
  shows "\<exists>s0 s'.
  Init s0 \<and> C_Path s0 ls s' \<and> R t' s'"
proof -
  from SIM INIT obtain s0 where S0: "Init s0" and R0: "R t0 s0"
    unfolding FW_Sim_CR_def by blast
  from FW_Sim_CR_path[OF SIM R0 PATH]
  obtain s' where P: "C_Path s0 ls s'" and R': "R t' s'" by blast
  from S0 P R' show ?thesis by blast
qed

subsection \<open>The 2-process common prefix and the two TSQ branches\<close>

text \<open>
  E1_TSQ_shape is the corrected common-prefix state conf_k from the new 2-process
  LaTeX proof.
\<close>

(* Centralized definitions *)

definition E1_TSQ_shape :: "TState \<Rightarrow> bool" where
  "E1_TSQ_shape 
  ts \<longleftrightarrow>
 
      t_pc ts P1 = ''TD_Loop'' \<and>
      t_scanned ts P1 = {P2} \<and>
      t_candNid ts P1 = BOT \<and>
      t_candTs ts P1 = TOP \<and>
      t_candPid ts P1 = BOT \<and>
      t_startTs ts P1 = TS 4 \<and>
      pools ts P1 = [(1, A1, TS 1), (3, A3, TS 3)] \<and>
      pools ts P2 = [(2, A2, TS 
  2)]"

definition E1_HWQ_shape :: "SysState \<Rightarrow> bool" where
  "E1_HWQ_shape s \<longleftrightarrow>
      system_invariant s \<and>
      X_var s = 4 \<and>
      Q_arr s 1 = A1 \<and>
      Q_arr s 
  2 = A2 \<and>
      Q_arr s 3 = A3 \<and>
      program_counter s P1 = ''D3'' \<and>
      program_counter s P2 = ''L0'' \<and>
      j_var s P1 \<in> {1,2,3}"



definition E1_HWQ_relaxed_shape :: "SysState \<Rightarrow> bool" where
  "E1_HWQ_relaxed_shape s \<longleftrightarrow>
      system_invariant s \<and>
   
       X_var s = 4 \<and>
      Q_arr s 2 = A2 \<and> Q_arr s 3 = A3 \<and>
      program_counter s 
  P2 = ''L0'' \<and>
      HasPendingDeq s P1 \<and>
      ( 
        (Q_arr s 1 = A1 \<and> (
          (program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s P1 = ''D3'' \<and> j_var s P1 
  = 1)
        ))
        \<or>
        (Q_arr s 1 = BOT 
  \<and> (program_counter s P1 = ''D4'' \<and> x_var s P1 = A1))
      )"


(* ========================================================================= *)
(* 1. Strengthenedtwo-track envelope (fully close the state space) *)
(* ========================================================================= *)

definition e3_before_last_labels :: "CRObs option list" where
"e3_before_last_labels = [
  Some (mk_obs deq BOT P2 call), None, None, None, None, None,
  Some (mk_obs deq A1 P2 ret),
  None, None
]"

definition e3_before_p2_ret_labels :: "CRObs option list" where
  "e3_before_p2_ret_labels =
     [Some (mk_obs deq BOT P2 call), None, None, None, None, None]"

definition e3_after_p2_ret_before_last_labels :: "CRObs option list" where
  "e3_after_p2_ret_before_last_labels =
     [None, None]"

(* ========================================================================= *)
(* Symmetric Pre-Ret envelope: history concrete *)
(* ========================================================================= *)
definition E3_Pre_Ret_Envelope :: "SysState \<Rightarrow> bool" where
  "E3_Pre_Ret_Envelope s \<longleftrightarrow>
     system_invariant s \<and>
     program_counter s P1 \<in> {''D1'',''D2'',''D3'',''D4''} \<and>
     program_counter s P2 \<in> {''L0'',''D1'',''D2'',''D3'',''D4''} \<and>
     (program_counter s P1 = ''D3'' \<longrightarrow> j_var s P1 \<in> {1,2}) \<and>
     (program_counter s P2 = 
  ''D3'' \<longrightarrow> j_var s P2 \<in> {1,2}) \<and>
     (program_counter s P1 = ''D4'' \<longrightarrow> x_var s P1 \<in> {A1,A2}) \<and>
     (program_counter s P2 = ''D4'' \<longrightarrow> x_var s P2 \<in> {A1,A2}) \<and>
     (Q_arr s 1 = BOT \<longleftrightarrow> (program_counter s P1 = ''D4'' \<and> x_var s P1 = A1) \<or> 
                          (program_counter s P2 = ''D4'' \<and> x_var s P2 = A1)) \<and>
 
      (Q_arr s 2 = BOT \<longleftrightarrow> (program_counter s P1 = ''D4'' \<and> x_var s P1 = A2) \<or> 
                          (program_counter s P2 = ''D4'' \<and> x_var s P2 = A2)) \<and>
     (Q_arr s 1 \<noteq> BOT \<longrightarrow> Q_arr s 1 = A1) \<and>
     (Q_arr s 2 \<noteq> BOT \<longrightarrow> Q_arr s 2 = A2) \<and>
     Q_arr s 3 = 
  A3 \<and>
     (program_counter s P1 = ''D3'' \<and> j_var s P1 = 2 \<longrightarrow> Q_arr s 1 = BOT) \<and>
     (program_counter s P2 = ''D3'' \<and> j_var s P2 = 2 \<longrightarrow> Q_arr s 1 = BOT) \<and>
     \<not>(program_counter s P1 = ''D4'' \<and> x_var s P1 = A1 \<and> program_counter s P2 = ''D4'' \<and> x_var s P2 = A1) \<and>
     \<not>(program_counter s P1 = ''D4'' \<and> x_var s P1 = A2 \<and> program_counter s P2 = ''D4'' \<and> x_var s P2 = 
  A2)"

definition E3_Post_Ret_Envelope :: "SysState \<Rightarrow> bool" where
  "E3_Post_Ret_Envelope s \<longleftrightarrow>
     system_invariant s \<and>
     program_counter s P2 = ''L0'' \<and>
     Q_arr s 1 = BOT \<and>
     program_counter s P1 \<in> {''D1'',''D2'',''D3'',''D4''} \<and>
     (program_counter s P1 = ''D3'' \<longrightarrow> j_var s P1 \<in> {1,2}) \<and>
     (program_counter s P1 = ''D4'' \<longrightarrow> x_var s P1 \<in> {A1,A2}) \<and>
     (Q_arr s 2 = BOT \<longleftrightarrow> program_counter s P1 = ''D4'' \<and> x_var s P1 = 
  A2) \<and>
     (Q_arr s 2 \<noteq> BOT \<longrightarrow> Q_arr s 2 = A2) \<and>
     Q_arr s 3 = A3"


(* ========================================================================= *)
(* Path-slicing utility: e1_after_p2_call extract P1 deq call *)
(* ========================================================================= *)

definition e1_before_p1_deq_call_labels :: "CRObs option list" where
  "e1_before_p1_deq_call_labels =
    [ None,
      Some (mk_obs enq A3 P1 call),
      None,
      None,
   
      Some (mk_obs enq A3 P1 ret) ]"

definition e1_after_p1_deq_call_labels :: "CRObs option list" where
  "e1_after_p1_deq_call_labels = [None, None, None]"


definition E1_HWQ_quantum_shape :: "SysState \<Rightarrow> bool" where
  "E1_HWQ_quantum_shape s \<longleftrightarrow>
      system_invariant s \<and>
      X_var s = 4 \<and>
      program_counter s P2 = ''L0'' \<and>
      HasPendingDeq s P1 \<and>
      (
        (Q_arr s 1 = A1 \<and>
          ((program_counter s 
  P1 \<in> {''D1'', ''D2''}) \<or>
           (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
        \<or>
        (Q_arr s 1 = BOT \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)
      ) \<and>
      {Q_arr s 2, Q_arr s 3} = {A2, A3}"


(* 1. e2 traceslicedefinition *)
definition e2_part1 :: "CRObs option list" where
  "e2_part1 = [None, None, Some (mk_obs deq A1 P1 ret)]"

definition e2_part2 :: "CRObs option list" where
  "e2_part2 =
     [Some (mk_obs deq BOT P1 call), None, None, None, None, None,
      Some (mk_obs deq A2 P1 ret)]"

definition e2_part3 :: "CRObs option list" where
  "e2_part3 = [Some (mk_obs deq BOT P1 call), None, None, None, None, None, Some (mk_obs deq A3 P1 ret)]"


(* ------------------------------------------------------------------------- *)
(* Auxiliary lemma. *)
(* ------------------------------------------------------------------------- *)

definition E1_credit :: "SysState \<Rightarrow> nat" where
  "E1_credit s = 
    (if program_counter s P1 = ''E1'' then 1 else 0) + 
    (if program_counter s P2 = ''E1'' then 1 else 0)"

(* Avoid fragile case syntax; use fst and snd to locate m and c *)
definition is_enq_call_cr :: "CRObs \<Rightarrow> nat" where
  "is_enq_call_cr obs = (if fst obs = enq \<and> snd (snd (snd obs)) = call then 1 else 0)"

definition is_enq_call_opt :: "CRObs option \<Rightarrow> nat" where
  "is_enq_call_opt l = (case l of Some obs \<Rightarrow> is_enq_call_cr obs | None \<Rightarrow> 0)"


definition Slots23_seed :: "SysState \<Rightarrow> bool" where
  "Slots23_seed s \<longleftrightarrow>
     {Q_arr s 2, Q_arr s 3} \<subseteq> {BOT, A2, A3} \<and>
     A3 \<in> {Q_arr s 2, Q_arr s 3}"

definition P2_pending_A2_safe :: "SysState \<Rightarrow> bool" where
  "P2_pending_A2_safe s \<equiv>
     program_counter s P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     v_var s P2 = A2 \<and>
     (program_counter s P2 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
     (program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"


(* End of definitions *)



lemma E1_HWQ_shapeD:
  assumes "E1_HWQ_shape s"
  shows "system_invariant s"
    and "X_var s = 4"
    and 
  "Q_arr s 1 = A1"
    and "Q_arr s 2 = A2"
    and "Q_arr s 3 = A3"
    and "program_counter s P1 = ''D3''"
 
    and "program_counter s P2 = ''L0''"
    and "j_var s P1 \<in> {1,2,3}"
  using assms unfolding E1_HWQ_shape_def by auto


(* ========================================================== *)
(* 1. Proof of existence of the e1 path (robust isolated-simplifier version) *)
(* ========================================================== *)
lemma tsq_e1_exists_2proc:
  assumes N2: "N_Procs = 2"
  shows "\<exists>t0 tk. T_Init t0 \<and> T_Path t0 e1_labels tk \<and> E1_TSQ_shape tk"
proof -
  (* Initial state *)
  let ?t0 = "\<lparr> t_pc = (\<lambda>_. ''TL0''), pools = (\<lambda>_. []), ts_counter = 1, nid_counter = 1, 
               t_V_var = 1, t_v = (\<lambda>_. BOT), t_nid = (\<lambda>_. BOT), t_ts = (\<lambda>_. TOP), 
               t_startTs = (\<lambda>_. TOP), t_candNid = (\<lambda>_. BOT), t_candTs = (\<lambda>_. TOP), 
               t_candPid = (\<lambda>_. BOT), t_retV = (\<lambda>_. BOT), t_scanned = (\<lambda>_. {}) \<rparr>"
  
  have I0: "T_Init ?t0" unfolding T_Init_def BOT_def by simp

  (* Package only the low-level step definitions; avoid T_StepCR.simps to prevent proof explosion *)
  note defs = T_Call_Enq_def T_E1_def T_E2_def T_E3_def 
              T_Call_Deq_def T_D1_def T_D2_EnterLoop_def 
              T_D3_Scan_def pool_getOldest_def T_D4_def Let_def BOT_def

  (* 1. P1 Call Enq A1 *)
  have "\<exists>t1. T_Call_Enq P1 ?t0 t1" unfolding defs by (auto simp: N2)
  then obtain t1 where D01: "T_Call_Enq P1 ?t0 t1" by blast
  have S01: "T_StepCR ?t0 (Some (mk_obs enq A1 P1 call)) t1"
  proof -
    have EQ: "t_V_var ?t0 = A1" unfolding defs by simp
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D01 have "T_StepCR ?t0 (Some (mk_obs enq (t_V_var ?t0) P1 call)) t1"
      by (intro T_StepCR.intros)
    thus ?thesis unfolding EQ by simp
  qed

  (* Step 2.1.1. *)
  have "\<exists>t2. T_E1 P1 t1 t2" using D01 unfolding defs by (auto simp: N2)
  then obtain t2 where D12: "T_E1 P1 t1 t2" by blast
  have S12: "T_StepCR t1 None t2" 
  proof -
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D12 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 3. P1 E2 *)
  have "\<exists>t3. T_E2 P1 t2 t3" using D01 D12 unfolding defs by (auto simp: N2)
  then obtain t3 where D23: "T_E2 P1 t2 t3" by blast
  have S23: "T_StepCR t2 None t3" 
  proof -
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D23 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 4. P1 E3 ret A1 *)
  have "\<exists>t4. T_E3 P1 t3 t4" using D01 D12 D23 unfolding defs by (auto simp: N2)
  then obtain t4 where D34: "T_E3 P1 t3 t4" by blast
  have S34: "T_StepCR t3 (Some (mk_obs enq A1 P1 ret)) t4"
  proof -
    have EQ: "t_v t3 P1 = A1" using D01 D12 D23 unfolding defs by auto
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D34 have "T_StepCR t3 (Some (mk_obs enq (t_v t3 P1) P1 ret)) t4"
      by (intro T_StepCR.intros)
    thus ?thesis unfolding EQ by simp
  qed

  (* 5. P2 Call Enq A2 *)
  have "\<exists>t5. T_Call_Enq P2 t4 t5" using D01 D12 D23 D34 unfolding defs by (auto simp: N2)
  then obtain t5 where D45: "T_Call_Enq P2 t4 t5" by blast
  have S45: "T_StepCR t4 (Some (mk_obs enq A2 P2 call)) t5"
  proof -
    have EQ: "t_V_var t4 = A2" using D01 D12 D23 D34 unfolding defs by auto
    have "P2 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D45 have "T_StepCR t4 (Some (mk_obs enq (t_V_var t4) P2 call)) t5"
      by (intro T_StepCR.intros)
    thus ?thesis unfolding EQ by simp
  qed

  (* 6. P2 E1 *)
  have "\<exists>t6. T_E1 P2 t5 t6" using D01 D12 D23 D34 D45 unfolding defs by (auto simp: N2)
  then obtain t6 where D56: "T_E1 P2 t5 t6" by blast
  have S56: "T_StepCR t5 None t6" 
  proof -
    have "P2 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D56 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 7. P1 Call Enq A3 *)
  have "\<exists>t7. T_Call_Enq P1 t6 t7" using D01 D12 D23 D34 D45 D56 unfolding defs by (auto simp: N2)
  then obtain t7 where D67: "T_Call_Enq P1 t6 t7" by blast
  have S67: "T_StepCR t6 (Some (mk_obs enq A3 P1 call)) t7"
  proof -
    have EQ: "t_V_var t6 = A3" using D01 D12 D23 D34 D45 D56 unfolding defs by auto
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D67 have "T_StepCR t6 (Some (mk_obs enq (t_V_var t6) P1 call)) t7"
      by (intro T_StepCR.intros)
    thus ?thesis unfolding EQ by simp
  qed

  (* 8. P1 E1 *)
  have "\<exists>t8. T_E1 P1 t7 t8" using D01 D12 D23 D34 D45 D56 D67 unfolding defs by (auto simp: N2)
  then obtain t8 where D78: "T_E1 P1 t7 t8" by blast
  have S78: "T_StepCR t7 None t8" 
  proof -
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D78 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 9. P1 E2 *)
  have "\<exists>t9. T_E2 P1 t8 t9" using D01 D12 D23 D34 D45 D56 D67 D78 unfolding defs by (auto simp: N2)
  then obtain t9 where D89: "T_E2 P1 t8 t9" by blast
  have S89: "T_StepCR t8 None t9" 
  proof -
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D89 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 10. P1 E3 ret A3 *)
  have "\<exists>t10. T_E3 P1 t9 t10" using D01 D12 D23 D34 D45 D56 D67 D78 D89 unfolding defs by (auto simp: N2)
  then obtain t10 where D910: "T_E3 P1 t9 t10" by blast
  have S910: "T_StepCR t9 (Some (mk_obs enq A3 P1 ret)) t10"
  proof -
    have EQ: "t_v t9 P1 = A3" using D01 D12 D23 D34 D45 D56 D67 D78 D89 unfolding defs by auto
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D910 have "T_StepCR t9 (Some (mk_obs enq (t_v t9 P1) P1 ret)) t10"
      by (intro T_StepCR.intros)
    thus ?thesis unfolding EQ by simp
  qed

  (* 11. P1 Call Deq BOT *)
  have "\<exists>t11. T_Call_Deq P1 t10 t11" using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 unfolding defs by (auto simp: N2)
  then obtain t11 where D1011: "T_Call_Deq P1 t10 t11" by blast
  have S1011: "T_StepCR t10 (Some (mk_obs deq BOT P1 call)) t11" 
  proof -
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D1011 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 12. P1 D1 *)
  have "\<exists>t12. T_D1 P1 t11 t12" using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 D1011 unfolding defs by (auto simp: N2)
  then obtain t12 where D1112: "T_D1 P1 t11 t12" by blast
  have S1112: "T_StepCR t11 None t12" 
  proof -
    have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D1112 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 13. P1 D2_EnterLoop *)
  have "\<exists>t13. T_D2_EnterLoop P1 t12 t13" using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 D1011 D1112 unfolding defs by (auto simp: N2)
  then obtain t13 where D1213: "T_D2_EnterLoop P1 t12 t13" by blast
  have S1213: "T_StepCR t12 None t13"
  proof -
    have "T_D2 P1 t12 t13" using D1213 unfolding T_D2_def by auto
    moreover have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    ultimately show ?thesis by (intro T_StepCR.intros)
  qed

  (* 14. P1 D3_Scan P2 (strong witness) *)
  have "\<exists>t14. T_D3_Scan P1 P2 t13 t14" using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 D1011 D1112 D1213 unfolding defs by (auto simp: N2)
  then obtain t14 where D1314: "T_D3_Scan P1 P2 t13 t14" by blast
  have S1314: "T_StepCR t13 None t14"
  proof -
    (* strict isolation method: Use only the previous step (D1213) PC state, without unfolding the global history！ *)
    have "t_pc t13 P1 = ''TD_Loop''" using D1213 unfolding T_D2_EnterLoop_def by simp
    moreover have "T_D3_Scan P1 P2 t13 t14" using D1314 by simp
    ultimately have "T_D3' P1 t13 t14" unfolding T_D3'_def by blast
    moreover have "P1 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    ultimately show ?thesis by (intro T_StepCR.intros)
  qed

  (* 15. P2 E2 *)
  have "\<exists>t15. T_E2 P2 t14 t15" using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 D1011 D1112 D1213 D1314 unfolding defs by (auto simp: N2)
  then obtain t15 where D1415: "T_E2 P2 t14 t15" by blast
  have S1415: "T_StepCR t14 None t15" 
  proof -
    have "P2 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D1415 show ?thesis by (intro T_StepCR.intros)
  qed

  (* 16. P2 E3 ret A2 *)
  have "\<exists>t16. T_E3 P2 t15 t16" using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 D1011 D1112 D1213 D1314 D1415 unfolding defs by (auto simp: N2)
  then obtain t16 where D1516: "T_E3 P2 t15 t16" by blast
  have S1516: "T_StepCR t15 (Some (mk_obs enq A2 P2 ret)) t16"
  proof -
    have EQ: "t_v t15 P2 = A2" using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 D1011 D1112 D1213 D1314 D1415 unfolding defs by auto
    have "P2 \<in> ProcSet" using N2 unfolding ProcSet_def by auto
    with D1516 have "T_StepCR t15 (Some (mk_obs enq (t_v t15 P2) P2 ret)) t16"
      by (intro T_StepCR.intros)
    thus ?thesis unfolding EQ by simp
  qed

  (* ========================================================== *)
  (* Compose the path and validate the final shape *)
  (* ========================================================== *)
  have PATH: "T_Path ?t0 e1_labels t16"
    unfolding e1_labels_def
    using S01 S12 S23 S34 S45 S56 S67 S78 S89 S910 S1011 S1112 S1213 S1314 S1415 S1516
    using T_Path.cons T_Path.nil by presburger

  have SH: "E1_TSQ_shape t16"
    using D01 D12 D23 D34 D45 D56 D67 D78 D89 D910 D1011 D1112 D1213 D1314 D1415 D1516
    unfolding defs E1_TSQ_shape_def
    by auto

  show ?thesis
    using I0 PATH SH by blast
qed

lemma tsq_e2_from_e1:
  assumes N2: "N_Procs = 2"
      and SH: "E1_TSQ_shape tk"
      and INV: "TSQ_State_Inv_Plus tk"
  shows "\<exists>t2. T_Path tk e2_labels t2"
proof -
  from SH have
      PC1: "t_pc tk P1 = ''TD_Loop''"
    and SC1: "t_scanned tk P1 = {P2}"
    and CN1: "t_candNid tk P1 = BOT"
    and CT1: "t_candTs tk P1 = TOP"
    and CP1: "t_candPid tk P1 = BOT"
    and ST1: "t_startTs tk P1 = TS 4"
    and POOL1: "pools tk P1 = [(1, A1, TS 1), (3, A3, TS 3)]"
    and POOL2: "pools tk P2 = [(2, A2, TS 2)]"
    unfolding E1_TSQ_shape_def by auto

  have TS_GT_3: "TS 3 <\<^sub>t\<^sub>s TS (ts_counter tk)"
    using INV POOL1
    unfolding TSQ_State_Inv_Plus_def TSQ_State_Inv_def
    by (metis list.set_intros(1,2) ts_type.distinct(1))

  hence TC_GT_3: "ts_counter tk > 3"
    by (cases "ts_counter tk") auto

  have P1_Proc: "P1 \<in> ProcSet"
   and P2_Proc: "P2 \<in> ProcSet"
   and P1_neq_P2: "P1 \<noteq> P2"
    using N2 unfolding ProcSet_def by auto

  have ProcSet_eq: "ProcSet = {P1, P2}"
    using N2 unfolding ProcSet_def by auto

  note basic_defs = BOT_def Let_def

  (* 1. P1 D3_Scan P1 *)
  have "\<exists>t1. T_D3_Scan P1 P1 tk t1"
  proof -
    have "P1 \<notin> t_scanned tk P1"
      using SC1 P1_neq_P2 by auto
    thus ?thesis
      using PC1 POOL1 CN1 CT1 CP1 ST1 P1_Proc
      unfolding T_D3_Scan_def pool_getOldest_def
     by (intro exI) (auto simp: BOT_def Let_def)
  qed
  then obtain t1 where D01: "T_D3_Scan P1 P1 tk t1" by blast

have TPC_t1: "t_pc t1 = t_pc tk"
proof -
  from D01 show ?thesis
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools tk P1)")
       (auto simp: Let_def split: if_splits prod.splits)
qed

have PC_t1: "t_pc t1 P1 = ''TD_Loop''"
  using TPC_t1 PC1
  by simp

have TSCANNED_t1:
  "t_scanned t1 =
   (\<lambda>x. if x = P1 then insert P1 (t_scanned tk P1) else t_scanned tk x)"
proof -
  from D01 show ?thesis
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools tk P1)")
       (auto simp: Let_def split: if_splits prod.splits)
qed

have SC_t1_raw: "t_scanned t1 P1 = insert P1 (t_scanned tk P1)"
  using TSCANNED_t1 by simp

have SC_t1: "t_scanned t1 P1 = {P1, P2}"
  using SC_t1_raw SC1 P1_neq_P2
  by auto

have TPOOLS_t1: "pools t1 = pools tk"
proof -
  from D01 show ?thesis
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools tk P1)")
       (auto simp: Let_def split: if_splits prod.splits)
qed

have POOL_t1_P1: "pools t1 P1 = [(1, A1, TS 1), (3, A3, TS 3)]"
  using TPOOLS_t1 POOL1
  by simp

have POOL_t1_P2: "pools t1 P2 = [(2, A2, TS 2)]"
  using TPOOLS_t1 POOL2
  by simp

  have CN_t1: "t_candNid t1 P1 = 1"
    using D01 P1_Proc PC1 SC1 CN1 CT1 CP1 ST1 POOL1
    unfolding T_D3_Scan_def pool_getOldest_def
    by (auto simp: basic_defs split: if_splits prod.splits)

  have CT_t1: "t_candTs t1 P1 = TS 1"
    using D01 P1_Proc PC1 SC1 CN1 CT1 CP1 ST1 POOL1
    unfolding T_D3_Scan_def pool_getOldest_def
    by (auto simp: basic_defs split: if_splits prod.splits)

  have CP_t1: "t_candPid t1 P1 = P1"
    using D01 P1_Proc PC1 SC1 CN1 CT1 CP1 ST1 POOL1
    unfolding T_D3_Scan_def pool_getOldest_def
    by (auto simp: basic_defs split: if_splits prod.splits)

have TSTART_t1: "t_startTs t1 = t_startTs tk"
proof -
  from D01 show ?thesis
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools tk P1)")
       (auto simp: Let_def split: if_splits prod.splits)
qed

have ST_t1: "t_startTs t1 P1 = TS 4"
  using TSTART_t1 ST1
  by simp

have TTSC_t1: "ts_counter t1 = ts_counter tk"
proof -
  from D01 show ?thesis
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools tk P1)")
       (auto simp: Let_def split: if_splits prod.splits)
qed

have TSC_t1: "ts_counter t1 = ts_counter tk"
  using TTSC_t1 .

  have SC_t1_Proc: "t_scanned t1 P1 = ProcSet"
    using SC_t1 ProcSet_eq by simp

  have S01: "T_StepCR tk None t1"
  proof -
    have "T_D3' P1 tk t1"
      using PC1 D01 unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 2. P1 D3_Eval (remove A1) *)
  have "\<exists>t2. T_D3_Eval P1 t1 t2"
    using PC_t1 SC_t1_Proc CN_t1 CP_t1 POOL_t1_P1
    unfolding T_D3_Eval_def
   by (intro exI) (auto simp: basic_defs)
  then obtain t2 where D12: "T_D3_Eval P1 t1 t2" by blast

have RM_t1:
  "pool_remove (pools t1 (t_candPid t1 P1)) (t_candNid t1 P1) = (A1, [(3, A3, TS 3)])"
  using CN_t1 CP_t1 POOL_t1_P1
  by simp

have A1NZ: "A1 \<noteq> BOT"
  by (simp add: BOT_def)

have PC_t2: "t_pc t2 P1 = ''TD_Remove_Done''"
  using D12 SC_t1_Proc CN_t1 CP_t1 RM_t1 A1NZ
  unfolding T_D3_Eval_def
  by (simp add: Let_def split: prod.splits)

  have RET_t2: "t_retV t2 P1 = A1"
    using D12 CN_t1 CP_t1 POOL_t1_P1
    unfolding T_D3_Eval_def
    by (auto simp: basic_defs split: if_splits prod.splits)

  have POOL_t2_P1: "pools t2 P1 = [(3, A3, TS 3)]"
    using D12 CN_t1 CP_t1 POOL_t1_P1
    unfolding T_D3_Eval_def
    by (auto simp:  basic_defs split: if_splits prod.splits)

have POOL_t2_P2: "pools t2 P2 = [(2, A2, TS 2)]"
  using D12 SC_t1_Proc RM_t1 CN_t1 CP_t1 POOL_t1_P2 P1_neq_P2
  unfolding T_D3_Eval_def
  by (auto simp: Let_def split: if_splits prod.splits)

have TSTART_t2: "t_startTs t2 = t_startTs t1"
proof -
  from D12 show ?thesis
    unfolding T_D3_Eval_def
    by (cases "pool_remove (pools t1 (t_candPid t1 P1)) (t_candNid t1 P1)")
       (auto simp: Let_def split: if_splits prod.splits)
qed

have ST_t2: "t_startTs t2 P1 = TS 4"
  using TSTART_t2 ST_t1
  by simp

have TTSC_t2: "ts_counter t2 = ts_counter t1"
proof -
  from D12 show ?thesis
    unfolding T_D3_Eval_def
    by (cases "pool_remove (pools t1 (t_candPid t1 P1)) (t_candNid t1 P1)")
       (auto simp: Let_def split: if_splits prod.splits)
qed

have TSC_t2: "ts_counter t2 = ts_counter tk"
  using TTSC_t2 TSC_t1
  by simp

  have S12: "T_StepCR t1 None t2"
  proof -
    have "T_D3' P1 t1 t2"
      using PC_t1 SC_t1_Proc D12 unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 3. P1 D4 ret A1 *)
  have "\<exists>t3. T_D4 P1 t2 t3"
    using PC_t2
    unfolding T_D4_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t3 where D23: "T_D4 P1 t2 t3" by blast

  have PC_t3: "t_pc t3 P1 = ''TL0''"
    using D23
    unfolding T_D4_def
    by simp

  have POOL_t3_P1: "pools t3 P1 = [(3, A3, TS 3)]"
    using D23 POOL_t2_P1
    unfolding T_D4_def
    by simp

  have POOL_t3_P2: "pools t3 P2 = [(2, A2, TS 2)]"
    using D23 POOL_t2_P2
    unfolding T_D4_def
    by simp

  have ST_t3: "t_startTs t3 P1 = TOP"
    using D23 ST_t2
    unfolding T_D4_def
    by simp

  have TSC_t3: "ts_counter t3 = ts_counter tk"
    using D23 TSC_t2
    unfolding T_D4_def
    by simp

  have S23: "T_StepCR t2 (Some (mk_obs deq A1 P1 ret)) t3"
  proof -
    have EQ: "t_retV t2 P1 = A1"
      using RET_t2 by simp
    have "T_StepCR t2 (Some (mk_obs deq (t_retV t2 P1) P1 ret)) t3"
      using D23 P1_Proc by (intro T_StepCR.T_D4_vis)
    thus ?thesis
      unfolding EQ by simp
  qed

  (* 4. P1 Call Deq BOT *)
  have "\<exists>t4. T_Call_Deq P1 t3 t4"
    using PC_t3
    unfolding T_Call_Deq_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t4 where D34: "T_Call_Deq P1 t3 t4" by blast

  have PC_t4: "t_pc t4 P1 = ''TD1''"
    using D34
    unfolding T_Call_Deq_def
    by simp

  have POOL_t4_P1: "pools t4 P1 = [(3, A3, TS 3)]"
    using D34 POOL_t3_P1
    unfolding T_Call_Deq_def
    by simp

  have POOL_t4_P2: "pools t4 P2 = [(2, A2, TS 2)]"
    using D34 POOL_t3_P2
    unfolding T_Call_Deq_def
    by simp

  have ST_t4: "t_startTs t4 P1 = TOP"
    using D34 ST_t3
    unfolding T_Call_Deq_def
    by simp

  have TSC_t4: "ts_counter t4 = ts_counter tk"
    using D34 TSC_t3
    unfolding T_Call_Deq_def
    by simp

  have S34: "T_StepCR t3 (Some (mk_obs deq BOT P1 call)) t4"
    using D34 P1_Proc by (intro T_StepCR.T_Call_Deq_vis)

  (* 5. P1 D1 *)
  have "\<exists>t5. T_D1 P1 t4 t5"
    using PC_t4
    unfolding T_D1_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t5 where D45: "T_D1 P1 t4 t5" by blast

have t5_eq:
  "t5 =
    t4\<lparr> ts_counter := Suc (ts_counter t4),
         t_startTs := (\<lambda>x. if x = P1 then TS (ts_counter t4) else t_startTs t4 x),
         t_candNid := (\<lambda>x. if x = P1 then BOT else t_candNid t4 x),
         t_candTs  := (\<lambda>x. if x = P1 then TOP else t_candTs t4 x),
         t_candPid := (\<lambda>x. if x = P1 then BOT else t_candPid t4 x),
         t_scanned := (\<lambda>x. if x = P1 then {} else t_scanned t4 x),
         t_pc := (\<lambda>x. if x = P1 then ''TD_Line4_Done'' else t_pc t4 x)\<rparr>"
proof -
  from D45 show ?thesis
    unfolding T_D1_def
    by (simp add: Let_def)
qed

have PC_t5: "t_pc t5 P1 = ''TD_Line4_Done''"
  using t5_eq by simp

have POOL_t5_P1: "pools t5 P1 = [(3, A3, TS 3)]"
  using t5_eq POOL_t4_P1 by simp

have POOL_t5_P2: "pools t5 P2 = [(2, A2, TS 2)]"
  using t5_eq POOL_t4_P2 by simp

have ST_t5: "t_startTs t5 P1 = TS (ts_counter tk)"
  using t5_eq TSC_t4 by simp

have CN_t5: "t_candNid t5 P1 = BOT"
  using t5_eq by simp

have CT_t5: "t_candTs t5 P1 = TOP"
  using t5_eq by simp

have CP_t5: "t_candPid t5 P1 = BOT"
  using t5_eq by simp

have SC_t5: "t_scanned t5 P1 = {}"
  using t5_eq by simp

have TSC_t5: "ts_counter t5 = ts_counter tk + 1"
  using t5_eq TSC_t4 by simp

  have S45: "T_StepCR t4 None t5"
    using D45 P1_Proc by (intro T_StepCR.T_D1_tau)

  (* 6. P1 D2_EnterLoop *)
  have "\<exists>t6. T_D2_EnterLoop P1 t5 t6"
    using PC_t5
    unfolding T_D2_EnterLoop_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t6 where D56: "T_D2_EnterLoop P1 t5 t6" by blast

  have PC_t6: "t_pc t6 P1 = ''TD_Loop''"
    using D56
    unfolding T_D2_EnterLoop_def
    by simp

  have SC_t6: "t_scanned t6 P1 = {}"
    using D56
    unfolding T_D2_EnterLoop_def
    by simp

  have CN_t6: "t_candNid t6 P1 = BOT"
    using D56
    unfolding T_D2_EnterLoop_def
    by simp

  have CT_t6: "t_candTs t6 P1 = TOP"
    using D56
    unfolding T_D2_EnterLoop_def
    by simp

  have CP_t6: "t_candPid t6 P1 = BOT"
    using D56
    unfolding T_D2_EnterLoop_def
    by simp

  have POOL_t6_P1: "pools t6 P1 = [(3, A3, TS 3)]"
    using D56 POOL_t5_P1
    unfolding T_D2_EnterLoop_def
    by simp

  have POOL_t6_P2: "pools t6 P2 = [(2, A2, TS 2)]"
    using D56 POOL_t5_P2
    unfolding T_D2_EnterLoop_def
    by simp

  have ST_t6: "t_startTs t6 P1 = TS (ts_counter tk)"
    using D56 ST_t5
    unfolding T_D2_EnterLoop_def
    by simp

  have TSC_t6: "ts_counter t6 = ts_counter tk + 1"
    using D56 TSC_t5
    unfolding T_D2_EnterLoop_def
    by simp

  have S56: "T_StepCR t5 None t6"
  proof -
    have "T_D2 P1 t5 t6"
      using D56 unfolding T_D2_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D2_tau)
  qed

  (* 7. P1 D3_Scan P1 *)
  have "\<exists>t7. T_D3_Scan P1 P1 t6 t7"
  proof -
    have P1_not_sc: "P1 \<notin> t_scanned t6 P1"
      using SC_t6 by simp
    have START_OK: "\<not> ts_less (t_startTs t6 P1) (TS 3)"
      using ST_t6 TC_GT_3 by (auto simp: basic_defs)
    show ?thesis
      using PC_t6 P1_not_sc P1_Proc POOL_t6_P1 CN_t6 CT_t6 CP_t6 START_OK
      unfolding T_D3_Scan_def pool_getOldest_def
      by (intro exI) (auto simp: basic_defs)
  qed
  then obtain t7 where D67: "T_D3_Scan P1 P1 t6 t7" by blast

  have TPC_t7: "t_pc t7 = t_pc t6"
  proof -
    from D67 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t6 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TSCANNED_t7:
    "t_scanned t7 =
     (\<lambda>x. if x = P1 then insert P1 (t_scanned t6 P1) else t_scanned t6 x)"
  proof -
    from D67 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t6 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TPOOLS_t7: "pools t7 = pools t6"
  proof -
    from D67 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t6 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TSTART_t7: "t_startTs t7 = t_startTs t6"
  proof -
    from D67 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t6 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TTSC_t7: "ts_counter t7 = ts_counter t6"
  proof -
    from D67 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t6 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have PC_t7: "t_pc t7 P1 = ''TD_Loop''"
    using TPC_t7 PC_t6 by simp

  have SC_t7_raw: "t_scanned t7 P1 = insert P1 (t_scanned t6 P1)"
    using TSCANNED_t7 by simp

  have SC_t7: "t_scanned t7 P1 = {P1}"
    using SC_t7_raw SC_t6 by simp

  have POOL_t7_P1: "pools t7 P1 = [(3, A3, TS 3)]"
    using TPOOLS_t7 POOL_t6_P1 by simp

  have POOL_t7_P2: "pools t7 P2 = [(2, A2, TS 2)]"
    using TPOOLS_t7 POOL_t6_P2 by simp

  have ST_t7: "t_startTs t7 P1 = TS (ts_counter tk)"
    using TSTART_t7 ST_t6 by simp

  have TSC_t7: "ts_counter t7 = ts_counter tk + 1"
    using TTSC_t7 TSC_t6 by simp

  have CN_t7: "t_candNid t7 P1 = 3"
    using D67 TC_GT_3
    by (auto simp: T_D3_Scan_def pool_getOldest_def basic_defs
                   PC_t6 SC_t6 CN_t6 CT_t6 CP_t6
                   POOL_t6_P1 POOL_t6_P2 ST_t6 TSC_t6
             split: if_splits prod.splits)

  have CT_t7: "t_candTs t7 P1 = TS 3"
    using D67 TC_GT_3
    by (auto simp: T_D3_Scan_def pool_getOldest_def basic_defs
                   PC_t6 SC_t6 CN_t6 CT_t6 CP_t6
                   POOL_t6_P1 POOL_t6_P2 ST_t6 TSC_t6
             split: if_splits prod.splits)

  have CP_t7: "t_candPid t7 P1 = P1"
    using D67 TC_GT_3
    by (auto simp: T_D3_Scan_def pool_getOldest_def basic_defs
                   PC_t6 SC_t6 CN_t6 CT_t6 CP_t6
                   POOL_t6_P1 POOL_t6_P2 ST_t6 TSC_t6
             split: if_splits prod.splits)

  have S67: "T_StepCR t6 None t7"
  proof -
    have "T_D3' P1 t6 t7"
      using PC_t6 D67 P1_Proc unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 8. P1 D3_Scan P2 *)
  have "\<exists>t8. T_D3_Scan P1 P2 t7 t8"
  proof -
    have P2_not_sc: "P2 \<notin> t_scanned t7 P1"
      using SC_t7 P1_neq_P2 by auto
    have START_OK: "\<not> ts_less (t_startTs t7 P1) (TS 2)"
      using ST_t7 TC_GT_3 by (auto simp: basic_defs)
    show ?thesis
      using PC_t7 P2_not_sc P2_Proc POOL_t7_P2 CN_t7 CT_t7 CP_t7 START_OK
      unfolding T_D3_Scan_def pool_getOldest_def
      by (intro exI) (auto simp: basic_defs)
  qed
  then obtain t8 where D78: "T_D3_Scan P1 P2 t7 t8" by blast

  have TPC_t8: "t_pc t8 = t_pc t7"
  proof -
    from D78 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t7 P2)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TSCANNED_t8:
    "t_scanned t8 =
      (\<lambda>x. if x = P1 then insert P2 (t_scanned t7 P1) else t_scanned t7 x)"
  proof -
    from D78 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t7 P2)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TPOOLS_t8: "pools t8 = pools t7"
  proof -
    from D78 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t7 P2)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TSTART_t8: "t_startTs t8 = t_startTs t7"
  proof -
    from D78 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t7 P2)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TTSC_t8: "ts_counter t8 = ts_counter t7"
  proof -
    from D78 show ?thesis
      unfolding T_D3_Scan_def
      by (cases "pool_getOldest (pools t7 P2)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have PC_t8: "t_pc t8 P1 = ''TD_Loop''"
    using TPC_t8 PC_t7 by simp

  have SC_t8_raw: "t_scanned t8 P1 = insert P2 (t_scanned t7 P1)"
    using TSCANNED_t8 by simp

  have SC_t8: "t_scanned t8 P1 = {P1, P2}"
    using SC_t8_raw SC_t7 P1_neq_P2 by auto

  have POOL_t8_P1: "pools t8 P1 = [(3, A3, TS 3)]"
    using TPOOLS_t8 POOL_t7_P1 by simp

  have POOL_t8_P2: "pools t8 P2 = [(2, A2, TS 2)]"
    using TPOOLS_t8 POOL_t7_P2 by simp

  have P2_not_sc_t7: "P2 \<notin> t_scanned t7 P1"
    using SC_t7 P1_neq_P2 by auto

  have OG2: "pool_getOldest (pools t7 P2) = (2, TS 2)"
    using POOL_t7_P2
    unfolding pool_getOldest_def
    by simp

  have BETTER2: "TS 2 <\<^sub>t\<^sub>s t_candTs t7 P1"
    using CT_t7
    by simp

  have START_OK2: "\<not> ts_less (t_startTs t7 P1) (TS 2)"
    using ST_t7 TC_GT_3
    by simp

have D78_core:
  "(let (nid, tstamp) = pool_getOldest (pools t7 P2);
        startTs = t_startTs t7 P1;
        candTs = t_candTs t7 P1;
        update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
    in
      t8 =
        t7\<lparr> t_candNid := (\<lambda>x. if x = P1 then if update then nid else t_candNid t7 P1 else t_candNid t7 x),
             t_candTs  := (\<lambda>x. if x = P1 then if update then tstamp else t_candTs t7 P1 else t_candTs t7 x),
             t_candPid := (\<lambda>x. if x = P1 then if update then P2 else t_candPid t7 P1 else t_candPid t7 x),
             t_scanned := (\<lambda>x. if x = P1 then t_scanned t7 P1 \<union> {P2} else t_scanned t7 x)\<rparr>)"
  using D78
  unfolding T_D3_Scan_def
  by blast

have t8_eq:
  "t8 =
    t7\<lparr> t_candNid := (\<lambda>x. if x = P1 then 2 else t_candNid t7 x),
         t_candTs  := (\<lambda>x. if x = P1 then TS 2 else t_candTs t7 x),
         t_candPid := (\<lambda>x. if x = P1 then P2 else t_candPid t7 x),
         t_scanned := (\<lambda>x. if x = P1 then t_scanned t7 P1 \<union> {P2} else t_scanned t7 x)\<rparr>"
proof -
  from D78_core show ?thesis
    using OG2 BETTER2 START_OK2
    by (simp add:  basic_defs split: prod.splits)
qed 

  have CN_t8: "t_candNid t8 P1 = 2"
    using t8_eq by simp

  have CT_t8: "t_candTs t8 P1 = TS 2"
    using t8_eq by simp

  have CP_t8: "t_candPid t8 P1 = P2"
    using t8_eq by simp

  have ST_t8: "t_startTs t8 P1 = TS (ts_counter tk)"
    using TSTART_t8 ST_t7 by simp

  have TSC_t8: "ts_counter t8 = ts_counter tk + 1"
    using TTSC_t8 TSC_t7 by simp

  have TSC_t8: "ts_counter t8 = ts_counter tk + 1"
    using TTSC_t8 TSC_t7 by simp

  have SC_t8_Proc: "t_scanned t8 P1 = ProcSet"
    using SC_t8 ProcSet_eq by simp

  have S78: "T_StepCR t7 None t8"
  proof -
    have "T_D3' P1 t7 t8"
      using PC_t7 D78 unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 9. P1 D3_Eval (remove A2) *)
  have RM_t8:
    "pool_remove (pools t8 (t_candPid t8 P1)) (t_candNid t8 P1) = (A2, [])"
    using CN_t8 CP_t8 POOL_t8_P2
    by simp

  have A2NZ: "A2 \<noteq> BOT"
    by (simp add: BOT_def)

  have "\<exists>t9. T_D3_Eval P1 t8 t9"
    using SC_t8_Proc CN_t8 CP_t8 RM_t8 A2NZ
    unfolding T_D3_Eval_def
    by (simp add: PC_t8)

  then obtain t9 where D89: "T_D3_Eval P1 t8 t9" by blast

  have PC_t9: "t_pc t9 P1 = ''TD_Remove_Done''"
    using D89 SC_t8_Proc CN_t8 CP_t8 RM_t8 A2NZ
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have RET_t9: "t_retV t9 P1 = A2"
    using D89 SC_t8_Proc CN_t8 CP_t8 RM_t8 A2NZ
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have POOL_t9_P1: "pools t9 P1 = [(3, A3, TS 3)]"
    using D89 SC_t8_Proc CN_t8 CP_t8 RM_t8 A2NZ POOL_t8_P1 P1_neq_P2
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have POOL_t9_P2: "pools t9 P2 = []"
    using D89 SC_t8_Proc CN_t8 CP_t8 RM_t8 A2NZ
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have TSTART_t9: "t_startTs t9 = t_startTs t8"
  proof -
    from D89 show ?thesis
      unfolding T_D3_Eval_def
      by (cases "pool_remove (pools t8 (t_candPid t8 P1)) (t_candNid t8 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have ST_t9: "t_startTs t9 P1 = TS (ts_counter tk)"
    using TSTART_t9 ST_t8
    by simp

  have TTSC_t9: "ts_counter t9 = ts_counter t8"
  proof -
    from D89 show ?thesis
      unfolding T_D3_Eval_def
      by (cases "pool_remove (pools t8 (t_candPid t8 P1)) (t_candNid t8 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TSC_t9: "ts_counter t9 = ts_counter tk + 1"
    using TTSC_t9 TSC_t8
    by simp

  have S89: "T_StepCR t8 None t9"
  proof -
    have "T_D3' P1 t8 t9"
      using PC_t8 SC_t8_Proc D89
      unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 10. P1 D4 ret A2 *)
  have "\<exists>t10. T_D4 P1 t9 t10"
    using PC_t9
    unfolding T_D4_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t10 where D910: "T_D4 P1 t9 t10" by blast

  have PC_t10: "t_pc t10 P1 = ''TL0''"
    using D910
    unfolding T_D4_def
    by simp

  have POOL_t10_P1: "pools t10 P1 = [(3, A3, TS 3)]"
    using D910 POOL_t9_P1
    unfolding T_D4_def
    by simp

  have POOL_t10_P2: "pools t10 P2 = []"
    using D910 POOL_t9_P2
    unfolding T_D4_def
    by simp

  have ST_t10: "t_startTs t10 P1 = TOP"
    using D910 ST_t9
    unfolding T_D4_def
    by simp

  have TSC_t10: "ts_counter t10 = ts_counter tk + 1"
    using D910 TSC_t9
    unfolding T_D4_def
    by simp

  have S910: "T_StepCR t9 (Some (mk_obs deq A2 P1 ret)) t10"
  proof -
    have EQ: "t_retV t9 P1 = A2"
      using RET_t9 by simp
    have "T_StepCR t9 (Some (mk_obs deq (t_retV t9 P1) P1 ret)) t10"
      using D910 P1_Proc by (intro T_StepCR.T_D4_vis)
    thus ?thesis
      unfolding EQ by simp
  qed

  (* 11. P1 Call Deq BOT *)
  have "\<exists>t11. T_Call_Deq P1 t10 t11"
    using PC_t10
    unfolding T_Call_Deq_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t11 where D1011: "T_Call_Deq P1 t10 t11" by blast

  have PC_t11: "t_pc t11 P1 = ''TD1''"
    using D1011
    unfolding T_Call_Deq_def
    by simp

  have POOL_t11_P1: "pools t11 P1 = [(3, A3, TS 3)]"
    using D1011 POOL_t10_P1
    unfolding T_Call_Deq_def
    by simp

  have POOL_t11_P2: "pools t11 P2 = []"
    using D1011 POOL_t10_P2
    unfolding T_Call_Deq_def
    by simp

  have ST_t11: "t_startTs t11 P1 = TOP"
    using D1011 ST_t10
    unfolding T_Call_Deq_def
    by simp

  have TSC_t11: "ts_counter t11 = ts_counter tk + 1"
    using D1011 TSC_t10
    unfolding T_Call_Deq_def
    by simp

  have S1011: "T_StepCR t10 (Some (mk_obs deq BOT P1 call)) t11"
    using D1011 P1_Proc by (intro T_StepCR.T_Call_Deq_vis)

  (* 12. P1 D1 *)
  have "\<exists>t12. T_D1 P1 t11 t12"
    using PC_t11
    unfolding T_D1_def
    by (intro exI) (auto simp: basic_defs)

  then obtain t12 where D1112: "T_D1 P1 t11 t12" by blast

  have t12_eq:
    "t12 =
      t11\<lparr> ts_counter := Suc (ts_counter t11),
           t_startTs := (\<lambda>x. if x = P1 then TS (ts_counter t11) else t_startTs t11 x),
           t_candNid := (\<lambda>x. if x = P1 then BOT else t_candNid t11 x),
           t_candTs  := (\<lambda>x. if x = P1 then TOP else t_candTs t11 x),
           t_candPid := (\<lambda>x. if x = P1 then BOT else t_candPid t11 x),
           t_scanned := (\<lambda>x. if x = P1 then {} else t_scanned t11 x),
           t_pc := (\<lambda>x. if x = P1 then ''TD_Line4_Done'' else t_pc t11 x)\<rparr>"
  proof -
    from D1112 show ?thesis
      unfolding T_D1_def
      by (simp add: Let_def)
  qed

  have PC_t12: "t_pc t12 P1 = ''TD_Line4_Done''"
    using t12_eq by simp

  have POOL_t12_P1: "pools t12 P1 = [(3, A3, TS 3)]"
    using t12_eq POOL_t11_P1 by simp

  have POOL_t12_P2: "pools t12 P2 = []"
    using t12_eq POOL_t11_P2 by simp

  have ST_t12: "t_startTs t12 P1 = TS (ts_counter tk + 1)"
    using t12_eq TSC_t11 by simp

  have CN_t12: "t_candNid t12 P1 = BOT"
    using t12_eq by simp

  have CT_t12: "t_candTs t12 P1 = TOP"
    using t12_eq by simp

  have CP_t12: "t_candPid t12 P1 = BOT"
    using t12_eq by simp

  have SC_t12: "t_scanned t12 P1 = {}"
    using t12_eq by simp

  have TSC_t12: "ts_counter t12 = ts_counter tk + 2"
    using t12_eq TSC_t11 by simp

  have S1112: "T_StepCR t11 None t12"
    using D1112 P1_Proc by (intro T_StepCR.T_D1_tau)

  (* 13. P1 D2_EnterLoop *)
  have "\<exists>t13. T_D2_EnterLoop P1 t12 t13"
    using PC_t12
    unfolding T_D2_EnterLoop_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t13 where D1213: "T_D2_EnterLoop P1 t12 t13" by blast

  have PC_t13: "t_pc t13 P1 = ''TD_Loop''"
    using D1213
    unfolding T_D2_EnterLoop_def
    by simp

  have SC_t13: "t_scanned t13 P1 = {}"
    using D1213
    unfolding T_D2_EnterLoop_def
    by simp

  have CN_t13: "t_candNid t13 P1 = BOT"
    using D1213
    unfolding T_D2_EnterLoop_def
    by simp

  have CT_t13: "t_candTs t13 P1 = TOP"
    using D1213
    unfolding T_D2_EnterLoop_def
    by simp

  have CP_t13: "t_candPid t13 P1 = BOT"
    using D1213
    unfolding T_D2_EnterLoop_def
    by simp

  have POOL_t13_P1: "pools t13 P1 = [(3, A3, TS 3)]"
    using D1213 POOL_t12_P1
    unfolding T_D2_EnterLoop_def
    by simp

  have POOL_t13_P2: "pools t13 P2 = []"
    using D1213 POOL_t12_P2
    unfolding T_D2_EnterLoop_def
    by simp

  have ST_t13: "t_startTs t13 P1 = TS (ts_counter tk + 1)"
    using D1213 ST_t12
    unfolding T_D2_EnterLoop_def
    by simp

  have TSC_t13: "ts_counter t13 = ts_counter tk + 2"
    using D1213 TSC_t12
    unfolding T_D2_EnterLoop_def
    by simp

  have S1213: "T_StepCR t12 None t13"
  proof -
    have "T_D2 P1 t12 t13"
      using D1213 unfolding T_D2_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D2_tau)
  qed

  (* 14. P1 D3_Scan P1 *)
  have "\<exists>t14. T_D3_Scan P1 P1 t13 t14"
  proof -
    have P1_not_sc: "P1 \<notin> t_scanned t13 P1"
      using SC_t13 by simp
    have START_OK3: "\<not> ts_less (t_startTs t13 P1) (TS 3)"
      using ST_t13 TC_GT_3
      by (auto simp: basic_defs)
    show ?thesis
      using PC_t13 P1_not_sc P1_Proc POOL_t13_P1 CN_t13 CT_t13 CP_t13 START_OK3
      unfolding T_D3_Scan_def pool_getOldest_def
      by (intro exI) (auto simp: basic_defs)
  qed
  then obtain t14 where D1314: "T_D3_Scan P1 P1 t13 t14" by blast

  have OG3: "pool_getOldest (pools t13 P1) = (3, TS 3)"
    using POOL_t13_P1
    unfolding pool_getOldest_def
    by simp

  have BETTER3: "TS 3 <\<^sub>t\<^sub>s t_candTs t13 P1"
    using CT_t13
    by (simp add: basic_defs)

  have START_OK3: "\<not> ts_less (t_startTs t13 P1) (TS 3)"
    using ST_t13 TC_GT_3
    by (auto simp: basic_defs)

  have D1314_core:
    "(let (nid, tstamp) = pool_getOldest (pools t13 P1);
          startTs = t_startTs t13 P1;
          candTs = t_candTs t13 P1;
          update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
      in
        t14 =
          t13\<lparr> t_candNid := (\<lambda>x. if x = P1 then if update then nid else t_candNid t13 P1 else t_candNid t13 x),
               t_candTs  := (\<lambda>x. if x = P1 then if update then tstamp else t_candTs t13 P1 else t_candTs t13 x),
               t_candPid := (\<lambda>x. if x = P1 then if update then P1 else t_candPid t13 P1 else t_candPid t13 x),
               t_scanned := (\<lambda>x. if x = P1 then t_scanned t13 P1 \<union> {P1} else t_scanned t13 x)\<rparr>)"
    using D1314
    unfolding T_D3_Scan_def
    by blast

  have t14_eq:
    "t14 =
      t13\<lparr> t_candNid := (\<lambda>x. if x = P1 then 3 else t_candNid t13 x),
           t_candTs  := (\<lambda>x. if x = P1 then TS 3 else t_candTs t13 x),
           t_candPid := (\<lambda>x. if x = P1 then P1 else t_candPid t13 x),
           t_scanned := (\<lambda>x. if x = P1 then t_scanned t13 P1 \<union> {P1} else t_scanned t13 x)\<rparr>"
    using D1314_core OG3 BETTER3 START_OK3
    by (simp add:  basic_defs split: prod.splits)

  have TPC_t14: "t_pc t14 = t_pc t13"
    using D1314
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools t13 P1)")
       (auto simp: Let_def split: if_splits prod.splits)

  have TPOOLS_t14: "pools t14 = pools t13"
    using D1314
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools t13 P1)")
       (auto simp: Let_def split: if_splits prod.splits)

  have TSTART_t14: "t_startTs t14 = t_startTs t13"
    using D1314
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools t13 P1)")
       (auto simp: Let_def split: if_splits prod.splits)

  have TTSC_t14: "ts_counter t14 = ts_counter t13"
    using D1314
    unfolding T_D3_Scan_def
    by (cases "pool_getOldest (pools t13 P1)")
       (auto simp: Let_def split: if_splits prod.splits)

  have PC_t14: "t_pc t14 P1 = ''TD_Loop''"
    using TPC_t14 PC_t13 by simp

  have SC_t14_raw: "t_scanned t14 P1 = t_scanned t13 P1 \<union> {P1}"
    using t14_eq by simp

  have SC_t14: "t_scanned t14 P1 = {P1}"
    using SC_t14_raw SC_t13 by simp

  have POOL_t14_P1: "pools t14 P1 = [(3, A3, TS 3)]"
    using TPOOLS_t14 POOL_t13_P1 by simp

  have POOL_t14_P2: "pools t14 P2 = []"
    using TPOOLS_t14 POOL_t13_P2 by simp

  have CN_t14: "t_candNid t14 P1 = 3"
    using t14_eq by simp

  have CT_t14: "t_candTs t14 P1 = TS 3"
    using t14_eq by simp

  have CP_t14: "t_candPid t14 P1 = P1"
    using t14_eq by simp

  have ST_t14: "t_startTs t14 P1 = TS (ts_counter tk + 1)"
    using TSTART_t14 ST_t13 by simp

  have TSC_t14: "ts_counter t14 = ts_counter tk + 2"
    using TTSC_t14 TSC_t13 by simp

  have S1314: "T_StepCR t13 None t14"
  proof -
    have "T_D3' P1 t13 t14"
      using PC_t13 D1314 unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 15. P1 D3_Scan P2 (empty pool, candidate unchanged) *)
  have "\<exists>t15. T_D3_Scan P1 P2 t14 t15"
  proof -
    have P2_not_sc: "P2 \<notin> t_scanned t14 P1"
      using SC_t14 P1_neq_P2 by auto
    show ?thesis
      using PC_t14 P2_not_sc P2_Proc POOL_t14_P2 CN_t14 CT_t14 CP_t14
      unfolding T_D3_Scan_def pool_getOldest_def
      by (intro exI) (auto simp: basic_defs)
  qed
  then obtain t15 where D1415: "T_D3_Scan P1 P2 t14 t15" by blast

  have OG4: "pool_getOldest (pools t14 P2) = (BOT, TOP)"
    using POOL_t14_P2
    unfolding pool_getOldest_def
    by simp

  have D1415_core:
    "(let (nid, tstamp) = pool_getOldest (pools t14 P2);
          startTs = t_startTs t14 P1;
          candTs = t_candTs t14 P1;
          update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
      in
        t15 =
          t14\<lparr> t_candNid := (\<lambda>x. if x = P1 then if update then nid else t_candNid t14 P1 else t_candNid t14 x),
               t_candTs  := (\<lambda>x. if x = P1 then if update then tstamp else t_candTs t14 P1 else t_candTs t14 x),
               t_candPid := (\<lambda>x. if x = P1 then if update then P2 else t_candPid t14 P1 else t_candPid t14 x),
               t_scanned := (\<lambda>x. if x = P1 then t_scanned t14 P1 \<union> {P2} else t_scanned t14 x)\<rparr>)"
    using D1415
    unfolding T_D3_Scan_def
    by blast

  have t15_eq:
    "t15 =
      t14\<lparr> t_candNid := (\<lambda>x. if x = P1 then t_candNid t14 P1 else t_candNid t14 x),
           t_candTs  := (\<lambda>x. if x = P1 then t_candTs t14 P1 else t_candTs t14 x),
           t_candPid := (\<lambda>x. if x = P1 then t_candPid t14 P1 else t_candPid t14 x),
           t_scanned := (\<lambda>x. if x = P1 then t_scanned t14 P1 \<union> {P2} else t_scanned t14 x)\<rparr>"
    using D1415_core OG4
    by (simp add:  basic_defs split: prod.splits)

  have PC_t15: "t_pc t15 P1 = ''TD_Loop''"
    using t15_eq PC_t14 by simp

  have SC_t15_raw: "t_scanned t15 P1 = t_scanned t14 P1 \<union> {P2}"
    using t15_eq by simp

  have SC_t15: "t_scanned t15 P1 = {P1, P2}"
    using SC_t15_raw SC_t14 P1_neq_P2 by auto

  have POOL_t15_P1: "pools t15 P1 = [(3, A3, TS 3)]"
    using t15_eq POOL_t14_P1 by simp

  have POOL_t15_P2: "pools t15 P2 = []"
    using t15_eq POOL_t14_P2 by simp

  have CN_t15: "t_candNid t15 P1 = 3"
    using t15_eq CN_t14 by simp

  have CT_t15: "t_candTs t15 P1 = TS 3"
    using t15_eq CT_t14 by simp

  have CP_t15: "t_candPid t15 P1 = P1"
    using t15_eq CP_t14 by simp

  have ST_t15: "t_startTs t15 P1 = TS (ts_counter tk + 1)"
    using t15_eq ST_t14 by simp

  have TSC_t15: "ts_counter t15 = ts_counter tk + 2"
    using t15_eq TSC_t14 by simp

  have SC_t15_Proc: "t_scanned t15 P1 = ProcSet"
    using SC_t15 ProcSet_eq by simp

  have S1415: "T_StepCR t14 None t15"
  proof -
    have "T_D3' P1 t14 t15"
      using PC_t14 D1415 unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 16. P1 D3_Eval (remove A3) *)
  have RM_t15:
    "pool_remove (pools t15 (t_candPid t15 P1)) (t_candNid t15 P1) = (A3, [])"
    using CN_t15 CP_t15 POOL_t15_P1
    by simp

  have A3NZ: "A3 \<noteq> BOT"
    using BOT_def by linarith

  have "\<exists>t16. T_D3_Eval P1 t15 t16"
    using SC_t15_Proc CN_t15 CP_t15 RM_t15 A3NZ
    unfolding T_D3_Eval_def
    using PC_t15 by force

  then obtain t16 where D1516: "T_D3_Eval P1 t15 t16" by blast

  have PC_t16: "t_pc t16 P1 = ''TD_Remove_Done''"
    using D1516 SC_t15_Proc CN_t15 CP_t15 RM_t15 A3NZ
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have RET_t16: "t_retV t16 P1 = A3"
    using D1516 SC_t15_Proc CN_t15 CP_t15 RM_t15 A3NZ
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have POOL_t16_P1: "pools t16 P1 = []"
    using D1516 SC_t15_Proc CN_t15 CP_t15 RM_t15 A3NZ
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have POOL_t16_P2: "pools t16 P2 = []"
    using D1516 SC_t15_Proc CN_t15 CP_t15 RM_t15 A3NZ POOL_t15_P2 P1_neq_P2
    unfolding T_D3_Eval_def
    by (simp add: Let_def split: prod.splits)

  have TSTART_t16: "t_startTs t16 = t_startTs t15"
  proof -
    from D1516 show ?thesis
      unfolding T_D3_Eval_def
      by (cases "pool_remove (pools t15 (t_candPid t15 P1)) (t_candNid t15 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have ST_t16: "t_startTs t16 P1 = TS (ts_counter tk + 1)"
    using TSTART_t16 ST_t15
    by simp

  have TTSC_t16: "ts_counter t16 = ts_counter t15"
  proof -
    from D1516 show ?thesis
      unfolding T_D3_Eval_def
      by (cases "pool_remove (pools t15 (t_candPid t15 P1)) (t_candNid t15 P1)")
         (auto simp: Let_def split: if_splits prod.splits)
  qed

  have TSC_t16: "ts_counter t16 = ts_counter tk + 2"
    using TTSC_t16 TSC_t15
    by simp

  have S1516: "T_StepCR t15 None t16"
  proof -
    have "T_D3' P1 t15 t16"
      using PC_t15 SC_t15_Proc D1516
      unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  (* 17. P1 D4 ret A3 *)
  have "\<exists>t17. T_D4 P1 t16 t17"
    using PC_t16
    unfolding T_D4_def
    by (intro exI) (auto simp: basic_defs)
  then obtain t17 where D1617: "T_D4 P1 t16 t17" by blast

  have S1617: "T_StepCR t16 (Some (mk_obs deq A3 P1 ret)) t17"
  proof -
    have EQ: "t_retV t16 P1 = A3"
      using RET_t16 by simp
    have "T_StepCR t16 (Some (mk_obs deq (t_retV t16 P1) P1 ret)) t17"
      using D1617 P1_Proc by (intro T_StepCR.T_D4_vis)
    thus ?thesis
      unfolding EQ by simp
  qed

  have PATH: "T_Path tk e2_labels t17"
    unfolding e2_labels_def
    apply (rule T_Path.cons[OF S01])
    apply (rule T_Path.cons[OF S12])
    apply (rule T_Path.cons[OF S23])
    apply (rule T_Path.cons[OF S34])
    apply (rule T_Path.cons[OF S45])
    apply (rule T_Path.cons[OF S56])
    apply (rule T_Path.cons[OF S67])
    apply (rule T_Path.cons[OF S78])
    apply (rule T_Path.cons[OF S89])
    apply (rule T_Path.cons[OF S910])
    apply (rule T_Path.cons[OF S1011])
    apply (rule T_Path.cons[OF S1112])
    apply (rule T_Path.cons[OF S1213])
    apply (rule T_Path.cons[OF S1314])
    apply (rule T_Path.cons[OF S1415])
    apply (rule T_Path.cons[OF S1516])
    apply (rule T_Path.cons[OF S1617])
    apply (rule T_Path.nil)
    done

  thus ?thesis
    by blast
qed

(* ========================================================== *)
(* 3. Derive existence of the e3 path from the E1 shape *)
(* ========================================================== *)
lemma tsq_e3_from_e1:
  assumes N2: "N_Procs = 2"
      and SH: "E1_TSQ_shape tk"
      and INV: "TSQ_State_Inv_Plus tk"
      and PC2: "t_pc tk P2 = ''TL0''"
  shows "\<exists>t3. T_Path tk e3_labels t3"
proof -
  from SH have
      PC1: "t_pc tk P1 = ''TD_Loop''"
    and SC1: "t_scanned tk P1 = {P2}"
    and CN1: "t_candNid tk P1 = BOT"
    and CT1: "t_candTs tk P1 = TOP"
    and CP1: "t_candPid tk P1 = BOT"
    and ST1: "t_startTs tk P1 = TS 4"
    and POOL1: "pools tk P1 = [(1, A1, TS 1), (3, A3, TS 3)]"
    and POOL2: "pools tk P2 = [(2, A2, TS 2)]"
    unfolding E1_TSQ_shape_def by auto

  have TS_GT_3: "TS 3 <\<^sub>t\<^sub>s TS (ts_counter tk)"
    using INV POOL1
    unfolding TSQ_State_Inv_Plus_def TSQ_State_Inv_def
    by (metis list.set_intros(1,2) ts_type.distinct(1))

  hence TC_GT_3: "ts_counter tk > 3"
    by (cases "ts_counter tk") auto

  have P1_Proc: "P1 \<in> ProcSet"
   and P2_Proc: "P2 \<in> ProcSet"
   and P1_neq_P2: "P1 \<noteq> P2"
    using N2 unfolding ProcSet_def by auto

  have ProcSet_eq: "ProcSet = {P1, P2}"
    using N2 unfolding ProcSet_def by auto

  note basic_defs = BOT_def Let_def

  define u1 where
    "u1 = tk\<lparr> t_pc := (\<lambda>x. if x = P2 then ''TD1'' else t_pc tk x) \<rparr>"

  define u2 where
    "u2 = u1\<lparr>
      ts_counter := ts_counter tk + 1,
      t_startTs := (\<lambda>x. if x = P2 then TS (ts_counter tk) else t_startTs u1 x),
      t_candNid := (\<lambda>x. if x = P2 then BOT else t_candNid u1 x),
      t_candTs := (\<lambda>x. if x = P2 then TOP else t_candTs u1 x),
      t_candPid := (\<lambda>x. if x = P2 then BOT else t_candPid u1 x),
      t_scanned := (\<lambda>x. if x = P2 then {} else t_scanned u1 x),
      t_pc := (\<lambda>x. if x = P2 then ''TD_Line4_Done'' else t_pc u1 x)\<rparr>"

  define u3 where
    "u3 = u2\<lparr>
      t_pc := (\<lambda>x. if x = P2 then ''TD_Loop'' else t_pc u2 x),
      t_scanned := (\<lambda>x. if x = P2 then {} else t_scanned u2 x),
      t_candNid := (\<lambda>x. if x = P2 then BOT else t_candNid u2 x),
      t_candPid := (\<lambda>x. if x = P2 then BOT else t_candPid u2 x),
      t_candTs  := (\<lambda>x. if x = P2 then TOP else t_candTs u2 x)\<rparr>"

  define u4 where
    "u4 = u3\<lparr>
      t_candNid := (\<lambda>x. if x = P2 then 1 else t_candNid u3 x),
      t_candTs  := (\<lambda>x. if x = P2 then TS 1 else t_candTs u3 x),
      t_candPid := (\<lambda>x. if x = P2 then P1 else t_candPid u3 x),
      t_scanned := (\<lambda>x. if x = P2 then {P1} else t_scanned u3 x)\<rparr>"

  define u5 where
    "u5 = u4\<lparr>
      t_scanned := (\<lambda>x. if x = P2 then ProcSet else t_scanned u4 x)\<rparr>"

  define u6 where
    "u6 = u5\<lparr>
      pools := (\<lambda>x. if x = P1 then [(3, A3, TS 3)] else pools u5 x),
      t_retV := (\<lambda>x. if x = P2 then A1 else t_retV u5 x),
      t_pc := (\<lambda>x. if x = P2 then ''TD_Remove_Done'' else t_pc u5 x)\<rparr>"

  define u7 where
    "u7 = u6\<lparr>
      t_pc := (\<lambda>x. if x = P2 then ''TL0'' else t_pc u6 x),
      t_startTs := (\<lambda>x. if x = P2 then TOP else t_startTs u6 x),
      t_candNid := (\<lambda>x. if x = P2 then BOT else t_candNid u6 x),
      t_candTs := (\<lambda>x. if x = P2 then TOP else t_candTs u6 x),
      t_candPid := (\<lambda>x. if x = P2 then BOT else t_candPid u6 x),
      t_scanned := (\<lambda>x. if x = P2 then {} else t_scanned u6 x),
      t_retV := (\<lambda>x. if x = P2 then BOT else t_retV u6 x)\<rparr>"

  define u8 where
    "u8 = u7\<lparr>
      t_candNid := (\<lambda>x. if x = P1 then 3 else t_candNid u7 x),
      t_candTs  := (\<lambda>x. if x = P1 then TS 3 else t_candTs u7 x),
      t_candPid := (\<lambda>x. if x = P1 then P1 else t_candPid u7 x),
      t_scanned := (\<lambda>x. if x = P1 then ProcSet else t_scanned u7 x)\<rparr>"

  define u9 where
    "u9 = u8\<lparr>
      pools := (\<lambda>x. if x = P1 then [] else pools u8 x),
      t_retV := (\<lambda>x. if x = P1 then A3 else t_retV u8 x),
      t_pc := (\<lambda>x. if x = P1 then ''TD_Remove_Done'' else t_pc u8 x)\<rparr>"

  define t3 where
    "t3 = u9\<lparr>
      t_pc := (\<lambda>x. if x = P1 then ''TL0'' else t_pc u9 x),
      t_startTs := (\<lambda>x. if x = P1 then TOP else t_startTs u9 x),
      t_candNid := (\<lambda>x. if x = P1 then BOT else t_candNid u9 x),
      t_candTs := (\<lambda>x. if x = P1 then TOP else t_candTs u9 x),
      t_candPid := (\<lambda>x. if x = P1 then BOT else t_candPid u9 x),
      t_scanned := (\<lambda>x. if x = P1 then {} else t_scanned u9 x),
      t_retV := (\<lambda>x. if x = P1 then BOT else t_retV u9 x)\<rparr>"

  have D01: "T_Call_Deq P2 tk u1"
    unfolding T_Call_Deq_def u1_def
    using PC2
    by (auto simp: basic_defs)

  have S01: "T_StepCR tk (Some (mk_obs deq BOT P2 call)) u1"
    using D01 P2_Proc
    by (intro T_StepCR.T_Call_Deq_vis)

  have D12: "T_D1 P2 u1 u2"
    unfolding T_D1_def u1_def u2_def
    using PC2
    by (auto simp: basic_defs)

  have S12: "T_StepCR u1 None u2"
    using D12 P2_Proc
    by (intro T_StepCR.T_D1_tau)

  have D23_loop: "T_D2_EnterLoop P2 u2 u3"
    unfolding T_D2_EnterLoop_def u2_def u3_def
    by (auto simp: basic_defs)

  have D23: "T_D2 P2 u2 u3"
    using D23_loop unfolding T_D2_def by blast

  have S23: "T_StepCR u2 None u3"
    using D23 P2_Proc
    by (intro T_StepCR.T_D2_tau)

  have U3_PC2: "t_pc u3 P2 = ''TD_Loop''"
    unfolding u3_def u2_def u1_def
    by simp

  have U3_SC2: "t_scanned u3 P2 = {}"
    unfolding u3_def u2_def u1_def
    by simp

  have U3_CN2: "t_candNid u3 P2 = BOT"
    unfolding u3_def u2_def u1_def
    by simp

  have U3_CT2: "t_candTs u3 P2 = TOP"
    unfolding u3_def u2_def u1_def
    by simp

  have U3_CP2: "t_candPid u3 P2 = BOT"
    unfolding u3_def u2_def u1_def
    by simp

  have U3_ST2: "t_startTs u3 P2 = TS (ts_counter tk)"
    unfolding u3_def u2_def u1_def
    by simp

  have U3_POOL1: "pools u3 P1 = [(1, A1, TS 1), (3, A3, TS 3)]"
    unfolding u3_def u2_def u1_def
    using POOL1 by simp

  have U3_P1_not_sc: "P1 \<notin> t_scanned u3 P2"
    using U3_SC2 by simp

  have OG1: "pool_getOldest (pools u3 P1) = (1, TS 1)"
    using U3_POOL1
    unfolding pool_getOldest_def
    by simp

  have START_OK1: "\<not> ts_less (t_startTs u3 P2) (TS 1)"
    using U3_ST2 TC_GT_3
    by (auto simp: basic_defs)

have D34_body:
  "(let (nid, tstamp) = pool_getOldest (pools u3 P1);
        startTs = t_startTs u3 P2;
        candTs = t_candTs u3 P2;
        update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
    in
      u4 =
        u3\<lparr>
          t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u3 P2 else t_candNid u3 x),
          t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u3 P2 else t_candTs u3 x),
          t_candPid := (\<lambda>x. if x = P2 then if update then P1 else t_candPid u3 P2 else t_candPid u3 x),
          t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
        \<rparr>)"
proof -
  have H1:
    "u4 =
      u3\<lparr>
        t_candNid := (\<lambda>x. if x = P2 then A1 else t_candNid u3 x),
        t_candTs  := (\<lambda>x. if x = P2 then TS A1 else t_candTs u3 x),
        t_candPid := (\<lambda>x. if x = P2 then P1 else t_candPid u3 x),
        t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
      \<rparr>"
    using U3_SC2
    unfolding u4_def
    by (metis sup_bot_left)

have H2a:
  "(let (nid, tstamp) = pool_getOldest (pools u3 P1);
        startTs = t_startTs u3 P2;
        candTs = t_candTs u3 P2;
        update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
    in
      u3\<lparr>
        t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u3 P2 else t_candNid u3 x),
        t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u3 P2 else t_candTs u3 x),
        t_candPid := (\<lambda>x. if x = P2 then if update then P1 else t_candPid u3 P2 else t_candPid u3 x),
        t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
      \<rparr>) =
   (let startTs = t_startTs u3 P2;
        candTs = t_candTs u3 P2;
        update = A1 \<noteq> BOT \<and> TS A1 <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s TS A1
    in
      u3\<lparr>
        t_candNid := (\<lambda>x. if x = P2 then if update then A1 else t_candNid u3 P2 else t_candNid u3 x),
        t_candTs  := (\<lambda>x. if x = P2 then if update then TS A1 else t_candTs u3 P2 else t_candTs u3 x),
        t_candPid := (\<lambda>x. if x = P2 then if update then P1 else t_candPid u3 P2 else t_candPid u3 x),
        t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
      \<rparr>)"
  using OG1
  by (metis case_prod_conv)

have UPD_TRUE:
  "A1 \<noteq> BOT \<and> TS A1 <\<^sub>t\<^sub>s t_candTs u3 P2 \<and> \<not> t_startTs u3 P2 <\<^sub>t\<^sub>s TS A1"
  using U3_CT2 START_OK1
  by (simp add: basic_defs)

have H2b:
  "(let startTs = t_startTs u3 P2;
        candTs = t_candTs u3 P2;
        update = A1 \<noteq> BOT \<and> TS A1 <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s TS A1
    in
      u3\<lparr>
        t_candNid := (\<lambda>x. if x = P2 then if update then A1 else t_candNid u3 P2 else t_candNid u3 x),
        t_candTs  := (\<lambda>x. if x = P2 then if update then TS A1 else t_candTs u3 P2 else t_candTs u3 x),
        t_candPid := (\<lambda>x. if x = P2 then if update then P1 else t_candPid u3 P2 else t_candPid u3 x),
        t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
      \<rparr>) =
   u3\<lparr>
     t_candNid := (\<lambda>x. if x = P2 then A1 else t_candNid u3 x),
     t_candTs  := (\<lambda>x. if x = P2 then TS A1 else t_candTs u3 x),
     t_candPid := (\<lambda>x. if x = P2 then P1 else t_candPid u3 x),
     t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
   \<rparr>"
  using UPD_TRUE
  by simp

have H2:
  "(let (nid, tstamp) = pool_getOldest (pools u3 P1);
        startTs = t_startTs u3 P2;
        candTs = t_candTs u3 P2;
        update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
    in
      u3\<lparr>
        t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u3 P2 else t_candNid u3 x),
        t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u3 P2 else t_candTs u3 x),
        t_candPid := (\<lambda>x. if x = P2 then if update then P1 else t_candPid u3 P2 else t_candPid u3 x),
        t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
      \<rparr>) =
   u3\<lparr>
     t_candNid := (\<lambda>x. if x = P2 then A1 else t_candNid u3 x),
     t_candTs  := (\<lambda>x. if x = P2 then TS A1 else t_candTs u3 x),
     t_candPid := (\<lambda>x. if x = P2 then P1 else t_candPid u3 x),
     t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
   \<rparr>"
  using H2a H2b
  by simp

have H1_sym:
  "u3\<lparr>
     t_candNid := (\<lambda>x. if x = P2 then A1 else t_candNid u3 x),
     t_candTs  := (\<lambda>x. if x = P2 then TS A1 else t_candTs u3 x),
     t_candPid := (\<lambda>x. if x = P2 then P1 else t_candPid u3 x),
     t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
   \<rparr> = u4"
  using H1 by simp

have H3:
  "(let (nid, tstamp) = pool_getOldest (pools u3 P1);
        startTs = t_startTs u3 P2;
        candTs = t_candTs u3 P2;
        update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
    in
      u3\<lparr>
        t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u3 P2 else t_candNid u3 x),
        t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u3 P2 else t_candTs u3 x),
        t_candPid := (\<lambda>x. if x = P2 then if update then P1 else t_candPid u3 P2 else t_candPid u3 x),
        t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
      \<rparr>) = u4"
  using H2 H1_sym by simp

show ?thesis
  using H3
  by auto
qed

  have D34: "T_D3_Scan P2 P1 u3 u4"
  proof -
    show ?thesis
      unfolding T_D3_Scan_def
    proof (intro conjI)
      show "t_pc u3 P2 = ''TD_Loop''"
        using U3_PC2 .
      show "P1 \<notin> t_scanned u3 P2"
        using U3_P1_not_sc .
      show "P1 \<in> ProcSet"
        using P1_Proc .
      show "(let (nid, tstamp) = pool_getOldest (pools u3 P1);
                 startTs = t_startTs u3 P2;
                 candTs = t_candTs u3 P2;
                 update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
             in
               u4 =
                 u3\<lparr>
                   t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u3 P2 else t_candNid u3 x),
                   t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u3 P2 else t_candTs u3 x),
                   t_candPid := (\<lambda>x. if x = P2 then if update then P1 else t_candPid u3 P2 else t_candPid u3 x),
                   t_scanned := (\<lambda>x. if x = P2 then t_scanned u3 P2 \<union> {P1} else t_scanned u3 x)
                 \<rparr>)"
        using D34_body .
    qed
  qed

  have S34: "T_StepCR u3 None u4"
  proof -
    have "T_D3' P2 u3 u4"
      using U3_PC2 D34
      unfolding T_D3'_def by blast
    thus ?thesis
      using P2_Proc by (intro T_StepCR.T_D3_tau)
  qed

  have S34: "T_StepCR u3 None u4"
  proof -
    have PC_u3: "t_pc u3 P2 = ''TD_Loop''"
      unfolding u3_def by simp
    have "T_D3' P2 u3 u4"
      using PC_u3 D34 unfolding T_D3'_def by blast
    thus ?thesis
      using P2_Proc by (intro T_StepCR.T_D3_tau)
  qed

  have U4_PC2: "t_pc u4 P2 = ''TD_Loop''"
    unfolding u4_def u3_def by simp

  have U4_SC2: "t_scanned u4 P2 = {P1}"
    unfolding u4_def by simp

  have U4_CN2: "t_candNid u4 P2 = A1"
    unfolding u4_def by simp

  have U4_CT2: "t_candTs u4 P2 = TS A1"
    unfolding u4_def by simp

  have U4_CP2: "t_candPid u4 P2 = P1"
    unfolding u4_def by simp

  have U4_POOL2: "pools u4 P2 = [(A2, A2, TS A2)]"
    unfolding u4_def u3_def u2_def u1_def
    using POOL2 by simp

  have OG2: "pool_getOldest (pools u4 P2) = (A2, TS A2)"
    using U4_POOL2
    unfolding pool_getOldest_def
    by simp

  have P2_not_sc: "P2 \<notin> t_scanned u4 P2"
    using U4_SC2 P1_neq_P2 by auto

  have UPD_FALSE:
    "\<not> (A2 \<noteq> BOT \<and> TS A2 <\<^sub>t\<^sub>s t_candTs u4 P2 \<and> \<not> t_startTs u4 P2 <\<^sub>t\<^sub>s TS A2)"
    using U4_CT2
    by (simp add: basic_defs)

  have D45_body:
    "(let (nid, tstamp) = pool_getOldest (pools u4 P2);
          startTs = t_startTs u4 P2;
          candTs = t_candTs u4 P2;
          update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
      in
        u5 =
          u4\<lparr>
            t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u4 P2 else t_candNid u4 x),
            t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u4 P2 else t_candTs u4 x),
            t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
            t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
          \<rparr>)"
  proof -
have SC_PROC_u4: "ProcSet = t_scanned u4 P2 \<union> {P2}"
  using U4_SC2 ProcSet_eq P1_neq_P2
  by auto

have CNI_noop:
  "(\<lambda>x. if x = P2 then t_candNid u4 P2 else t_candNid u4 x) = t_candNid u4"
  by auto

have CTS_noop:
  "(\<lambda>x. if x = P2 then t_candTs u4 P2 else t_candTs u4 x) = t_candTs u4"
  by auto

have CPI_noop:
  "(\<lambda>x. if x = P2 then t_candPid u4 P2 else t_candPid u4 x) = t_candPid u4"
  by auto

have SCS_eq:
  "(\<lambda>x. if x = P2 then ProcSet else t_scanned u4 x) =
   (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)"
  using SC_PROC_u4
  by fastforce

have H1:
  "u5 =
    u4\<lparr>
      t_candNid := (\<lambda>x. if x = P2 then t_candNid u4 P2 else t_candNid u4 x),
      t_candTs  := (\<lambda>x. if x = P2 then t_candTs u4 P2 else t_candTs u4 x),
      t_candPid := (\<lambda>x. if x = P2 then t_candPid u4 P2 else t_candPid u4 x),
      t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
    \<rparr>"
proof -
  have
    "u5 =
      u4\<lparr>
        t_candNid := t_candNid u4,
        t_candTs  := t_candTs u4,
        t_candPid := t_candPid u4,
        t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
      \<rparr>"
    unfolding u5_def
    using SCS_eq
    by simp
  thus ?thesis
    using CNI_noop CTS_noop CPI_noop
    by simp
qed

    let ?L =
      "(let (nid, tstamp) = pool_getOldest (pools u4 P2);
            startTs = t_startTs u4 P2;
            candTs = t_candTs u4 P2;
            update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
        in
          u4\<lparr>
            t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u4 P2 else t_candNid u4 x),
            t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u4 P2 else t_candTs u4 x),
            t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
            t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
          \<rparr>)"

    let ?R =
      "(let startTs = t_startTs u4 P2;
            candTs = t_candTs u4 P2;
            update = A2 \<noteq> BOT \<and> TS A2 <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s TS A2
        in
          u4\<lparr>
            t_candNid := (\<lambda>x. if x = P2 then if update then A2 else t_candNid u4 P2 else t_candNid u4 x),
            t_candTs  := (\<lambda>x. if x = P2 then if update then TS A2 else t_candTs u4 P2 else t_candTs u4 x),
            t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
            t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
          \<rparr>)"

    have H2a: "?L = ?R"
    proof -
      have "?L =
        (let (nid, tstamp) = (A2, TS A2);
              startTs = t_startTs u4 P2;
              candTs = t_candTs u4 P2;
              update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
          in
            u4\<lparr>
              t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u4 P2 else t_candNid u4 x),
              t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u4 P2 else t_candTs u4 x),
              t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
              t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
            \<rparr>)"
        using OG2 by simp
      also have "... = ?R"
        by (meson case_prod_conv)
      finally show ?thesis .
    qed

    have H2b:
      "(let startTs = t_startTs u4 P2;
            candTs = t_candTs u4 P2;
            update = A2 \<noteq> BOT \<and> TS A2 <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s TS A2
        in
          u4\<lparr>
            t_candNid := (\<lambda>x. if x = P2 then if update then A2 else t_candNid u4 P2 else t_candNid u4 x),
            t_candTs  := (\<lambda>x. if x = P2 then if update then TS A2 else t_candTs u4 P2 else t_candTs u4 x),
            t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
            t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
          \<rparr>) =
       u4\<lparr>
         t_candNid := (\<lambda>x. if x = P2 then t_candNid u4 P2 else t_candNid u4 x),
         t_candTs  := (\<lambda>x. if x = P2 then t_candTs u4 P2 else t_candTs u4 x),
         t_candPid := (\<lambda>x. if x = P2 then t_candPid u4 P2 else t_candPid u4 x),
         t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
       \<rparr>"
      using UPD_FALSE
      by auto

    have H2:
      "(let (nid, tstamp) = pool_getOldest (pools u4 P2);
            startTs = t_startTs u4 P2;
            candTs = t_candTs u4 P2;
            update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
        in
          u4\<lparr>
            t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u4 P2 else t_candNid u4 x),
            t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u4 P2 else t_candTs u4 x),
            t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
            t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
          \<rparr>) =
       u4\<lparr>
         t_candNid := (\<lambda>x. if x = P2 then t_candNid u4 P2 else t_candNid u4 x),
         t_candTs  := (\<lambda>x. if x = P2 then t_candTs u4 P2 else t_candTs u4 x),
         t_candPid := (\<lambda>x. if x = P2 then t_candPid u4 P2 else t_candPid u4 x),
         t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
       \<rparr>"
      using H2a H2b by simp

    have H1_sym:
      "u4\<lparr>
         t_candNid := (\<lambda>x. if x = P2 then t_candNid u4 P2 else t_candNid u4 x),
         t_candTs  := (\<lambda>x. if x = P2 then t_candTs u4 P2 else t_candTs u4 x),
         t_candPid := (\<lambda>x. if x = P2 then t_candPid u4 P2 else t_candPid u4 x),
         t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
       \<rparr> = u5"
      using H1 by simp

    have H3:
      "(let (nid, tstamp) = pool_getOldest (pools u4 P2);
            startTs = t_startTs u4 P2;
            candTs = t_candTs u4 P2;
            update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
        in
          u4\<lparr>
            t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u4 P2 else t_candNid u4 x),
            t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u4 P2 else t_candTs u4 x),
            t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
            t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
          \<rparr>) = u5"
      using H2 H1_sym
      by (rule trans)

    show ?thesis
      using H3
      using OG2 by force 
  qed

  have D45: "T_D3_Scan P2 P2 u4 u5"
  proof -
    show ?thesis
      unfolding T_D3_Scan_def
    proof (intro conjI)
      show "t_pc u4 P2 = ''TD_Loop''"
        using U4_PC2 .
      show "P2 \<notin> t_scanned u4 P2"
        using P2_not_sc .
      show "P2 \<in> ProcSet"
        using P2_Proc .
      show "(let (nid, tstamp) = pool_getOldest (pools u4 P2);
                 startTs = t_startTs u4 P2;
                 candTs = t_candTs u4 P2;
                 update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
             in
               u5 =
                 u4\<lparr>
                   t_candNid := (\<lambda>x. if x = P2 then if update then nid else t_candNid u4 P2 else t_candNid u4 x),
                   t_candTs  := (\<lambda>x. if x = P2 then if update then tstamp else t_candTs u4 P2 else t_candTs u4 x),
                   t_candPid := (\<lambda>x. if x = P2 then if update then P2 else t_candPid u4 P2 else t_candPid u4 x),
                   t_scanned := (\<lambda>x. if x = P2 then t_scanned u4 P2 \<union> {P2} else t_scanned u4 x)
                 \<rparr>)"
        using D45_body .
    qed
  qed

  have S45: "T_StepCR u4 None u5"
  proof -
    have "T_D3' P2 u4 u5"
      using U4_PC2 D45 unfolding T_D3'_def by blast
    thus ?thesis
      using P2_Proc by (intro T_StepCR.T_D3_tau)
  qed

  have SC_u5: "t_scanned u5 P2 = ProcSet"
    unfolding u5_def u4_def by simp

  have U5_PC2: "t_pc u5 P2 = ''TD_Loop''"
    unfolding u5_def u4_def u3_def
    by simp

  have U5_SC2: "t_scanned u5 P2 = ProcSet"
    unfolding u5_def
    by simp

  have U5_CN2: "t_candNid u5 P2 = A1"
    unfolding u5_def u4_def
    by simp

  have U5_CT2: "t_candTs u5 P2 = TS A1"
    unfolding u5_def u4_def
    by simp

  have U5_CP2: "t_candPid u5 P2 = P1"
    unfolding u5_def u4_def
    by simp

  have U5_ST2: "t_startTs u5 P2 = TS (ts_counter tk)"
    unfolding u5_def u4_def u3_def u2_def u1_def
    by simp

  have U5_TSC: "ts_counter u5 = ts_counter tk + 1"
    unfolding u5_def u4_def u3_def u2_def u1_def
    by simp

  have U5_POOL1: "pools u5 P1 = [(1, A1, TS 1), (3, A3, TS 3)]"
    unfolding u5_def u4_def u3_def u2_def u1_def
    using POOL1 by simp

  have U5_POOL2: "pools u5 P2 = [(2, A2, TS 2)]"
    unfolding u5_def u4_def u3_def u2_def u1_def
    using POOL2 by simp

  have RM_u5:
    "pool_remove (pools u5 (t_candPid u5 P2)) (t_candNid u5 P2) = (A1, [(3, A3, TS 3)])"
    using U5_CN2 U5_CP2 U5_POOL1
    by simp

  have A1NZ: "A1 \<noteq> BOT"
    by (simp add: BOT_def)

  have RM_u5_fst:
    "fst (pool_remove (pools u5 (t_candPid u5 P2)) (t_candNid u5 P2)) = A1"
    using RM_u5 by simp

  have RM_u5_snd:
    "snd (pool_remove (pools u5 (t_candPid u5 P2)) (t_candNid u5 P2)) = [(3, A3, TS 3)]"
    using RM_u5 by simp

  have RET_EQ:
    "(\<lambda>x. if x = P2
          then fst (pool_remove (pools u5 (t_candPid u5 P2)) (t_candNid u5 P2))
          else t_retV u5 x)
     =
     (\<lambda>x. if x = P2 then A1 else t_retV u5 x)"
    using RM_u5_fst
    by auto

  have POOLS_EQ:
    "(\<lambda>x. if x = t_candPid u5 P2
          then snd (pool_remove (pools u5 (t_candPid u5 P2)) (t_candNid u5 P2))
          else pools u5 x)
     =
     (\<lambda>x. if x = P1 then [(3, A3, TS 3)] else pools u5 x)"
    using U5_CP2 RM_u5_snd
    by auto

  have A1_val: "A1 = Suc P1"
    by simp

  have RM_EXACT:
    "pool_remove (pools u5 (t_candPid u5 P2)) (t_candNid u5 P2)
     = (A1, [(A3, A3, TS 3)])"
    using RM_u5 A1_val
    by blast

  have D56: "T_D3_Eval P2 u5 u6"
  proof -
    have CORE:
      "(let cNid = t_candNid u5 P2;
            cPid = t_candPid u5 P2
        in
          if cNid \<noteq> BOT then
            let (val, new_pool) = pool_remove (pools u5 cPid) cNid
            in
              if val \<noteq> BOT then
                u6 =
                  u5\<lparr>
                    pools := (\<lambda>x. if x = cPid then new_pool else pools u5 x),
                    t_retV := (\<lambda>x. if x = P2 then val else t_retV u5 x),
                    t_pc := (\<lambda>x. if x = P2 then ''TD_Remove_Done'' else t_pc u5 x)
                  \<rparr>
              else
                u6 = u5\<lparr>t_pc := (\<lambda>x. if x = P2 then ''TD1'' else t_pc u5 x)\<rparr>
          else
            u6 = u5\<lparr>t_pc := (\<lambda>x. if x = P2 then ''TD1'' else t_pc u5 x)\<rparr>)"
    proof -
      have Cnid: "t_candNid u5 P2 = A1"
        using U5_CN2 .

      have Cpid: "t_candPid u5 P2 = P1"
        using U5_CP2 .

      have U6_SHAPE:
        "u6 =
          u5\<lparr>
            pools := (\<lambda>x. if x = P1 then [(3, A3, TS 3)] else pools u5 x),
            t_retV := (\<lambda>x. if x = P2 then A1 else t_retV u5 x),
            t_pc := (\<lambda>x. if x = P2 then ''TD_Remove_Done'' else t_pc u5 x)
          \<rparr>"
        unfolding u6_def
        by simp

      have A1_eq_SucP1: "A1 = Suc P1"
        by simp

      have RM1_suc:
        "pool_remove (pools u5 P1) (Suc P1) = (Suc P1, [(A3, A3, TS 3)])"
        using RM_u5 U5_CN2 U5_CP2 by auto

      have U6_SHAPE_suc:
        "u6 =
          u5\<lparr>
            pools := (\<lambda>x. if x = P1 then [(A3, A3, TS 3)] else pools u5 x),
            t_retV := (\<lambda>x. if x = Suc P1 then Suc P1 else t_retV u5 x),
            t_pc := (\<lambda>x. if x = Suc P1 then ''TD_Remove_Done'' else t_pc u5 x)
          \<rparr>"
        using One_nat_def u6_def by presburger

      have INNER:
        "(let (val, new_pool) = pool_remove (pools u5 P1) (Suc P1)
          in
            if val \<noteq> BOT then
              u6 =
                u5\<lparr>
                  pools := (\<lambda>x. if x = P1 then new_pool else pools u5 x),
                  t_retV := (\<lambda>x. if x = Suc P1 then val else t_retV u5 x),
                  t_pc := (\<lambda>x. if x = Suc P1 then ''TD_Remove_Done'' else t_pc u5 x)
                \<rparr>
            else
              u6 = u5\<lparr>t_pc := (\<lambda>x. if x = Suc P1 then ''TD1'' else t_pc u5 x)\<rparr>)"
        using RM1_suc A1NZ U6_SHAPE_suc
        by simp

      show ?thesis
        by (metis A1NZ INNER One_nat_def U5_CN2 U5_CP2)
    qed

    from U5_PC2 U5_SC2 CORE show ?thesis
      unfolding T_D3_Eval_def
      by simp
  qed



  have PC_u6: "t_pc u6 P2 = ''TD_Remove_Done''"
    unfolding u6_def
    by simp

  have RET_u6: "t_retV u6 P2 = A1"
    unfolding u6_def
    by simp

  have POOL_u6_P1: "pools u6 P1 = [(3, A3, TS 3)]"
    unfolding u6_def
    using U5_POOL1
    by simp

  have POOL_u6_P2: "pools u6 P2 = [(2, A2, TS 2)]"
    unfolding u6_def
    using U5_POOL2 P1_neq_P2
    by simp

  have ST_u6: "t_startTs u6 P2 = TS (ts_counter tk)"
    unfolding u6_def
    using U5_ST2
    by simp

  have TSC_u6: "ts_counter u6 = ts_counter tk + 1"
    unfolding u6_def
    using U5_TSC
    by simp

  have S56: "T_StepCR u5 None u6"
  proof -
    have "T_D3' P2 u5 u6"
      using U5_PC2 U5_SC2 D56
      unfolding T_D3'_def by blast
    thus ?thesis
      using P2_Proc by (intro T_StepCR.T_D3_tau)
  qed

  have S56: "T_StepCR u5 None u6"
  proof -
    have PC_u5: "t_pc u5 P2 = ''TD_Loop''"
      unfolding u5_def u4_def u3_def by simp
    have "T_D3' P2 u5 u6"
      using PC_u5 SC_u5 D56 unfolding T_D3'_def by blast
    thus ?thesis
      using P2_Proc by (intro T_StepCR.T_D3_tau)
  qed

  have RET_u6: "t_retV u6 P2 = A1"
    unfolding u6_def by simp

  have D67: "T_D4 P2 u6 u7"
    unfolding T_D4_def u6_def u7_def
    by (auto simp: basic_defs)

  have S67: "T_StepCR u6 (Some (mk_obs deq A1 P2 ret)) u7"
  proof -
    have "T_StepCR u6 (Some (mk_obs deq (t_retV u6 P2) P2 ret)) u7"
      using D67 P2_Proc by (intro T_StepCR.T_D4_vis)
    thus ?thesis
      using RET_u6 by simp
  qed

  have SC_u6_P1: "t_scanned u6 P1 = {P2}"
    using SC1
    unfolding u6_def u5_def u4_def u3_def u2_def u1_def
    by simp

  have SC_u7_P1: "t_scanned u7 P1 = {P2}"
    using SC_u6_P1
    unfolding u7_def
    by simp

  have P1_not_sc: "P1 \<notin> t_scanned u7 P1"
    using SC_u7_P1 P1_neq_P2
    by auto

  have U7_PC1: "t_pc u7 P1 = ''TD_Loop''"
    using PC1
    unfolding u7_def u6_def u5_def u4_def u3_def u2_def u1_def
    by simp

  have U7_SC1: "t_scanned u7 P1 = {P2}"
    using SC1
    unfolding u7_def u6_def u5_def u4_def u3_def u2_def u1_def
    by simp

  have U7_CN1: "t_candNid u7 P1 = BOT"
    using CN1
    unfolding u7_def u6_def u5_def u4_def u3_def u2_def u1_def
    by simp

  have U7_CT1: "t_candTs u7 P1 = TOP"
    using CT1
    unfolding u7_def u6_def u5_def u4_def u3_def u2_def u1_def
    by simp

  have U7_CP1: "t_candPid u7 P1 = BOT"
    using CP1
    unfolding u7_def u6_def u5_def u4_def u3_def u2_def u1_def
    by simp

  have U7_ST1: "t_startTs u7 P1 = TS 4"
    using ST1
    unfolding u7_def u6_def u5_def u4_def u3_def u2_def u1_def
    by simp

  have U7_POOL1: "pools u7 P1 = [(A3, A3, TS A3)]"
    using POOL_u6_P1
    unfolding u7_def
    by simp

  have P1_not_sc: "P1 \<notin> t_scanned u7 P1"
    using U7_SC1 P1_neq_P2
    by auto

  have OG3: "pool_getOldest (pools u7 P1) = (A3, TS A3)"
    using U7_POOL1
    unfolding pool_getOldest_def
    by simp

  have START_OK3: "\<not> ts_less (t_startTs u7 P1) (TS A3)"
    using U7_ST1 TC_GT_3
    by (auto simp: basic_defs)

  have SC_PROC_u7: "ProcSet = t_scanned u7 P1 \<union> {P1}"
    using U7_SC1 ProcSet_eq P1_neq_P2
    by auto

  have D78_body:
    "(let (nid, tstamp) = pool_getOldest (pools u7 P1);
          startTs = t_startTs u7 P1;
          candTs = t_candTs u7 P1;
          update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
      in
        u8 =
          u7\<lparr>
            t_candNid := (\<lambda>x. if x = P1 then if update then nid else t_candNid u7 P1 else t_candNid u7 x),
            t_candTs  := (\<lambda>x. if x = P1 then if update then tstamp else t_candTs u7 P1 else t_candTs u7 x),
            t_candPid := (\<lambda>x. if x = P1 then if update then P1 else t_candPid u7 P1 else t_candPid u7 x),
            t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
          \<rparr>)"
  proof -
    have H1:
      "u8 =
        u7\<lparr>
          t_candNid := (\<lambda>x. if x = P1 then A3 else t_candNid u7 x),
          t_candTs  := (\<lambda>x. if x = P1 then TS A3 else t_candTs u7 x),
          t_candPid := (\<lambda>x. if x = P1 then P1 else t_candPid u7 x),
          t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
        \<rparr>"
      using SC_PROC_u7
      unfolding u8_def
      by meson

    let ?L =
      "(let (nid, tstamp) = pool_getOldest (pools u7 P1);
            startTs = t_startTs u7 P1;
            candTs = t_candTs u7 P1;
            update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
        in
          u7\<lparr>
            t_candNid := (\<lambda>x. if x = P1 then if update then nid else t_candNid u7 P1 else t_candNid u7 x),
            t_candTs  := (\<lambda>x. if x = P1 then if update then tstamp else t_candTs u7 P1 else t_candTs u7 x),
            t_candPid := (\<lambda>x. if x = P1 then if update then P1 else t_candPid u7 P1 else t_candPid u7 x),
            t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
          \<rparr>)"

    let ?R =
      "(let startTs = t_startTs u7 P1;
            candTs = t_candTs u7 P1;
            update = A3 \<noteq> BOT \<and> TS A3 <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s TS A3
        in
          u7\<lparr>
            t_candNid := (\<lambda>x. if x = P1 then if update then A3 else t_candNid u7 P1 else t_candNid u7 x),
            t_candTs  := (\<lambda>x. if x = P1 then if update then TS A3 else t_candTs u7 P1 else t_candTs u7 x),
            t_candPid := (\<lambda>x. if x = P1 then if update then P1 else t_candPid u7 P1 else t_candPid u7 x),
            t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
          \<rparr>)"

    have H2a: "?L = ?R"
    proof -
      have "?L =
        (let (nid, tstamp) = (A3, TS A3);
              startTs = t_startTs u7 P1;
              candTs = t_candTs u7 P1;
              update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
          in
            u7\<lparr>
              t_candNid := (\<lambda>x. if x = P1 then if update then nid else t_candNid u7 P1 else t_candNid u7 x),
              t_candTs  := (\<lambda>x. if x = P1 then if update then tstamp else t_candTs u7 P1 else t_candTs u7 x),
              t_candPid := (\<lambda>x. if x = P1 then if update then P1 else t_candPid u7 P1 else t_candPid u7 x),
              t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
            \<rparr>)"
        using OG3 by simp
      also have "... = ?R"
        by (meson case_prod_conv)
      finally show ?thesis .
    qed

    have UPD_TRUE3:
      "A3 \<noteq> BOT \<and> TS A3 <\<^sub>t\<^sub>s t_candTs u7 P1 \<and> \<not> t_startTs u7 P1 <\<^sub>t\<^sub>s TS A3"
      using U7_CT1 START_OK3
      by (simp add: basic_defs)

    have H2b:
      "?R =
       u7\<lparr>
         t_candNid := (\<lambda>x. if x = P1 then A3 else t_candNid u7 x),
         t_candTs  := (\<lambda>x. if x = P1 then TS A3 else t_candTs u7 x),
         t_candPid := (\<lambda>x. if x = P1 then P1 else t_candPid u7 x),
         t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
       \<rparr>"
      using UPD_TRUE3
      by simp

    have H2:
      "?L =
       u7\<lparr>
         t_candNid := (\<lambda>x. if x = P1 then A3 else t_candNid u7 x),
         t_candTs  := (\<lambda>x. if x = P1 then TS A3 else t_candTs u7 x),
         t_candPid := (\<lambda>x. if x = P1 then P1 else t_candPid u7 x),
         t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
       \<rparr>"
      using H2a H2b
      by simp

    have H1_sym:
      "u7\<lparr>
         t_candNid := (\<lambda>x. if x = P1 then A3 else t_candNid u7 x),
         t_candTs  := (\<lambda>x. if x = P1 then TS A3 else t_candTs u7 x),
         t_candPid := (\<lambda>x. if x = P1 then P1 else t_candPid u7 x),
         t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
       \<rparr> = u8"
      using H1 by simp

    have H3: "?L = u8"
      using H2 H1_sym
      by (rule trans)

    show ?thesis
      using H3
      using OG3 by fastforce 
  qed

  have D78: "T_D3_Scan P1 P1 u7 u8"
  proof -
    show ?thesis
      unfolding T_D3_Scan_def
    proof (intro conjI)
      show "t_pc u7 P1 = ''TD_Loop''"
        using U7_PC1 .
      show "P1 \<notin> t_scanned u7 P1"
        using P1_not_sc .
      show "P1 \<in> ProcSet"
        using P1_Proc .
      show "(let (nid, tstamp) = pool_getOldest (pools u7 P1);
                 startTs = t_startTs u7 P1;
                 candTs = t_candTs u7 P1;
                 update = nid \<noteq> BOT \<and> tstamp <\<^sub>t\<^sub>s candTs \<and> \<not> startTs <\<^sub>t\<^sub>s tstamp
             in
               u8 =
                 u7\<lparr>
                   t_candNid := (\<lambda>x. if x = P1 then if update then nid else t_candNid u7 P1 else t_candNid u7 x),
                   t_candTs  := (\<lambda>x. if x = P1 then if update then tstamp else t_candTs u7 P1 else t_candTs u7 x),
                   t_candPid := (\<lambda>x. if x = P1 then if update then P1 else t_candPid u7 P1 else t_candPid u7 x),
                   t_scanned := (\<lambda>x. if x = P1 then t_scanned u7 P1 \<union> {P1} else t_scanned u7 x)
                 \<rparr>)"
        using D78_body .
    qed
  qed

  have S78: "T_StepCR u7 None u8"
  proof -
    have "T_D3' P1 u7 u8"
      using U7_PC1 D78
      unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  have SC_u8: "t_scanned u8 P1 = ProcSet"
    unfolding u8_def u7_def by (simp add: ProcSet_eq SC1)

  have U8_PC1: "t_pc u8 P1 = ''TD_Loop''"
    using U7_PC1
    unfolding u8_def
    by simp

  have U8_SC1_Proc: "t_scanned u8 P1 = ProcSet"
    unfolding u8_def
    by simp

  have U8_CN1: "t_candNid u8 P1 = A3"
    unfolding u8_def
    by simp

  have U8_CT1: "t_candTs u8 P1 = TS A3"
    unfolding u8_def
    by simp

  have U8_CP1: "t_candPid u8 P1 = P1"
    unfolding u8_def
    by simp

  have U8_POOL1: "pools u8 P1 = [(A3, A3, TS A3)]"
    using U7_POOL1
    unfolding u8_def
    by simp

  have U8_POOL2: "pools u8 P2 = pools u7 P2"
    unfolding u8_def
    by simp

  have A3NZ: "A3 \<noteq> BOT"
    by (simp add: BOT_def)

  have RM_u8:
    "pool_remove (pools u8 (t_candPid u8 P1)) (t_candNid u8 P1) = (A3, [])"
    using U8_CN1 U8_CP1 U8_POOL1
    by  simp

  have D89: "T_D3_Eval P1 u8 u9"
  proof -
    have CORE:
      "(let cNid = t_candNid u8 P1;
            cPid = t_candPid u8 P1
        in
          if cNid \<noteq> BOT then
            let (val, new_pool) = pool_remove (pools u8 cPid) cNid
            in
              if val \<noteq> BOT then
                u9 =
                  u8\<lparr>
                    pools := (\<lambda>x. if x = cPid then new_pool else pools u8 x),
                    t_retV := (\<lambda>x. if x = P1 then val else t_retV u8 x),
                    t_pc := (\<lambda>x. if x = P1 then ''TD_Remove_Done'' else t_pc u8 x)
                  \<rparr>
              else
                u9 = u8\<lparr>t_pc := (\<lambda>x. if x = P1 then ''TD1'' else t_pc u8 x)\<rparr>
          else
            u9 = u8\<lparr>t_pc := (\<lambda>x. if x = P1 then ''TD1'' else t_pc u8 x)\<rparr>)"
    proof -
      have RM_EXACT: "pool_remove (pools u8 P1) A3 = (A3, [])"
        using RM_u8 U8_CN1 U8_CP1
        by simp

      from U8_CN1 U8_CP1 A3NZ RM_EXACT
      show ?thesis
        unfolding u9_def
        by (simp add: Let_def split: prod.splits if_splits)
    qed

    from U8_PC1 U8_SC1_Proc CORE show ?thesis
      unfolding T_D3_Eval_def
      by simp
  qed

  have S89: "T_StepCR u8 None u9"
  proof -
    have PC_u8_P1: "t_pc u8 P1 = ''TD_Loop''"
      using PC1 unfolding u8_def u7_def
      using U8_PC1 u7_def u8_def by force
    have "T_D3' P1 u8 u9"
      using PC_u8_P1 SC_u8 D89 unfolding T_D3'_def by blast
    thus ?thesis
      using P1_Proc by (intro T_StepCR.T_D3_tau)
  qed

  have RET_u9: "t_retV u9 P1 = A3"
    unfolding u9_def by simp

  have D910: "T_D4 P1 u9 t3"
    unfolding T_D4_def u9_def t3_def
    by (auto simp: basic_defs)

  have S910: "T_StepCR u9 (Some (mk_obs deq A3 P1 ret)) t3"
  proof -
    have "T_StepCR u9 (Some (mk_obs deq (t_retV u9 P1) P1 ret)) t3"
      using D910 P1_Proc by (intro T_StepCR.T_D4_vis)
    thus ?thesis
      using RET_u9 by simp
  qed

  have PATH: "T_Path tk e3_labels t3"
    unfolding e3_labels_def
    apply (rule T_Path.cons[OF S01])
    apply (rule T_Path.cons[OF S12])
    apply (rule T_Path.cons[OF S23])
    apply (rule T_Path.cons[OF S34])
    apply (rule T_Path.cons[OF S45])
    apply (rule T_Path.cons[OF S56])
    apply (rule T_Path.cons[OF S67])
    apply (rule T_Path.cons[OF S78])
    apply (rule T_Path.cons[OF S89])
    apply (rule T_Path.cons[OF S910])
    apply (rule T_Path.nil)
    done

  show ?thesis
    using PATH by blast
qed


lemma tsq_e1_has_inv_plus:
  assumes W: "\<exists>t0 tk.
  T_Init t0 \<and> T_Path t0 e1_labels tk \<and> E1_TSQ_shape tk"
  shows "\<exists>tk.
  E1_TSQ_shape tk \<and> TSQ_State_Inv_Plus tk"
proof -
  from W obtain t0 tk where I0: "T_Init t0" and P: "T_Path t0 e1_labels tk" and SH: "E1_TSQ_shape tk" by blast
  have INV: "TSQ_State_Inv_Plus tk" using T_Path_TSQ_State_Inv_Plus[OF I0 P] .
  from SH INV show ?thesis by blast
qed



end
