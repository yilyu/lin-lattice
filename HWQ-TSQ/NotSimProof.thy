theory NotSimProof
  imports TraceInv
    "../HWQ-U/ULinProof"
    NotSimLemmas
begin


subsection \<open>Concrete HWQ obligations after matching the common prefix\<close>


lemma E1_HWQ_pending_deq_P1:
  assumes SH: "E1_HWQ_shape s"
  shows "HasPendingDeq s P1"
proof -
  have INV: "system_invariant (fst s, snd s)"
    and PC: "program_counter (fst s, snd s) P1 = ''D3''"
    using E1_HWQ_shapeD[OF SH] by auto
  show ?thesis
   
    using D3_has_pending_deq[OF INV PC] by auto
qed



text \<open>
 
   Helper lemmas required by Scheme A.
\<close>
lemma C_Path_snocE:
  assumes P: "C_Path s (xs @ [x]) t"
  shows "\<exists>u.
  C_Path s xs u \<and> C_Match u x t"
  using P
proof (induction xs arbitrary: s)
  case Nil
  then have P': "C_Path s [x] t" by simp
  then obtain u where M: "C_Match s x u" and P0: "C_Path u [] t"
    by (cases) auto
  from P0 have "u = t"
    by (cases) auto
  with M show ?case
    using C_Path.nil by blast
next
  case (Cons a xs)
  have P': "C_Path s (a # (xs @ [x])) t"
    using Cons.prems by simp
  
  then obtain s1 where M0: "C_Match s a s1" and P1: "C_Path s1 (xs @ [x]) t"
    by (cases) auto
  from Cons.IH[OF P1] obtain u where PX: "C_Path s1 xs u" and MX: "C_Match u x t"
    by blast
  have "C_Path s (a # xs) u"
    using M0 PX by (rule C_Path.cons)
  thus ?case
    using MX
    by blast
qed

lemma C_Match_someE:
  assumes "C_Match s (Some a) t"
  shows "\<exists>u v. C_Tau_Star s u \<and> C_StepCR u (Some a) v \<and> 
  C_Tau_Star v 
  t"
  using assms by (cases rule: C_Match.cases) auto

lemma C_Match_noneE:
  assumes M: "C_Match s None t"
  shows "C_Tau_Star s t"
  using M
  by (cases) auto




lemma C_Path_appendE:
  assumes P: "C_Path s (xs @ ys) 
  t"
  shows "\<exists>u.
  C_Path s xs u \<and> C_Path u ys t"
  using P
proof (induction xs arbitrary: s)
  case Nil
  (* xs, xs @ ys ys, path *)
  have "C_Path s [] s" 
    using C_Path.nil .
  then show ?case
    using Nil.prems
    by fastforce 
next
  case (Cons a xs')
  (* prefixunfold, a # (xs' @ ys) *)
  have "C_Path s (a # (xs' @ ys)) t"
    using Cons.prems by simp
    
  (*  cases 
   (Inversion)， 
  M  P_rest *)
  then obtain s1 where M: "C_Match s a s1" and P_rest: "C_Path s1 (xs' @ ys) t"
    by cases auto

  (* path induction hypothesis, state u *)
  from Cons.IH[OF P_rest] obtain u where 
      P_xs': "C_Path s1 xs' u" 
    and P_ys: "C_Path u ys t"
    by blast

  (* M P_xs' path *)
  have "C_Path s (a # xs') u"
    using C_Path.cons[OF M P_xs'] .

  (* Comment. *)
  with P_ys show 
  
  ?case
    by blast
qed



lemma hwq_p1_deq_call_extract_local_state:
  assumes MCALL: "C_Match s_before (Some (mk_obs deq BOT P1 call)) s_aftercall"
  shows "\<exists>u_call 
  v_call.
           C_Tau_Star s_before u_call \<and>
           C_StepCR u_call (Some (mk_obs deq BOT P1 call)) v_call \<and>
           C_Tau_Star v_call s_aftercall \<and>
           program_counter v_call P1 = ''D1''"
proof -
  obtain u_call v_call where
      TAU1: "C_Tau_Star s_before u_call"
    and STEP: "C_StepCR u_call (Some (mk_obs deq BOT P1 call)) v_call"
    and TAU2: "C_Tau_Star v_call s_aftercall"
    using C_Match_someE[OF MCALL] by blast

  
  from STEP obtain p where
      PIN: "p \<in> ProcSet"
    and SL0: "Sys_L0 p u_call v_call"
    and PC:  "program_counter v_call p = ''D1''"
    and LAB: "mk_obs deq BOT p call = mk_obs deq BOT P1 call"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  from LAB have pP1: "p = P1"
    unfolding mk_obs_def by auto

  have PCP1: "program_counter v_call P1 = ''D1''"
    using PC pP1 by simp

  show ?thesis
    using TAU1 STEP 
  TAU2 PCP1 by blast
qed




(* Step 1. *)
lemma C_Tau_preserves_his_and_s_var:
  assumes "C_Tau s s'"
  shows "his_seq s' = his_seq s" and "s_var s' p = s_var s p"
proof -
  from assms have "C_StepCR s None s'" unfolding C_Tau_def by simp
  then obtain q where PIN: "q \<in> ProcSet" and STEP:
    "Sys_E1 q s s' \<or> Sys_E2 q s s' \<or> Sys_D1 q s s' \<or> Sys_D2 q s s' \<or> Sys_D3 q s s'"
   
    by cases auto
    
  show "his_seq s' = his_seq s"
    using STEP
    by (elim disjE) (auto simp: Sys_E1_def Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def 
                                C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def 
                           
    U_E2_def U_D2_def his_seq_def
                                T_D2_EnterLoop_def Let_def split: if_splits)
                                
  show "s_var s' p = s_var s p"
    using STEP
    by (elim disjE) (auto simp: Sys_E1_def 
  Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def 
 
                                C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def 
                                U_E2_def U_D2_def s_var_def
                        
    T_D2_EnterLoop_def Let_def split: if_splits)
qed




(* Auxiliary lemma. *)
lemma C_Path_Nones_is_Tau_Star:
  assumes "C_Path s ls u"
      and "set ls \<subseteq> {None}"
  shows "C_Tau_Star s u"
  using assms
proof (induction s ls u rule: C_Path.induct)
  case nil
  then show ?case using C_Tau_Star.refl by simp
next
  case (cons s l s1 ls s2)
  have "l = None" using cons.prems by simp
  with cons.hyps(1) have T1: "C_Tau_Star s s1" using C_Match_noneE by simp
  have T2: "C_Tau_Star s1 s2" using cons.IH cons.prems by simp
  show 
  ?case using C_Tau_Star_trans[OF T1 T2] .
qed




lemma C_Tau_no_P2_E1_preserves_E1:
  assumes N2: "N_Procs = 2"
      and TAU: "C_Tau s t"
      and PC: "program_counter s P2 = ''E1''"
      and NOE1: "\<not> Sys_E1 P2 s t"
  shows "program_counter t P2 = ''E1''"
proof -
  have STEP0: "C_StepCR s None t"
    using TAU unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP: "Sys_E1 p s t \<or> Sys_E2 p s t \<or> Sys_D1 p s t \<or> Sys_D2 p s t \<or> Sys_D3 p s t"
    by (cases rule: C_StepCR.cases) auto

  have p_not_P2: "p \<noteq> P2"
  proof
    assume pP2: "p = P2"
    (* isolationdirectclose by contradiction P2, elim disjE *)
    have C1: "Sys_E1 p s t \<Longrightarrow> False" using pP2 NOE1 by simp
    have C2: "Sys_E2 p s t \<Longrightarrow> False" using pP2 PC unfolding Sys_E2_def C_E2_def program_counter_def Let_def by auto
    have C3: "Sys_D1 p s t \<Longrightarrow> False" using pP2 PC unfolding Sys_D1_def C_D1_def program_counter_def Let_def by auto
    have C4: "Sys_D2 p s t \<Longrightarrow> False" using pP2 PC unfolding Sys_D2_def C_D2_def program_counter_def T_D2_EnterLoop_def Let_def by auto
    have C5: "Sys_D3 p s t \<Longrightarrow> False" using pP2 PC unfolding Sys_D3_def C_D3_def program_counter_def Let_def by auto
    from STEP C1 C2 C3 C4 C5 show False by blast
  qed

  have pP1: "p = P1"
    using PIN N2 p_not_P2 by auto

  (* isolation P1, P1 state, P2 PC *)
  have C1: "Sys_E1 p s t \<Longrightarrow> ?thesis" using pP1 PC unfolding Sys_E1_def C_E1_def program_counter_def Let_def by (auto split: if_splits)
  have C2: "Sys_E2 p s t \<Longrightarrow> ?thesis" using pP1 PC unfolding Sys_E2_def C_E2_def program_counter_def Let_def by (auto split: if_splits)
  have C3: "Sys_D1 p s t \<Longrightarrow> ?thesis" using pP1 PC unfolding Sys_D1_def C_D1_def program_counter_def Let_def by (auto split: if_splits)
  have C4: "Sys_D2 p s t \<Longrightarrow> ?thesis" using pP1 PC unfolding Sys_D2_def C_D2_def program_counter_def T_D2_EnterLoop_def Let_def by (auto split: if_splits)
  have C5: "Sys_D3 p s t \<Longrightarrow> ?thesis" using pP1 PC unfolding Sys_D3_def C_D3_def program_counter_def Let_def by (auto split: if_splits)

  from STEP C1 C2 C3 C4 C5 show ?thesis by blast
qed

lemma C_Tau_Star_no_P2_E1_preserves_E1:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and PC: "program_counter s P2 = ''E1''"
      and NOE1: "\<And>s' t'. C_Tau s' t' \<Longrightarrow> \<not> Sys_E1 P2 s' t'"
  shows "program_counter t P2 = ''E1''"
  using TAUS PC
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have PC2: "program_counter s2 P2 = ''E1''"
    using C_Tau_no_P2_E1_preserves_E1[OF N2 step.hyps(1) step.prems]
          NOE1[OF step.hyps(1)]
    by blast
  show ?case
    using step.IH[OF PC2] .
qed




(* ========================================================================= *)
(* State-collapse engine (Wave Function Collapse via e2) *)
(* ========================================================================= *)

lemma e2_labels_split:
  "e2_labels = e2_part1 @ (e2_part2 @ e2_part3)"
  unfolding e2_labels_def e2_part1_def e2_part2_def e2_part3_def by simp

(* Unwrapping helper lemma: e2 trace ret *)
lemma e2_part1_snoc: "e2_part1 = [None, None] @ [Some (mk_obs deq A1 P1 ret)]"
  unfolding e2_part1_def by simp

lemma e2_part2_snoc:
  "e2_part2 =
     [Some (mk_obs deq BOT P1 call), None, None, None, None, None] @
     [Some (mk_obs deq A2 P1 ret)]"
  unfolding e2_part2_def by simp

lemma e2_part3_snoc: "e2_part3 = [Some (mk_obs deq BOT P1 call), None, None, None, None, None] @ [Some (mk_obs deq A3 P1 ret)]"
  unfolding e2_part3_def by simp

(* ========================================================================= *)
(* State-collapse helper lemma: P1 (Symbolic Execution) *)
(* ========================================================================= *)

lemma Tau_preserves_quantum_shape_step:
  assumes N2: "N_Procs = 2"
      and PRE: "E1_HWQ_quantum_shape s"
      and TAU: "C_Tau s s'"
  shows "E1_HWQ_quantum_shape s'"
proof -
  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp

  from PRE have INV: "system_invariant s"
    and X4: "X_var s = 4"
    and PCP2: "program_counter s P2 = ''L0''"
    and HPD: "HasPendingDeq s P1"
    and BR:
      "((Q_arr s 1 = A1) \<and>
         ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
       \<or>
       ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
    and Q23: "{Q_arr s 2, Q_arr s 3} = {A2, A3}"
    unfolding E1_HWQ_quantum_shape_def by auto

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto

  have pneqP2: "p \<noteq> P2"
  proof
    assume pP2: "p = P2"
    from STEP show False
      using pP2 PCP2
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def Let_def
      by auto
  qed

  have pP1: "p = P1"
    using PIN N2 pneqP2 by auto

  have STEP1: "Sys_D1 P1 s s' \<or> Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
    using STEP pP1 BR
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def program_counter_def
    by auto

  have NXT: "Next s s'"
    using C_StepCR_into_Next[OF STEP0] .
  have INV': "system_invariant s'"
    using Sys_Inv_Step[OF INV NXT] .

  have X4': "X_var s' = 4"
    using STEP1 X4
    unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
              X_var_def Let_def
    by (elim disjE) (auto split: if_splits)

  have PCP2': "program_counter s' P2 = ''L0''"
    using STEP1 PCP2
    unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
              program_counter_def Let_def
    by (elim disjE) (auto split: if_splits)

  have Q23': "{Q_arr s' 2, Q_arr s' 3} = {A2, A3}"
    using STEP1 BR Q23
    unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
              Q_arr_def program_counter_def j_var_def Let_def
    by (elim disjE) (auto split: if_splits)

  have BR':
      "((Q_arr s' 1 = A1) \<and>
         ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
       \<or>
       ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1)"
    using BR
  proof (elim disjE)
    assume SCAN:
      "(Q_arr s 1 = A1) \<and>
       ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1))"
    then have Q1: "Q_arr s 1 = A1"
      and SC: "((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
                (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1))"
      by auto
    from STEP1 show ?thesis
    proof (elim disjE)
      assume D1: "Sys_D1 P1 s s'"
      then have "Q_arr s' 1 = A1"
        using Q1 unfolding Sys_D1_def C_D1_def Q_arr_def by auto
      moreover have "program_counter s' P1 = ''D2''"
        using D1 unfolding Sys_D1_def C_D1_def program_counter_def by auto
      ultimately show ?thesis by auto
    next
      assume D2: "Sys_D2 P1 s s'"
      from SC show ?thesis
      proof (elim disjE)
        assume H: "program_counter s P1 \<in> {''D1'', ''D2''}"
        then have "program_counter s P1 = ''D2''"
          using D2 unfolding Sys_D2_def C_D2_def program_counter_def by auto
        then show ?thesis
          using D2 Q1
          unfolding Sys_D2_def C_D2_def program_counter_def Q_arr_def j_var_def Let_def
          by (auto split: if_splits)
      next
        assume H: "program_counter s P1 = ''D3'' \<and> j_var s P1 = 1"
        with D2 show ?thesis
          unfolding Sys_D2_def C_D2_def program_counter_def by auto
      qed
    next
      assume D3: "Sys_D3 P1 s s'"
      from SC show ?thesis
      proof (elim disjE)
        assume H: "program_counter s P1 \<in> {''D1'', ''D2''}"
        with D3 show ?thesis
          unfolding Sys_D3_def C_D3_def program_counter_def by auto
      next
        assume D3J1: "program_counter s P1 = ''D3'' \<and> j_var s P1 = 1"
        then have PCD3: "program_counter s P1 = ''D3''"
          and J1: "j_var s P1 = 1"
          by auto
        have "Q_arr s' 1 = BOT"
          using D3 Q1 PCD3 J1
          unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def
          by auto
        moreover have "program_counter s' P1 = ''D4''"
          using D3 Q1 PCD3 J1
          unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def
          by (simp add: BOT_def)
        moreover have "x_var s' P1 = A1"
          using D3 Q1 PCD3 J1
          unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def
          by auto
        ultimately show ?thesis by auto
      qed
    qed
  next
    assume LOCK:
      "(Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1"
    from STEP1 LOCK show ?thesis
      unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def
      by auto
  qed

  have HPD': "HasPendingDeq s' P1"
  proof -
    have hI12': "hI12_D_Phase_Pending_Deq s'"
      using INV' unfolding system_invariant_def by auto
    have "program_counter s' P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using BR' by auto
    then show ?thesis
      using hI12' unfolding hI12_D_Phase_Pending_Deq_def by blast
  qed

  show ?thesis
    unfolding E1_HWQ_quantum_shape_def
    using INV' X4' PCP2' HPD' BR' Q23'
    by auto
qed

lemma Tau_Star_preserves_quantum_shape:
  assumes N2: "N_Procs = 2"
      and PRE: "E1_HWQ_quantum_shape s"
      and TAUS: "C_Tau_Star s s'"
  shows "E1_HWQ_quantum_shape s'"
  using TAUS PRE
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have SH2: "E1_HWQ_quantum_shape s2"
    using Tau_preserves_quantum_shape_step[OF N2 step.prems step.hyps(1)] .
  show ?case
    using step.IH[OF SH2] .
qed

lemma Tau_preserves_quantum_slots23_step:
  assumes N2: "N_Procs = 2"
      and PRE: "E1_HWQ_quantum_shape s"
      and TAU: "C_Tau s s'"
  shows "Q_arr s' 2 = Q_arr s 2 \<and> Q_arr s' 3 = Q_arr s 3"
proof -
  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp

  from PRE have PCP2: "program_counter s P2 = ''L0''"
    and BR:
      "((Q_arr s 1 = A1) \<and>
         ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
       \<or>
       ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
    unfolding E1_HWQ_quantum_shape_def by auto

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto

  have pneqP2: "p \<noteq> P2"
  proof
    assume pP2: "p = P2"
    from STEP show False
      using pP2 PCP2
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def Let_def
      by auto
  qed

  have pP1: "p = P1"
    using PIN N2 pneqP2 by auto

  have STEP1: "Sys_D1 P1 s s' \<or> Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
    using STEP pP1 BR
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def program_counter_def
    by auto

  show ?thesis
    using STEP1 BR
    unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
              Q_arr_def program_counter_def j_var_def Let_def
    by (elim disjE) (auto split: if_splits)
qed

lemma Tau_Star_preserves_quantum_slots23:
  assumes N2: "N_Procs = 2"
      and PRE: "E1_HWQ_quantum_shape s"
      and TAUS: "C_Tau_Star s s'"
  shows "Q_arr s' 2 = Q_arr s 2 \<and> Q_arr s' 3 = Q_arr s 3"
  using TAUS PRE
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have SH2: "E1_HWQ_quantum_shape s2"
    using Tau_preserves_quantum_shape_step[OF N2 step.prems step.hyps(1)] .
  have EQ2: "Q_arr s2 2 = Q_arr s1 2 \<and> Q_arr s2 3 = Q_arr s1 3"
    using Tau_preserves_quantum_slots23_step[OF N2 step.prems step.hyps(1)] .
  have "Q_arr s3 2 = Q_arr s2 2 \<and> Q_arr s3 3 = Q_arr s2 3"
    using step.IH[OF SH2] .
  with EQ2 show ?case
    by auto
qed

lemma C_Tau_impossible_if_P1P2_L0:
  assumes N2: "N_Procs = 2"
      and PC1: "program_counter s P1 = ''L0''"
      and PC2: "program_counter s P2 = ''L0''"
      and TAU: "C_Tau s s'"
  shows False
proof -
  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp
  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto
  have "p = P1 \<or> p = P2"
    using PIN N2 by auto
  then show False
    using STEP PC1 PC2
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
              Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
              program_counter_def Let_def
    by auto
qed

lemma C_Tau_Star_eq_if_P1P2_L0:
  assumes N2: "N_Procs = 2"
      and PC1: "program_counter s P1 = ''L0''"
      and PC2: "program_counter s P2 = ''L0''"
      and TAUS: "C_Tau_Star s s'"
  shows "s' = s"
  using TAUS PC1 PC2
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case step
  (* , auto C_Tau_impossible_if_P1P2_L0 automatic *)
  then show ?case
    using C_Tau_impossible_if_P1P2_L0[OF N2]
    by blast 
qed

(* Auxiliary lemma. *)
lemma hwq_e2_snapshot_after_ret1:
  assumes N2: "N_Procs = 2"
      and SHQ: "E1_HWQ_quantum_shape sk0"
      and PATH1: "C_Path sk0 e2_part1 s_ret1"
  shows "program_counter s_ret1 P1 = ''L0'' \<and>
         program_counter s_ret1 P2 = ''L0'' \<and>
         X_var s_ret1 = 4 \<and>
         Q_arr s_ret1 1 = BOT \<and>
         Q_arr s_ret1 2 = Q_arr sk0 2 \<and>
         Q_arr s_ret1 3 = Q_arr sk0 3"
proof -
  (* Step 1. *)
  from SHQ have INV0: "system_invariant sk0"
    and X4_0: "X_var sk0 = 4"
    and PC2_0: "program_counter sk0 P2 = ''L0''"
    and Q23_0: "{Q_arr sk0 2, Q_arr sk0 3} = {A2, A3}"
    and BR0:
      "((Q_arr sk0 1 = A1) \<and> ((program_counter sk0 P1 \<in> {''D1'', ''D2''}) \<or> (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1)))
       \<or>
       ((Q_arr sk0 1 = BOT) \<and> program_counter sk0 P1 = ''D4'' \<and> x_var sk0 P1 = A1)"
    unfolding E1_HWQ_quantum_shape_def by auto

  (* Step 2.2.1.1.1. *)
  have SPLIT1: "e2_part1 = [None, None] @ [Some (mk_obs deq A1 P1 ret)]"
    unfolding e2_part1_def by simp

  obtain m1 where PATH_PRE: "C_Path sk0 [None, None] m1"
              and MATCH_RET: "C_Match m1 (Some (mk_obs deq A1 P1 ret)) s_ret1"
    using C_Path_snocE[OF PATH1[unfolded SPLIT1]] by blast

  (* Step 3.1.1.2.3.4. *)
  (* : P2 L0, trace P2 call, P2 preserve L0 *)
  obtain u1 v1 where TAU_A: "C_Tau_Star m1 u1"
                 and D4_ACT: "C_StepCR u1 (Some (mk_obs deq A1 P1 ret)) v1"
                 and TAU_B: "C_Tau_Star v1 s_ret1"
    using C_Match_someE[OF MATCH_RET] by blast

  (* Step 4.4. *)
  from D4_ACT obtain p where PIN: "p \<in> ProcSet"
    and SD4: "Sys_D4 p u1 v1"
    and LAB: "mk_obs deq (x_var u1 p) p ret = mk_obs deq A1 P1 ret"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  from LAB have pP1: "p = P1" by (simp add: mk_obs_def)

  have PC1_v1: "program_counter v1 P1 = ''L0''"
    using SD4 pP1 unfolding Sys_D4_def C_D4_def program_counter_def by auto

have TAUS_PRE: "C_Tau_Star sk0 m1"
    using C_Path_Nones_is_Tau_Star[OF PATH_PRE] by auto

  have TAUS_U1: "C_Tau_Star sk0 u1"
    using C_Tau_Star_trans[OF TAUS_PRE TAU_A] .

  have SHQ_u1: "E1_HWQ_quantum_shape u1"
    using Tau_Star_preserves_quantum_shape[OF N2 SHQ TAUS_U1] .

  have Q23_u1: "Q_arr u1 2 = Q_arr sk0 2 \<and> Q_arr u1 3 = Q_arr sk0 3"
    using Tau_Star_preserves_quantum_slots23[OF N2 SHQ TAUS_U1] .

  have PC1_u1: "program_counter u1 P1 = ''D4''"
    using SD4 pP1
    unfolding Sys_D4_def C_D4_def program_counter_def
    by auto

  have XV_u1: "x_var u1 P1 = A1"
    using LAB pP1 by (simp add: mk_obs_def)

  have Q1_u1: "Q_arr u1 1 = BOT"
    using SHQ_u1 PC1_u1 XV_u1
    unfolding E1_HWQ_quantum_shape_def
    by auto

  have PC2_u1: "program_counter u1 P2 = ''L0''"
    using SHQ_u1 unfolding E1_HWQ_quantum_shape_def by auto

  have X4_u1: "X_var u1 = 4"
    using SHQ_u1 unfolding E1_HWQ_quantum_shape_def by auto

  have PC2_v1: "program_counter v1 P2 = ''L0''"
    using SD4 pP1 PC2_u1
    unfolding Sys_D4_def C_D4_def program_counter_def
    by auto

  have X4_v1: "X_var v1 = 4"
    using SD4 pP1 X4_u1
    unfolding Sys_D4_def C_D4_def X_var_def
    by auto

  have Q1_v1: "Q_arr v1 1 = BOT"
    using SD4 pP1 Q1_u1
    unfolding Sys_D4_def C_D4_def Q_arr_def
    by auto

  have Q2_v1: "Q_arr v1 2 = Q_arr sk0 2"
    using SD4 pP1 Q23_u1
    unfolding Sys_D4_def C_D4_def Q_arr_def
    by auto

  have Q3_v1: "Q_arr v1 3 = Q_arr sk0 3"
    using SD4 pP1 Q23_u1
    unfolding Sys_D4_def C_D4_def Q_arr_def
    by auto

  have EQ_TAIL: "s_ret1 = v1"
    using C_Tau_Star_eq_if_P1P2_L0[OF N2 PC1_v1 PC2_v1 TAU_B] .

  have FINAL_P1: "program_counter s_ret1 P1 = ''L0''"
    using PC1_v1 EQ_TAIL by simp
  have FINAL_P2: "program_counter s_ret1 P2 = ''L0''"
    using PC2_v1 EQ_TAIL by simp
  have FINAL_X4: "X_var s_ret1 = 4"
    using X4_v1 EQ_TAIL by simp
  have FINAL_Q1: "Q_arr s_ret1 1 = BOT"
    using Q1_v1 EQ_TAIL by simp
  have FINAL_Q2: "Q_arr s_ret1 2 = Q_arr sk0 2"
    using Q2_v1 EQ_TAIL by simp
  have FINAL_Q3: "Q_arr s_ret1 3 = Q_arr sk0 3"
    using Q3_v1 EQ_TAIL by simp

  show ?thesis
    using FINAL_P1 FINAL_P2 FINAL_X4 FINAL_Q1 FINAL_Q2 FINAL_Q3 by auto
qed

(* ========================================================================= *)
(* State-collapse helper lemma: P1 (Symbolic Execution) *)
(* ========================================================================= *)

(* Step 1.0. *)
lemma hwq_L0_L0_no_tau:
  assumes "N_Procs = 2"
      and "program_counter s P1 = ''L0''"
      and "program_counter s P2 = ''L0''"
      and "C_Tau s s'"
  shows False
proof -
  from assms(4) have "C_StepCR s None s'" unfolding C_Tau_def by simp
  then obtain p where PIN: "p \<in> ProcSet" and "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto
  moreover have "p = P1 \<or> p = P2" using PIN assms(1) by auto
  ultimately show False
    using assms(2) assms(3)
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def program_counter_def
    by auto
qed

lemma hwq_L0_L0_tau_star_eq:
  assumes "N_Procs = 2"
      and "C_Tau_Star s s'"
      and "program_counter s P1 = ''L0''"
      and "program_counter s P2 = ''L0''"
  shows "s' = s"
using assms(2) assms(3) assms(4)
proof (induction rule: C_Tau_Star.induct)
  case refl then show ?case by simp
next
  case (step s1 s2 s3)
  have False using hwq_L0_L0_no_tau[OF assms(1) step.prems(1) step.prems(2) step.hyps(1)] .
  then show ?case by simp
qed

(* Step 2.1.2. *)
lemma hwq_p1_deq_symbolic_execution_step:
  assumes N2: "N_Procs = 2"
      and TAU: "C_Tau s t"
      and INV_S: "program_counter s P2 = ''L0'' \<and>
                  X_var s = 4 \<and> Q_arr s 1 = BOT \<and> V \<noteq> BOT \<and>
                  ((Q_arr s 2 = V \<and>
                    (program_counter s P1 = ''D1'' \<or>
                     program_counter s P1 = ''D2'' \<or>
                     (program_counter s P1 = ''D3'' \<and> j_var s P1 \<in> {1, 2})))
                   \<or>
                   (Q_arr s 2 = BOT \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = V))"
  shows "program_counter t P2 = ''L0'' \<and>
         X_var t = 4 \<and> Q_arr t 1 = BOT \<and> V \<noteq> BOT \<and>
         ((Q_arr t 2 = V \<and>
           (program_counter t P1 = ''D1'' \<or>
            program_counter t P1 = ''D2'' \<or>
            (program_counter t P1 = ''D3'' \<and> j_var t P1 \<in> {1, 2})))
          \<or>
          (Q_arr t 2 = BOT \<and> program_counter t P1 = ''D4'' \<and> x_var t P1 = V))"
proof -
  from TAU have STEP0: "C_StepCR s None t" unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP: "Sys_E1 p s t \<or> Sys_E2 p s t \<or> Sys_D1 p s t \<or> Sys_D2 p s t \<or> Sys_D3 p s t"
    by (cases rule: C_StepCR.cases) auto

  from INV_S have PC2: "program_counter s P2 = ''L0''"
    and X4: "X_var s = 4"
    and Q1: "Q_arr s 1 = BOT"
    and VNB: "V \<noteq> BOT"
    and P1_STATE:
      "((Q_arr s 2 = V \<and>
         (program_counter s P1 = ''D1'' \<or>
          program_counter s P1 = ''D2'' \<or>
          (program_counter s P1 = ''D3'' \<and> j_var s P1 \<in> {1, 2})))
        \<or>
        (Q_arr s 2 = BOT \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = V))"
    by auto

  have pP1: "p = P1"
  proof (rule ccontr)
    assume pneq: "p \<noteq> P1"
    from PIN N2 pneq have pP2: "p = P2" by auto
    from STEP show False
      using pP2 PC2
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def Let_def
      by auto
  qed

  have STEP_P1: "Sys_E1 P1 s t \<or> Sys_E2 P1 s t \<or> Sys_D1 P1 s t \<or> Sys_D2 P1 s t \<or> Sys_D3 P1 s t"
    using STEP pP1 by simp

  (* isolation, *)
  have CASE_E1: "Sys_E1 P1 s t \<Longrightarrow> ?thesis"
    using P1_STATE unfolding Sys_E1_def C_E1_def program_counter_def by auto

  have CASE_E2: "Sys_E2 P1 s t \<Longrightarrow> ?thesis"
    using P1_STATE unfolding Sys_E2_def C_E2_def program_counter_def by auto

  have CASE_D1: "Sys_D1 P1 s t \<Longrightarrow> ?thesis"
    using P1_STATE PC2 X4 Q1 VNB
    unfolding Sys_D1_def C_D1_def program_counter_def j_var_def X_var_def Q_arr_def x_var_def Let_def 
    by (auto split: if_splits)

  have CASE_D2: "Sys_D2 P1 s t \<Longrightarrow> ?thesis"
    using P1_STATE PC2 X4 Q1 VNB
    unfolding Sys_D2_def C_D2_def program_counter_def j_var_def X_var_def Q_arr_def x_var_def T_D2_EnterLoop_def Let_def 
    by (auto split: if_splits)

  have CASE_D3: "Sys_D3 P1 s t \<Longrightarrow> ?thesis"
    using P1_STATE PC2 X4 Q1 VNB
    unfolding Sys_D3_def C_D3_def program_counter_def j_var_def X_var_def Q_arr_def x_var_def Let_def BOT_def 
    by (auto split: if_splits)

  from STEP_P1 CASE_E1 CASE_E2 CASE_D1 CASE_D2 CASE_D3 show ?thesis 
    by blast
qed

(* 3. Inductive closure *)
lemma hwq_p1_deq_symbolic_execution_tau_star:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and INV_S: "program_counter s P2 = ''L0'' \<and> X_var s = 4 \<and> Q_arr s 1 = BOT \<and> V \<noteq> BOT \<and>
                  ((Q_arr s 2 = V \<and>
                    (program_counter s P1 = ''D1'' \<or>
                     program_counter s P1 = ''D2'' \<or>
                     (program_counter s P1 = ''D3'' \<and> j_var s P1 \<in> {1, 2})))
                   \<or>
                   (Q_arr s 2 = BOT \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = V))"
  shows "program_counter t P2 = ''L0'' \<and> X_var t = 4 \<and> Q_arr t 1 = BOT \<and> V \<noteq> BOT \<and>
         ((Q_arr t 2 = V \<and>
           (program_counter t P1 = ''D1'' \<or>
            program_counter t P1 = ''D2'' \<or>
            (program_counter t P1 = ''D3'' \<and> j_var t P1 \<in> {1, 2})))
          \<or>
          (Q_arr t 2 = BOT \<and> program_counter t P1 = ''D4'' \<and> x_var t P1 = V))"
  using TAUS INV_S
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by auto
next
  case (step s1 s2 s3)
  have INV_S2:
    "program_counter s2 P2 = ''L0'' \<and> X_var s2 = 4 \<and> Q_arr s2 1 = BOT \<and> V \<noteq> BOT \<and>
     ((Q_arr s2 2 = V \<and>
       (program_counter s2 P1 = ''D1'' \<or>
        program_counter s2 P1 = ''D2'' \<or>
        (program_counter s2 P1 = ''D3'' \<and> j_var s2 P1 \<in> {1, 2})))
      \<or>
      (Q_arr s2 2 = BOT \<and> program_counter s2 P1 = ''D4'' \<and> x_var s2 P1 = V))"
    using hwq_p1_deq_symbolic_execution_step[OF N2 step.hyps(1) step.prems] .

  show ?case using step.IH[OF INV_S2] .
qed

(* Final main body: apply precise unchanged *)

lemma hwq_e2_second_deq_returns_q2:
  assumes N2: "N_Procs = 2"
      and PC1: "program_counter s_ret1 P1 = ''L0''"
      and PC2: "program_counter s_ret1 P2 = ''L0''"
      and X4: "X_var s_ret1 = 4"
      and Q1: "Q_arr s_ret1 1 = BOT"
      and Q2: "Q_arr s_ret1 2 = V"
      and V_NOT_BOT: "V \<noteq> BOT"
      and MATCH2_SNOC: "C_Path s_ret1 [Some (mk_obs deq BOT P1 call), None, None, None, None, None] m2"
      and TAU: "C_Tau_Star m2 u2"
      and STEP: "C_StepCR u2 (Some (mk_obs deq A2 P1 ret)) v2"
  shows "x_var u2 P1 = V"
proof -
  from MATCH2_SNOC obtain s_c where
      MCALL: "C_Match s_ret1 (Some (mk_obs deq BOT P1 call)) s_c"
    and PNONES: "C_Path s_c [None, None, None, None, None] m2"
    by (cases rule: C_Path.cases) auto

  obtain uc vc where
      T1: "C_Tau_Star s_ret1 uc"
    and SCALL: "C_StepCR uc (Some (mk_obs deq BOT P1 call)) vc"
    and T2: "C_Tau_Star vc s_c"
    using C_Match_someE[OF MCALL] by blast

  have UC_EQ: "uc = s_ret1"
    using C_Tau_Star_eq_if_P1P2_L0[OF N2 PC1 PC2 T1] .

  have SCALL_SIMP: "C_StepCR s_ret1 (Some (mk_obs deq BOT P1 call)) vc"
    using SCALL UC_EQ by simp

  from SCALL_SIMP obtain p where
      PIN: "p \<in> ProcSet"
    and SL0: "Sys_L0 p s_ret1 vc"
    and PCD1: "program_counter vc p = ''D1''"
    and LAB: "mk_obs deq BOT p call = mk_obs deq BOT P1 call"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  have pP1: "p = P1"
    using LAB
    unfolding mk_obs_def
    by auto

  have CL0: "C_L0 p (fst s_ret1) (fst vc)"
    using SL0
    unfolding Sys_L0_def
    by auto

  have VC_PC1: "program_counter vc P1 = ''D1''"
    using PCD1 pP1
    by simp

  have VC_PC2: "program_counter vc P2 = ''L0''"
    using CL0 pP1 PC2
    unfolding C_L0_def program_counter_def Let_def
    by (auto split: if_splits)

  have VC_X4: "X_var vc = 4"
    using CL0 X4
    unfolding C_L0_def X_var_def Let_def
    by (auto split: if_splits)

  have VC_Q1: "Q_arr vc 1 = BOT"
    using CL0 Q1
    unfolding C_L0_def Q_arr_def Let_def
    by (auto split: if_splits)

  have VC_Q2: "Q_arr vc 2 = V"
    using CL0 Q2
    unfolding C_L0_def Q_arr_def Let_def
    by (auto split: if_splits)

  have VC_STATE:
    "program_counter vc P2 = ''L0'' \<and>
     X_var vc = 4 \<and>
     Q_arr vc 1 = BOT \<and>
     V \<noteq> BOT \<and>
     ((Q_arr vc 2 = V \<and>
       (program_counter vc P1 = ''D1'' \<or>
        program_counter vc P1 = ''D2'' \<or>
        (program_counter vc P1 = ''D3'' \<and> j_var vc P1 \<in> {1, 2})))
      \<or>
      (Q_arr vc 2 = BOT \<and> program_counter vc P1 = ''D4'' \<and> x_var vc P1 = V))"
    using VC_PC1 VC_PC2 VC_X4 VC_Q1 VC_Q2 V_NOT_BOT
    by auto

  have SET_NONE5: "set [None, None, None, None, None] \<subseteq> {None}"
    by auto

  have TAU_c_m2: "C_Tau_Star s_c m2"
    using C_Path_Nones_is_Tau_Star[OF PNONES SET_NONE5] .

  have TAU_vc_m2: "C_Tau_Star vc m2"
    using C_Tau_Star_trans[OF T2 TAU_c_m2] .

  have TAU_TOTAL: "C_Tau_Star vc u2"
    using C_Tau_Star_trans[OF TAU_vc_m2 TAU] .

  have U2_FULL:
    "program_counter u2 P2 = ''L0'' \<and>
     X_var u2 = 4 \<and>
     Q_arr u2 1 = BOT \<and>
     V \<noteq> BOT \<and>
     ((Q_arr u2 2 = V \<and>
       (program_counter u2 P1 = ''D1'' \<or>
        program_counter u2 P1 = ''D2'' \<or>
        (program_counter u2 P1 = ''D3'' \<and> j_var u2 P1 \<in> {1, 2})))
      \<or>
      (Q_arr u2 2 = BOT \<and> program_counter u2 P1 = ''D4'' \<and> x_var u2 P1 = V))"
    using hwq_p1_deq_symbolic_execution_tau_star[OF N2 TAU_TOTAL VC_STATE] .

  have U2_INV:
    "((Q_arr u2 2 = V \<and>
       (program_counter u2 P1 = ''D1'' \<or>
        program_counter u2 P1 = ''D2'' \<or>
        (program_counter u2 P1 = ''D3'' \<and> j_var u2 P1 \<in> {1, 2})))
      \<or>
      (Q_arr u2 2 = BOT \<and> program_counter u2 P1 = ''D4'' \<and> x_var u2 P1 = V))"
    using U2_FULL by auto

  from STEP obtain p_ret where
      SD4: "Sys_D4 p_ret u2 v2"
    and LAB_RET: "mk_obs deq (x_var u2 p_ret) p_ret ret = mk_obs deq A2 P1 ret"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  have p_retP1: "p_ret = P1"
    using LAB_RET
    unfolding mk_obs_def
    by auto

  have PC_u2: "program_counter u2 P1 = ''D4''"
    using SD4 p_retP1
    unfolding Sys_D4_def C_D4_def program_counter_def
    by auto

  from U2_INV PC_u2 show ?thesis
    by auto
qed

(* ========================================================================= *)
(* Auxiliary lemma. *)
(* Proof step. *)
(* ========================================================================= *)

lemma hwq_e2_forces_exact_shape:
  assumes N2: "N_Procs = 2"
      and SHQ: "E1_HWQ_quantum_shape sk0"
      and E2MATCH: "C_Path sk0 e2_labels s2"
  shows "Q_arr sk0 2 = A2 \<and> Q_arr sk0 3 = A3"
proof -
  have SPLIT: "e2_labels = e2_part1 @ (e2_part2 @ e2_part3)"
    using e2_labels_split by simp

  obtain s_ret1 where
      PATH1: "C_Path sk0 e2_part1 s_ret1"
    and REST1: "C_Path s_ret1 (e2_part2 @ e2_part3) s2"
    using C_Path_appendE[OF E2MATCH[unfolded SPLIT]] by blast

  obtain s_ret2 where
      PATH2: "C_Path s_ret1 e2_part2 s_ret2"
    and PATH3: "C_Path s_ret2 e2_part3 s2"
    using C_Path_appendE[OF REST1] by blast

  obtain m2 where
      MATCH2_SNOC: "C_Path s_ret1 [Some (mk_obs deq BOT P1 call), None, None, None, None, None] m2"
    and MATCH2_RET: "C_Match m2 (Some (mk_obs deq A2 P1 ret)) s_ret2"
    using C_Path_snocE[OF PATH2[unfolded e2_part2_snoc]] by blast

  obtain u2 v2 where
      TAU2: "C_Tau_Star m2 u2"
    and D4_2: "C_StepCR u2 (Some (mk_obs deq A2 P1 ret)) v2"
    and TAU2B: "C_Tau_Star v2 s_ret2"
    using C_Match_someE[OF MATCH2_RET] by blast

  have X2: "x_var u2 P1 = A2"
  proof -
    from D4_2 obtain p where
        SD4: "Sys_D4 p u2 v2"
      and LAB: "mk_obs deq (x_var u2 p) p ret = mk_obs deq A2 P1 ret"
      by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)
    from LAB show ?thesis
      by (auto simp: mk_obs_def)
  qed

  have SNAP1:
    "program_counter s_ret1 P1 = ''L0'' \<and>
     program_counter s_ret1 P2 = ''L0'' \<and>
     X_var s_ret1 = 4 \<and>
     Q_arr s_ret1 1 = BOT \<and>
     Q_arr s_ret1 2 = Q_arr sk0 2 \<and>
     Q_arr s_ret1 3 = Q_arr sk0 3"
    using hwq_e2_snapshot_after_ret1[OF N2 SHQ PATH1] .

  have Q23: "{Q_arr sk0 2, Q_arr sk0 3} = {A2, A3}"
    using SHQ unfolding E1_HWQ_quantum_shape_def by auto

  have "Q_arr sk0 2 = A2 \<and> Q_arr sk0 3 = A3"
  proof (rule ccontr)
    assume NOT_EXACT: "\<not> (Q_arr sk0 2 = A2 \<and> Q_arr sk0 3 = A3)"

    have REVERSED2: "Q_arr sk0 2 = A3"
      using Q23 NOT_EXACT
      by (simp add: doubleton_eq_iff) 

    from SNAP1 have
        PC1_r1: "program_counter s_ret1 P1 = ''L0''"
      and PC2_r1: "program_counter s_ret1 P2 = ''L0''"
      and X4_r1: "X_var s_ret1 = 4"
      and Q1_r1: "Q_arr s_ret1 1 = BOT"
      and Q2_r1: "Q_arr s_ret1 2 = Q_arr sk0 2"
      and Q3_r1: "Q_arr s_ret1 3 = Q_arr sk0 3"
      by auto

    have Q2_r1_A3: "Q_arr s_ret1 2 = A3"
      using Q2_r1 REVERSED2 by simp

    have XA3: "x_var u2 P1 = A3"
      using hwq_e2_second_deq_returns_q2[OF N2 PC1_r1 PC2_r1 X4_r1 Q1_r1 Q2_r1_A3 _ MATCH2_SNOC TAU2 D4_2]
      using BOT_def by linarith

    from XA3 X2 show False
      by simp
  qed

  thus ?thesis .
qed

(* Proof step. *)
lemma collapse_quantum_to_relaxed:
  assumes N2: "N_Procs = 2"
      and SHQ: "E1_HWQ_quantum_shape sk0"
      and E2MATCH: "C_Path sk0 e2_labels s2"
  shows "E1_HWQ_relaxed_shape sk0"
  using assms hwq_e2_forces_exact_shape 
  unfolding E1_HWQ_quantum_shape_def E1_HWQ_relaxed_shape_def 
  by auto



(* ==================================================================== *)
(* replace: overwrite E1_HWQ_pre_shape_tau_stable *)
(* ==================================================================== *)

text \<open>
  The core bridge for weak simulation: absorbing leading tau-stars into the first visible step.
  \<close>
lemma C_Path_absorb_leading_tau:
  assumes TAU: "C_Tau_Star s0 s1"
      and PATH: "C_Path s1 ls s2"
      and NOT_EMP: "ls \<noteq> []"
  shows "C_Path s0 ls s2"
proof -
  from PATH NOT_EMP obtain l xs u where
      EQ: "ls = l # xs"
    and M: "C_Match s1 l u"
    and P: "C_Path u xs s2"
    by (cases rule: C_Path.cases) auto

  have M_new: "C_Match s0 l u"
  proof (cases l)
    case None
   
  
     then have T: "C_Tau_Star s1 u"
      using M C_Match_noneE by auto
    have "C_Tau_Star s0 u"
      using C_Tau_Star_trans[OF TAU T] .
  then show ?thesis
      using None C_Match.match_tau by simp
  next
    case (Some a)
    from Some M have M': "C_Match s1 (Some a) u" by simp
    from C_Match_someE[OF M'] obtain v1 v2 where
        T1: "C_Tau_Star s1 v1"
      and STEP: "C_StepCR v1 (Some a) v2"
      and T2: "C_Tau_Star v2 u"
      by blast
    have "C_Tau_Star s0 v1"
      using C_Tau_Star_trans[OF 
  
  TAU T1] .
    then show ?thesis
      using STEP T2 Some by (auto intro: C_Match.match_vis)
  qed

  show ?thesis
    unfolding EQ using C_Path.cons[OF M_new P] .
  qed

subsection \<open>Relaxed Endpoint Shapes and Closures\<close>

text \<open>
  These two shapes map exactly to the physics of the weak matching endpoint.
  During the trailing tau sequence before P2 returns, P1 may remain scanning 
  in {D1,D2,D3}, or it may cross into D4 and commit to returning A1.
  \<close>


subsection \<open>Contradiction Branching\<close>



text \<open>New Bridge Lemmas\<close>

lemma scanning_D3_j1_implies_old_shape:
  assumes SH: "E1_HWQ_relaxed_shape sk0"
   
      and D3J1: "Q_arr sk0 1 = A1 \<and> program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1"
  shows "E1_HWQ_shape sk0"
proof -
  from SH have
      INV: "system_invariant sk0"
    and X4:  "X_var sk0 = 4"
    and Q2:  "Q_arr sk0 2 = A2"
    and Q3:  "Q_arr sk0 3 = A3"
    
  and PCP2: "program_counter sk0 P2 = ''L0''"
    unfolding E1_HWQ_relaxed_shape_def
    by auto
  from D3J1 have Q1: "Q_arr sk0 1 = 
  A1"
    and PCP1: "program_counter sk0 P1 = ''D3''"
    and J1: "j_var sk0 P1 = 1"
    by auto
  
  have J_IN: "j_var sk0 P1 \<in> {1,2,3}"
    using J1 by simp

  show ?thesis
    unfolding E1_HWQ_shape_def
    using INV X4 Q1 Q2 Q3 PCP1 PCP2 J_IN
    by auto
qed

subsection \<open>Envelopes and Contradiction for E3\<close>



lemma e3_labels_split_last:
  "e3_labels = e3_before_last_labels @ [Some (mk_obs deq A3 P1 ret)]"
  unfolding e3_labels_def e3_before_last_labels_def
  by simp



lemma e3_before_last_split_ret:
  "e3_before_last_labels =
     e3_before_p2_ret_labels @
     [Some (mk_obs deq A1 P2 ret)] @
     e3_after_p2_ret_before_last_labels"
  unfolding e3_before_last_labels_def
            e3_before_p2_ret_labels_def
            e3_after_p2_ret_before_last_labels_def
  by simp

(* 1: P2 return A1 envelope *)


(* ========================================================================= *)
(* 2.                 
                                      *)
(* ========================================================================= *)

lemma pre_envelope_base:
  assumes SH: "E1_HWQ_relaxed_shape sk0"
      and P12: "program_counter sk0 P1 \<in> {''D1'', ''D2''}"
  shows "E3_Pre_Ret_Envelope sk0"
proof -
  from SH have INV: "system_invariant sk0"
    and P2L0: "program_counter sk0 P2 = ''L0''"
    and Q2: "Q_arr sk0 2 = A2"
    and Q3: "Q_arr sk0 3 = A3"
  
    unfolding E1_HWQ_relaxed_shape_def by auto
  from SH P12 have Q1: "Q_arr sk0 1 = A1"
    unfolding E1_HWQ_relaxed_shape_def by auto
  show ?thesis
    unfolding E3_Pre_Ret_Envelope_def
    using INV P12 P2L0 Q1 Q2 Q3
    using BOT_def by auto
qed

lemma envelope_transition_at_p2_ret:
  assumes N2: "N_Procs = 2"
      and ENV: "E3_Pre_Ret_Envelope s"
      and VIS: "C_StepCR s (Some (mk_obs deq A1 P2 ret)) s'"
  shows "E3_Post_Ret_Envelope s'"
proof -
  from ENV have INV: "system_invariant s"
    and P1_PC: "program_counter s 
  P1 \<in> {''D1'',''D2'',''D3'',''D4''}"
    and P1_D3: "program_counter s P1 = ''D3'' \<longrightarrow> j_var s P1 \<in> {1,2}"
    and P1_D4: "program_counter s P1 = ''D4'' \<longrightarrow> x_var s P1 \<in> {A1,A2}"
    and Q1_IFF: "Q_arr s 1 = BOT \<longleftrightarrow> (program_counter s P1 = ''D4'' \<and> x_var s P1 = A1) \<or>
                                      (program_counter s P2 = ''D4'' 
  \<and> x_var s P2 = A1)"
    and Q2_IFF: "Q_arr s 2 = BOT \<longleftrightarrow> (program_counter s P1 = ''D4'' \<and> x_var s P1 = A2) \<or>
                                      (program_counter s P2 = ''D4'' \<and> x_var s P2 = A2)"
    and Q2_VAL: "Q_arr s 2 \<noteq> BOT \<longrightarrow> Q_arr s 2 = A2"
    and Q3_A3: "Q_arr s 
  3 = A3"
    unfolding E3_Pre_Ret_Envelope_def by auto

  have NXT: "Next s s'" using C_StepCR_into_Next[OF VIS] .
  have INV': "system_invariant s'" using Sys_Inv_Step[OF INV NXT] .

  from VIS show ?thesis
  proof cases
    case (C_Sys_D4_vis p)
    from C_Sys_D4_vis have pP2: "p = P2" and xA1: "x_var s p = A1"
      unfolding mk_obs_def by auto

    from C_Sys_D4_vis pP2
    have P1_PC_eq: "program_counter s' P1 = program_counter s P1"
     and P1_J_eq:  "j_var s' P1 = j_var s P1"
     and P1_X_eq:  "x_var s' P1 = x_var s P1"
     and P2_PC_new: 
  "program_counter s' P2 = ''L0''" (* P2 return L0 *)
     and Q1_eq:    "Q_arr s' 1 = Q_arr s 1"
     and Q2_eq:    "Q_arr s' 2 = Q_arr s 2"
     and Q3_eq:    "Q_arr s' 3 = Q_arr s 3"
      unfolding Sys_D4_def C_D4_def program_counter_def j_var_def x_var_def Q_arr_def Let_def
      by (auto split: if_splits)

    (* Proof step. *)
    have Q1_BOT_new: "Q_arr s' 1 = BOT"
 
     proof -
      have "program_counter s P2 = ''D4'' \<and> x_var s P2 = A1"
        using C_Sys_D4_vis pP2 xA1 unfolding Sys_D4_def C_D4_def program_counter_def by auto
      hence "(program_counter s P1 = ''D4'' \<and> x_var s P1 = A1) \<or> 
             (program_counter s P2 = ''D4'' \<and> x_var s P2 = A1)" by blast
      with Q1_IFF have "Q_arr s 1 = BOT" by simp
   
      with Q1_eq show "Q_arr s' 1 = BOT" by simp
    qed

    have Q2_IFF_new: "Q_arr s' 2 = BOT \<longleftrightarrow> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2"
    proof
      assume "Q_arr s' 2 = BOT"
      with Q2_eq have "Q_arr s 2 = BOT" by simp
      with Q2_IFF have "(program_counter s P1 = ''D4'' \<and> x_var s P1 = A2) \<or>
            
              (program_counter s P2 = ''D4'' \<and> x_var s P2 = A2)" by simp
      moreover have "x_var s P2 = A1" using xA1 pP2 by simp
      ultimately have "program_counter s P1 = ''D4'' \<and> x_var s P1 = A2" by auto
      with P1_PC_eq P1_X_eq show "program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2" by simp
    next
      assume "program_counter s' P1 = ''D4'' \<and> 
  x_var s' P1 = A2"
      with P1_PC_eq P1_X_eq have "program_counter s P1 = ''D4'' \<and> x_var s P1 = A2" by simp
      hence "(program_counter s P1 = ''D4'' \<and> x_var s P1 = A2) \<or> 
             (program_counter s P2 = ''D4'' \<and> x_var s P2 = A2)" by blast
      with Q2_IFF have "Q_arr s 2 = BOT" by simp
      with Q2_eq show "Q_arr s' 2 = BOT" by 
  simp
    qed

    have Q2_VAL_new: "Q_arr s' 2 \<noteq> BOT \<longrightarrow> Q_arr s' 2 = A2"
      using Q2_eq Q2_VAL by auto

    show ?thesis
      unfolding E3_Post_Ret_Envelope_def
      using INV' P2_PC_new Q1_BOT_new P1_PC P1_D3 P1_D4 P1_PC_eq P1_J_eq P1_X_eq Q3_A3 Q3_eq Q2_IFF_new Q2_VAL_new
      by auto
  qed (auto simp: mk_obs_def)
qed

(* ========================================================================= *)
(* 3.  tau （）                     
                  *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Proof step. *)
(* ========================================================================= *)
lemma pre_ret_envelope_preserved_by_tau:
  assumes N2: "N_Procs = 2"
      and ENV: "E3_Pre_Ret_Envelope s"
      and TAU: "C_Tau s s'"
  shows "E3_Pre_Ret_Envelope s'"
proof -
  have STEP0: "C_StepCR s None s'" using TAU unfolding C_Tau_def by simp
  have NXT: "Next s s'" using C_StepCR_into_Next[OF STEP0] .
  from ENV have INV: "system_invariant s" unfolding E3_Pre_Ret_Envelope_def by auto
  have INV': "system_invariant s'" using Sys_Inv_Step[OF INV NXT] .
  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP: "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto
  have p_cases: "p = P1 \<or> p = P2" using PIN N2 by auto

  from p_cases show ?thesis
  proof
    (* ==================== P1 branch ==================== *)
    assume pP1: "p = P1"
    from STEP show ?thesis
    proof (elim disjE)
   
      assume H: "Sys_E1 p s s'"
      have False using H pP1 ENV unfolding Sys_E1_def C_E1_def E3_Pre_Ret_Envelope_def program_counter_def by auto
      then show ?thesis ..
    next
      assume H: "Sys_E2 p s s'"
      have False using H pP1 ENV unfolding Sys_E2_def C_E2_def E3_Pre_Ret_Envelope_def program_counter_def by auto
      then show ?thesis ..
    next
      assume H: "Sys_D1 p s s'"
      show ?thesis 
  using H pP1 N2 ENV INV' unfolding E3_Pre_Ret_Envelope_def Sys_D1_def C_D1_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def by (auto split: if_splits)
    next
      assume H: "Sys_D2 p s s'"
      show ?thesis using H pP1 N2 ENV INV' unfolding E3_Pre_Ret_Envelope_def Sys_D2_def C_D2_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def by (auto split: if_splits)
    next
      assume H: "Sys_D3 p s s'"
      have J_cases: "j_var s P1 = 1 \<or> j_var s P1 = 2" 
     
       using H pP1 ENV unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def by auto
      from J_cases show ?thesis
      proof
        assume J1: "j_var s P1 = 1"
        have Q1_cases: "Q_arr s 1 = BOT \<or> Q_arr s 1 = A1" using ENV unfolding E3_Pre_Ret_Envelope_def
          by fastforce 
        from Q1_cases show ?thesis
        proof
   
          assume Q1_BOT: "Q_arr s 1 = BOT"
          show ?thesis using H pP1 J1 Q1_BOT N2 ENV INV' 
            unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
            by (auto split: if_splits)
        next
          assume Q1_A1: "Q_arr s 1 = A1"
      
      show ?thesis using H pP1 J1 Q1_A1 N2 ENV INV' 
            unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
            by (auto split: if_splits)
        qed
      next
        assume J2: "j_var s P1 = 2"
        have Q2_cases: "Q_arr s 2 = BOT \<or> Q_arr s 2 = A2" 
  using ENV unfolding E3_Pre_Ret_Envelope_def
          by meson
        from Q2_cases show ?thesis
        proof
          assume Q2_BOT: "Q_arr s 2 = BOT"
          show ?thesis using H pP1 J2 Q2_BOT N2 ENV INV' 
            unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
         
           by (auto split: if_splits)
        next
          assume Q2_A2: "Q_arr s 2 = A2"
          show ?thesis using H pP1 J2 Q2_A2 N2 ENV INV' 
            unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
            by (auto split: if_splits)
        qed
     
    qed
    qed
  next
    (* ==================== P2 branch ==================== *)
    assume pP2: "p = P2"
    from STEP show ?thesis
    proof (elim disjE)
      assume H: "Sys_E1 p s s'"
      have False using H pP2 ENV unfolding Sys_E1_def C_E1_def E3_Pre_Ret_Envelope_def program_counter_def by auto
      then show ?thesis ..
    next
      assume H: "Sys_E2 p s s'"
      have False using H 
  pP2 ENV unfolding Sys_E2_def C_E2_def E3_Pre_Ret_Envelope_def program_counter_def by auto
      then show ?thesis ..
    next
      assume H: "Sys_D1 p s s'"
      show ?thesis using H pP2 N2 ENV INV' unfolding E3_Pre_Ret_Envelope_def Sys_D1_def C_D1_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def by (auto split: if_splits)
    next
      assume H: "Sys_D2 p s s'"
      show ?thesis using H pP2 N2 ENV INV' unfolding E3_Pre_Ret_Envelope_def Sys_D2_def C_D2_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def by (auto 
  split: if_splits)
    next
      assume H: "Sys_D3 p s s'"
      (* Symmetric: P1, P2 j_var 1 2 *)
      have J_cases: "j_var s P2 = 1 \<or> j_var s P2 = 2" 
        using H pP2 ENV unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def by auto
      from J_cases show ?thesis
      proof
        assume J1: "j_var s P2 = 1"
 
         have Q1_cases: "Q_arr s 1 = BOT \<or> Q_arr s 1 = A1" using ENV unfolding E3_Pre_Ret_Envelope_def
          by meson 
        from Q1_cases show ?thesis
        proof
          assume Q1_BOT: "Q_arr s 1 = BOT"
          show ?thesis using H pP2 J1 Q1_BOT N2 ENV INV' 
          
    unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
            by (auto split: if_splits)
        next
          assume Q1_A1: "Q_arr s 1 = A1"
          show ?thesis using H pP2 J1 Q1_A1 N2 ENV INV' 
            unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
       
            by (auto split: if_splits)
        qed
      next
        assume J2: "j_var s P2 = 2"
        have Q2_cases: "Q_arr s 2 = BOT \<or> Q_arr s 2 = A2" using ENV unfolding E3_Pre_Ret_Envelope_def by meson
        from Q2_cases show ?thesis
        proof
          assume Q2_BOT: "Q_arr s 2 = BOT"
   
         show ?thesis using H pP2 J2 Q2_BOT N2 ENV INV' 
            unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
            by (auto split: if_splits)
        next
          assume Q2_A2: "Q_arr s 2 = A2"
          show ?thesis using H pP2 J2 Q2_A2 N2 ENV INV' 
  
             unfolding E3_Pre_Ret_Envelope_def Sys_D3_def C_D3_def program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def 
            by (auto split: if_splits)
        qed
      qed
    qed
  qed
qed


lemma post_ret_envelope_preserved_by_tau:
  assumes N2: "N_Procs = 2"
      and ENV: "E3_Post_Ret_Envelope s"
      and TAU: "C_Tau s s'"
  shows "E3_Post_Ret_Envelope s'"
proof -
  from ENV have INV: "system_invariant s"
    and P2L0: "program_counter 
  s P2 = ''L0''"
    and Q1BOT: "Q_arr s 1 = BOT"
    and P1PC: "program_counter s P1 \<in> {''D1'',''D2'',''D3'',''D4''}"
    and P1D3: "program_counter s P1 = ''D3'' \<longrightarrow> j_var s P1 \<in> {1,2}"
    and P1D4: "program_counter s P1 = ''D4'' \<longrightarrow> x_var s P1 \<in> {A1,A2}"
    and Q2IFF: "Q_arr s 2 = BOT \<longleftrightarrow> program_counter s P1 = ''D4'' \<and> x_var s P1 = A2"
    and Q2VAL: "Q_arr s 2 \<noteq> BOT \<longrightarrow> Q_arr s 2 = A2"
    and Q3A3: "Q_arr 
  s 3 = A3"
    unfolding E3_Post_Ret_Envelope_def by auto

  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto

  have pP1: "p = P1"
  proof -
    have "p = P1 \<or> p = P2"
  
      using PIN N2 by auto
    then show ?thesis
    proof
      assume "p = P1"
      then show ?thesis .
  next
      assume pP2: "p = P2"
      from STEP show ?thesis
      proof (elim disjE)
        assume H: "Sys_E1 p s s'"
        with pP2 P2L0 show ?thesis
          unfolding Sys_E1_def C_E1_def program_counter_def by auto
      next
        assume H: "Sys_E2 p s s'"
        with pP2 P2L0 show ?thesis
  
          unfolding Sys_E2_def C_E2_def program_counter_def by auto
      next
        assume H: "Sys_D1 p s s'"
        with pP2 P2L0 show ?thesis
          unfolding Sys_D1_def C_D1_def program_counter_def by auto
      next
        assume H: "Sys_D2 p s s'"
        with pP2 P2L0 show ?thesis
          
  unfolding Sys_D2_def C_D2_def program_counter_def Let_def by auto
      next
        assume H: "Sys_D3 p s s'"
        with pP2 P2L0 show ?thesis
          unfolding Sys_D3_def C_D3_def program_counter_def Let_def by auto
      qed
    qed
  qed

  have STEP1: "Sys_D1 P1 s s' \<or> Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
    using STEP pP1 P1PC
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def program_counter_def
  
    by auto

  have NXT: "Next s s'"
    using C_StepCR_into_Next[OF STEP0] .
  have INV': "system_invariant s'"
    using Sys_Inv_Step[OF INV NXT] .
  have P2L0': "program_counter s' P2 = ''L0''"
    using STEP1 P2L0
    unfolding Sys_D1_def C_D1_def
              Sys_D2_def C_D2_def
              Sys_D3_def C_D3_def
              program_counter_def Let_def
    by (elim disjE) (auto split: if_splits)

  have Q1BOT': "Q_arr s' 1 = BOT"
    using STEP1 Q1BOT P1D3
    unfolding Sys_D1_def C_D1_def
       
         Sys_D2_def C_D2_def
              Sys_D3_def C_D3_def
              Q_arr_def program_counter_def j_var_def Let_def
    by (elim disjE) (auto split: if_splits)

  have P1PC': "program_counter s' P1 \<in> {''D1'',''D2'',''D3'',''D4''}"
    using STEP1 P1PC P1D3 Q1BOT Q2IFF Q2VAL
    unfolding Sys_D1_def C_D1_def
              Sys_D2_def C_D2_def
            
    Sys_D3_def C_D3_def
              program_counter_def Q_arr_def j_var_def x_var_def Let_def
    by (elim disjE) (auto split: if_splits)

  have P1D3': "program_counter s' P1 = ''D3'' \<longrightarrow> j_var s' P1 \<in> {1,2}"
  proof
    assume PCP1': "program_counter s' P1 = ''D3''"
    from STEP1 show "j_var s' P1 \<in> {1,2}"
    proof
      assume H: "Sys_D1 P1 s s'"
      with PCP1' show ?thesis
        unfolding 
  Sys_D1_def C_D1_def program_counter_def by auto
    next
      assume H: "Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
      then show ?thesis
      proof
        assume D2: "Sys_D2 P1 s s'"
        with PCP1' show ?thesis
          unfolding Sys_D2_def C_D2_def program_counter_def j_var_def Let_def
          by (auto split: if_splits)
      next
    
       assume D3: "Sys_D3 P1 s s'"
        have Jold: "j_var s P1 \<in> {1,2}"
          using P1D3 D3 unfolding Sys_D3_def C_D3_def program_counter_def by auto
        have Q2notBOT: "Q_arr s 2 \<noteq> BOT"
        proof
          assume "Q_arr s 2 = BOT"
          with Q2IFF have "program_counter s P1 = ''D4'' \<and> x_var s P1 
  = A2"
            by simp
          with D3 show False
            unfolding Sys_D3_def C_D3_def program_counter_def by auto
        qed
        (* Core fix: precondition using from *)
        from PCP1' D3 Jold Q1BOT Q2notBOT Q2VAL show ?thesis
          unfolding Sys_D3_def C_D3_def
       
               program_counter_def j_var_def x_var_def Q_arr_def Let_def BOT_def
          by (auto split: if_splits)
      qed
    qed
  qed

  have P1D4': "program_counter s' P1 = ''D4'' \<longrightarrow> x_var s' P1 \<in> {A1,A2}"
  proof
    assume PCP1': "program_counter s' P1 = ''D4''"
    from STEP1 show "x_var s' P1 \<in> {A1,A2}"
    proof
      assume H: "Sys_D1 P1 s s'"
     
    with PCP1' show ?thesis
        unfolding Sys_D1_def C_D1_def program_counter_def by auto
    next
      assume H: "Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
      then show ?thesis
      proof
        assume D2: "Sys_D2 P1 s s'"
        with PCP1' show ?thesis
          unfolding Sys_D2_def C_D2_def program_counter_def by (auto split: if_splits)
      next
  
         assume D3: "Sys_D3 P1 s s'"
        have Jold: "j_var s P1 \<in> {1,2}"
          using P1D3 D3 unfolding Sys_D3_def C_D3_def program_counter_def by auto
        have XoldBOTorA2:
          "j_var s P1 = 1 \<longrightarrow> x_var s' P1 = BOT" and
          "j_var s P1 = 2 \<longrightarrow> x_var s' P1 = A2"
       
    proof -
          show "j_var s P1 = 1 \<longrightarrow> x_var s' P1 = BOT"
            using D3 Q1BOT
            unfolding Sys_D3_def C_D3_def x_var_def Q_arr_def j_var_def program_counter_def Let_def BOT_def
            by (auto split: if_splits)
          show "j_var s P1 = 2 \<longrightarrow> x_var s' P1 = A2"
       
             using D3 Q2IFF Q2VAL
            unfolding Sys_D3_def C_D3_def x_var_def Q_arr_def j_var_def program_counter_def Let_def
            by (auto split: if_splits)
        qed
        from PCP1' D3 Jold Q1BOT Q2IFF Q2VAL show ?thesis
          unfolding Sys_D3_def C_D3_def
                    program_counter_def x_var_def 
  Q_arr_def j_var_def Let_def
          by (auto split: if_splits)
      qed
    qed
  qed

  have Q2IFF': "Q_arr s' 2 = BOT \<longleftrightarrow> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2"
  proof
    assume Q2B: "Q_arr s' 2 = BOT"
    from STEP1 show "program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2"
    proof
      assume H: "Sys_D1 P1 s s'"
      with Q2B Q2IFF 
  show ?thesis
        unfolding Sys_D1_def C_D1_def Q_arr_def program_counter_def x_var_def by auto
    next
      assume H: "Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
      then show ?thesis
      proof
        assume D2: "Sys_D2 P1 s s'"
        with Q2B Q2IFF show ?thesis
          unfolding Sys_D2_def C_D2_def Q_arr_def program_counter_def x_var_def Let_def by (auto split: if_splits)
     
    next
        assume D3: "Sys_D3 P1 s s'"
        with Q2B Q1BOT Q2IFF Q2VAL show ?thesis
          unfolding Sys_D3_def C_D3_def
                    Q_arr_def program_counter_def x_var_def j_var_def Let_def
          by (auto split: if_splits)
      qed
    qed
  next
    assume H: "program_counter s' P1 = ''D4'' 
  \<and> x_var s' P1 = A2"
    then show "Q_arr s' 2 = BOT"
      using STEP1 Q1BOT Q2IFF Q2VAL P1D3
      unfolding Sys_D1_def C_D1_def
                Sys_D2_def C_D2_def
                Sys_D3_def C_D3_def
                Q_arr_def program_counter_def x_var_def j_var_def Let_def BOT_def
      by (elim disjE) (auto split: 
  if_splits)
  qed

  have Q2VAL': "Q_arr s' 2 \<noteq> BOT \<longrightarrow> Q_arr s' 2 = A2"
  proof
    assume Q2NB: "Q_arr s' 2 \<noteq> BOT"
    from STEP1 show "Q_arr s' 2 = A2"
    proof
      assume H: "Sys_D1 P1 s s'"
      then show ?thesis
        using Q2NB Q2VAL
        unfolding Sys_D1_def C_D1_def Q_arr_def by auto
    next
      assume H: "Sys_D2 P1 s 
  s' \<or> Sys_D3 P1 s s'"
      then show ?thesis
      proof
        assume D2: "Sys_D2 P1 s s'"
        then show ?thesis
          using Q2NB Q2VAL
          unfolding Sys_D2_def C_D2_def Q_arr_def Let_def  by (auto split: if_splits)
      next
        assume D3: "Sys_D3 P1 s s'"
        
  with Q2NB Q1BOT Q2IFF Q2VAL show ?thesis
          unfolding Sys_D3_def C_D3_def
                    Q_arr_def program_counter_def x_var_def j_var_def Let_def
          by (auto split: if_splits)
      qed
    qed
  qed

  have Q3A3': "Q_arr s' 3 = A3"
    using STEP1 Q3A3 P1D3
    unfolding Sys_D1_def C_D1_def
            
    Sys_D2_def C_D2_def
              Sys_D3_def C_D3_def
              Q_arr_def j_var_def program_counter_def Let_def
    by (elim disjE) (auto split: if_splits)

  show ?thesis
    unfolding E3_Post_Ret_Envelope_def
    using INV' P2L0' Q1BOT' P1PC' P1D3' P1D4' Q2IFF' Q2VAL' Q3A3'
    by auto
qed

(* ========================================================================= *)
(* 4.  e3  Post-Envelope                       
                      *)
(* ========================================================================= *)

lemma pre_ret_envelope_preserved_by_tau_star:
  assumes N2: "N_Procs = 2"
      and ENV: "E3_Pre_Ret_Envelope s"
      and TAUS: "C_Tau_Star s t"
  shows "E3_Pre_Ret_Envelope t"
  using TAUS ENV
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s s1 s2)
  have ENV1: "E3_Pre_Ret_Envelope s1"
    using pre_ret_envelope_preserved_by_tau[OF N2 step.prems step.hyps(1)] .
  show ?case
    using step.IH[OF ENV1] .
qed

lemma post_ret_envelope_preserved_by_tau_star:
  assumes N2: "N_Procs = 2"
      and ENV: "E3_Post_Ret_Envelope s"
      and TAUS: "C_Tau_Star s t"
  shows "E3_Post_Ret_Envelope t"
  using TAUS ENV
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s s1 s2)
  have ENV1: "E3_Post_Ret_Envelope s1"
    using post_ret_envelope_preserved_by_tau[OF N2 step.prems step.hyps(1)] .
  show ?case
    using step.IH[OF ENV1] .
qed

lemma pre_envelope_preserved_by_p2_deq_call:
  assumes ENV: "E3_Pre_Ret_Envelope s"
      and VIS: "C_StepCR s (Some (mk_obs deq BOT P2 call)) s'"
  shows "E3_Pre_Ret_Envelope s'"
proof -
  from ENV have INV: "system_invariant s"
    and P1_PC: "program_counter s P1 \<in> {''D1'',''D2'',''D3'',''D4''}"
    and P2_PC: "program_counter s P2 \<in> {''L0'',''D1'',''D2'',''D3'',''D4''}"
    and P1_D3: "program_counter s P1 = ''D3'' \<longrightarrow> j_var s P1 \<in> {1,2}"
    and P2_D3: "program_counter s P2 = ''D3'' \<longrightarrow> j_var s P2 \<in> {1,2}"
    and 
  P1_D4: "program_counter s P1 = ''D4'' \<longrightarrow> x_var s P1 \<in> {A1,A2}"
    and P2_D4: "program_counter s P2 = ''D4'' \<longrightarrow> x_var s P2 \<in> {A1,A2}"
    and Q1_IFF: "Q_arr s 1 = BOT \<longleftrightarrow>
                   (program_counter s P1 = ''D4'' \<and> x_var s P1 = A1) \<or>
                   (program_counter s P2 = ''D4'' \<and> x_var s P2 = A1)"
   
    and Q2_IFF: "Q_arr s 2 = BOT \<longleftrightarrow>
                   (program_counter s P1 = ''D4'' \<and> x_var s P1 = A2) \<or>
                   (program_counter s P2 = ''D4'' \<and> x_var s P2 = A2)"
    and Q1_VAL: "Q_arr s 1 \<noteq> BOT \<longrightarrow> Q_arr s 1 = A1"
    and Q2_VAL: "Q_arr s 2 \<noteq> BOT \<longrightarrow> Q_arr s 2 = A2"
 
     and Q3_A3: "Q_arr s 3 = A3"
    (* Extract the new historical tracking and mutex rules *)
    and HIST1: "program_counter s P1 = ''D3'' \<and> j_var s P1 = 2 \<longrightarrow> Q_arr s 1 = BOT"
    and HIST2: "program_counter s P2 = ''D3'' \<and> j_var s P2 = 2 \<longrightarrow> Q_arr s 1 = BOT"
    and MUTEX1: "\<not>(program_counter s P1 = ''D4'' \<and> x_var s P1 = A1 \<and> program_counter s P2 = ''D4'' \<and> x_var s P2 = A1)"
    and MUTEX2: 
  "\<not>(program_counter s P1 = ''D4'' \<and> x_var s P1 = A2 \<and> program_counter s P2 = ''D4'' \<and> x_var s P2 = A2)"
    unfolding E3_Pre_Ret_Envelope_def by auto

  have NXT: "Next s s'"
    using C_StepCR_into_Next[OF VIS] .
  have INV': "system_invariant s'"
    using Sys_Inv_Step[OF INV NXT] .
  from VIS show ?thesis
  proof cases
    case (C_Sys_L0_deq_vis p)
    have pP2: "p = P2"
      using C_Sys_L0_deq_vis unfolding mk_obs_def by auto
    hence pneq: "p \<noteq> P1"
      by simp
    have PC_P2_new: "program_counter s' P2 = ''D1''"
      using C_Sys_L0_deq_vis pP2 by simp

    have P1_PC_eq: "program_counter s' P1 = program_counter s P1"
      using C_Sys_L0_deq_vis pneq
      unfolding Sys_L0_def C_L0_def program_counter_def Let_def
    
    by (auto split: if_splits)
    have P1_J_eq: "j_var s' P1 = j_var s P1"
      using C_Sys_L0_deq_vis pneq
      unfolding Sys_L0_def C_L0_def j_var_def Let_def
      by (auto split: if_splits)
    have P1_X_eq: "x_var s' P1 = x_var s P1"
      using C_Sys_L0_deq_vis pneq
      unfolding Sys_L0_def C_L0_def x_var_def Let_def
      by (auto split: if_splits)
    
    (* We also need P2's local variables, which are 
  untouched by Sys_L0 *)
    have P2_J_eq: "j_var s' P2 = j_var s P2"
      using C_Sys_L0_deq_vis pP2
      unfolding Sys_L0_def C_L0_def j_var_def Let_def
      by (auto split: if_splits)
    have P2_X_eq: "x_var s' P2 = x_var s P2"
      using C_Sys_L0_deq_vis pP2
      unfolding Sys_L0_def C_L0_def x_var_def Let_def
      by (auto split: if_splits)

    have Q1_eq: "Q_arr s' 1 = Q_arr s 1"
      using 
  C_Sys_L0_deq_vis pneq
      unfolding Sys_L0_def C_L0_def Q_arr_def Let_def
      by (auto split: if_splits)
    have Q2_eq: "Q_arr s' 2 = Q_arr s 2"
      using C_Sys_L0_deq_vis pneq
      unfolding Sys_L0_def C_L0_def Q_arr_def Let_def
      by (auto split: if_splits)
    have Q3_eq: "Q_arr s' 3 = Q_arr s 3"
      using C_Sys_L0_deq_vis pneq
      unfolding Sys_L0_def C_L0_def Q_arr_def Let_def
      by (auto split: if_splits)

have P2_old_L0: 
  "program_counter s P2 = ''L0''"
  using C_Sys_L0_deq_vis pP2
  unfolding Sys_L0_def C_L0_def program_counter_def
  by auto

have P2_old_not_D4: "program_counter s P2 \<noteq> ''D4''"
  using P2_old_L0 by simp

have P2_new_not_D3: "program_counter s' P2 \<noteq> ''D3''"
  using PC_P2_new by simp

have P2_new_not_D4: "program_counter s' P2 \<noteq> ''D4''"
  using PC_P2_new by simp

have Q1_IFF': "(Q_arr s' 1 = BOT) \<longleftrightarrow>
  (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1) \<or>
  (program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A1)"
proof -
  have "(Q_arr s' 1 = BOT) \<longleftrightarrow> (Q_arr s 1 = BOT)"
    using 
  Q1_eq by simp
  also have "... \<longleftrightarrow>
      ((program_counter s P1 = ''D4'' \<and> x_var s P1 = A1) \<or>
       (program_counter s P2 = ''D4'' \<and> x_var s P2 = A1))"
    using Q1_IFF by simp
  also have "... \<longleftrightarrow> (program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
    using P2_old_not_D4 by auto
  also have "... \<longleftrightarrow> (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1)"
    using P1_PC_eq P1_X_eq by auto
  also have "... 
  \<longleftrightarrow>
      ((program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1) \<or>
       (program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A1))"
    using P2_new_not_D4 by auto
  finally show ?thesis .
  qed

have Q2_IFF': "(Q_arr s' 2 = BOT) \<longleftrightarrow>
  (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2) \<or>
  (program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A2)"
proof -
  have "(Q_arr s' 2 = BOT) \<longleftrightarrow> (Q_arr s 2 = BOT)"
    using Q2_eq by simp
  also have "... \<longleftrightarrow>
      ((program_counter s P1 = ''D4'' \<and> x_var s P1 = A2) \<or>
       (program_counter s P2 = ''D4'' \<and> x_var s P2 = A2))"
    using Q2_IFF by simp
 
   also have "... \<longleftrightarrow> (program_counter s P1 = ''D4'' \<and> x_var s P1 = A2)"
    using P2_old_not_D4 by auto
  also have "... \<longleftrightarrow> (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2)"
    using P1_PC_eq P1_X_eq by auto
  also have "... \<longleftrightarrow>
      ((program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2) \<or>
       (program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A2))"
    using P2_new_not_D4 by auto
  finally show ?thesis .
  qed

have Q1_VAL': "Q_arr s' 1 \<noteq> BOT \<longrightarrow> Q_arr s' 1 = A1"
  using Q1_eq Q1_VAL by auto

have Q2_VAL': "Q_arr s' 2 \<noteq> BOT \<longrightarrow> Q_arr s' 2 = A2"
  using Q2_eq Q2_VAL by auto

have HIST1': "program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 2 \<longrightarrow> Q_arr s' 1 = BOT"
  using HIST1 P1_PC_eq P1_J_eq Q1_eq by auto

have HIST2': "program_counter s' P2 = ''D3'' \<and> j_var s' P2 = 2 \<longrightarrow> Q_arr s' 1 = BOT"
  using P2_new_not_D3 by auto

have MUTEX1': "\<not> (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1 \<and>
 
                  program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A1)"
  using P2_new_not_D4 by auto

have MUTEX2': "\<not> (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2 \<and>
                  program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A2)"
  using P2_new_not_D4 by auto

show ?thesis
proof (unfold E3_Pre_Ret_Envelope_def, intro conjI)
  show "system_invariant s'"
    using INV' .
  show "program_counter s' P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using P1_PC P1_PC_eq by simp
  show "program_counter s' P2 \<in> {''L0'', ''D1'', ''D2'', ''D3'', ''D4''}"
    using PC_P2_new by simp
  show "program_counter s' P1 = ''D3'' \<longrightarrow> j_var s' P1 \<in> {1, 2}"
    using P1_D3 P1_PC_eq P1_J_eq by auto
  show "program_counter s' P2 = ''D3'' \<longrightarrow> j_var s' P2 \<in> {1, 2}"
    using P2_new_not_D3 by auto
  show "program_counter s' P1 = ''D4'' \<longrightarrow> x_var s' P1 \<in> {A1, A2}"
    using P1_D4 P1_PC_eq P1_X_eq 
  by auto
  show "program_counter s' P2 = ''D4'' \<longrightarrow> x_var s' P2 \<in> {A1, A2}"
    using P2_new_not_D4 by auto
  show "(Q_arr s' 1 = BOT) \<longleftrightarrow>
        (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1) \<or>
        (program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A1)"
    using Q1_IFF' .
  show "(Q_arr s' 2 = BOT) \<longleftrightarrow>
        (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2) \<or>
        (program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A2)"
    using Q2_IFF' .
  show "Q_arr s' 1 \<noteq> BOT \<longrightarrow> Q_arr s' 1 = A1"
    using Q1_VAL' .
  show "Q_arr s' 2 \<noteq> BOT \<longrightarrow> Q_arr s' 2 = A2"
    using Q2_VAL' .
  show "Q_arr s' 3 = A3"
    using Q3_eq Q3_A3 by simp
  show "program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 2 \<longrightarrow> Q_arr s' 1 = BOT"
    using HIST1' .
  show "program_counter s' P2 = ''D3'' \<and> j_var s' P2 = 2 \<longrightarrow> Q_arr s' 1 = BOT"
    using HIST2' .
  show "\<not> (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1 \<and>
           program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A1)"
    using MUTEX1' .
  show "\<not> (program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A2 \<and>
           program_counter s' P2 = ''D4'' \<and> x_var s' P2 = A2)"
    using MUTEX2' .
  qed
  qed (auto simp: mk_obs_def)
qed

lemma pre_ret_envelope_preserved_by_none_path:
  assumes N2: "N_Procs = 2"
      and ENV: "E3_Pre_Ret_Envelope s"
      and PATH: "C_Path s ls t"
      and NO: "set ls \<subseteq> {None}"
  shows "E3_Pre_Ret_Envelope t"
  using PATH ENV NO
proof (induction rule: C_Path.induct)
  case nil
  then show ?case by simp
next
  case (cons s l s1 ls s2)
  have lNone: "l = None"
    using cons.prems(2) by auto
  have TAUS: "C_Tau_Star s s1"
    using cons.hyps(1) lNone C_Match_noneE by 
  simp
  have ENV1: "E3_Pre_Ret_Envelope s1"
    using pre_ret_envelope_preserved_by_tau_star[OF N2 cons.prems(1) TAUS] .
  have NOls: "set ls \<subseteq> {None}"
    using cons.prems(2) by auto
  show ?case
    using cons.IH[OF ENV1 NOls] .
  qed

lemma post_ret_envelope_preserved_by_none_path:
  assumes N2: "N_Procs = 2"
      and ENV: "E3_Post_Ret_Envelope s"
      and PATH: "C_Path s ls t"
      and NO: "set ls \<subseteq> {None}"
  shows "E3_Post_Ret_Envelope t"
  using PATH ENV NO
proof (induction rule: C_Path.induct)
  case nil
  then show ?case by simp
next
  case (cons s l s1 ls s2)
  have lNone: "l = None"
    using cons.prems(2) by auto
  have TAUS: "C_Tau_Star s s1"
    using cons.hyps(1) lNone C_Match_noneE by simp
  have ENV1: "E3_Post_Ret_Envelope 
  s1"
    using post_ret_envelope_preserved_by_tau_star[OF N2 cons.prems(1) TAUS] .
  have NOls: "set ls \<subseteq> {None}"
    using cons.prems(2) by auto
  show ?case
    using cons.IH[OF ENV1 NOls] .
  qed

lemma hwq_e3_prefix_guarantees_post_envelope:
  assumes N2: "N_Procs = 2"
      and SH: "E1_HWQ_relaxed_shape sk0"
      and P12: "program_counter sk0 P1 \<in> {''D1'', ''D2''}"
      and PREF_BEF: "C_Path sk0 e3_before_p2_ret_labels m"
      and RET_ACT:  "C_Match m (Some (mk_obs deq A1 P2 ret)) u1"
      and PREF_AFT: "C_Path u1 e3_after_p2_ret_before_last_labels u"
      and TAU_TAIL: "C_Tau_Star u u0"
  shows "E3_Post_Ret_Envelope u0"
proof -
  have BASE: "E3_Pre_Ret_Envelope sk0"
    using pre_envelope_base[OF SH P12] .

  have SPLIT_BEF:
    "e3_before_p2_ret_labels =
      [Some (mk_obs deq BOT P2 call)] @ [None, None, None, None, None]"
    unfolding e3_before_p2_ret_labels_def by simp

  obtain s_call where
      CALL_PATH: "C_Path sk0 [Some (mk_obs deq BOT P2 call)] s_call"
    and TAIL_PATH: "C_Path s_call [None, None, None, None, None] m"
    using C_Path_appendE[OF PREF_BEF[unfolded SPLIT_BEF]]
    by blast

  have MCALL: "C_Match sk0 (Some (mk_obs deq BOT P2 call)) s_call"
  proof -
    from CALL_PATH obtain u where
        M: "C_Match sk0 (Some (mk_obs deq BOT P2 call)) u"
      and P0: "C_Path u [] s_call"
      by (cases rule: C_Path.cases) auto
    from P0 have "u = s_call"
      by (cases rule: C_Path.cases) auto
    with M show ?thesis
      by simp
  qed

  have CALL_ENV: "E3_Pre_Ret_Envelope s_call"
  proof -
    obtain u0 v0 where
        T1: "C_Tau_Star sk0 u0"
      and STEP: "C_StepCR u0 (Some (mk_obs deq BOT P2 call)) v0"
      and T2: "C_Tau_Star v0 s_call"
      using C_Match_someE[OF MCALL] by blast

    have ENV_u0: "E3_Pre_Ret_Envelope u0"
      using pre_ret_envelope_preserved_by_tau_star[OF N2 BASE T1] .

    have ENV_v0: "E3_Pre_Ret_Envelope v0"
      using pre_envelope_preserved_by_p2_deq_call[OF ENV_u0 STEP] .

    show ?thesis
      using pre_ret_envelope_preserved_by_tau_star[OF N2 ENV_v0 T2] .
  qed

  have PRE_m: "E3_Pre_Ret_Envelope m"
    using pre_ret_envelope_preserved_by_none_path[OF N2 CALL_ENV TAIL_PATH]
    by auto

  have POST_u1: "E3_Post_Ret_Envelope u1"
  proof -
    obtain r0 r1 where
        T1: "C_Tau_Star m r0"
      and STEP: "C_StepCR r0 (Some (mk_obs deq A1 P2 ret)) r1"
      and T2: "C_Tau_Star r1 u1"
      using C_Match_someE[OF RET_ACT] by blast

    have PRE_r0: "E3_Pre_Ret_Envelope r0"
      using pre_ret_envelope_preserved_by_tau_star[OF N2 PRE_m T1] .

    have POST_r1: "E3_Post_Ret_Envelope r1"
      using envelope_transition_at_p2_ret[OF N2 PRE_r0 STEP] .

    show ?thesis
      using post_ret_envelope_preserved_by_tau_star[OF N2 POST_r1 T2] .
  qed

  have POST_u: "E3_Post_Ret_Envelope u"
    using post_ret_envelope_preserved_by_none_path[OF N2 POST_u1 PREF_AFT]
    by (auto simp: e3_after_p2_ret_before_last_labels_def)

  show ?thesis
    using post_ret_envelope_preserved_by_tau_star[OF N2 POST_u TAU_TAIL] .
qed

text \<open>Old lemmas kept intact for the scanning branch bridging\<close>

lemma hwq_case_j1_impossible:
  assumes N2: "N_Procs = 2"
      and SH: "E1_HWQ_shape sk0"
      and J1: "j_var sk0 P1 = 1"
      and E3MATCH: "C_Path sk0 e3_labels s3"
  shows False
proof -
  have BASE: "E3_Pre_Ret_Envelope sk0"
    using SH J1
    unfolding E1_HWQ_shape_def E3_Pre_Ret_Envelope_def
    by (auto simp: BOT_def)

  obtain u where
      PREF: "C_Path sk0 e3_before_last_labels u"
    and LAST: "C_Match u (Some (mk_obs deq A3 P1 ret)) s3"
    using C_Path_snocE[OF E3MATCH[unfolded e3_labels_split_last]]
    by blast

  obtain m where
      PREF_BEF: "C_Path sk0 e3_before_p2_ret_labels m"
    and REST: "C_Path m ([Some (mk_obs deq A1 P2 ret)] @ e3_after_p2_ret_before_last_labels) u"
    using C_Path_appendE[OF PREF[unfolded e3_before_last_split_ret]]
    by blast

  obtain u1 where
      RET_ACT: "C_Match m (Some (mk_obs deq A1 P2 ret)) u1"
    and PREF_AFT: "C_Path u1 e3_after_p2_ret_before_last_labels u"
    using REST
    by (cases rule: C_Path.cases) auto

  obtain u0 v0 where
      T1: "C_Tau_Star u u0"
    and STEP: "C_StepCR u0 (Some (mk_obs deq A3 P1 ret)) v0"
    and T2: "C_Tau_Star v0 s3"
    using C_Match_someE[OF LAST] by blast

  have SPLIT_BEF:
    "e3_before_p2_ret_labels =
      [Some (mk_obs deq BOT P2 call)] @ [None, None, None, None, None]"
    unfolding e3_before_p2_ret_labels_def by simp

  obtain s_call where
      CALL_PATH: "C_Path sk0 [Some (mk_obs deq BOT P2 call)] s_call"
    and TAIL_PATH: "C_Path s_call [None, None, None, None, None] m"
    using C_Path_appendE[OF PREF_BEF[unfolded SPLIT_BEF]]
    by blast

  have MCALL: "C_Match sk0 (Some (mk_obs deq BOT P2 call)) s_call"
  proof -
    from CALL_PATH obtain z where
        M: "C_Match sk0 (Some (mk_obs deq BOT P2 call)) z"
      and P0: "C_Path z [] s_call"
      by (cases rule: C_Path.cases) auto
    from P0 have "z = s_call"
      by (cases rule: C_Path.cases) auto
    with M show ?thesis
      by simp
  qed

  have CALL_ENV: "E3_Pre_Ret_Envelope s_call"
  proof -
    obtain a0 b0 where
        T0: "C_Tau_Star sk0 a0"
      and STEP0: "C_StepCR a0 (Some (mk_obs deq BOT P2 call)) b0"
      and T0': "C_Tau_Star b0 s_call"
      using C_Match_someE[OF MCALL] by blast
    have ENV_a0: "E3_Pre_Ret_Envelope a0"
      using pre_ret_envelope_preserved_by_tau_star[OF N2 BASE T0] .
    have ENV_b0: "E3_Pre_Ret_Envelope b0"
      using pre_envelope_preserved_by_p2_deq_call[OF ENV_a0 STEP0] .
    show ?thesis
      using pre_ret_envelope_preserved_by_tau_star[OF N2 ENV_b0 T0'] .
  qed

  have PRE_m: "E3_Pre_Ret_Envelope m"
    using pre_ret_envelope_preserved_by_none_path[OF N2 CALL_ENV TAIL_PATH]
    by auto

  have POST_u1: "E3_Post_Ret_Envelope u1"
  proof -
    obtain r0 r1 where
        T0: "C_Tau_Star m r0"
      and STEP0: "C_StepCR r0 (Some (mk_obs deq A1 P2 ret)) r1"
      and T0': "C_Tau_Star r1 u1"
      using C_Match_someE[OF RET_ACT] by blast
    have PRE_r0: "E3_Pre_Ret_Envelope r0"
      using pre_ret_envelope_preserved_by_tau_star[OF N2 PRE_m T0] .
    have POST_r1: "E3_Post_Ret_Envelope r1"
      using envelope_transition_at_p2_ret[OF N2 PRE_r0 STEP0] .
    show ?thesis
      using post_ret_envelope_preserved_by_tau_star[OF N2 POST_r1 T0'] .
  qed

  have POST_u: "E3_Post_Ret_Envelope u"
    using post_ret_envelope_preserved_by_none_path[OF N2 POST_u1 PREF_AFT]
    by (auto simp: e3_after_p2_ret_before_last_labels_def)

  have ENV: "E3_Post_Ret_Envelope u0"
    using post_ret_envelope_preserved_by_tau_star[OF N2 POST_u T1] .

  from STEP obtain p where
      PIN: "p \<in> ProcSet"
    and SD4: "Sys_D4 p u0 v0"
    and LAB: "mk_obs deq (x_var u0 p) p ret = mk_obs deq A3 P1 ret"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  from LAB have pP1: "p = P1" and XRET: "x_var u0 P1 = A3"
    unfolding mk_obs_def by auto

  have PCu0: "program_counter u0 P1 = ''D4''"
    using SD4 pP1
    unfolding Sys_D4_def C_D4_def program_counter_def
    by auto

  from ENV PCu0 XRET show False
    unfolding E3_Post_Ret_Envelope_def
    by auto
qed

(* ========================================================================= *)
(* Step 5.1.2.3. *)
(* ========================================================================= *)

lemma hwq_scanning_D1D2_impossible:
  assumes N2: "N_Procs = 2"
      and SH: "E1_HWQ_relaxed_shape sk0"
      and Q1: "Q_arr sk0 1 = A1"
      and P12: "program_counter 
  sk0 P1 \<in> {''D1'', ''D2''}"
      and E2MATCH: "C_Path sk0 e2_labels s2"
      and E3MATCH: "C_Path sk0 e3_labels s3"
  shows False
proof -
  obtain u where
      PREF: "C_Path sk0 e3_before_last_labels u"
    and LAST: "C_Match u (Some (mk_obs deq A3 P1 ret)) s3"
    using C_Path_snocE[OF E3MATCH[unfolded e3_labels_split_last]]
    by blast

  obtain m where
      PREF_BEF: "C_Path sk0 e3_before_p2_ret_labels m"
    and REST: "C_Path m ([Some (mk_obs deq A1 P2 ret)] @ e3_after_p2_ret_before_last_labels) 
  u"
    using C_Path_appendE[OF PREF[unfolded e3_before_last_split_ret]]
    by blast

  obtain u1 where
      RET_ACT: "C_Match m (Some (mk_obs deq A1 P2 ret)) u1"
    and PREF_AFT: "C_Path u1 e3_after_p2_ret_before_last_labels u"
    using REST by (cases rule: C_Path.cases) auto

  obtain u0 v0 where
      T1: "C_Tau_Star u u0"
    and STEP: "C_StepCR u0 (Some (mk_obs deq A3 P1 ret)) v0"
    and T2: "C_Tau_Star v0 s3"
    using C_Match_someE[OF LAST] by blast

  from STEP obtain p 
  where
      PIN: "p \<in> ProcSet"
    and SD4: "Sys_D4 p u0 v0"
    and LAB: "mk_obs deq (x_var u0 p) p ret = mk_obs deq A3 P1 ret"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  from LAB have pP1: "p = P1" and XRET: "x_var u0 P1 = A3"
    unfolding mk_obs_def by auto

  have PCu0: "program_counter u0 P1 = ''D4''"
    using SD4 pP1 unfolding Sys_D4_def C_D4_def program_counter_def by auto

  have ENV: "E3_Post_Ret_Envelope u0"
    using hwq_e3_prefix_guarantees_post_envelope[OF N2 
  SH P12 PREF_BEF RET_ACT PREF_AFT T1] .

  from ENV PCu0 XRET show False
    unfolding E3_Post_Ret_Envelope_def by auto
qed


lemma hwq_scanning_branch_impossible:
  assumes N2: "N_Procs = 2"
      and SH: "E1_HWQ_relaxed_shape sk0"
      and SCAN: "Q_arr sk0 1 = A1 \<and>
                 (program_counter sk0 P1 
  \<in> {''D1'', ''D2''} \<or>
                  (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 
  = 1))"
      and E2MATCH: "C_Path sk0 e2_labels s2"
      and E3MATCH: "C_Path sk0 e3_labels s3"
  shows False
proof -
  from SCAN have Q1: "Q_arr sk0 1 = A1"
    and PCS:
      "program_counter sk0 P1 \<in> {''D1'', ''D2''} \<or>
       (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 
  = 1)"
    by auto

  from PCS show False
  proof (elim disjE) (* Core fix: elim disjE cases PCS *)
    assume 
  P12: "program_counter sk0 P1 \<in> {''D1'', ''D2''}"
    then show False
      using hwq_scanning_D1D2_impossible[OF N2 SH Q1 P12 E2MATCH E3MATCH]
      by simp 
  next
    assume D3J1: "program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1"
    have OLD: "E1_HWQ_shape sk0"
      using scanning_D3_j1_implies_old_shape[OF SH] Q1 D3J1 by auto
   
     have J1: "j_var sk0 P1 = 1"
      using D3J1 by auto
    show False
  
      using hwq_case_j1_impossible[OF N2 OLD J1 E3MATCH] .
  qed
qed

lemma C_Tau_preserves_D4_x_P1:
  assumes TAU: "C_Tau s s'"
      and PC:  "program_counter s P1 = ''D4''"
      and XV:  "x_var s P1 = A1"
  shows "program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1"
proof -
  from TAU have STEP0: "C_StepCR s None s'"
    unfolding C_Tau_def by simp
  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 
  
  p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto

  from STEP show ?thesis
  proof (elim disjE)
    assume H: "Sys_E1 p s s'"
    then show ?thesis
      using PC XV
      unfolding Sys_E1_def C_E1_def program_counter_def x_var_def Let_def
      by (cases "p = P1") (auto split: if_splits)
  next
    assume H: "Sys_E2 p s s'"
    then show ?thesis
      using PC XV
  
    
      unfolding Sys_E2_def C_E2_def program_counter_def x_var_def Let_def
      by (cases "p = P1") (auto split: if_splits)
  next
    assume H: "Sys_D1 p s s'"
    then show ?thesis
      using PC XV
      unfolding Sys_D1_def C_D1_def program_counter_def x_var_def Let_def
      by (cases "p = P1") (auto split: if_splits)
  next
    assume H: "Sys_D2 p s s'"
    then show ?thesis
      using PC 
  XV
      unfolding Sys_D2_def C_D2_def program_counter_def x_var_def Let_def
      by (cases "p = P1") (auto split: if_splits)
  next
    assume H: "Sys_D3 p s s'"
    then show ?thesis
      using PC XV
      unfolding Sys_D3_def C_D3_def
                program_counter_def x_var_def Q_arr_def j_var_def Let_def
      by (cases "p = P1") (auto split: if_splits)
  qed
qed

lemma C_Tau_Star_preserves_D4_x_P1:
  assumes TAUS: "C_Tau_Star s s'"
 
       and PC:   "program_counter s P1 = ''D4''"
      and XV:   "x_var s P1 = A1"
  shows "program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1"
  using TAUS PC XV
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s s1 s2)
  have STEP1: "program_counter s1 P1 = ''D4'' \<and> x_var s1 P1 = A1"
    using C_Tau_preserves_D4_x_P1[OF step.hyps(1) step.prems(1) step.prems(2)] .
  then show ?case
    using step.IH by blast
qed

lemma C_StepCR_vis_other_preserves_D4_x_P1:
  assumes STEP:  "C_StepCR s (Some obs) s'"
      and OTHER: "fst (snd (snd obs)) \<noteq> P1"
      and PC:    "program_counter s P1 = ''D4''"
      and XV:    "x_var s P1 = A1"
  shows "program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1"
proof -
  from STEP show ?thesis
  proof cases
    case (C_Sys_L0_enq_vis p)
    have pneq: "p \<noteq> P1"
  
  
      using OTHER C_Sys_L0_enq_vis unfolding mk_obs_def by auto
    then show ?thesis
      using C_Sys_L0_enq_vis PC XV
      unfolding Sys_L0_def C_L0_def program_counter_def x_var_def Let_def
      by (auto split: if_splits)
  next
    case (C_Sys_L0_deq_vis p)
    have pneq: "p \<noteq> P1"
      using OTHER C_Sys_L0_deq_vis unfolding mk_obs_def by auto
    then show ?thesis
      using C_Sys_L0_deq_vis PC XV
      unfolding Sys_L0_def C_L0_def program_counter_def 
  x_var_def Let_def
 
       by (auto split: if_splits)
  next
    case (C_Sys_E3_vis p)
    have pneq: "p \<noteq> P1"
      using OTHER C_Sys_E3_vis unfolding mk_obs_def by auto
    then show ?thesis
      using C_Sys_E3_vis PC XV
      unfolding Sys_E3_def C_E3_def program_counter_def x_var_def Let_def
      by (auto split: if_splits)
  next
    case (C_Sys_D4_vis p)
    have pneq: "p \<noteq> P1"
      using OTHER C_Sys_D4_vis 
  unfolding mk_obs_def by auto
 
     then show ?thesis
      using C_Sys_D4_vis PC XV
      unfolding Sys_D4_def C_D4_def program_counter_def x_var_def Let_def
      by (auto split: if_splits)
  qed
qed

lemma C_Path_no_P1_vis_preserves_D4_x_P1:
  assumes PATH: "C_Path s ls u"
      and NO1:  "\<forall>obs.
  Some obs \<in> set ls \<longrightarrow> fst (snd (snd obs)) \<noteq> P1"
      and PC:   "program_counter s P1 = ''D4''"
      and XV:   "x_var s P1 = A1"
  shows "program_counter u P1 = ''D4'' \<and> x_var u P1 = A1"
  using PATH NO1 PC XV
proof (induction s ls u rule: C_Path.induct)
  case nil
  then show ?case by simp
next
  case (cons s l s1 ls s2)
  have Lcond:  "\<forall>obs.
  l = Some obs \<longrightarrow> fst (snd (snd obs)) \<noteq> P1"
    using cons.prems(1) by auto
  have LScond: "\<forall>obs.
  Some obs \<in> set ls \<longrightarrow> fst (snd (snd obs)) \<noteq> P1"
    using cons.prems(1) by auto

  have STEP1: "program_counter s1 P1 = ''D4'' \<and> x_var s1 P1 = A1"
    using cons.hyps(1)
  proof (cases rule: C_Match.cases)
    case match_tau
    then show ?thesis
      using C_Tau_Star_preserves_D4_x_P1[OF match_tau(2) cons.prems(2) cons.prems(3)] by blast
  next
    case (match_vis u0 a v0)
    have UV: "program_counter u0 P1 = ''D4'' \<and> x_var u0 P1 = A1"
      using C_Tau_Star_preserves_D4_x_P1[OF match_vis(2) 
  
  cons.prems(2) cons.prems(3)] .
    have a_not_P1: "fst (snd (snd a)) \<noteq> P1"
      using Lcond match_vis(1) by auto
    have VV: "program_counter v0 P1 = ''D4'' \<and> x_var v0 P1 = A1"
      using C_StepCR_vis_other_preserves_D4_x_P1[OF match_vis(3) a_not_P1] UV by blast
    then show ?thesis
      using C_Tau_Star_preserves_D4_x_P1[OF match_vis(4)] by blast
  qed

  show ?case
    using cons.IH[OF LScond] STEP1 by blast
qed

lemma hwq_committed_D4_impossible:
  assumes SH: "E1_HWQ_relaxed_shape sk0"
      and COMMITTED: "Q_arr sk0 1 = BOT \<and> program_counter sk0 P1 = ''D4'' \<and> x_var sk0 P1 = A1"
      and E3MATCH: "C_Path sk0 e3_labels s3"
  shows False
proof -
  obtain u where
      PREF: "C_Path sk0 e3_before_last_labels u"
    and LAST: "C_Match u (Some (mk_obs deq A3 P1 ret)) s3"
    using C_Path_snocE[OF E3MATCH[unfolded e3_labels_split_last]]
    by blast

  have NO1:
    "\<forall>obs. Some obs \<in> set e3_before_last_labels \<longrightarrow> fst (snd (snd obs)) \<noteq> P1"
    unfolding e3_before_last_labels_def mk_obs_def
    by auto

  from COMMITTED have
      PC0: "program_counter sk0 P1 = ''D4''"
    and XV0: "x_var sk0 P1 = A1"
    by auto

  have PCu: "program_counter u P1 = ''D4''"
    and XVu: "x_var u P1 = A1"
    using C_Path_no_P1_vis_preserves_D4_x_P1[OF PREF NO1 PC0 XV0]
    by auto

  obtain u0 v0 where
      T1: "C_Tau_Star u u0"
    and STEP: "C_StepCR u0 (Some (mk_obs deq A3 P1 ret)) v0"
    and T2: "C_Tau_Star v0 s3"
    using C_Match_someE[OF LAST] by blast

  have PCu0: "program_counter u0 P1 = ''D4''"
    and XVu0: "x_var u0 P1 = A1"
    using C_Tau_Star_preserves_D4_x_P1[OF T1 PCu XVu]
    by auto

  from STEP obtain p where
      PIN: "p \<in> ProcSet"
    and SD4: "Sys_D4 p u0 v0"
    and LAB: "mk_obs deq (x_var u0 p) p ret = mk_obs deq A3 P1 ret"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  from LAB have pP1: "p = P1"
    and XRET: "x_var u0 P1 = A3"
    unfolding mk_obs_def
    by auto

  from XVu0 XRET show False
    by simp
qed

lemma hwq_no_common_match_from_e1:
  assumes N2: "N_Procs = 2"
      and SH_RELAXED: "E1_HWQ_relaxed_shape sk0"
      and E2MATCH: 
  "C_Path sk0 e2_labels s2"
      and E3MATCH: "C_Path sk0 e3_labels 
  s3"
  shows False
proof -
  (* Step 1. *)
  from SH_RELAXED have 
    "(Q_arr sk0 1 = A1 \<and> (program_counter sk0 P1 \<in> {''D1'', ''D2''} \<or> (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1))) \<or> 
     (Q_arr sk0 1 = BOT \<and> program_counter sk0 P1 = ''D4'' \<and> x_var sk0 P1 = A1)"
    unfolding E1_HWQ_relaxed_shape_def by auto
  then show False
  proof (elim disjE)
    (* Branch 1. *)
    assume SCAN: "Q_arr sk0 1 = A1 \<and> (program_counter sk0 
  P1 \<in> {''D1'', ''D2''} \<or> (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1))"
    show False 
      using hwq_scanning_branch_impossible[OF N2 SH_RELAXED SCAN E2MATCH E3MATCH] .
  next
    (* Branch 2. *)
    assume COMMITTED: "Q_arr sk0 1 = BOT \<and> program_counter sk0 P1 = ''D4'' \<and> x_var sk0 P1 = A1"
    show False 
      using hwq_committed_D4_impossible[OF SH_RELAXED COMMITTED E3MATCH] .
  qed
qed


(* ========================================================================= *)
(* e1 prefix final stateextractBridge *)
(* ========================================================================= *)

(* e1_labels prefix + P2 return *)
lemma e1_labels_snoc_P2_ret:
  "e1_labels = [
      Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
      Some (mk_obs enq A2 P2 call), None,
      Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret),
      Some (mk_obs deq BOT P1 call), None, None, None, None
    ] @ [Some (mk_obs enq A2 P2 ret)]"
  unfolding e1_labels_def by simp


(* Auxiliary lemma. *)
lemma C_Tau_no_E1_preserves_E1:
  assumes N2: "N_Procs = 2"
      and TAU: "C_Tau s t"
      and PC: "program_counter s p = ''E1''"
      and NOE1: "\<not> Sys_E1 p s t"
  shows "program_counter t p = ''E1''"
proof -
  have STEP0: "C_StepCR s None t"
    using TAU unfolding C_Tau_def by simp

  from STEP0 obtain q where PIN: "q \<in> ProcSet"
    and STEP: "Sys_E1 q s t \<or> Sys_E2 q s t \<or> Sys_D1 q s t \<or> Sys_D2 q s t \<or> Sys_D3 q s t"
    by (cases rule: C_StepCR.cases) auto

  have q_not_p: "q \<noteq> p"
  proof
    assume qp: "q = p"
    have C1: "Sys_E1 q s t \<Longrightarrow> False" using qp NOE1 by simp
    have C2: "Sys_E2 q s t \<Longrightarrow> False" using qp PC unfolding Sys_E2_def C_E2_def program_counter_def Let_def by auto
    have C3: "Sys_D1 q s t \<Longrightarrow> False" using qp PC unfolding Sys_D1_def C_D1_def program_counter_def Let_def by auto
    have C4: "Sys_D2 q s t \<Longrightarrow> False" using qp PC unfolding Sys_D2_def C_D2_def program_counter_def T_D2_EnterLoop_def Let_def by auto
    have C5: "Sys_D3 q s t \<Longrightarrow> False" using qp PC unfolding Sys_D3_def C_D3_def program_counter_def Let_def by auto
    from STEP C1 C2 C3 C4 C5 show False by blast
  qed

  have C1: "Sys_E1 q s t \<Longrightarrow> ?thesis" using q_not_p PC unfolding Sys_E1_def C_E1_def program_counter_def Let_def by (auto split: if_splits)
  have C2: "Sys_E2 q s t \<Longrightarrow> ?thesis" using q_not_p PC unfolding Sys_E2_def C_E2_def program_counter_def Let_def by (auto split: if_splits)
  have C3: "Sys_D1 q s t \<Longrightarrow> ?thesis" using q_not_p PC unfolding Sys_D1_def C_D1_def program_counter_def Let_def by (auto split: if_splits)
  have C4: "Sys_D2 q s t \<Longrightarrow> ?thesis" using q_not_p PC unfolding Sys_D2_def C_D2_def program_counter_def T_D2_EnterLoop_def Let_def by (auto split: if_splits)
  have C5: "Sys_D3 q s t \<Longrightarrow> ?thesis" using q_not_p PC unfolding Sys_D3_def C_D3_def program_counter_def Let_def by (auto split: if_splits)

  from STEP C1 C2 C3 C4 C5 show ?thesis by blast
qed

lemma C_Tau_Star_no_E1_preserves_E1:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and PC: "program_counter s p = ''E1''"
      and NOE1: "\<And>s' t'. C_Tau s' t' \<Longrightarrow> \<not> Sys_E1 p s' t'"
  shows "program_counter t p = ''E1''"
  using TAUS PC
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have PC2: "program_counter s2 p = ''E1''"
    using C_Tau_no_E1_preserves_E1[OF N2 step.hyps(1) step.prems]
          NOE1[OF step.hyps(1)]
    by blast
  show ?case
    using step.IH[OF PC2] .
qed



(* ========================================================================= *)
(* extract precondition: PC () *)
(* ========================================================================= *)
lemma hwq_other_proc_preserves_pc:
  assumes MOVED: "Sys_E1 q s s' \<or> Sys_E2 q s s' \<or> Sys_D1 q s s' \<or> Sys_D2 q s s' \<or> Sys_D3 q s s'"
      and NEQ: "p \<noteq> q"
  shows "program_counter s' p = program_counter s p"
  using MOVED NEQ
  unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def Sys_D1_def C_D1_def 
            Sys_D2_def C_D2_def Sys_D3_def C_D3_def 
            program_counter_def Let_def T_D2_EnterLoop_def
  by (auto split: if_splits)


(* ------------------------------------------------------------------------- *)
(* extract: isolation, Bug *)
(* ------------------------------------------------------------------------- *)
lemma my_C_Path_ConsE:
  assumes "C_Path s (x # xs) t"
  obtains s_mid where "C_Match s x s_mid" and "C_Path s_mid xs t"
  using assms by (cases rule: C_Path.cases) blast

lemma my_C_Match_NoneE:
  assumes "C_Match s None t"
  shows "C_Tau_Star s t"
  using assms by (cases rule: C_Match.cases) blast

lemma my_C_Match_SomeE:
  assumes "C_Match s (Some obs) t"
  obtains u v where "C_Tau_Star s u" and "C_StepCR u (Some obs) v" and "C_Tau_Star v t"
  using assms by (cases rule: C_Match.cases) blast

(* ========================================================================= *)
(* Proof step. *)
(* ========================================================================= *)
lemma hwq_tau_star_leaves_E1_via_Sys_E1:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and PC_S: "program_counter s p = ''E1''"
      and PC_T: "program_counter t p \<noteq> ''E1''"
  shows "\<exists>u v. C_Tau_Star s u \<and> C_Tau u v \<and> Sys_E1 p u v \<and> C_Tau_Star v t"
  using TAUS PC_S PC_T
proof (induction rule: C_Tau_Star.induct)
  case (refl s)
  (* : s = t, PC_S E1, PC_T E1, close by contradiction *)
  then show ?case by simp
next
  case (step s mid t)
  note TAU_S_MID = step.hyps(1)
  note TAUS_MID_T = step.hyps(2)
  note IH = step.IH
  note PC_S = step.prems(1)
  note PC_T = step.prems(2)

  (* Core: mid, p E1？ *)
  show ?case
  proof (cases "program_counter mid p = ''E1''")
    case True
    (* E1:, direct induction hypothesis mid ->* t *)
    have "\<exists>u v. C_Tau_Star mid u \<and> C_Tau u v \<and> Sys_E1 p u v \<and> C_Tau_Star v t"
      using IH[OF True PC_T] .
    then obtain u v where 
      "C_Tau_Star mid u" "C_Tau u v" "Sys_E1 p u v" "C_Tau_Star v t" by blast
    
    (* :, induction step, s -> mid *)
    moreover have "C_Tau_Star s u"
      using C_Tau_Star.step[OF TAU_S_MID `C_Tau_Star mid u`] .
    
    ultimately show ?thesis by blast
  next
    case False
    (* E1 ！ s -> mid ！ *)
    (* Auxiliary lemma. *)
    have "Sys_E1 p s mid"
    proof (rule ccontr)
      assume "\<not> Sys_E1 p s mid"
      then have "program_counter mid p = ''E1''"
        using C_Tau_no_E1_preserves_E1[OF N2 TAU_S_MID PC_S] by simp
      with False show False by contradiction
    qed
    
    (* : u s, v mid *)
    have "C_Tau_Star s s" by (simp add: C_Tau_Star.refl)
    moreover have "C_Tau s mid" using TAU_S_MID .
    moreover have "C_Tau_Star mid t" using TAUS_MID_T .
    ultimately show ?thesis
      using `Sys_E1 p s mid` by blast
  qed
qed





(* Bridge 1: P2_DONE concrete *)
lemma hwq_full_e1_P2_DONE:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
  shows "program_counter sk0 P2 = ''L0''"
proof -
  obtain m where
      PREFIX: "C_Path s0 [
        Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
        Some (mk_obs enq A2 P2 call), None,
        Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret),
        Some (mk_obs deq BOT P1 call), None, None, None, None
      ] m"
    and LAST: "C_Match m (Some (mk_obs enq A2 P2 ret)) sk0"
    using C_Path_snocE[OF E1FULL[unfolded e1_labels_snoc_P2_ret]]
    by blast

  obtain u v where
      TAU_M_U: "C_Tau_Star m u"
    and RET_STEP: "C_StepCR u (Some (mk_obs enq A2 P2 ret)) v"
    and TAU_V_SK0: "C_Tau_Star v sk0"
    using C_Match_someE[OF LAST] by blast

  have PC_V_P2: "program_counter v P2 = ''L0''"
  proof -
    from RET_STEP show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP2: "p = P2"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP2 show ?thesis
        unfolding Sys_E3_def C_E3_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have C_Tau_preserves_P2_L0:
    "\<And>s t. C_Tau s t \<Longrightarrow> program_counter s P2 = ''L0'' \<Longrightarrow> program_counter t P2 = ''L0''"
  proof -
    fix s t
    assume TAU: "C_Tau s t"
       and PC:  "program_counter s P2 = ''L0''"

    have STEP0: "C_StepCR s None t"
      using TAU unfolding C_Tau_def by simp

    from STEP0 obtain p where PIN: "p \<in> ProcSet"
      and STEP: "Sys_E1 p s t \<or> Sys_E2 p s t \<or> Sys_D1 p s t \<or> Sys_D2 p s t \<or> Sys_D3 p s t"
      by (cases rule: C_StepCR.cases) auto

    have p_not_P2: "p \<noteq> P2"
    proof
      assume pP2: "p = P2"
      from STEP show False
        using pP2 PC
        unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                  Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                  program_counter_def T_D2_EnterLoop_def Let_def
        by auto
    qed

    have pP1: "p = P1"
      using PIN N2 p_not_P2 by auto

    show "program_counter t P2 = ''L0''"
      using STEP pP1 PC
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def T_D2_EnterLoop_def Let_def
      by (elim disjE) (auto split: if_splits)
  qed

  have C_Tau_Star_preserves_P2_L0:
    "\<And>s t. C_Tau_Star s t \<Longrightarrow> program_counter s P2 = ''L0'' \<Longrightarrow> program_counter t P2 = ''L0''"
  proof -
    fix s t
    assume TAUS: "C_Tau_Star s t"
       and PC:   "program_counter s P2 = ''L0''"
    show "program_counter t P2 = ''L0''"
      using TAUS PC
    proof (induction rule: C_Tau_Star.induct)
      case refl
      then show ?case by simp
    next
      case (step s1 s2 s3)
      have PC2: "program_counter s2 P2 = ''L0''"
        using C_Tau_preserves_P2_L0[OF step.hyps(1) step.prems] .
      show ?case
        using step.IH[OF PC2] .
    qed
  qed

  show ?thesis
    using C_Tau_Star_preserves_P2_L0[OF TAU_V_SK0 PC_V_P2] .
qed

(* ========================================================================= *)
(* Bridge 2 Helper toolkit: X_var preservation *)
(* ========================================================================= *)

(* Helper 1: Sys_E1, single-step X_var *)
lemma C_StepCR_X_var_effect:
  assumes "C_StepCR s l t"
  shows "X_var t = X_var s \<or> (\<exists>p. Sys_E1 p s t \<and> X_var t = X_var s + 1)"
  using assms
  by (cases rule: C_StepCR.cases) 
     (auto simp: Sys_E1_def C_E1_def Sys_E2_def C_E2_def Sys_E3_def C_E3_def 
                 Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def 
                 Sys_D4_def C_D4_def Sys_L0_def C_L0_def X_var_def Let_def 
                 T_D2_EnterLoop_def
           split: if_splits)

(* Helper 2: Tau_Star, X_var *)
lemma C_Tau_Star_X_var_mono:
  assumes "C_Tau_Star s t"
  shows "X_var s \<le> X_var t"
  using assms
proof (induction rule: C_Tau_Star.induct)
  case refl then show ?case by simp
next
  case (step s1 s2 s3)
  have "C_StepCR s1 None s2" using step.hyps(1) unfolding C_Tau_def by simp
  then have "X_var s2 = X_var s1 \<or> (\<exists>p. Sys_E1 p s1 s2 \<and> X_var s2 = X_var s1 + 1)"
    using C_StepCR_X_var_effect by blast
  then have "X_var s1 \<le> X_var s2" by auto
  with step.IH show ?case by auto
qed

(* Helper 3: L0, call, Tau_Star, E1, X_var increase *)
(* Main theorem obtain state, *)


(* ========================================================================= *)
(* Bridge 2 Main theorem: X_var *)
(* ========================================================================= *)
(* Step 1.1.2.1. *)
lemma C_StepCR_P1_vis_preserves_P2_E1:
  assumes VIS: "C_StepCR s (Some obs) t"
      and PID: "fst (snd (snd obs)) = P1"
      and PC:  "program_counter s P2 = ''E1''"
  shows "program_counter t P2 = ''E1''"
  using VIS PID PC
  by (cases rule: C_StepCR.cases)
     (auto simp: mk_obs_def Sys_L0_def C_L0_def Sys_E3_def C_E3_def Sys_D4_def C_D4_def program_counter_def Let_def split: if_splits)



(* ------------------------------------------------------------------------- *)
(* Core slice:, *)
(* ------------------------------------------------------------------------- *)
lemma C_Path_mid_preserves_P2_E1_if_no_P2_E1:
  assumes N2: "N_Procs = 2"
      and PATH: "C_Path s [None, Some (mk_obs enq A3 P1 call), None, None, 
                           Some (mk_obs enq A3 P1 ret), Some (mk_obs deq BOT P1 call), 
                           None, None, None, None] t"
      and PC: "program_counter s P2 = ''E1''"
      and NOE1_TAU: "\<And>s' t'. C_Tau s' t' \<Longrightarrow> \<not> Sys_E1 P2 s' t'"
  shows "program_counter t P2 = ''E1''"
proof -
  (* 1: None *)
  obtain s1 where M1: "C_Match s None s1" 
    and P1: "C_Path s1 [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret), Some (mk_obs deq BOT P1 call), None, None, None, None] t"
    using my_C_Path_ConsE[OF PATH] .
  have T1: "C_Tau_Star s s1" using my_C_Match_NoneE[OF M1] .
  have PC1: "program_counter s1 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T1 PC NOE1_TAU] .

  (* 2: A3 call *)
  obtain s2 where M2: "C_Match s1 (Some (mk_obs enq A3 P1 call)) s2" 
    and P2: "C_Path s2 [None, None, Some (mk_obs enq A3 P1 ret), Some (mk_obs deq BOT P1 call), None, None, None, None] t"
    using my_C_Path_ConsE[OF P1] .
  obtain u2 v2 where T2a: "C_Tau_Star s1 u2" and V2: "C_StepCR u2 (Some (mk_obs enq A3 P1 call)) v2" and T2b: "C_Tau_Star v2 s2" 
    using my_C_Match_SomeE[OF M2] .
  have PC_u2: "program_counter u2 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T2a PC1 NOE1_TAU] .
  have PC_v2: "program_counter v2 P2 = ''E1''" using C_StepCR_P1_vis_preserves_P2_E1[OF V2 _ PC_u2] by (auto simp: mk_obs_def)
  have PC2: "program_counter s2 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T2b PC_v2 NOE1_TAU] .

  (* 3: None, None *)
  obtain s3 where M3: "C_Match s2 None s3" and P3: "C_Path s3 [None, Some (mk_obs enq A3 P1 ret), Some (mk_obs deq BOT P1 call), None, None, None, None] t"
    using my_C_Path_ConsE[OF P2] .
  have T3: "C_Tau_Star s2 s3" using my_C_Match_NoneE[OF M3] .
  have PC3: "program_counter s3 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T3 PC2 NOE1_TAU] .

  obtain s4 where M4: "C_Match s3 None s4" and P4: "C_Path s4 [Some (mk_obs enq A3 P1 ret), Some (mk_obs deq BOT P1 call), None, None, None, None] t"
    using my_C_Path_ConsE[OF P3] .
  have T4: "C_Tau_Star s3 s4" using my_C_Match_NoneE[OF M4] .
  have PC4: "program_counter s4 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T4 PC3 NOE1_TAU] .

  (* 4: A3 ret *)
  obtain s5 where M5: "C_Match s4 (Some (mk_obs enq A3 P1 ret)) s5" and P5: "C_Path s5 [Some (mk_obs deq BOT P1 call), None, None, None, None] t"
    using my_C_Path_ConsE[OF P4] .
  obtain u5 v5 where T5a: "C_Tau_Star s4 u5" and V5: "C_StepCR u5 (Some (mk_obs enq A3 P1 ret)) v5" and T5b: "C_Tau_Star v5 s5" 
    using my_C_Match_SomeE[OF M5] .
  have PC_u5: "program_counter u5 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T5a PC4 NOE1_TAU] .
  have PC_v5: "program_counter v5 P2 = ''E1''" using C_StepCR_P1_vis_preserves_P2_E1[OF V5 _ PC_u5] by (auto simp: mk_obs_def)
  have PC5: "program_counter s5 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T5b PC_v5 NOE1_TAU] .

  (* 5: deq BOT call *)
  obtain s6 where M6: "C_Match s5 (Some (mk_obs deq BOT P1 call)) s6" and P6: "C_Path s6 [None, None, None, None] t"
    using my_C_Path_ConsE[OF P5] .
  obtain u6 v6 where T6a: "C_Tau_Star s5 u6" and V6: "C_StepCR u6 (Some (mk_obs deq BOT P1 call)) v6" and T6b: "C_Tau_Star v6 s6" 
    using my_C_Match_SomeE[OF M6] .
  have PC_u6: "program_counter u6 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T6a PC5 NOE1_TAU] .
  have PC_v6: "program_counter v6 P2 = ''E1''" using C_StepCR_P1_vis_preserves_P2_E1[OF V6 _ PC_u6] by (auto simp: mk_obs_def)
  have PC6: "program_counter s6 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T6b PC_v6 NOE1_TAU] .

  (* 6: tail 4 None *)
  obtain s7 where M7: "C_Match s6 None s7" and P7: "C_Path s7 [None, None, None] t" using my_C_Path_ConsE[OF P6] .
  have T7: "C_Tau_Star s6 s7" using my_C_Match_NoneE[OF M7] .
  have PC7: "program_counter s7 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T7 PC6 NOE1_TAU] .

  obtain s8 where M8: "C_Match s7 None s8" and P8: "C_Path s8 [None, None] t" using my_C_Path_ConsE[OF P7] .
  have T8: "C_Tau_Star s7 s8" using my_C_Match_NoneE[OF M8] .
  have PC8: "program_counter s8 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T8 PC7 NOE1_TAU] .

  obtain s9 where M9: "C_Match s8 None s9" and P9: "C_Path s9 [None] t" using my_C_Path_ConsE[OF P8] .
  have T9: "C_Tau_Star s8 s9" using my_C_Match_NoneE[OF M9] .
  have PC9: "program_counter s9 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T9 PC8 NOE1_TAU] .

  obtain s10 where M10: "C_Match s9 None s10" and P10: "C_Path s10 [] t" using my_C_Path_ConsE[OF P9] .
  have T10: "C_Tau_Star s9 s10" using my_C_Match_NoneE[OF M10] .
  have PC10: "program_counter s10 P2 = ''E1''" using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 T10 PC9 NOE1_TAU] .

  (* validate *)
  have S10_T: "s10 = t" using P10 by (cases rule: C_Path.cases) auto
  show ?thesis using PC10 S10_T by simp
qed

lemma p1_a1_call_ret_contains_E1_before_sk0:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
  shows "\<exists>sA1 tA1. Sys_E1 P1 sA1 tA1"
proof (rule ccontr)
  assume NOE1: "\<not> (\<exists>sA1 tA1. Sys_E1 P1 sA1 tA1)"

  have NOE1_TAU: "\<And>s' t'. C_Tau s' t' \<Longrightarrow> \<not> Sys_E1 P1 s' t'"
  proof -
    fix s' t' assume "C_Tau s' t'"
    show "\<not> Sys_E1 P1 s' t'" using NOE1 by blast
  qed

  have SPLIT: "e1_labels = [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @ 
                           [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call), None, None, 
                            Some (mk_obs enq A3 P1 ret), Some (mk_obs deq BOT P1 call), None, None, None, None, 
                            Some (mk_obs enq A2 P2 ret)]"
    unfolding e1_labels_def by simp

  obtain s_a1_ret where 
    P_A1_SEG: "C_Path s0 [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    using C_Path_appendE[OF E1FULL[unfolded SPLIT]] by blast

  (* precondition: peel off call *)
  obtain s1 where 
    M_CALL: "C_Match s0 (Some (mk_obs enq A1 P1 call)) s1" and
    P_REST: "C_Path s1 [None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    using my_C_Path_ConsE[OF P_A1_SEG] .

  obtain u_call_pre u_call_post where
    TAU_PRE: "C_Tau_Star s0 u_call_pre" and
    STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A1 P1 call)) u_call_post" and
    TAU_POST: "C_Tau_Star u_call_post s1"
    using my_C_Match_SomeE[OF M_CALL] .

  have PC1_0: "program_counter s0 P1 = ''L0''"
    using INIT unfolding Init_def program_counter_def by auto
  have PC2_0: "program_counter s0 P2 = ''L0''"
    using INIT unfolding Init_def program_counter_def by auto

  have U_PRE_EQ: "u_call_pre = s0"
    using C_Tau_Star_eq_if_P1P2_L0[OF N2 PC1_0 PC2_0 TAU_PRE] .

  have PC_P1_POST_CALL: "program_counter u_call_post P1 = ''E1''"
  proof -
    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_L0_enq_vis pP1 show ?thesis
        unfolding Sys_L0_def C_L0_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  (* postcondition: snocE peel offtail ret, [] TODO *)
  have P_REST_APP: "C_Path s1 ([None, None] @ [Some (mk_obs enq A1 P1 ret)]) s_a1_ret"
    using P_REST by simp

  obtain s3 where 
    P_NONES: "C_Path s1 [None, None] s3" and 
    M_RET: "C_Match s3 (Some (mk_obs enq A1 P1 ret)) s_a1_ret"
    using C_Path_snocE[OF P_REST_APP] by blast

  (* middle segment: ConsE extract None *)
  obtain s2 where 
    M_N1: "C_Match s1 None s2" and P_N2: "C_Path s2 [None] s3"
    using my_C_Path_ConsE[OF P_NONES] .

  obtain s3_bis where
    M_N2: "C_Match s2 None s3_bis" and P_EMP: "C_Path s3_bis [] s3"
    using my_C_Path_ConsE[OF P_N2] .

  have S3_EQ: "s3_bis = s3"
    using P_EMP by (cases rule: C_Path.cases) auto

  obtain u_ret_pre u_ret_post where
    TAU_RET_PRE: "C_Tau_Star s3 u_ret_pre" and
    STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A1 P1 ret)) u_ret_post"
    using my_C_Match_SomeE[OF M_RET] .

  have PC_P1_RET_PRE_NOT_E1: "program_counter u_ret_pre P1 \<noteq> ''E1''"
  proof
    assume EQ: "program_counter u_ret_pre P1 = ''E1''"
    from STEP_RET show False
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP1 EQ show False
        unfolding Sys_E3_def C_E3_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  (* explicit, *)
  have T1: "C_Tau_Star s1 s2" using my_C_Match_NoneE[OF M_N1] .
  have T2: "C_Tau_Star s2 s3" using my_C_Match_NoneE[OF M_N2] S3_EQ by simp

  have T12: "C_Tau_Star s1 s3"
    using C_Tau_Star_trans[OF T1 T2] .

  have T123: "C_Tau_Star u_call_post s3"
    using C_Tau_Star_trans[OF TAU_POST T12] .

  have TAU_TOTAL: "C_Tau_Star u_call_post u_ret_pre"
    using C_Tau_Star_trans[OF T123 TAU_RET_PRE] .

  have PC_RET_PRE_IS_E1: "program_counter u_ret_pre P1 = ''E1''"
    using C_Tau_Star_no_E1_preserves_E1[OF N2 TAU_TOTAL PC_P1_POST_CALL NOE1_TAU] .

  from PC_RET_PRE_IS_E1 PC_P1_RET_PRE_NOT_E1 show False by simp
qed


lemma p2_a2_call_ret_contains_E1_before_sk0:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
  shows "\<exists>sA2 tA2. Sys_E1 P2 sA2 tA2"
proof (rule ccontr)
  assume NOE1: "\<not> (\<exists>sA2 tA2. Sys_E1 P2 sA2 tA2)"

  have NOE1_TAU: "\<And>s' t'. C_Tau s' t' \<Longrightarrow> \<not> Sys_E1 P2 s' t'"
  proof -
    fix s' t'
    assume "C_Tau s' t'"
    show "\<not> Sys_E1 P2 s' t'"
      using NOE1 by blast
  qed

have SPLIT:
  "e1_labels =
    ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @
     [Some (mk_obs enq A2 P2 call)]) @
    ([None,
      Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret),
      Some (mk_obs deq BOT P1 call), None, None, None, None]) @
    [Some (mk_obs enq A2 P2 ret)]"
  unfolding e1_labels_def by simp

obtain s_call_pre where
    P_PRE:
      "C_Path s0
        ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @
         [Some (mk_obs enq A2 P2 call)]) s_call_pre"
  and P_REST:
      "C_Path s_call_pre
        ([None,
          Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret),
          Some (mk_obs deq BOT P1 call), None, None, None, None] @
         [Some (mk_obs enq A2 P2 ret)]) sk0"
  using C_Path_appendE[OF E1FULL[unfolded SPLIT]]
  by blast

  obtain m_mid where
      P_MID:
        "C_Path s_call_pre
          [None,
           Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret),
           Some (mk_obs deq BOT P1 call), None, None, None, None] m_mid"
    and M_RET: "C_Match m_mid (Some (mk_obs enq A2 P2 ret)) sk0"
    using C_Path_snocE[OF P_REST]
    by blast

  obtain s_before_call where
      P_BEFORE:
        "C_Path s0 [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_before_call"
    and M_CALL: "C_Match s_before_call (Some (mk_obs enq A2 P2 call)) s_call_pre"
    using C_Path_snocE[OF P_PRE]
    by blast

  obtain u_call_pre u_call_post where
      TAU_PRE_CALL: "C_Tau_Star s_before_call u_call_pre"
    and STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A2 P2 call)) u_call_post"
    and TAU_POST_CALL: "C_Tau_Star u_call_post s_call_pre"
    using my_C_Match_SomeE[OF M_CALL] .

  have PC_P2_POST_CALL: "program_counter u_call_post P2 = ''E1''"
  proof -
    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have pP2: "p = P2"
        unfolding mk_obs_def by auto
      from C_Sys_L0_enq_vis pP2 show ?thesis
        unfolding Sys_L0_def C_L0_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  obtain v_ret_pre v_ret_post where
      TAU_PRE_RET: "C_Tau_Star m_mid v_ret_pre"
    and STEP_RET: "C_StepCR v_ret_pre (Some (mk_obs enq A2 P2 ret)) v_ret_post"
    and TAU_POST_RET: "C_Tau_Star v_ret_post sk0"
    using my_C_Match_SomeE[OF M_RET] .

  have PC_P2_PRE_RET_NOT_E1: "program_counter v_ret_pre P2 \<noteq> ''E1''"
  proof
    assume EQ: "program_counter v_ret_pre P2 = ''E1''"
    from STEP_RET show False
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP2: "p = P2"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP2 EQ show False
        unfolding Sys_E3_def C_E3_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have PC_call_pre: "program_counter s_call_pre P2 = ''E1''"
    using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 TAU_POST_CALL PC_P2_POST_CALL NOE1_TAU] .

  have PC_mid: "program_counter m_mid P2 = ''E1''"
    using C_Path_mid_preserves_P2_E1_if_no_P2_E1[OF N2 P_MID PC_call_pre NOE1_TAU] .

  have PC_ret_pre: "program_counter v_ret_pre P2 = ''E1''"
    using C_Tau_Star_no_P2_E1_preserves_E1[OF N2 TAU_PRE_RET PC_mid NOE1_TAU] .

  from PC_ret_pre PC_P2_PRE_RET_NOT_E1 show False
    by simp
qed


lemma p1_a3_call_ret_contains_E1_before_sk0:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
  shows "\<exists>sA3 tA3. Sys_E1 P1 sA3 tA3"
proof (rule ccontr)
  assume NOE1: "\<not> (\<exists>sA3 tA3. Sys_E1 P1 sA3 tA3)"

  have NOE1_TAU: "\<And>s' t'. C_Tau s' t' \<Longrightarrow> \<not> Sys_E1 P1 s' t'"
  proof -
    fix s' t'
    assume "C_Tau s' t'"
    show "\<not> Sys_E1 P1 s' t'"
      using NOE1 by blast
  qed

  have SPLIT:
    "e1_labels =
      ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
        Some (mk_obs enq A2 P2 call), None]) @
      ([Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]) @
      ([Some (mk_obs deq BOT P1 call), None, None, None, None,
        Some (mk_obs enq A2 P2 ret)])"
    unfolding e1_labels_def by simp

  obtain s_before_call where
      P_BEFORE:
        "C_Path s0
          [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
           Some (mk_obs enq A2 P2 call), None] s_before_call"
    and P_REST:
        "C_Path s_before_call
          ([Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)] @
           [Some (mk_obs deq BOT P1 call), None, None, None, None,
            Some (mk_obs enq A2 P2 ret)]) sk0"
    using C_Path_appendE[OF E1FULL[unfolded SPLIT]]
    by blast

  obtain s_a3_ret where
      P_A3_SEG:
        "C_Path s_before_call
          [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)] s_a3_ret"
    and P_TAIL:
        "C_Path s_a3_ret
          [Some (mk_obs deq BOT P1 call), None, None, None, None,
           Some (mk_obs enq A2 P2 ret)] sk0"
    using C_Path_appendE[OF P_REST]
    by blast

  obtain s1 where
      M_CALL: "C_Match s_before_call (Some (mk_obs enq A3 P1 call)) s1"
    and P_REST1: "C_Path s1 [None, None, Some (mk_obs enq A3 P1 ret)] s_a3_ret"
    using my_C_Path_ConsE[OF P_A3_SEG] .

  obtain u_call_pre u_call_post where
      TAU_PRE: "C_Tau_Star s_before_call u_call_pre"
    and STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A3 P1 call)) u_call_post"
    and TAU_POST: "C_Tau_Star u_call_post s1"
    using my_C_Match_SomeE[OF M_CALL] .

  have PC_P1_POST_CALL: "program_counter u_call_post P1 = ''E1''"
  proof -
    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_L0_enq_vis pP1 show ?thesis
        unfolding Sys_L0_def C_L0_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  obtain s2 where
      M_N1: "C_Match s1 None s2"
    and P_REST2: "C_Path s2 [None, Some (mk_obs enq A3 P1 ret)] s_a3_ret"
    using my_C_Path_ConsE[OF P_REST1] .

  have T1: "C_Tau_Star s1 s2"
    using my_C_Match_NoneE[OF M_N1] .

  obtain s3 where
      M_N2: "C_Match s2 None s3"
    and P_REST3: "C_Path s3 [Some (mk_obs enq A3 P1 ret)] s_a3_ret"
    using my_C_Path_ConsE[OF P_REST2] .

  have T2: "C_Tau_Star s2 s3"
    using my_C_Match_NoneE[OF M_N2] .

  obtain s4 where
      M_RET: "C_Match s3 (Some (mk_obs enq A3 P1 ret)) s4"
    and P_END: "C_Path s4 [] s_a3_ret"
    using my_C_Path_ConsE[OF P_REST3] .

  have S4_EQ: "s4 = s_a3_ret"
    using P_END by (cases rule: C_Path.cases) auto

  obtain u_ret_pre u_ret_post where
      TAU_RET_PRE: "C_Tau_Star s3 u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A3 P1 ret)) u_ret_post"
    and TAU_RET_POST: "C_Tau_Star u_ret_post s4"
    using my_C_Match_SomeE[OF M_RET] .

  have PC_P1_RET_PRE_NOT_E1: "program_counter u_ret_pre P1 \<noteq> ''E1''"
  proof
    assume EQ: "program_counter u_ret_pre P1 = ''E1''"
    from STEP_RET show False
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP1 EQ show False
        unfolding Sys_E3_def C_E3_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have T12: "C_Tau_Star s1 s3"
    using C_Tau_Star_trans[OF T1 T2] .

  have T123: "C_Tau_Star u_call_post s3"
    using C_Tau_Star_trans[OF TAU_POST T12] .

  have TAU_TOTAL: "C_Tau_Star u_call_post u_ret_pre"
    using C_Tau_Star_trans[OF T123 TAU_RET_PRE] .

  have PC_RET_PRE_IS_E1: "program_counter u_ret_pre P1 = ''E1''"
    using C_Tau_Star_no_E1_preserves_E1[OF N2 TAU_TOTAL PC_P1_POST_CALL NOE1_TAU] .

  from PC_RET_PRE_IS_E1 PC_P1_RET_PRE_NOT_E1 show False
    by simp
qed





(* E1 state tau step preserve (L0_enq E1) *)
lemma C_Tau_not_E1_preserves:
  assumes "C_Tau s t" and "program_counter s p \<noteq> ''E1''"
  shows "program_counter t p \<noteq> ''E1''"
proof -
  from \<open>C_Tau s t\<close> have "C_StepCR s None t" unfolding C_Tau_def by simp
  then obtain q where "q \<in> ProcSet" and "Sys_E1 q s t \<or> Sys_E2 q s t \<or> Sys_D1 q s t \<or> Sys_D2 q s t \<or> Sys_D3 q s t"
    by (cases rule: C_StepCR.cases) auto
  then show ?thesis
    using assms(2)
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def program_counter_def Let_def
    by (auto split: if_splits)
qed

lemma C_Tau_Star_not_E1_preserves:
  assumes "C_Tau_Star s t" and "program_counter s p \<noteq> ''E1''"
  shows "program_counter t p \<noteq> ''E1''"
  using assms
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  (* Step 1.1.2. *)
  have PC_S2: "program_counter s2 p \<noteq> ''E1''"
    using C_Tau_not_E1_preserves[OF step.hyps(1) step.prems] .
    
  (* Step 2.2.3. *)
  then show ?case
    using step.IH by simp
qed

(* P2 visible step P1 PC *)
lemma C_StepCR_P2_vis_preserves_P1_PC:
  assumes "C_StepCR s (Some obs) t" and "fst (snd (snd obs)) = P2"
  shows "program_counter t P1 = program_counter s P1"
  using assms by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def Sys_L0_def C_L0_def Sys_E3_def C_E3_def Sys_D4_def C_D4_def program_counter_def Let_def split: if_splits)

(* Step 1. *)
lemma C_Tau_potential_eq:
  assumes N2: "N_Procs = 2"
      and TAU: "C_Tau s t"
  shows "X_var t + E1_credit t = X_var s + E1_credit s"
proof -
  from TAU have "C_StepCR s None t" unfolding C_Tau_def by simp
  then obtain p where P_IN: "p \<in> ProcSet"
    and STEP: "Sys_E1 p s t \<or> Sys_E2 p s t \<or> Sys_D1 p s t \<or> Sys_D2 p s t \<or> Sys_D3 p s t"
    by (cases rule: C_StepCR.cases) auto

  have p_cases: "p = P1 \<or> p = P2"
    using P_IN N2 unfolding ProcSet_def by auto

  have C1: "Sys_E1 p s t \<Longrightarrow> ?thesis"
    using p_cases unfolding Sys_E1_def C_E1_def E1_credit_def X_var_def program_counter_def Let_def by (auto split: if_splits)
  have C2: "Sys_E2 p s t \<Longrightarrow> ?thesis"
    using p_cases unfolding Sys_E2_def C_E2_def E1_credit_def X_var_def program_counter_def Let_def by (auto split: if_splits)
  have C3: "Sys_D1 p s t \<Longrightarrow> ?thesis"
    using p_cases unfolding Sys_D1_def C_D1_def E1_credit_def X_var_def program_counter_def Let_def by (auto split: if_splits)
  have C4: "Sys_D2 p s t \<Longrightarrow> ?thesis"
    using p_cases unfolding Sys_D2_def C_D2_def E1_credit_def X_var_def program_counter_def Let_def by (auto split: if_splits)
  have C5: "Sys_D3 p s t \<Longrightarrow> ?thesis"
    using p_cases unfolding Sys_D3_def C_D3_def E1_credit_def X_var_def program_counter_def Let_def by (auto split: if_splits)

  from STEP C1 C2 C3 C4 C5 show ?thesis by blast
qed

lemma C_Tau_Star_potential_eq:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
  shows "X_var t + E1_credit t = X_var s + E1_credit s"
  using TAUS
proof (induction rule: C_Tau_Star.induct)
  case refl then show ?case by simp
next
  case (step s1 s2 s3)
  have "X_var s2 + E1_credit s2 = X_var s1 + E1_credit s1"
    using C_Tau_potential_eq[OF N2 step.hyps(1)] .
  thus ?case using step.IH by arith
qed

(* Step 2. *)
lemma C_StepCR_Vis_potential_eq:
  assumes N2: "N_Procs = 2"
      and VIS: "C_StepCR s (Some obs) t"
  shows "X_var t + E1_credit t = X_var s + E1_credit s + is_enq_call_cr obs"
  using VIS
proof (cases rule: C_StepCR.cases)
  case (C_Sys_L0_enq_vis p)
  have p_cases: "p = P1 \<or> p = P2"
    using C_Sys_L0_enq_vis N2 unfolding ProcSet_def by auto
  then show ?thesis 
    using C_Sys_L0_enq_vis
    unfolding Sys_L0_def C_L0_def E1_credit_def X_var_def program_counter_def is_enq_call_cr_def mk_obs_def Let_def
    by (auto split: if_splits)
next
  case (C_Sys_L0_deq_vis p)
  have p_cases: "p = P1 \<or> p = P2" using C_Sys_L0_deq_vis N2 unfolding ProcSet_def by auto
  then show ?thesis using C_Sys_L0_deq_vis unfolding Sys_L0_def C_L0_def E1_credit_def X_var_def program_counter_def is_enq_call_cr_def mk_obs_def Let_def by (auto split: if_splits)
next
  case (C_Sys_E3_vis p)
  have p_cases: "p = P1 \<or> p = P2" using C_Sys_E3_vis N2 unfolding ProcSet_def by auto
  then show ?thesis using C_Sys_E3_vis unfolding Sys_E3_def C_E3_def E1_credit_def X_var_def program_counter_def is_enq_call_cr_def mk_obs_def Let_def by (auto split: if_splits)
next
  case (C_Sys_D4_vis p)
  have p_cases: "p = P1 \<or> p = P2" using C_Sys_D4_vis N2 unfolding ProcSet_def by auto
  then show ?thesis using C_Sys_D4_vis unfolding Sys_D4_def C_D4_def E1_credit_def X_var_def program_counter_def is_enq_call_cr_def mk_obs_def Let_def by (auto split: if_splits)
qed 

(* Step 3. *)
lemma C_Match_potential_eq:
  assumes N2: "N_Procs = 2"
      and MATCH: "C_Match s l t"
  shows "X_var t + E1_credit t = X_var s + E1_credit s + is_enq_call_opt l"
  using MATCH
proof (cases rule: C_Match.cases)
  case match_tau
  then have L_EQ: "l = None"
    and TS: "C_Tau_Star s t"
    by auto
  have "X_var t + E1_credit t = X_var s + E1_credit s"
    using C_Tau_Star_potential_eq[OF N2 TS] .
  thus ?thesis
    using L_EQ
    unfolding is_enq_call_opt_def
    by simp
next
  case match_vis
  then obtain u a v where
      L_EQ: "l = Some a"
    and T1:   "C_Tau_Star s u"
    and V:    "C_StepCR u (Some a) v"
    and T2:   "C_Tau_Star v t"
    by auto

  have B1: "X_var u + E1_credit u = X_var s + E1_credit s"
    using C_Tau_Star_potential_eq[OF N2 T1] .

  have B2: "X_var v + E1_credit v = X_var u + E1_credit u + is_enq_call_cr a"
    using C_StepCR_Vis_potential_eq[OF N2 V] .

  have B3: "X_var t + E1_credit t = X_var v + E1_credit v"
    using C_Tau_Star_potential_eq[OF N2 T2] .

  have "X_var t + E1_credit t = X_var s + E1_credit s + is_enq_call_cr a"
    using B1 B2 B3 by arith
  thus ?thesis
    using L_EQ
    unfolding is_enq_call_opt_def
    by simp
qed

(* 4. global path equality *)
lemma C_Path_potential_eq:
  assumes N2: "N_Procs = 2"
      and PATH: "C_Path s labels t"
  shows "X_var t + E1_credit t = X_var s + E1_credit s + sum_list (map is_enq_call_opt labels)"
  using PATH
proof (induction rule: C_Path.induct)
  case nil then show ?case by simp
next
  case (cons s l s1 ls s2)
  have B_MATCH: "X_var s1 + E1_credit s1 = X_var s + E1_credit s + is_enq_call_opt l"
    using C_Match_potential_eq[OF N2 cons.hyps(1)] .
  have B_PATH: "X_var s2 + E1_credit s2 = X_var s1 + E1_credit s1 + sum_list (map is_enq_call_opt ls)"
    using cons.IH .
  show ?case using B_MATCH B_PATH by auto
qed

(* Auxiliary lemma. *)
lemma hwq_full_e1_P1_suffix_not_E1:
  assumes "C_Path s_before_deq ([Some (mk_obs deq BOT P1 call), None, None, None, None] @ [Some (mk_obs enq A2 P2 ret)]) sk0"
  shows "program_counter sk0 P1 \<noteq> ''E1''"
proof -
  (* direct Helperprecise path *)
  obtain s_deq_post where P_DEQ: "C_Path s_before_deq [Some (mk_obs deq BOT P1 call), None, None, None, None] s_deq_post"
    and M_RET: "C_Match s_deq_post (Some (mk_obs enq A2 P2 ret)) sk0"
    using C_Path_snocE[OF assms] by blast

  obtain s1 where M_DEQ: "C_Match s_before_deq (Some (mk_obs deq BOT P1 call)) s1" 
    and P_N4: "C_Path s1 [None, None, None, None] s_deq_post"
    using my_C_Path_ConsE[OF P_DEQ] .
    
  obtain u_deq_pre u_deq_post where "C_Tau_Star s_before_deq u_deq_pre"
    and STEP_DEQ: "C_StepCR u_deq_pre (Some (mk_obs deq BOT P1 call)) u_deq_post"
    and T_DEQ_POST: "C_Tau_Star u_deq_post s1" 
    using my_C_Match_SomeE[OF M_DEQ] .

  (* Core1: deq call, P1 D1, E1 *)
  have PC_P1_D1: "program_counter u_deq_post P1 \<noteq> ''E1''"
    using STEP_DEQ by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def Sys_L0_def C_L0_def program_counter_def Let_def split: if_splits)

  have PC_P1_S1: "program_counter s1 P1 \<noteq> ''E1''"
    using C_Tau_Star_not_E1_preserves[OF T_DEQ_POST PC_P1_D1] .

  (* Core2: None, tau step E1 E1 *)
  obtain s2 where M_N1: "C_Match s1 None s2" and P_N3: "C_Path s2 [None, None, None] s_deq_post" using my_C_Path_ConsE[OF P_N4] .
  obtain s3 where M_N2: "C_Match s2 None s3" and P_N2: "C_Path s3 [None, None] s_deq_post" using my_C_Path_ConsE[OF P_N3] .
  obtain s4 where M_N3: "C_Match s3 None s4" and P_N1: "C_Path s4 [None] s_deq_post" using my_C_Path_ConsE[OF P_N2] .
  obtain s5 where M_N4: "C_Match s4 None s5" and P_N0: "C_Path s5 [] s_deq_post" using my_C_Path_ConsE[OF P_N1] .
  have S5_EQ: "s5 = s_deq_post" using P_N0 by (cases rule: C_Path.cases) auto

  have T_N_ALL: "C_Tau_Star s1 s_deq_post"
    using C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N1] 
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N2] 
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N3] my_C_Match_NoneE[OF M_N4]]]] S5_EQ by simp

  have PC_P1_DEQ_POST: "program_counter s_deq_post P1 \<noteq> ''E1''"
    using C_Tau_Star_not_E1_preserves[OF T_N_ALL PC_P1_S1] .

  (* Core3: P2 visible step *)
  obtain u_ret_pre u_ret_post where T_RET_PRE: "C_Tau_Star s_deq_post u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
    and T_RET_POST: "C_Tau_Star u_ret_post sk0" 
    using my_C_Match_SomeE[OF M_RET] .

  have PC_P1_RET_PRE: "program_counter u_ret_pre P1 \<noteq> ''E1''"
    using C_Tau_Star_not_E1_preserves[OF T_RET_PRE PC_P1_DEQ_POST] .

  have PC_P1_RET_POST: "program_counter u_ret_post P1 \<noteq> ''E1''"
    using C_StepCR_P2_vis_preserves_P1_PC[OF STEP_RET] PC_P1_RET_PRE by (simp add: mk_obs_def)

  show ?thesis
    using C_Tau_Star_not_E1_preserves[OF T_RET_POST PC_P1_RET_POST] .
qed

lemma hwq_full_e1_X4:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
      and INV: "system_invariant sk0"
  shows "X_var sk0 = 4"
proof -
  (* Step 1. *)
  have X0: "X_var s0 = 1"
    using INIT unfolding Init_def X_var_def by auto
  
  have CREDIT0: "E1_credit s0 = 0"
    using INIT unfolding Init_def E1_credit_def program_counter_def by auto

  have E1_BUDGET: "sum_list (map is_enq_call_opt e1_labels) = 3"
    unfolding e1_labels_def is_enq_call_opt_def is_enq_call_cr_def mk_obs_def
    by simp

  have POTENTIAL_EQ:
      "X_var sk0 + E1_credit sk0 =
       X_var s0 + E1_credit s0 + sum_list (map is_enq_call_opt e1_labels)"
    using C_Path_potential_eq[OF N2 E1FULL] .

  (* Step 2.0. *)
  (* Step 2.2. *)
  have PC_P2_L0: "program_counter sk0 P2 = ''L0''"
    using hwq_full_e1_P2_DONE[OF N2 INIT E1FULL] .

  hence PC_P2_NOT_E1: "program_counter sk0 P2 \<noteq> ''E1''"
    by simp

  (* Step 2.1. *)
  have SPLIT:
    "e1_labels =
      ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
        Some (mk_obs enq A2 P2 call), None,
        Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)])
      @
      ([Some (mk_obs deq BOT P1 call), None, None, None, None]
        @ [Some (mk_obs enq A2 P2 ret)])"
    unfolding e1_labels_def by simp

  obtain s_before_deq where
      P_SUFFIX:
        "C_Path s_before_deq
          ([Some (mk_obs deq BOT P1 call), None, None, None, None]
            @ [Some (mk_obs enq A2 P2 ret)]) sk0"
    using C_Path_appendE[OF E1FULL[unfolded SPLIT]]
    by blast

  have PC_P1_NOT_E1: "program_counter sk0 P1 \<noteq> ''E1''"
    using hwq_full_e1_P1_suffix_not_E1[OF P_SUFFIX] .

  have CREDIT_SK0: "E1_credit sk0 = 0"
    unfolding E1_credit_def
    using PC_P1_NOT_E1 PC_P2_NOT_E1
    by simp

  (* Step 3. *)
  show ?thesis
    using POTENTIAL_EQ X0 CREDIT0 E1_BUDGET CREDIT_SK0
    by arith
qed

(* Bridge 3: P1 pending-state *)

(* ========================================================================= *)
(* P1 D (Pending Deq) stateenvelopepreserve *)
(* ========================================================================= *)

(* Step 1.1. *)
lemma C_Tau_preserves_D_phase_P1:
  assumes "C_Tau s t"
      and "program_counter s P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
  shows "program_counter t P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
proof -
  from \<open>C_Tau s t\<close> have "C_StepCR s None t" unfolding C_Tau_def by simp
  then obtain p where "p \<in> ProcSet" 
    and "Sys_E1 p s t \<or> Sys_E2 p s t \<or> Sys_D1 p s t \<or> Sys_D2 p s t \<or> Sys_D3 p s t"
    by (cases rule: C_StepCR.cases) auto
  then show ?thesis
    using assms(2)
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def 
              Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def 
              program_counter_def Let_def BOT_def
    by (auto split: if_splits)
qed

(* Step 2. *)
lemma C_Tau_Star_preserves_D_phase_P1:
  assumes "C_Tau_Star s t"
      and "program_counter s P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
  shows "program_counter t P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
  using assms
proof (induction rule: C_Tau_Star.induct)
  case refl then show ?case by simp
next
  case (step s1 s2 s3)
  have "program_counter s2 P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using C_Tau_preserves_D_phase_P1[OF step.hyps(1) step.prems] .
  thus ?case using step.IH by simp
qed

lemma hwq_full_e1_P1_suffix_in_D_phase:
  assumes SUFFIX: "C_Path s_before_deq ([Some (mk_obs deq BOT P1 call), None, None, None, None] @ [Some (mk_obs enq A2 P2 ret)]) sk0"
  shows "program_counter sk0 P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
proof -
  (* Step 1. *)
  obtain s_deq_post where P_DEQ: "C_Path s_before_deq [Some (mk_obs deq BOT P1 call), None, None, None, None] s_deq_post"
    and M_RET: "C_Match s_deq_post (Some (mk_obs enq A2 P2 ret)) sk0"
    using C_Path_snocE[OF SUFFIX] by blast

  obtain s1 where M_DEQ: "C_Match s_before_deq (Some (mk_obs deq BOT P1 call)) s1" 
    and P_N4: "C_Path s1 [None, None, None, None] s_deq_post"
    using my_C_Path_ConsE[OF P_DEQ] .
    
  obtain u_deq_pre u_deq_post where "C_Tau_Star s_before_deq u_deq_pre"
    and STEP_DEQ: "C_StepCR u_deq_pre (Some (mk_obs deq BOT P1 call)) u_deq_post"
    and T_DEQ_POST: "C_Tau_Star u_deq_post s1" 
    using my_C_Match_SomeE[OF M_DEQ] .

  (* Step 2.1.1. *)
  have PC_P1_D1: "program_counter u_deq_post P1 = ''D1''"
    using STEP_DEQ by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def Sys_L0_def C_L0_def program_counter_def Let_def split: if_splits)
  hence IN_D_u_post: "program_counter u_deq_post P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}" by simp

  (* Step 3. *)
  have IN_D_s1: "program_counter s1 P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using C_Tau_Star_preserves_D_phase_P1[OF T_DEQ_POST IN_D_u_post] .

  (* Step 4.4. *)
  obtain s2 where M_N1: "C_Match s1 None s2" and P_N3: "C_Path s2 [None, None, None] s_deq_post" using my_C_Path_ConsE[OF P_N4] .
  obtain s3 where M_N2: "C_Match s2 None s3" and P_N2: "C_Path s3 [None, None] s_deq_post" using my_C_Path_ConsE[OF P_N3] .
  obtain s4 where M_N3: "C_Match s3 None s4" and P_N1: "C_Path s4 [None] s_deq_post" using my_C_Path_ConsE[OF P_N2] .
  obtain s5 where M_N4: "C_Match s4 None s5" and P_N0: "C_Path s5 [] s_deq_post" using my_C_Path_ConsE[OF P_N1] .
  have S5_EQ: "s5 = s_deq_post" using P_N0 by (cases rule: C_Path.cases) auto

  have T_N_ALL: "C_Tau_Star s1 s_deq_post"
    using C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N1] 
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N2] 
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N3] my_C_Match_NoneE[OF M_N4]]]] S5_EQ by simp

  have IN_D_deq_post: "program_counter s_deq_post P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using C_Tau_Star_preserves_D_phase_P1[OF T_N_ALL IN_D_s1] .

  (* Step 5.2. *)
  obtain u_ret_pre u_ret_post where T_RET_PRE: "C_Tau_Star s_deq_post u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
    and T_RET_POST: "C_Tau_Star u_ret_post sk0" 
    using my_C_Match_SomeE[OF M_RET] .

  have IN_D_ret_pre: "program_counter u_ret_pre P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using C_Tau_Star_preserves_D_phase_P1[OF T_RET_PRE IN_D_deq_post] .

  have IN_D_ret_post: "program_counter u_ret_post P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
  proof -
    have "program_counter u_ret_post P1 = program_counter u_ret_pre P1"
      using C_StepCR_P2_vis_preserves_P1_PC[OF STEP_RET] by (simp add: mk_obs_def)
    thus ?thesis using IN_D_ret_pre by simp
  qed

  show ?thesis
    using C_Tau_Star_preserves_D_phase_P1[OF T_RET_POST IN_D_ret_post] .
qed

lemma hwq_full_e1_pending_deq_P1:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
      and INV: "system_invariant sk0"
      and X4: "X_var sk0 = 4"
  shows "HasPendingDeq sk0 P1"
proof -
  have SPLIT: "e1_labels = 
      ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
        Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]) @ 
      ([Some (mk_obs deq BOT P1 call), None, None, None, None] @ [Some (mk_obs enq A2 P2 ret)])"
    unfolding e1_labels_def by simp

  obtain s_before_deq where
    SUFFIX:
      "C_Path s_before_deq
        ([Some (mk_obs deq BOT P1 call), None, None, None, None]
          @ [Some (mk_obs enq A2 P2 ret)]) sk0"
    using C_Path_appendE[OF E1FULL[unfolded SPLIT]] by blast

  have DPHASE: "program_counter sk0 P1 \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
    using hwq_full_e1_P1_suffix_in_D_phase[OF SUFFIX] .

  have H12: "hI12_D_Phase_Pending_Deq sk0"
    using INV unfolding system_invariant_def by auto

  show ?thesis
    using H12 DPHASE
    unfolding hI12_D_Phase_Pending_Deq_def
    by blast
qed

(* Bridge 4: P1 local branch state *)


(* ========================================================================= *)
(* Branch 1.1. *)
(* ========================================================================= *)
lemma Tau_preserves_P1_branch_step:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and PCP2: "program_counter s P2 = ''L0''"
      and BR:
        "((Q_arr s 1 = A1) \<and>
           ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
         \<or>
         ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
      and TAU: "C_Tau s s'"
  shows
    "((Q_arr s' 1 = A1) \<and>
       ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
     \<or>
     ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1)"
proof -
  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto

  have pneqP2: "p \<noteq> P2"
  proof
    assume pP2: "p = P2"
    from STEP show False
      using pP2 PCP2
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def Let_def
      by auto
  qed

  have pP1: "p = P1"
    using PIN N2 pneqP2 by auto

  have STEP1: "Sys_D1 P1 s s' \<or> Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
    using STEP pP1 BR
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def program_counter_def
    by auto

  show ?thesis
    using BR
  proof (elim disjE)
    assume SCAN:
      "(Q_arr s 1 = A1) \<and>
       ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1))"
    then have Q1: "Q_arr s 1 = A1"
      and SC: "((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
                (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1))"
      by auto
    from STEP1 show ?thesis
    proof (elim disjE)
      assume D1: "Sys_D1 P1 s s'"
      then have "Q_arr s' 1 = A1"
        using Q1 unfolding Sys_D1_def C_D1_def Q_arr_def by auto
      moreover have "program_counter s' P1 = ''D2''"
        using D1 unfolding Sys_D1_def C_D1_def program_counter_def by auto
      ultimately show ?thesis by auto
    next
      assume D2: "Sys_D2 P1 s s'"
      from SC show ?thesis
      proof (elim disjE)
        assume H: "program_counter s P1 \<in> {''D1'', ''D2''}"
        then have "program_counter s P1 = ''D2''"
          using D2 unfolding Sys_D2_def C_D2_def program_counter_def by auto
        then show ?thesis
          using D2 Q1
          unfolding Sys_D2_def C_D2_def program_counter_def Q_arr_def j_var_def Let_def
          by (auto split: if_splits)
      next
        assume H: "program_counter s P1 = ''D3'' \<and> j_var s P1 = 1"
        with D2 show ?thesis
          unfolding Sys_D2_def C_D2_def program_counter_def by auto
      qed
    next
      assume D3: "Sys_D3 P1 s s'"
      from SC show ?thesis
      proof (elim disjE)
        assume H: "program_counter s P1 \<in> {''D1'', ''D2''}"
        with D3 show ?thesis
          unfolding Sys_D3_def C_D3_def program_counter_def by auto
      next
        assume D3J1: "program_counter s P1 = ''D3'' \<and> j_var s P1 = 1"
        then have PCD3: "program_counter s P1 = ''D3''"
          and J1: "j_var s P1 = 1"
          by auto
        have "Q_arr s' 1 = BOT"
          using D3 Q1 PCD3 J1
          unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def
          by auto
        moreover have "program_counter s' P1 = ''D4''"
          using D3 Q1 PCD3 J1
          unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def
          by (simp add: BOT_def)
        moreover have "x_var s' P1 = A1"
          using D3 Q1 PCD3 J1
          unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def
          by auto
        ultimately show ?thesis by auto
      qed
    qed
  next
    assume LOCK:
      "(Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1"
    from STEP1 LOCK show ?thesis
      unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def
      by auto
  qed
qed

lemma Tau_Star_preserves_P1_branch:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and PCP2: "program_counter s P2 = ''L0''"
      and BR:
        "((Q_arr s 1 = A1) \<and>
           ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
         \<or>
         ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
      and TAUS: "C_Tau_Star s s'"
  shows
    "((Q_arr s' 1 = A1) \<and>
       ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
     \<or>
     ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1)"
  using TAUS INV PCP2 BR
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  from step.prems have INV1: "system_invariant s1"
    and PCP21: "program_counter s1 P2 = ''L0''"
    and BR1:
      "((Q_arr s1 1 = A1) \<and>
         ((program_counter s1 P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s1 P1 = ''D3'' \<and> j_var s1 P1 = 1)))
       \<or>
       ((Q_arr s1 1 = BOT) \<and> program_counter s1 P1 = ''D4'' \<and> x_var s1 P1 = A1)"
    by auto

  have STEP0: "C_StepCR s1 None s2"
    using step.hyps(1) unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s1 s2 \<or> Sys_E2 p s1 s2 \<or> Sys_D1 p s1 s2 \<or> Sys_D2 p s1 s2 \<or> Sys_D3 p s1 s2"
    by (cases rule: C_StepCR.cases) auto

  have pneqP2: "p \<noteq> P2"
  proof
    assume pP2: "p = P2"
    from STEP show False
      using pP2 PCP21
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def Let_def
      by auto
  qed

  have pP1: "p = P1"
    using PIN N2 pneqP2 by auto

  have STEP1: "Sys_D1 P1 s1 s2 \<or> Sys_D2 P1 s1 s2 \<or> Sys_D3 P1 s1 s2"
    using STEP pP1 BR1
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def program_counter_def
    by auto

  have NXT: "Next s1 s2"
    using C_StepCR_into_Next[OF STEP0] .

  have INV2: "system_invariant s2"
    using Sys_Inv_Step[OF INV1 NXT] .

  have PCP22: "program_counter s2 P2 = ''L0''"
    using STEP1 PCP21
    unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
              program_counter_def Let_def
    by (elim disjE) (auto split: if_splits)

  have BR2:
    "((Q_arr s2 1 = A1) \<and>
       ((program_counter s2 P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s2 P1 = ''D3'' \<and> j_var s2 P1 = 1)))
     \<or>
     ((Q_arr s2 1 = BOT) \<and> program_counter s2 P1 = ''D4'' \<and> x_var s2 P1 = A1)"
    using Tau_preserves_P1_branch_step[OF N2 INV1 PCP21 BR1 step.hyps(1)] .

  show ?case
    using step.IH[OF INV2 PCP22 BR2] .
qed


lemma C_StepCR_P2_ret_preserves_P1_branch:
  assumes N2: "N_Procs = 2"
      and STEP: "C_StepCR s (Some (mk_obs enq A2 P2 ret)) s'"
      and BR:
        "((Q_arr s 1 = A1) \<and>
           ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
         \<or>
         ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
  shows "program_counter s' P2 = ''L0'' \<and>
         (((Q_arr s' 1 = A1) \<and>
           ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
          \<or>
          ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1))"
proof -
  from STEP show ?thesis
  proof (cases rule: C_StepCR.cases)
    case (C_Sys_E3_vis p)
    then have pP2: "p = P2"
      unfolding mk_obs_def by auto
    have PC2': "program_counter s' P2 = ''L0''"
      using C_Sys_E3_vis pP2
      unfolding Sys_E3_def C_E3_def program_counter_def Let_def
      by (auto split: if_splits)
    have BR':
      "((Q_arr s' 1 = A1) \<and>
         ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
       \<or>
       ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1)"
      using BR C_Sys_E3_vis pP2
      unfolding Sys_E3_def C_E3_def
                program_counter_def Q_arr_def j_var_def x_var_def Let_def
      by (auto split: if_splits)
    from PC2' BR' show ?thesis by blast
  qed (auto simp: mk_obs_def)
qed



(* ========================================================================= *)
(* Bridge 4 refactor: keep only the current route                            *)
(*                                                                           *)
(* Suggested cleanup before inserting this proof block: *)
(* - hwq_p2_e1_pipeline_preserves_q1 (, v_var = A2) *)
(* - hwq_a2_call_tau_preserves_q1 (/ XNZ) *)
(* - hwq_a3_call_ret_preserves_q1 (, P2SAFE) *)
(* - hwq_full_e1_pre_deq_p2_weak_shape (not kept in the current block) *)
(* ========================================================================= *)

lemma hwq_p1_e1_to_e3_pipeline:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and PC1_S: "program_counter s P1 = ''E1''"
      and PC2_S: "program_counter s P2 = ''L0''"
      and X_S:   "X_var s = 1"
      and V1_S:  "v_var s P1 = A1"
  shows "program_counter t P2 = ''L0'' \<and>
         (program_counter t P1 = ''E3'' \<longrightarrow> Q_arr t 1 = A1)"
proof -
  have INIT_INV:
    "program_counter s P2 = ''L0'' \<and>
     program_counter s P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s P1 = ''E1'' \<longrightarrow> X_var s = 1 \<and> v_var s P1 = A1) \<and>
     (program_counter s P1 = ''E2'' \<longrightarrow> i_var s P1 = 1 \<and> X_var s = 2 \<and> v_var s P1 = A1) \<and>
     (program_counter s P1 = ''E3'' \<longrightarrow> Q_arr s 1 = A1)"
    using PC1_S PC2_S X_S V1_S by auto

  have MAIN:
    "program_counter t P2 = ''L0'' \<and>
     program_counter t P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter t P1 = ''E1'' \<longrightarrow> X_var t = 1 \<and> v_var t P1 = A1) \<and>
     (program_counter t P1 = ''E2'' \<longrightarrow> i_var t P1 = 1 \<and> X_var t = 2 \<and> v_var t P1 = A1) \<and>
     (program_counter t P1 = ''E3'' \<longrightarrow> Q_arr t 1 = A1)"
    using TAUS INIT_INV
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    from step.prems obtain
        P2L0: "program_counter s1 P2 = ''L0''"
      and PC1SET: "program_counter s1 P1 \<in> {''E1'', ''E2'', ''E3''}"
      and E1INV: "(program_counter s1 P1 = ''E1'' \<longrightarrow> X_var s1 = 1 \<and> v_var s1 P1 = A1)"
      and E2INV: "(program_counter s1 P1 = ''E2'' \<longrightarrow> i_var s1 P1 = 1 \<and> X_var s1 = 2 \<and> v_var s1 P1 = A1)"
      and E3INV: "(program_counter s1 P1 = ''E3'' \<longrightarrow> Q_arr s1 1 = A1)"
      by blast

    have STEP0: "C_StepCR s1 None s2"
      using step.hyps(1) unfolding C_Tau_def by simp

    from STEP0 obtain p where PIN: "p \<in> ProcSet"
      and STEP:
        "Sys_E1 p s1 s2 \<or> Sys_E2 p s1 s2 \<or> Sys_D1 p s1 s2 \<or> Sys_D2 p s1 s2 \<or> Sys_D3 p s1 s2"
      by (cases rule: C_StepCR.cases) auto

    have p_not_P2: "p \<noteq> P2"
    proof
      assume pP2: "p = P2"
      from STEP show False
        using pP2 P2L0
        unfolding Sys_E1_def C_E1_def
                  Sys_E2_def C_E2_def
                  Sys_D1_def C_D1_def
                  Sys_D2_def C_D2_def
                  Sys_D3_def C_D3_def
                  program_counter_def T_D2_EnterLoop_def Let_def
        by auto
    qed

    have pP1: "p = P1"
      using PIN N2 p_not_P2 by auto

    have MID:
      "program_counter s2 P2 = ''L0'' \<and>
       program_counter s2 P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
       (program_counter s2 P1 = ''E1'' \<longrightarrow> X_var s2 = 1 \<and> v_var s2 P1 = A1) \<and>
       (program_counter s2 P1 = ''E2'' \<longrightarrow> i_var s2 P1 = 1 \<and> X_var s2 = 2 \<and> v_var s2 P1 = A1) \<and>
       (program_counter s2 P1 = ''E3'' \<longrightarrow> Q_arr s2 1 = A1)"
    proof -
      from STEP show ?thesis
      proof (elim disjE)
        assume H: "Sys_E1 p s1 s2"
        have PCE1: "program_counter s1 P1 = ''E1''"
          using H pP1
          unfolding Sys_E1_def C_E1_def program_counter_def Let_def
          by auto
        have X1: "X_var s1 = 1" and V1: "v_var s1 P1 = A1"
          using E1INV PCE1 by auto
        show ?thesis
          using H pP1 P2L0 X1 V1
          unfolding Sys_E1_def C_E1_def
                    program_counter_def X_var_def v_var_def i_var_def Q_arr_def Let_def
          by (auto split: if_splits)
      next
        assume H: "Sys_E2 p s1 s2"
        have PCE2: "program_counter s1 P1 = ''E2''"
          using H pP1
          unfolding Sys_E2_def C_E2_def program_counter_def Let_def
          by auto
        have I1: "i_var s1 P1 = 1" and X2: "X_var s1 = 2" and V1: "v_var s1 P1 = A1"
          using E2INV PCE2 by auto
        show ?thesis
          using H pP1 P2L0 I1 X2 V1
          unfolding Sys_E2_def C_E2_def
                    program_counter_def X_var_def v_var_def i_var_def Q_arr_def Let_def
          by (auto split: if_splits)
      next
        assume H: "Sys_D1 p s1 s2"
        then show ?thesis
          using pP1 PC1SET
          unfolding Sys_D1_def C_D1_def program_counter_def Let_def
          by auto
      next
        assume H: "Sys_D2 p s1 s2"
        then show ?thesis
          using pP1 PC1SET
          unfolding Sys_D2_def C_D2_def program_counter_def T_D2_EnterLoop_def Let_def
          by auto
      next
        assume H: "Sys_D3 p s1 s2"
        then show ?thesis
          using pP1 PC1SET
          unfolding Sys_D3_def C_D3_def program_counter_def Let_def
          by auto
      qed
    qed

    show ?case
      using step.IH[OF MID] .
  qed

  from MAIN show ?thesis
    by blast
qed


lemma C_Tau_preserves_P2_L0:
  assumes N2: "N_Procs = 2"
      and TAU: "C_Tau s t"
      and PC:  "program_counter s P2 = ''L0''"
  shows "program_counter t P2 = ''L0''"
proof -
  have STEP0: "C_StepCR s None t"
    using TAU unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP: "Sys_E1 p s t \<or> Sys_E2 p s t \<or> Sys_D1 p s t \<or> Sys_D2 p s t \<or> Sys_D3 p s t"
    by (cases rule: C_StepCR.cases) auto

  have p_not_P2: "p \<noteq> P2"
  proof
    assume pP2: "p = P2"
    from STEP show False
      using pP2 PC
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def T_D2_EnterLoop_def Let_def
      by auto
  qed

  have pP1: "p = P1"
    using PIN N2 p_not_P2 by auto

  show ?thesis
    using STEP pP1 PC
    unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
              Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
              program_counter_def T_D2_EnterLoop_def Let_def
    by (elim disjE) (auto split: if_splits)
qed


lemma C_Tau_Star_preserves_P2_L0:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and PC:   "program_counter s P2 = ''L0''"
  shows "program_counter t P2 = ''L0''"
  using TAUS PC
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have PC2: "program_counter s2 P2 = ''L0''"
    using C_Tau_preserves_P2_L0[OF N2 step.hyps(1) step.prems] .
  show ?case
    using step.IH[OF PC2] .
qed


lemma hwq_a1_segment_q1_shape:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and P_A1: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
  shows "program_counter s_a1_ret P1 = ''L0'' \<and>
         program_counter s_a1_ret P2 = ''L0'' \<and>
         Q_arr s_a1_ret 1 = A1"
proof -
  have PC1_0: "program_counter s0 P1 = ''L0''"
    using INIT unfolding Init_def program_counter_def by auto
  have PC2_0: "program_counter s0 P2 = ''L0''"
    using INIT unfolding Init_def program_counter_def by auto
  have X0: "X_var s0 = 1"
    using INIT unfolding Init_def X_var_def by auto
  have V0: "V_var s0 = 1"
    using INIT unfolding Init_def V_var_def by auto

  obtain s1 where
      M_CALL: "C_Match s0 (Some (mk_obs enq A1 P1 call)) s1"
    and P_REST: "C_Path s1 [None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    using my_C_Path_ConsE[OF P_A1] .

  obtain u_call_pre u_call_post where
      TAU_PRE: "C_Tau_Star s0 u_call_pre"
    and STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A1 P1 call)) u_call_post"
    and TAU_POST: "C_Tau_Star u_call_post s1"
    using my_C_Match_SomeE[OF M_CALL] .

  have U_PRE_EQ: "u_call_pre = s0"
    using C_Tau_Star_eq_if_P1P2_L0[OF N2 PC1_0 PC2_0 TAU_PRE] .

  have CALL_POST:
    "program_counter u_call_post P1 = ''E1'' \<and>
     program_counter u_call_post P2 = ''L0'' \<and>
     X_var u_call_post = 1 \<and>
     v_var u_call_post P1 = A1"
  proof -
    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      have P2_ne_P1: "P2 \<noteq> P1"
        by simp
      from C_Sys_L0_enq_vis pP1 U_PRE_EQ X0 V0 PC2_0 show ?thesis
        unfolding Sys_L0_def C_L0_def
                  program_counter_def X_var_def v_var_def V_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  obtain s2 where
      M_N1: "C_Match s1 None s2"
    and P_N2: "C_Path s2 [None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    using my_C_Path_ConsE[OF P_REST] .

  obtain s3 where
      M_N2: "C_Match s2 None s3"
    and P_RET: "C_Path s3 [Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    using my_C_Path_ConsE[OF P_N2] .

  obtain s4 where
      M_RET: "C_Match s3 (Some (mk_obs enq A1 P1 ret)) s4"
    and P_EMP: "C_Path s4 [] s_a1_ret"
    using my_C_Path_ConsE[OF P_RET] .

  have S4_EQ: "s4 = s_a1_ret"
    using P_EMP by (cases rule: C_Path.cases) auto

  have T1: "C_Tau_Star s1 s2"
    using my_C_Match_NoneE[OF M_N1] .
  have T2: "C_Tau_Star s2 s3"
    using my_C_Match_NoneE[OF M_N2] .
  have T12: "C_Tau_Star s1 s3"
    using C_Tau_Star_trans[OF T1 T2] .
  have T_PIPE: "C_Tau_Star u_call_post s3"
    using C_Tau_Star_trans[OF TAU_POST T12] .

  obtain u_ret_pre u_ret_post where
      TAU_RET_PRE: "C_Tau_Star s3 u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A1 P1 ret)) u_ret_post"
    and TAU_RET_POST: "C_Tau_Star u_ret_post s_a1_ret"
    using my_C_Match_SomeE[OF M_RET] S4_EQ by blast

  have PC_P1_RET_PRE: "program_counter u_ret_pre P1 = ''E3''"
  proof -
    from STEP_RET show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP1 show ?thesis
        unfolding Sys_E3_def C_E3_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have T_TO_RET: "C_Tau_Star u_call_post u_ret_pre"
    using C_Tau_Star_trans[OF T_PIPE TAU_RET_PRE] .

  have PIPE_ALL:
    "program_counter u_ret_pre P2 = ''L0'' \<and>
     (program_counter u_ret_pre P1 = ''E3'' \<longrightarrow> Q_arr u_ret_pre 1 = A1)"
    using hwq_p1_e1_to_e3_pipeline[OF N2 T_TO_RET]
          CALL_POST
    by auto

  have P2_PIPE_L0: "program_counter u_ret_pre P2 = ''L0''"
    using PIPE_ALL by auto

  have PIPE:
    "(program_counter u_ret_pre P1 = ''E3'' \<longrightarrow> Q_arr u_ret_pre 1 = A1)"
    using PIPE_ALL by auto

  have Q1_ret_pre: "Q_arr u_ret_pre 1 = A1"
    using PIPE PC_P1_RET_PRE by auto

  have POST_RET:
    "program_counter u_ret_post P1 = ''L0'' \<and>
     program_counter u_ret_post P2 = ''L0'' \<and>
     Q_arr u_ret_post 1 = A1"
  proof -
    from STEP_RET show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP1 P2_PIPE_L0 Q1_ret_pre show ?thesis
        unfolding Sys_E3_def C_E3_def
                  program_counter_def Q_arr_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have END_EQ_parts:
    "fst u_ret_post = fst s_a1_ret \<and> snd u_ret_post = snd s_a1_ret"
    using C_Tau_Star_eq_if_P1P2_L0[OF N2]
          POST_RET TAU_RET_POST
    by blast

  have END_EQ: "u_ret_post = s_a1_ret"
    using END_EQ_parts
    by (cases u_ret_post, cases s_a1_ret) auto

  from POST_RET END_EQ show ?thesis
    by simp
qed


lemma hwq_a1_segment_XNZ:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and P_A1: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
  shows "X_var s_a1_ret \<noteq> 1"
proof
  assume X1: "X_var s_a1_ret = 1"

  have SNAP:
    "program_counter s_a1_ret P1 = ''L0'' \<and>
     program_counter s_a1_ret P2 = ''L0'' \<and>
     Q_arr s_a1_ret 1 = A1"
    using hwq_a1_segment_q1_shape[OF N2 INIT P_A1] .

  have RS: "Reachable_Sys s_a1_ret"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] P_A1] .

  have INV: "system_invariant s_a1_ret"
    using Reachable_Sys_system_invariant[OF RS] .

  have sI2: "sI2_X_var_Upper_Bound s_a1_ret"
    using INV unfolding system_invariant_def by auto

  have Q1_BOT: "Q_arr s_a1_ret 1 = BOT"
    using sI2 X1
    unfolding sI2_X_var_Upper_Bound_def
    by auto

  from SNAP Q1_BOT show False
    by (simp add: BOT_def)
qed


lemma hwq_p2_e1_pipeline_preserves_q1_weak:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and P1L0: "program_counter s P1 = ''L0''"
      and P2E1: "program_counter s P2 = ''E1''"
      and Q1:   "Q_arr s 1 = A1"
      and XNZ:  "X_var s \<noteq> 1"
  shows "program_counter t P1 = ''L0'' \<and>
         program_counter t P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         Q_arr t 1 = A1 \<and>
         X_var t \<noteq> 1 \<and>
         (program_counter t P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P2 \<noteq> 1)"
proof -
  have INIT_INV:
    "program_counter s P1 = ''L0'' \<and>
     program_counter s P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s 1 = A1 \<and>
     X_var s \<noteq> 1 \<and>
     (program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"
    using P1L0 P2E1 Q1 XNZ by auto

  have MAIN:
    "program_counter t P1 = ''L0'' \<and>
     program_counter t P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr t 1 = A1 \<and>
     X_var t \<noteq> 1 \<and>
     (program_counter t P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P2 \<noteq> 1)"
    using TAUS INIT_INV
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    from step.prems obtain
        P1L0_1: "program_counter s1 P1 = ''L0''"
      and P2SET_1: "program_counter s1 P2 \<in> {''E1'', ''E2'', ''E3''}"
      and Q1_1: "Q_arr s1 1 = A1"
      and XNZ_1: "X_var s1 \<noteq> 1"
      and I2NZ_1: "(program_counter s1 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s1 P2 \<noteq> 1)"
      by blast

    have STEP0: "C_StepCR s1 None s2"
      using step.hyps(1) unfolding C_Tau_def by simp

    from STEP0 obtain p where PIN: "p \<in> ProcSet"
      and STEP:
        "Sys_E1 p s1 s2 \<or> Sys_E2 p s1 s2 \<or> Sys_D1 p s1 s2 \<or> Sys_D2 p s1 s2 \<or> Sys_D3 p s1 s2"
      by (cases rule: C_StepCR.cases) auto

    have p_not_P1: "p \<noteq> P1"
    proof
      assume pP1: "p = P1"
      from STEP show False
        using pP1 P1L0_1
        unfolding Sys_E1_def C_E1_def
                  Sys_E2_def C_E2_def
                  Sys_D1_def C_D1_def
                  Sys_D2_def C_D2_def
                  Sys_D3_def C_D3_def
                  program_counter_def T_D2_EnterLoop_def Let_def
        by auto
    qed

    have pP2: "p = P2"
      using PIN N2 p_not_P1 by auto

    have MID:
      "program_counter s2 P1 = ''L0'' \<and>
       program_counter s2 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
       Q_arr s2 1 = A1 \<and>
       X_var s2 \<noteq> 1 \<and>
       (program_counter s2 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s2 P2 \<noteq> 1)"
    proof -
      from STEP show ?thesis
      proof (elim disjE)
        assume H: "Sys_E1 p s1 s2"
        have PCE1: "program_counter s1 P2 = ''E1''"
          using H pP2
          unfolding Sys_E1_def C_E1_def program_counter_def Let_def
          by auto
        show ?thesis
          using H pP2 P1L0_1 Q1_1 XNZ_1
          unfolding Sys_E1_def C_E1_def
                    program_counter_def X_var_def i_var_def Q_arr_def Let_def
          by (simp add: Model.X_var_def Val_def 
               p_not_P1 sI2_X_var_Upper_Bound_def
              system_invariant_def)
      next
        assume H: "Sys_E2 p s1 s2"
        have PCE2: "program_counter s1 P2 = ''E2''"
          using H pP2
          unfolding Sys_E2_def C_E2_def program_counter_def Let_def
          by auto
        have INZ: "i_var s1 P2 \<noteq> 1"
          using I2NZ_1 PCE2 by auto
        show ?thesis
          using H pP2 P1L0_1 Q1_1 XNZ_1 INZ
          unfolding Sys_E2_def C_E2_def
                    program_counter_def X_var_def i_var_def Q_arr_def Let_def
          by (auto split: if_splits)
      next
        assume H: "Sys_D1 p s1 s2"
        then show ?thesis
          using pP2 P2SET_1
          unfolding Sys_D1_def C_D1_def program_counter_def Let_def
          by auto
      next
        assume H: "Sys_D2 p s1 s2"
        then show ?thesis
          using pP2 P2SET_1
          unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def program_counter_def Let_def
          by auto
      next
        assume H: "Sys_D3 p s1 s2"
        then show ?thesis
          using pP2 P2SET_1
          unfolding Sys_D3_def C_D3_def program_counter_def Let_def
          by auto
      qed
    qed

    show ?case
      using step.IH[OF MID] .
  qed

  from MAIN show ?thesis
    by blast
qed


lemma hwq_a2_call_tau_preserves_q1:
  assumes N2: "N_Procs = 2"
      and PATH: "C_Path s_a1_ret [Some (mk_obs enq A2 P2 call), None] s_mid"
      and SNAP: "program_counter s_a1_ret P1 = ''L0'' \<and>
                 program_counter s_a1_ret P2 = ''L0'' \<and>
                 Q_arr s_a1_ret 1 = A1"
      and XNZ:  "X_var s_a1_ret \<noteq> 1"
  shows "program_counter s_mid P1 = ''L0'' \<and>
         program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         Q_arr s_mid 1 = A1 \<and>
         X_var s_mid \<noteq> 1 \<and>
         (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
proof -
  from SNAP have PC1_0: "program_counter s_a1_ret P1 = ''L0''"
    and PC2_0: "program_counter s_a1_ret P2 = ''L0''"
    and Q1_0:  "Q_arr s_a1_ret 1 = A1"
    by auto

  obtain s1 where
      M_CALL: "C_Match s_a1_ret (Some (mk_obs enq A2 P2 call)) s1"
    and P_NONE: "C_Path s1 [None] s_mid"
    using my_C_Path_ConsE[OF PATH] .

  obtain u_pre u_post where
      TAU_PRE: "C_Tau_Star s_a1_ret u_pre"
    and STEP_CALL: "C_StepCR u_pre (Some (mk_obs enq A2 P2 call)) u_post"
    and TAU_POST: "C_Tau_Star u_post s1"
    using my_C_Match_SomeE[OF M_CALL] .

  have U_PRE_EQ: "u_pre = s_a1_ret"
    using C_Tau_Star_eq_if_P1P2_L0[OF N2 PC1_0 PC2_0 TAU_PRE] .

  have CALL_POST:
    "program_counter u_post P1 = ''L0'' \<and>
     program_counter u_post P2 = ''E1'' \<and>
     Q_arr u_post 1 = A1 \<and>
     X_var u_post \<noteq> 1"
  proof -
    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have pP2: "p = P2"
        unfolding mk_obs_def by auto
      from C_Sys_L0_enq_vis pP2 U_PRE_EQ PC1_0 PC2_0 Q1_0 XNZ show ?thesis
        unfolding Sys_L0_def C_L0_def
                  program_counter_def Q_arr_def X_var_def V_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  obtain s2 where
      M_NONE: "C_Match s1 None s2"
    and P_EMP: "C_Path s2 [] s_mid"
    using my_C_Path_ConsE[OF P_NONE] .

  have S2_EQ: "s2 = s_mid"
    using P_EMP by (cases rule: C_Path.cases) auto

  have T_NONE: "C_Tau_Star s1 s_mid"
    using my_C_Match_NoneE[OF M_NONE] S2_EQ by simp

  have T_TOTAL: "C_Tau_Star u_post s_mid"
    using C_Tau_Star_trans[OF TAU_POST T_NONE] .

  show ?thesis
    using hwq_p2_e1_pipeline_preserves_q1_weak[OF N2 T_TOTAL]
          CALL_POST
    by auto
qed


lemma hwq_two_pending_enq_tau_preserves_q1:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and P1SAFE:
        "program_counter s P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s P1 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
         (program_counter s P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P1 \<noteq> 1)"
      and P2SAFE:
        "program_counter s P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s P2 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
         (program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"
      and Q1: "Q_arr s 1 = A1"
  shows "Q_arr t 1 = A1 \<and>
         program_counter t P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter t P1 = ''E1'' \<longrightarrow> X_var t \<noteq> 1) \<and>
         (program_counter t P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P1 \<noteq> 1) \<and>
         program_counter t P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter t P2 = ''E1'' \<longrightarrow> X_var t \<noteq> 1) \<and>
         (program_counter t P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P2 \<noteq> 1)"
proof -
  have INIT_INV:
    "Q_arr s 1 = A1 \<and>
     program_counter s P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s P1 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
     (program_counter s P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P1 \<noteq> 1) \<and>
     program_counter s P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s P2 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
     (program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"
    using P1SAFE P2SAFE Q1 by auto

  have MAIN:
    "Q_arr t 1 = A1 \<and>
     program_counter t P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter t P1 = ''E1'' \<longrightarrow> X_var t \<noteq> 1) \<and>
     (program_counter t P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P1 \<noteq> 1) \<and>
     program_counter t P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter t P2 = ''E1'' \<longrightarrow> X_var t \<noteq> 1) \<and>
     (program_counter t P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P2 \<noteq> 1)"
    using TAUS INIT_INV
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    from step.prems obtain
        Q1_1: "Q_arr s1 1 = A1"
      and P1SET_1: "program_counter s1 P1 \<in> {''E1'', ''E2'', ''E3''}"
      and P1E1SAFE_1: "(program_counter s1 P1 = ''E1'' \<longrightarrow> X_var s1 \<noteq> 1)"
      and P1I_SAFE_1: "(program_counter s1 P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s1 P1 \<noteq> 1)"
      and P2SET_1: "program_counter s1 P2 \<in> {''E1'', ''E2'', ''E3''}"
      and P2E1SAFE_1: "(program_counter s1 P2 = ''E1'' \<longrightarrow> X_var s1 \<noteq> 1)"
      and P2I_SAFE_1: "(program_counter s1 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s1 P2 \<noteq> 1)"
      by blast

    have STEP0: "C_StepCR s1 None s2"
      using step.hyps(1) unfolding C_Tau_def by simp

    from STEP0 obtain p where PIN: "p \<in> ProcSet"
      and STEP:
        "Sys_E1 p s1 s2 \<or> Sys_E2 p s1 s2 \<or> Sys_D1 p s1 s2 \<or> Sys_D2 p s1 s2 \<or> Sys_D3 p s1 s2"
      by (cases rule: C_StepCR.cases) auto

    have p_cases: "p = P1 \<or> p = P2"
      using PIN N2 by auto

    have MID:
      "Q_arr s2 1 = A1 \<and>
       program_counter s2 P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
       (program_counter s2 P1 = ''E1'' \<longrightarrow> X_var s2 \<noteq> 1) \<and>
       (program_counter s2 P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s2 P1 \<noteq> 1) \<and>
       program_counter s2 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
       (program_counter s2 P2 = ''E1'' \<longrightarrow> X_var s2 \<noteq> 1) \<and>
       (program_counter s2 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s2 P2 \<noteq> 1)"
    proof -
      from p_cases show ?thesis
      proof
        assume pP1: "p = P1"
        from STEP show ?thesis
        proof (elim disjE)
          assume H: "Sys_E1 p s1 s2"
          have P1E1: "program_counter s1 P1 = ''E1''"
            using H pP1
            unfolding Sys_E1_def C_E1_def program_counter_def Let_def
            by auto
          have XNZ1: "X_var s1 \<noteq> 1"
            using P1E1SAFE_1 P1E1 by auto
          have XPOS1: "0 < X_var s1"
            using H
            unfolding Sys_E1_def system_invariant_def hI4_X_var_Lin_Sync_def
            by auto
          show ?thesis
            using H pP1 Q1_1 P2SET_1 P2E1SAFE_1 P2I_SAFE_1 XNZ1 XPOS1
            unfolding Sys_E1_def C_E1_def
                      program_counter_def X_var_def i_var_def Q_arr_def Let_def
            by (auto split: if_splits)
        next
          assume H: "Sys_E2 p s1 s2"
          have P1E2: "program_counter s1 P1 = ''E2''"
            using H pP1
            unfolding Sys_E2_def C_E2_def program_counter_def Let_def
            by auto
          have I1NZ: "i_var s1 P1 \<noteq> 1"
            using P1I_SAFE_1 P1E2 by auto
          show ?thesis
            using H pP1 Q1_1 P2SET_1 P2E1SAFE_1 P2I_SAFE_1 I1NZ
            unfolding Sys_E2_def C_E2_def
                      program_counter_def X_var_def i_var_def Q_arr_def Let_def
            by (auto split: if_splits)
        next
          assume H: "Sys_D1 p s1 s2"
          then show ?thesis
            using pP1 P1SET_1
            unfolding Sys_D1_def C_D1_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_D2 p s1 s2"
          then show ?thesis
            using pP1 P1SET_1
            unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_D3 p s1 s2"
          then show ?thesis
            using pP1 P1SET_1
            unfolding Sys_D3_def C_D3_def program_counter_def Let_def
            by auto
        qed
      next
        assume pP2: "p = P2"
        from STEP show ?thesis
        proof (elim disjE)
          assume H: "Sys_E1 p s1 s2"
          have P2E1: "program_counter s1 P2 = ''E1''"
            using H pP2
            unfolding Sys_E1_def C_E1_def program_counter_def Let_def
            by auto
          have XNZ1: "X_var s1 \<noteq> 1"
            using P2E1SAFE_1 P2E1 by auto
          have XPOS1: "0 < X_var s1"
            using H
            unfolding Sys_E1_def system_invariant_def hI4_X_var_Lin_Sync_def
            by auto
          show ?thesis
            using H pP2 Q1_1 P1SET_1 P1E1SAFE_1 P1I_SAFE_1 XNZ1 XPOS1
            unfolding Sys_E1_def C_E1_def
                      program_counter_def X_var_def i_var_def Q_arr_def Let_def
            by (auto split: if_splits)
        next
          assume H: "Sys_E2 p s1 s2"
          have P2E2: "program_counter s1 P2 = ''E2''"
            using H pP2
            unfolding Sys_E2_def C_E2_def program_counter_def Let_def
            by auto
          have I2NZ: "i_var s1 P2 \<noteq> 1"
            using P2I_SAFE_1 P2E2 by auto
          show ?thesis
            using H pP2 Q1_1 P1SET_1 P1E1SAFE_1 P1I_SAFE_1 I2NZ
            unfolding Sys_E2_def C_E2_def
                      program_counter_def X_var_def i_var_def Q_arr_def Let_def
            by (auto split: if_splits)
        next
          assume H: "Sys_D1 p s1 s2"
          then show ?thesis
            using pP2 P2SET_1
            unfolding Sys_D1_def C_D1_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_D2 p s1 s2"
          then show ?thesis
            using pP2 P2SET_1
            unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_D3 p s1 s2"
          then show ?thesis
            using pP2 P2SET_1
            unfolding Sys_D3_def C_D3_def program_counter_def Let_def
            by auto
        qed
      qed
    qed

    show ?case
      using step.IH[OF MID] .
  qed

  from MAIN show ?thesis
    by blast
qed

lemma hwq_p2_pending_tau_preserves_q1_weak:
  assumes N2: "N_Procs = 2"
      and TAUS: "C_Tau_Star s t"
      and P1L0: "program_counter s P1 = ''L0''"
      and P2SET: "program_counter s P2 \<in> {''E1'', ''E2'', ''E3''}"
      and P2E1SAFE: "(program_counter s P2 = ''E1'' \<longrightarrow> X_var s \<noteq> 1)"
      and P2ISAFE: "(program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"
      and Q1: "Q_arr s 1 = A1"
  shows "program_counter t P1 = ''L0'' \<and>
         program_counter t P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         Q_arr t 1 = A1 \<and>
         (program_counter t P2 = ''E1'' \<longrightarrow> X_var t \<noteq> 1) \<and>
         (program_counter t P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P2 \<noteq> 1)"
proof -
  have INIT_INV:
    "program_counter s P1 = ''L0'' \<and>
     program_counter s P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s 1 = A1 \<and>
     (program_counter s P2 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
     (program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"
    using P1L0 P2SET Q1 P2E1SAFE P2ISAFE by auto

  have MAIN:
    "program_counter t P1 = ''L0'' \<and>
     program_counter t P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr t 1 = A1 \<and>
     (program_counter t P2 = ''E1'' \<longrightarrow> X_var t \<noteq> 1) \<and>
     (program_counter t P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var t P2 \<noteq> 1)"
    using TAUS INIT_INV
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    from step.prems obtain
        P1L0_1: "program_counter s1 P1 = ''L0''"
      and P2SET_1: "program_counter s1 P2 \<in> {''E1'', ''E2'', ''E3''}"
      and Q1_1: "Q_arr s1 1 = A1"
      and P2E1SAFE_1: "(program_counter s1 P2 = ''E1'' \<longrightarrow> X_var s1 \<noteq> 1)"
      and P2ISAFE_1: "(program_counter s1 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s1 P2 \<noteq> 1)"
      by blast

    have STEP0: "C_StepCR s1 None s2"
      using step.hyps(1) unfolding C_Tau_def by simp

    from STEP0 obtain p where PIN: "p \<in> ProcSet"
      and STEP:
        "Sys_E1 p s1 s2 \<or> Sys_E2 p s1 s2 \<or> Sys_D1 p s1 s2 \<or> Sys_D2 p s1 s2 \<or> Sys_D3 p s1 s2"
      by (cases rule: C_StepCR.cases) auto

    have p_not_P1: "p \<noteq> P1"
    proof
      assume pP1: "p = P1"
      from STEP show False
        using pP1 P1L0_1
        unfolding Sys_E1_def C_E1_def
                  Sys_E2_def C_E2_def
                  Sys_D1_def C_D1_def
                  Sys_D2_def C_D2_def
                  Sys_D3_def C_D3_def
                  program_counter_def T_D2_EnterLoop_def Let_def
        by auto
    qed

    have pP2: "p = P2"
      using PIN N2 p_not_P1 by auto

    have MID:
      "program_counter s2 P1 = ''L0'' \<and>
       program_counter s2 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
       Q_arr s2 1 = A1 \<and>
       (program_counter s2 P2 = ''E1'' \<longrightarrow> X_var s2 \<noteq> 1) \<and>
       (program_counter s2 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s2 P2 \<noteq> 1)"
    proof -
      from STEP show ?thesis
      proof (elim disjE)
        assume H: "Sys_E1 p s1 s2"
        have P2E1: "program_counter s1 P2 = ''E1''"
          using H pP2
          unfolding Sys_E1_def C_E1_def program_counter_def Let_def
          by auto
        have XNZ1: "X_var s1 \<noteq> 1"
          using P2E1SAFE_1 P2E1 by auto
        show ?thesis
          using H pP2 P1L0_1 Q1_1 XNZ1
          unfolding Sys_E1_def C_E1_def
                    program_counter_def X_var_def i_var_def Q_arr_def Let_def
          by (auto split: if_splits)
      next
        assume H: "Sys_E2 p s1 s2"
        have P2E2: "program_counter s1 P2 = ''E2''"
          using H pP2
          unfolding Sys_E2_def C_E2_def program_counter_def Let_def
          by auto
        have I2NZ: "i_var s1 P2 \<noteq> 1"
          using P2ISAFE_1 P2E2 by auto
        show ?thesis
          using H pP2 P1L0_1 Q1_1 I2NZ
          unfolding Sys_E2_def C_E2_def
                    program_counter_def X_var_def i_var_def Q_arr_def Let_def
          by (auto split: if_splits)
      next
        assume H: "Sys_D1 p s1 s2"
        then show ?thesis
          using pP2 P2SET_1
          unfolding Sys_D1_def C_D1_def program_counter_def Let_def
          by auto
      next
        assume H: "Sys_D2 p s1 s2"
        then show ?thesis
          using pP2 P2SET_1
          unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def program_counter_def Let_def
          by auto
      next
        assume H: "Sys_D3 p s1 s2"
        then show ?thesis
          using pP2 P2SET_1
          unfolding Sys_D3_def C_D3_def program_counter_def Let_def
          by auto
      qed
    qed

    show ?case
      using step.IH[OF MID] .
  qed

  from MAIN show ?thesis
    by blast
qed

lemma hwq_a3_call_ret_preserves_p2_safe_shape:
  assumes N2: "N_Procs = 2"
      and PATH: "C_Path s_mid
        [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]
        s_before_deq"
      and SNAP: "program_counter s_mid P1 = ''L0'' \<and>
                 Q_arr s_mid 1 = A1 \<and>
                 X_var s_mid \<noteq> 1"
      and P2SAFE: "program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
                   (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
  shows "Q_arr s_before_deq 1 = A1 \<and>
         program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1) \<and>
         (program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1)"
proof -
  from SNAP have PC1_0: "program_counter s_mid P1 = ''L0''"
    and Q1_0: "Q_arr s_mid 1 = A1"
    and XNZ_0: "X_var s_mid \<noteq> 1"
    by auto

  from P2SAFE have P2SET_0: "program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''}"
    and I2NZ_0: "(program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    by auto

  obtain s1 where
      M_CALL: "C_Match s_mid (Some (mk_obs enq A3 P1 call)) s1"
    and P_REST1: "C_Path s1 [None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF PATH] .

  obtain u_call_pre u_call_post where
      TAU_PRE: "C_Tau_Star s_mid u_call_pre"
    and STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A3 P1 call)) u_call_post"
    and TAU_POST: "C_Tau_Star u_call_post s1"
    using my_C_Match_SomeE[OF M_CALL] .

  have PRE_SAFE:
    "program_counter u_call_pre P1 = ''L0'' \<and>
     program_counter u_call_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr u_call_pre 1 = A1 \<and>
     (program_counter u_call_pre P2 = ''E1'' \<longrightarrow> X_var u_call_pre \<noteq> 1) \<and>
     (program_counter u_call_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_pre P2 \<noteq> 1)"
    using hwq_p2_pending_tau_preserves_q1_weak[OF N2 TAU_PRE PC1_0 P2SET_0 _ I2NZ_0 Q1_0]
          XNZ_0
    by auto

  have CALL_SAFE:
    "program_counter u_call_post P1 = ''E1'' \<and>
     (program_counter u_call_post P1 = ''E1'' \<longrightarrow> X_var u_call_post \<noteq> 1) \<and>
     (program_counter u_call_post P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_post P1 \<noteq> 1) \<and>
     program_counter u_call_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_call_post P2 = ''E1'' \<longrightarrow> X_var u_call_post \<noteq> 1) \<and>
     (program_counter u_call_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_post P2 \<noteq> 1) \<and>
     Q_arr u_call_post 1 = A1"
  proof -
    from PRE_SAFE obtain
        PC1_PRE: "program_counter u_call_pre P1 = ''L0''"
      and P2SET_PRE: "program_counter u_call_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and Q1_PRE: "Q_arr u_call_pre 1 = A1"
      and P2E1SAFE_PRE: "(program_counter u_call_pre P2 = ''E1'' \<longrightarrow> X_var u_call_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_call_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_pre P2 \<noteq> 1)"
      by blast

    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto

      have INV_PRE: "system_invariant u_call_pre"
        using C_Sys_L0_enq_vis
        using Sys_L0_def by blast

      have XNZ_PRE: "X_var u_call_pre \<noteq> 1"
      proof
        assume X1: "X_var u_call_pre = 1"
        have S2: "sI2_X_var_Upper_Bound u_call_pre"
          using INV_PRE unfolding system_invariant_def by auto
        have QBOT: "Q_arr u_call_pre 1 = BOT"
          using S2 X1
          unfolding sI2_X_var_Upper_Bound_def
          by auto
        from Q1_PRE QBOT show False
          using BOT_def by linarith
      qed

      from C_Sys_L0_enq_vis pP1 PC1_PRE Q1_PRE P2SET_PRE P2E1SAFE_PRE P2I_SAFE_PRE XNZ_PRE
      show ?thesis
        unfolding Sys_L0_def C_L0_def
                  program_counter_def X_var_def i_var_def Q_arr_def v_var_def V_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  obtain s2 where
      M_N1: "C_Match s1 None s2"
    and P_REST2: "C_Path s2 [None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P_REST1] .

  obtain s3 where
      M_N2: "C_Match s2 None s3"
    and P_REST3: "C_Path s3 [Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P_REST2] .

  obtain s4 where
      M_RET: "C_Match s3 (Some (mk_obs enq A3 P1 ret)) s4"
    and P_EMP: "C_Path s4 [] s_before_deq"
    using my_C_Path_ConsE[OF P_REST3] .

  have S4_EQ: "s4 = s_before_deq"
    using P_EMP by (cases rule: C_Path.cases) auto

  have T1: "C_Tau_Star s1 s2"
    using my_C_Match_NoneE[OF M_N1] .
  have T2: "C_Tau_Star s2 s3"
    using my_C_Match_NoneE[OF M_N2] .
  have T12: "C_Tau_Star s1 s3"
    using C_Tau_Star_trans[OF T1 T2] .
  have T_TOTAL: "C_Tau_Star u_call_post s3"
    using C_Tau_Star_trans[OF TAU_POST T12] .

  have MID_SAFE:
    "Q_arr s3 1 = A1 \<and>
     program_counter s3 P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s3 P1 = ''E1'' \<longrightarrow> X_var s3 \<noteq> 1) \<and>
     (program_counter s3 P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s3 P1 \<noteq> 1) \<and>
     program_counter s3 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s3 P2 = ''E1'' \<longrightarrow> X_var s3 \<noteq> 1) \<and>
     (program_counter s3 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s3 P2 \<noteq> 1)"
    using hwq_two_pending_enq_tau_preserves_q1[OF N2 T_TOTAL]
          CALL_SAFE
    by auto

  obtain u_ret_pre u_ret_post where
      TAU_RET_PRE: "C_Tau_Star s3 u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A3 P1 ret)) u_ret_post"
    and TAU_RET_POST: "C_Tau_Star u_ret_post s4"
    using my_C_Match_SomeE[OF M_RET] .

  have PRE_RET:
    "Q_arr u_ret_pre 1 = A1 \<and>
     program_counter u_ret_pre P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_pre P1 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1) \<and>
     (program_counter u_ret_pre P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P1 \<noteq> 1) \<and>
     program_counter u_ret_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_pre P2 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1) \<and>
     (program_counter u_ret_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P2 \<noteq> 1)"
    using hwq_two_pending_enq_tau_preserves_q1[OF N2 TAU_RET_PRE]
          MID_SAFE
    by auto

  have POST_RET:
    "program_counter u_ret_post P1 = ''L0'' \<and>
     Q_arr u_ret_post 1 = A1 \<and>
     program_counter u_ret_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_post P2 = ''E1'' \<longrightarrow> X_var u_ret_post \<noteq> 1) \<and>
     (program_counter u_ret_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_post P2 \<noteq> 1)"
  proof -
    from PRE_RET obtain
        Q1_PRE: "Q_arr u_ret_pre 1 = A1"
      and P1SET_PRE: "program_counter u_ret_pre P1 \<in> {''E1'', ''E2'', ''E3''}"
      and P1E1SAFE_PRE: "(program_counter u_ret_pre P1 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1)"
      and P1I_SAFE_PRE: "(program_counter u_ret_pre P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P1 \<noteq> 1)"
      and P2SET_PRE: "program_counter u_ret_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and P2E1SAFE_PRE: "(program_counter u_ret_pre P2 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_ret_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P2 \<noteq> 1)"
      by blast

    from STEP_RET show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP1 Q1_PRE P2SET_PRE P2E1SAFE_PRE P2I_SAFE_PRE
      show ?thesis
        unfolding Sys_E3_def C_E3_def
                  program_counter_def Q_arr_def X_var_def i_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have FINAL_SAFE:
    "program_counter s4 P1 = ''L0'' \<and>
     program_counter s4 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s4 1 = A1 \<and>
     (program_counter s4 P2 = ''E1'' \<longrightarrow> X_var s4 \<noteq> 1) \<and>
     (program_counter s4 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s4 P2 \<noteq> 1)"
    using hwq_p2_pending_tau_preserves_q1_weak[OF N2 TAU_RET_POST]
          POST_RET
    by auto

  from FINAL_SAFE S4_EQ show ?thesis
    by simp
qed

lemma hwq_a3_call_ret_preserves_q1:
  assumes N2: "N_Procs = 2"
      and PATH: "C_Path s_mid
        [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]
        s_before_deq"
      and SNAP: "program_counter s_mid P1 = ''L0'' \<and>
                 Q_arr s_mid 1 = A1 \<and>
                 X_var s_mid \<noteq> 1"
      and P2SAFE: "program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
                   (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
  shows "Q_arr s_before_deq 1 = A1 \<and>
         program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''}"
  using hwq_a3_call_ret_preserves_p2_safe_shape[OF N2 PATH SNAP P2SAFE]
  by auto


lemma hwq_tail_after_a1_preserves_q1:
  assumes N2: "N_Procs = 2"
      and PATH: "C_Path s_a1_ret
        [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
      and SNAP: "program_counter s_a1_ret P1 = ''L0'' \<and>
                 program_counter s_a1_ret P2 = ''L0'' \<and>
                 Q_arr s_a1_ret 1 = A1"
      and XNZ:  "X_var s_a1_ret \<noteq> 1"
  shows "Q_arr s_before_deq 1 = A1"
proof -
  have SPLIT:
    "[Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A2 P2 call), None] @
     [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s_mid where
      P12: "C_Path s_a1_ret [Some (mk_obs enq A2 P2 call), None] s_mid"
    and P34: "C_Path s_mid
         [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]
         s_before_deq"
    using C_Path_appendE[OF PATH[unfolded SPLIT]] by blast

  have MID_SNAP:
    "program_counter s_mid P1 = ''L0'' \<and>
     program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s_mid 1 = A1 \<and>
     X_var s_mid \<noteq> 1 \<and>
     (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    using hwq_a2_call_tau_preserves_q1[OF N2 P12 SNAP XNZ] .

  have END_SNAP:
    "Q_arr s_before_deq 1 = A1 \<and>
     program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''}"
    using hwq_a3_call_ret_preserves_q1[OF N2 P34]
          MID_SNAP
    by auto

  from END_SNAP show ?thesis
    by auto
qed


lemma hwq_full_e1_pre_deq_q1_shape:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
  shows "Q_arr s_before_deq 1 = A1"
proof -
  have SPLIT:
    "[Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
      Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @
     [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s_a1_ret where
      P_A1: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    and P_TAIL: "C_Path s_a1_ret
        [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using C_Path_appendE[OF PREFIX[unfolded SPLIT]] by blast

  have SNAP_A1:
    "program_counter s_a1_ret P1 = ''L0'' \<and>
     program_counter s_a1_ret P2 = ''L0'' \<and>
     Q_arr s_a1_ret 1 = A1"
    using hwq_a1_segment_q1_shape[OF N2 INIT P_A1] .

  have XNZ_A1: "X_var s_a1_ret \<noteq> 1"
    using hwq_a1_segment_XNZ[OF N2 INIT P_A1] .

  show ?thesis
    using hwq_tail_after_a1_preserves_q1[OF N2 P_TAIL SNAP_A1 XNZ_A1] .
qed



lemma Init_no_EnqCallInHis:
  assumes INIT: "Init s0"
  shows "\<not> EnqCallInHis s0 q a sn"
  using INIT
  unfolding EnqCallInHis_def Init_def his_seq_def
  by auto

lemma C_Tau_Star_preserves_his_seq:
  assumes TAUS: "C_Tau_Star s t"
  shows "his_seq t = his_seq s"
  using TAUS
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have H12: "his_seq s2 = his_seq s1"
    using C_Tau_preserves_his_and_s_var(1)[OF step.hyps(1)] .
  from step.IH H12 show ?case by simp
qed

lemma EnqCallInHis_append_non_enq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [e]"
      and NON: "act_name e \<noteq> enq \<or> act_cr e \<noteq> call"
  shows "EnqCallInHis s' q a sn \<longleftrightarrow> EnqCallInHis s q a sn"
proof
  assume H: "EnqCallInHis s' q a sn"
  show "EnqCallInHis s q a sn"
    using EnqCall_rev[OF H HIS NON] .
next
  assume H: "EnqCallInHis s q a sn"
  show "EnqCallInHis s' q a sn"
    using EnqCall_mono[OF H HIS] .
qed

lemma C_Path_no_enq_call_preserves_EnqCallInHis:
  assumes PATH: "C_Path s labs t"
      and NO_ENQ_CALL: "\<forall>x\<in>set labs. \<forall>p a. x \<noteq> Some (mk_obs enq a p call)"
  shows "EnqCallInHis t q a sn \<longleftrightarrow> EnqCallInHis s q a sn"
  using PATH NO_ENQ_CALL
proof (induction rule: C_Path.induct)
  case nil
  then show ?case by simp
next
  case (cons s l s1 ls s2)
  have NO_HEAD: "\<forall>p a. l \<noteq> Some (mk_obs enq a p call)"
    using cons.prems by auto
  have NO_TAIL: "\<forall>x\<in>set ls. \<forall>p a. x \<noteq> Some (mk_obs enq a p call)"
    using cons.prems by auto

  have MATCH_KEEP: "EnqCallInHis s1 q a sn \<longleftrightarrow> EnqCallInHis s q a sn"
    using cons.hyps(1) NO_HEAD
  proof (cases rule: C_Match.cases)
    case match_tau
    then have TS: "C_Tau_Star s s1" by auto
    have HIS: "his_seq s1 = his_seq s"
      using C_Tau_Star_preserves_his_seq[OF TS] .
    then show ?thesis
      unfolding EnqCallInHis_def Model.EnqCallInHis_def
      by auto
  next
    case match_vis
    then obtain u obs v where
        L_EQ: "l = Some obs"
      and T1: "C_Tau_Star s u"
      and V_STEP: "C_StepCR u (Some obs) v"
      and T2: "C_Tau_Star v s1"
      by auto

    have HIS_PRE: "his_seq u = his_seq s"
      using C_Tau_Star_preserves_his_seq[OF T1] .
    have HIS_POST: "his_seq s1 = his_seq v"
      using C_Tau_Star_preserves_his_seq[OF T2] .

    have PRE_KEEP: "EnqCallInHis u q a sn \<longleftrightarrow> EnqCallInHis s q a sn"
      using HIS_PRE
      unfolding EnqCallInHis_def Model.EnqCallInHis_def
      by auto

    have POST_KEEP: "EnqCallInHis s1 q a sn \<longleftrightarrow> EnqCallInHis v q a sn"
      using HIS_POST
      unfolding EnqCallInHis_def Model.EnqCallInHis_def
      by auto

    have STEP_KEEP: "EnqCallInHis v q a sn \<longleftrightarrow> EnqCallInHis u q a sn"
      using V_STEP
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have "l = Some (mk_obs enq (v_var u p) p call)"
        using L_EQ
        by (simp add: NO_HEAD) 
      with NO_HEAD show ?thesis
        by auto
    next
      case (C_Sys_L0_deq_vis p)
      have L0_rel: "L0 p u v"
        using C_Sys_L0_deq_vis unfolding L0_def by auto
      have PCD1: "program_counter v p = ''D1''"
        using C_Sys_L0_deq_vis unfolding Sys_L0_def C_L0_def program_counter_def Let_def 
        by (auto split: if_splits)
        
      have HIS: "his_seq v = his_seq u @ [mk_act deq BOT p (s_var u p) call]"
        using L0_D1_history_append[OF L0_rel PCD1] .
        
      have NON: "act_name (mk_act deq BOT p (s_var u p) call) \<noteq> enq
                 \<or> act_cr (mk_act deq BOT p (s_var u p) call) \<noteq> call"
        by (simp add: mk_act_def act_name_def act_cr_def)
      show ?thesis
        using EnqCallInHis_append_non_enq_call_iff[OF HIS NON] .
    next
      case (C_Sys_E3_vis p)
      obtain us_mid where
          U3: "U_E3 p (CState.v_var (fst u) p) (s_var u p) (snd u) us_mid"
        and U4: "U_E4 p us_mid (snd v)"
        using C_Sys_E3_vis(2) unfolding Sys_E3_def
        using Sys_E3_def local.C_Sys_E3_vis(3) by blast
      have HIS: "his_seq v = his_seq u @ [mk_act enq (v_var u p) p (s_var u p) ret]"
        using U3 U4
        unfolding his_seq_def v_var_def s_var_def U_E3_def U_E4_def
        by auto
      have NON: "act_name (mk_act enq (v_var u p) p (s_var u p) ret) \<noteq> enq
                 \<or> act_cr (mk_act enq (v_var u p) p (s_var u p) ret) \<noteq> call"
        by (simp add: mk_act_def act_name_def act_cr_def)
      show ?thesis
        using EnqCallInHis_append_non_enq_call_iff[OF HIS NON] .
    next
      case (C_Sys_D4_vis p)
      obtain us_mid where
          U3: "U_D3 p (CState.x_var (fst u) p) (s_var u p) (snd u) us_mid"
        and U4: "U_D4 p us_mid (snd v)"
        using C_Sys_D4_vis(2) unfolding Sys_D4_def
        using Sys_D4_def local.C_Sys_D4_vis(3) by auto 
      have HIS: "his_seq v = his_seq u @ [mk_act deq (x_var u p) p (s_var u p) ret]"
        using U3 U4
        unfolding his_seq_def x_var_def s_var_def U_D3_def U_D4_def
        by auto
      have NON: "act_name (mk_act deq (x_var u p) p (s_var u p) ret) \<noteq> enq
                 \<or> act_cr (mk_act deq (x_var u p) p (s_var u p) ret) \<noteq> call"
        by (simp add: mk_act_def act_name_def act_cr_def)
      show ?thesis
        using EnqCallInHis_append_non_enq_call_iff[OF HIS NON] .
    qed

    from PRE_KEEP STEP_KEEP POST_KEEP show ?thesis
      by blast
  qed

  have TAIL_KEEP: "EnqCallInHis s2 q a sn \<longleftrightarrow> EnqCallInHis s1 q a sn"
    using cons.IH[OF NO_TAIL] .
  from TAIL_KEEP MATCH_KEEP show ?case
    by blast
qed

lemma C_Path_single_enq_call_history:
  assumes PATH: "C_Path s [Some (mk_obs enq a p call)] t"
  shows "his_seq t = his_seq s @ [mk_act enq a p (s_var s p) call]"
proof -
  obtain s_mid where
      M: "C_Match s (Some (mk_obs enq a p call)) s_mid"
    and Pnil: "C_Path s_mid [] t"
    using my_C_Path_ConsE[OF PATH] by blast

  have MID_EQ: "s_mid = t"
    using Pnil by (cases rule: C_Path.cases) auto

  obtain u v where
      TPRE: "C_Tau_Star s u"
    and STEP: "C_StepCR u (Some (mk_obs enq a p call)) v"
    and TPOST: "C_Tau_Star v t"
    using my_C_Match_SomeE[OF M] MID_EQ by blast

  (* : using induction *)
  have HIS_PRE: "his_seq u = his_seq s"
    using TPRE
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    have H12: "his_seq s2 = his_seq s1"
      using C_Tau_preserves_his_and_s_var(1)[OF step.hyps(1)] .
    from step.IH H12 show ?case by simp
  qed

  (* : using induction *)
  have SVAR_PRE: "s_var u p = s_var s p"
    using TPRE
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    have H12: "s_var s2 p = s_var s1 p"
      using C_Tau_preserves_his_and_s_var(2)[OF step.hyps(1)] .
    from step.IH H12 show ?case by simp
  qed

  (* : using induction *)
  have HIS_POST: "his_seq t = his_seq v"
    using TPOST
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    have H12: "his_seq s2 = his_seq s1"
      using C_Tau_preserves_his_and_s_var(1)[OF step.hyps(1)] .
    from step.IH H12 show ?case by simp
  qed

  have HIS_STEP: "his_seq v = his_seq u @ [mk_act enq a p (s_var u p) call]"
  proof -
    from STEP show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p0)
      have p0_eq: "p0 = p"
        using C_Sys_L0_enq_vis unfolding mk_obs_def by auto
      have a_eq: "a = V_var u"
        using C_Sys_L0_enq_vis unfolding mk_obs_def by auto
      have L0STEP: "L0 p u v"
        using C_Sys_L0_enq_vis p0_eq unfolding L0_def by auto
        
      (* Core: explicitunfoldstate definition, extract PC_E1 *)
      have PC_E1: "program_counter v p = ''E1''"
        using C_Sys_L0_enq_vis p0_eq 
        unfolding Sys_L0_def C_L0_def program_counter_def Let_def 
        by (auto split: if_splits)
        
      have HIS: "his_seq v = his_seq u @ [mk_act enq (V_var u) p (s_var u p) call]"
        using L0_E1_history_append[OF L0STEP PC_E1] .
        
      with a_eq show ?thesis by simp
    qed (auto simp: mk_obs_def)
  qed

  show ?thesis
    using HIS_PRE SVAR_PRE HIS_POST HIS_STEP
    by simp
qed


lemma hwq_full_e1_pre_deq_p2_safe_shape:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
  shows "P2_pending_A2_safe s_before_deq"
proof -
  have SPLIT:
    "[Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
      Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @
     [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s_a1_ret where
      P_A1: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    and P_TAIL: "C_Path s_a1_ret
        [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using C_Path_appendE[OF PREFIX[unfolded SPLIT]]
    by blast

  have SNAP_A1:
    "program_counter s_a1_ret P1 = ''L0'' \<and>
     program_counter s_a1_ret P2 = ''L0'' \<and>
     Q_arr s_a1_ret 1 = A1"
    using hwq_a1_segment_q1_shape[OF N2 INIT P_A1] .

  have XNZ_A1: "X_var s_a1_ret \<noteq> 1"
    using hwq_a1_segment_XNZ[OF N2 INIT P_A1] .

  have SPLIT_TAIL:
    "[Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A2 P2 call), None] @
     [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s_mid where
      P12: "C_Path s_a1_ret [Some (mk_obs enq A2 P2 call), None] s_mid"
    and P34: "C_Path s_mid
         [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]
         s_before_deq"
    using C_Path_appendE[OF P_TAIL[unfolded SPLIT_TAIL]]
    by blast

  have MID_SAFE:
    "program_counter s_mid P1 = ''L0'' \<and>
     program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s_mid 1 = A1 \<and>
     X_var s_mid \<noteq> 1 \<and>
     (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    using hwq_a2_call_tau_preserves_q1[OF N2 P12 SNAP_A1 XNZ_A1]
    by auto

  have END_SAFE:
    "Q_arr s_before_deq 1 = A1 \<and>
     program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1) \<and>
     (program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1)"
    using hwq_a3_call_ret_preserves_p2_safe_shape[OF N2 P34] MID_SAFE
    by auto

  have RS0: "Reachable_Sys s_before_deq"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] PREFIX] .

  have INV0: "system_invariant s_before_deq"
    using Reachable_Sys_system_invariant[OF RS0] .

  have ONLY_P2_A2: "\<And>a sn. EnqCallInHis s_before_deq P2 a sn \<Longrightarrow> a = A2"
  proof -
    fix a sn
    assume EC_FINAL: "EnqCallInHis s_before_deq P2 a sn"

    have SPLIT6:
      "[Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
        Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
        None, None, Some (mk_obs enq A3 P1 ret)]
       =
       [Some (mk_obs enq A1 P1 call)] @
       [None, None, Some (mk_obs enq A1 P1 ret)] @
       [Some (mk_obs enq A2 P2 call)] @
       [None] @
       [Some (mk_obs enq A3 P1 call)] @
       [None, None, Some (mk_obs enq A3 P1 ret)]"
      by simp

    obtain s1 s2 s3 s4 s5 where
        P1SEG: "C_Path s0 [Some (mk_obs enq A1 P1 call)] s1"
      and P2SEG: "C_Path s1 [None, None, Some (mk_obs enq A1 P1 ret)] s2"
      and P3SEG: "C_Path s2 [Some (mk_obs enq A2 P2 call)] s3"
      and P4SEG: "C_Path s3 [None] s4"
      and P5SEG: "C_Path s4 [Some (mk_obs enq A3 P1 call)] s5"
      and P6SEG: "C_Path s5 [None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
      using C_Path_appendE[OF PREFIX[unfolded SPLIT6]]
      by (meson C_Path_appendE)

    have HIS1:
      "his_seq s1 = his_seq s0 @ [mk_act enq A1 P1 (s_var s0 P1) call]"
      using C_Path_single_enq_call_history[OF P1SEG] .

    have HIS3:
      "his_seq s3 = his_seq s2 @ [mk_act enq A2 P2 (s_var s2 P2) call]"
      using C_Path_single_enq_call_history[OF P3SEG] .

    have HIS5:
      "his_seq s5 = his_seq s4 @ [mk_act enq A3 P1 (s_var s4 P1) call]"
      using C_Path_single_enq_call_history[OF P5SEG] .

    have NO_ENQ_CALL_P2SEG:
      "\<forall>x\<in>set [None, None, Some (mk_obs enq A1 P1 ret)]. \<forall>p a0.
         x \<noteq> Some (mk_obs enq a0 p call)"
      unfolding mk_obs_def by auto

    have NO_ENQ_CALL_P4SEG:
      "\<forall>x\<in>set [None]. \<forall>p a0.
         x \<noteq> Some (mk_obs enq a0 p call)"
      unfolding mk_obs_def by auto

    have NO_ENQ_CALL_P6SEG:
      "\<forall>x\<in>set [None, None, Some (mk_obs enq A3 P1 ret)]. \<forall>p a0.
         x \<noteq> Some (mk_obs enq a0 p call)"
      unfolding mk_obs_def by auto

    have P6_KEEP:
      "EnqCallInHis s_before_deq P2 a sn \<longleftrightarrow> EnqCallInHis s5 P2 a sn"
      using C_Path_no_enq_call_preserves_EnqCallInHis[OF P6SEG NO_ENQ_CALL_P6SEG] .

    have P4_KEEP:
      "EnqCallInHis s4 P2 a sn \<longleftrightarrow> EnqCallInHis s3 P2 a sn"
      using C_Path_no_enq_call_preserves_EnqCallInHis[OF P4SEG NO_ENQ_CALL_P4SEG] .

    have P2_KEEP:
      "EnqCallInHis s2 P2 a sn \<longleftrightarrow> EnqCallInHis s1 P2 a sn"
      using C_Path_no_enq_call_preserves_EnqCallInHis[OF P2SEG NO_ENQ_CALL_P2SEG] .

    have EC5: "EnqCallInHis s5 P2 a sn"
      using EC_FINAL P6_KEEP by blast

    have EC4: "EnqCallInHis s4 P2 a sn"
      using EC5 EnqCallInHis_append_enq_call_iff[OF HIS5]
      by auto

    have EC3: "EnqCallInHis s3 P2 a sn"
      using EC4 P4_KEEP by blast

    have EC2: "EnqCallInHis s2 P2 a sn \<or> a = A2"
      using EC3 EnqCallInHis_append_enq_call_iff[OF HIS3]
      by auto

    show "a = A2"
    proof (cases "a = A2")
      case True
      then show ?thesis .
    next
      case False
      then have EC2': "EnqCallInHis s2 P2 a sn"
        using EC2 by auto

      have EC1: "EnqCallInHis s1 P2 a sn"
        using EC2' P2_KEEP by blast

      have EC0: "EnqCallInHis s0 P2 a sn"
        using EC1 EnqCallInHis_append_enq_call_iff[OF HIS1]
        by auto

      have INIT0: "\<not> EnqCallInHis s0 P2 a sn"
        using Init_no_EnqCallInHis[OF INIT] .

      from EC0 INIT0 show ?thesis
        by blast
    qed
  qed

  have H1: "hI1_E_Phase_Pending_Enq s_before_deq"
    using INV0
    unfolding system_invariant_def
    by auto

  have P2E: "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''}"
    using END_SAFE by auto

have HP2: "HasPendingEnq s_before_deq P2 (v_var s_before_deq P2)"
  using H1 P2E
  unfolding hI1_E_Phase_Pending_Enq_def
  by blast

obtain sn where EC_P2:
  "EnqCallInHis s_before_deq P2 (v_var s_before_deq P2) sn"
  using HP2
  unfolding HasPendingEnq_def
  by metis

  have V2A2: "v_var s_before_deq P2 = A2"
    using ONLY_P2_A2[OF EC_P2] .

  show ?thesis
    unfolding P2_pending_A2_safe_def
    using END_SAFE V2A2
    by auto
qed



(* ========================================================================= *)
(* Bridge 4 helper A: single-step Tau preserve "P1 deq-branch + P2 pending-safe" *)
(* ========================================================================= *)
lemma Tau_preserves_P1_branch_step_P2_pending_safe:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and BR:
        "((Q_arr s 1 = A1) \<and>
           ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
         \<or>
         ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
      and P2SAFE:
        "program_counter s P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s P2 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
         (program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"
      and TAU: "C_Tau s s'"
  shows
    "(((Q_arr s' 1 = A1) \<and>
        ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
         (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
       \<or>
       ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1))
     \<and>
     (program_counter s' P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
      (program_counter s' P2 = ''E1'' \<longrightarrow> X_var s' \<noteq> 1) \<and>
      (program_counter s' P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' P2 \<noteq> 1))"
proof -
  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto

  have p_cases: "p = P1 \<or> p = P2"
    using PIN N2 by auto

  from p_cases show ?thesis
  proof
    assume pP1: "p = P1"

    have STEP1: "Sys_D1 P1 s s' \<or> Sys_D2 P1 s s' \<or> Sys_D3 P1 s s'"
      using STEP pP1 BR
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def program_counter_def
      by auto

    (* 1: STEP1, local unfold, auto *)
    have P2SAFE':
      "program_counter s' P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
       (program_counter s' P2 = ''E1'' \<longrightarrow> X_var s' \<noteq> 1) \<and>
       (program_counter s' P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' P2 \<noteq> 1)"
      using STEP1
    proof (elim disjE)
      assume D1: "Sys_D1 P1 s s'"
      thus ?thesis using P2SAFE
        unfolding Sys_D1_def C_D1_def program_counter_def X_var_def i_var_def Let_def by auto
    next
      assume D2: "Sys_D2 P1 s s'"
      thus ?thesis using P2SAFE
        unfolding Sys_D2_def C_D2_def program_counter_def X_var_def i_var_def Let_def T_D2_EnterLoop_def 
        by (auto split: if_splits)
    next
      assume D3: "Sys_D3 P1 s s'"
      thus ?thesis using P2SAFE
        unfolding Sys_D3_def C_D3_def program_counter_def X_var_def i_var_def Let_def 
        by (auto split: if_splits)
    qed

    have BR':
      "((Q_arr s' 1 = A1) \<and>
         ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
       \<or>
       ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1)"
      using BR
    proof (elim disjE)
      assume SCAN:
        "(Q_arr s 1 = A1) \<and>
         ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1))"
      then have Q1: "Q_arr s 1 = A1"
        and SC:
          "((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1))"
        by auto
      from STEP1 show ?thesis
      proof (elim disjE)
        assume D1: "Sys_D1 P1 s s'"
        then have "Q_arr s' 1 = A1"
          using Q1 unfolding Sys_D1_def C_D1_def Q_arr_def Let_def by auto
        moreover have "program_counter s' P1 = ''D2''"
          using D1 unfolding Sys_D1_def C_D1_def program_counter_def Let_def by auto
        ultimately show ?thesis by auto
      next
        assume D2: "Sys_D2 P1 s s'"
        from SC show ?thesis
        proof (elim disjE)
          assume H: "program_counter s P1 \<in> {''D1'', ''D2''}"
          then have "program_counter s P1 = ''D2''"
            using D2 unfolding Sys_D2_def C_D2_def program_counter_def Let_def by auto
          then show ?thesis
            using D2 Q1
            unfolding Sys_D2_def C_D2_def program_counter_def Q_arr_def j_var_def Let_def T_D2_EnterLoop_def
            by (auto split: if_splits)
        next
          assume H: "program_counter s P1 = ''D3'' \<and> j_var s P1 = 1"
          with D2 show ?thesis
            unfolding Sys_D2_def C_D2_def program_counter_def Let_def T_D2_EnterLoop_def by auto
        qed
      next
        assume D3: "Sys_D3 P1 s s'"
        from SC show ?thesis
        proof (elim disjE)
          assume H: "program_counter s P1 \<in> {''D1'', ''D2''}"
          with D3 show ?thesis
            unfolding Sys_D3_def C_D3_def program_counter_def Let_def by auto
        next
          assume D3J1: "program_counter s P1 = ''D3'' \<and> j_var s P1 = 1"
          then have PCD3: "program_counter s P1 = ''D3''"
            and J1: "j_var s P1 = 1"
            by auto
          
          have "Q_arr s' 1 = BOT"
            using D3 Q1 PCD3 J1
            unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def BOT_def
            by auto
          moreover have "program_counter s' P1 = ''D4''"
            using D3 Q1 PCD3 J1
            unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def BOT_def
            by (auto split: if_splits)
          moreover have "x_var s' P1 = A1"
            using D3 Q1 PCD3 J1
            unfolding Sys_D3_def C_D3_def Q_arr_def program_counter_def j_var_def x_var_def Let_def BOT_def
            by auto
          ultimately show ?thesis by auto
        qed
      qed
    next
      assume LOCK:
        "(Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1"
      from STEP1 LOCK show ?thesis
        unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                  program_counter_def Let_def T_D2_EnterLoop_def
        by auto
    qed

    from BR' P2SAFE' show ?thesis
      by blast

  next
    assume pP2: "p = P2"

    have STEP2: "Sys_E1 P2 s s' \<or> Sys_E2 P2 s s'"
      using STEP pP2 P2SAFE
      unfolding Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def T_D2_EnterLoop_def Let_def
      by auto

    have P2SAFE':
      "program_counter s' P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
       (program_counter s' P2 = ''E1'' \<longrightarrow> X_var s' \<noteq> 1) \<and>
       (program_counter s' P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' P2 \<noteq> 1)"
      using STEP2
    proof (elim disjE)
      assume E1: "Sys_E1 P2 s s'"
      have PCE1: "program_counter s P2 = ''E1''"
        using E1 unfolding Sys_E1_def C_E1_def program_counter_def Let_def by auto
      have XNZ: "X_var s \<noteq> 1"
        using P2SAFE PCE1 by auto
      from E1 XNZ show ?thesis
        using P2SAFE
        unfolding Sys_E1_def C_E1_def program_counter_def X_var_def i_var_def Let_def
        by (auto split: if_splits)
    next
      assume E2: "Sys_E2 P2 s s'"
      have PCE2: "program_counter s P2 = ''E2''"
        using E2 unfolding Sys_E2_def C_E2_def program_counter_def Let_def by auto
      have I2NZ: "i_var s P2 \<noteq> 1"
        using P2SAFE PCE2 by auto
      from E2 I2NZ show ?thesis
        using P2SAFE
        unfolding Sys_E2_def C_E2_def program_counter_def X_var_def i_var_def Let_def
        by (auto split: if_splits)
    qed

have BR':
      "((Q_arr s' 1 = A1) \<and>
         ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
       \<or>
       ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1)"
      using STEP2
    proof (elim disjE)
      assume E1: "Sys_E1 P2 s s'"
      then show ?thesis
        using BR P2SAFE
        unfolding Sys_E1_def C_E1_def
                  program_counter_def Q_arr_def j_var_def x_var_def Let_def
        by (auto split: if_splits)
    next
      assume E2: "Sys_E2 P2 s s'"
      have PCE2: "program_counter s P2 = ''E2''"
        using E2 unfolding Sys_E2_def C_E2_def program_counter_def Let_def by auto
      have I2NZ: "i_var s P2 \<noteq> 1"
        using P2SAFE PCE2 by auto
      then show ?thesis
        using BR E2 P2SAFE
        unfolding Sys_E2_def C_E2_def
                  program_counter_def Q_arr_def j_var_def x_var_def i_var_def Let_def
        by (auto split: if_splits)
    qed

    from BR' P2SAFE' show ?thesis
      by blast
  qed
qed


(* ========================================================================= *)
(* Bridge 4 helper B: Tau* preserve "P1 deq-branch + P2 pending-safe" *)
(* ========================================================================= *)
lemma Tau_Star_preserves_P1_branch_P2_pending_safe:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and BR:
        "((Q_arr s 1 = A1) \<and>
           ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
         \<or>
         ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
      and P2SAFE:
        "program_counter s P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s P2 = ''E1'' \<longrightarrow> X_var s \<noteq> 1) \<and>
         (program_counter s P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s P2 \<noteq> 1)"
      and TAUS: "C_Tau_Star s s'"
  shows
    "(((Q_arr s' 1 = A1) \<and>
        ((program_counter s' P1 \<in> {''D1'', ''D2''}) \<or>
         (program_counter s' P1 = ''D3'' \<and> j_var s' P1 = 1)))
       \<or>
       ((Q_arr s' 1 = BOT) \<and> program_counter s' P1 = ''D4'' \<and> x_var s' P1 = A1))
     \<and>
     (program_counter s' P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
      (program_counter s' P2 = ''E1'' \<longrightarrow> X_var s' \<noteq> 1) \<and>
      (program_counter s' P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s' P2 \<noteq> 1))"
  using TAUS INV BR P2SAFE
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s_mid s_next s_end)
  have STEP0: "C_StepCR s_mid None s_next"
    using step.hyps(1) unfolding C_Tau_def by simp

  have NXT: "Next s_mid s_next"
    using C_StepCR_into_Next[OF STEP0] .

  have INV_NEXT: "system_invariant s_next"
    using Sys_Inv_Step[OF step.prems(1) NXT] .

  have STEP1:
    "(((Q_arr s_next 1 = A1) \<and>
        ((program_counter s_next P1 \<in> {''D1'', ''D2''}) \<or>
         (program_counter s_next P1 = ''D3'' \<and> j_var s_next P1 = 1)))
       \<or>
       ((Q_arr s_next 1 = BOT) \<and> program_counter s_next P1 = ''D4'' \<and> x_var s_next P1 = A1))
     \<and>
     (program_counter s_next P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
      (program_counter s_next P2 = ''E1'' \<longrightarrow> X_var s_next \<noteq> 1) \<and>
      (program_counter s_next P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_next P2 \<noteq> 1))"
    using Tau_preserves_P1_branch_step_P2_pending_safe[
            OF N2 step.prems(1) step.prems(2) step.prems(3) step.hyps(1)] .

  from STEP1 have
      BR_NEXT:
        "((Q_arr s_next 1 = A1) \<and>
           ((program_counter s_next P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s_next P1 = ''D3'' \<and> j_var s_next P1 = 1)))
         \<or>
         ((Q_arr s_next 1 = BOT) \<and> program_counter s_next P1 = ''D4'' \<and> x_var s_next P1 = A1)"
    and P2SAFE_NEXT:
        "program_counter s_next P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s_next P2 = ''E1'' \<longrightarrow> X_var s_next \<noteq> 1) \<and>
         (program_counter s_next P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_next P2 \<noteq> 1)"
    by blast+

  show ?case
    using step.IH[OF INV_NEXT BR_NEXT P2SAFE_NEXT] .
qed

lemma hwq_quantum_branch_suffix_from_pre_deq:
  assumes N2: "N_Procs = 2"
      and INV0: "system_invariant s_before_deq"
      and PC1_0: "program_counter s_before_deq P1 = ''L0''"
      and PATH:
        "C_Path s_before_deq
          ([Some (mk_obs deq BOT P1 call), None, None, None, None] @
           [Some (mk_obs enq A2 P2 ret)]) sk0"
      and PREQ1: "Q_arr s_before_deq 1 = A1"
      and P2SAFE:
        "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1) \<and>
         (program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1)"
  shows
    "(Q_arr sk0 1 = A1 \<and>
       ((program_counter sk0 P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1)))
     \<or>
     (Q_arr sk0 1 = BOT \<and> program_counter sk0 P1 = ''D4'' \<and> x_var sk0 P1 = A1)"
proof -
  have TauStar_preserves_INV:
    "\<And>x y. C_Tau_Star x y \<Longrightarrow> system_invariant x \<Longrightarrow> system_invariant y"
  proof -
    fix x y
    assume T: "C_Tau_Star x y"
       and I: "system_invariant x"
    from T I show "system_invariant y"
    proof (induction rule: C_Tau_Star.induct)
      case refl
      then show ?case by simp
    next
      case (step s1 s2 s3)
      have STEP0: "C_StepCR s1 None s2"
        using step.hyps(1) unfolding C_Tau_def by simp
      have NXT: "Next s1 s2"
        using C_StepCR_into_Next[OF STEP0] .
      have INV2: "system_invariant s2"
        using Sys_Inv_Step[OF step.prems NXT] .
      show ?case
        using step.IH[OF INV2] .
    qed
  qed

  obtain s_deq_post where
      P_DEQ: "C_Path s_before_deq
        [Some (mk_obs deq BOT P1 call), None, None, None, None] s_deq_post"
    and M_RET: "C_Match s_deq_post (Some (mk_obs enq A2 P2 ret)) sk0"
    using C_Path_snocE[OF PATH] by blast

  obtain s1 where
      M_DEQ: "C_Match s_before_deq (Some (mk_obs deq BOT P1 call)) s1"
    and P_N4: "C_Path s1 [None, None, None, None] s_deq_post"
    using my_C_Path_ConsE[OF P_DEQ] .

  obtain u_deq_pre u_deq_post where
      T_DEQ_PRE: "C_Tau_Star s_before_deq u_deq_pre"
    and STEP_DEQ: "C_StepCR u_deq_pre (Some (mk_obs deq BOT P1 call)) u_deq_post"
    and T_DEQ_POST: "C_Tau_Star u_deq_post s1"
    using my_C_Match_SomeE[OF M_DEQ] .

  have INV_u_deq_pre: "system_invariant u_deq_pre"
    using TauStar_preserves_INV[OF T_DEQ_PRE INV0] .

  have PRE_DEQ_SAFE:
    "program_counter u_deq_pre P1 = ''L0'' \<and>
     Q_arr u_deq_pre 1 = A1 \<and>
     program_counter u_deq_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_deq_pre P2 = ''E1'' \<longrightarrow> X_var u_deq_pre \<noteq> 1) \<and>
     (program_counter u_deq_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_deq_pre P2 \<noteq> 1)"
    using hwq_p2_pending_tau_preserves_q1_weak[OF N2 T_DEQ_PRE PC1_0 _ _ _ PREQ1]
          P2SAFE
    by auto

  have BR_CALL:
    "((Q_arr u_deq_post 1 = A1) \<and>
       ((program_counter u_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter u_deq_post P1 = ''D3'' \<and> j_var u_deq_post P1 = 1)))
     \<or>
     ((Q_arr u_deq_post 1 = BOT) \<and> program_counter u_deq_post P1 = ''D4'' \<and> x_var u_deq_post P1 = A1)"
  proof -
    from PRE_DEQ_SAFE obtain
        PC1_PRE: "program_counter u_deq_pre P1 = ''L0''"
      and Q1_PRE: "Q_arr u_deq_pre 1 = A1"
      and P2SET_PRE: "program_counter u_deq_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and P2E1SAFE_PRE: "(program_counter u_deq_pre P2 = ''E1'' \<longrightarrow> X_var u_deq_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_deq_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_deq_pre P2 \<noteq> 1)"
      by blast

    from STEP_DEQ show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_deq_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_L0_deq_vis pP1 PC1_PRE Q1_PRE
      show ?thesis
        unfolding Sys_L0_def C_L0_def
                  program_counter_def Q_arr_def j_var_def x_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have POST_DEQ_SAFE:
    "program_counter u_deq_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_deq_post P2 = ''E1'' \<longrightarrow> X_var u_deq_post \<noteq> 1) \<and>
     (program_counter u_deq_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_deq_post P2 \<noteq> 1)"
  proof -
    from PRE_DEQ_SAFE obtain
        PC1_PRE: "program_counter u_deq_pre P1 = ''L0''"
      and Q1_PRE: "Q_arr u_deq_pre 1 = A1"
      and P2SET_PRE: "program_counter u_deq_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and P2E1SAFE_PRE: "(program_counter u_deq_pre P2 = ''E1'' \<longrightarrow> X_var u_deq_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_deq_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_deq_pre P2 \<noteq> 1)"
      by blast

    from STEP_DEQ show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_deq_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_L0_deq_vis pP1 P2SET_PRE P2E1SAFE_PRE P2I_SAFE_PRE
      show ?thesis
        unfolding Sys_L0_def C_L0_def
                  program_counter_def X_var_def i_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have NXT_DEQ: "Next u_deq_pre u_deq_post"
    using C_StepCR_into_Next[OF STEP_DEQ] .

  have INV_u_deq_post: "system_invariant u_deq_post"
    using Sys_Inv_Step[OF INV_u_deq_pre NXT_DEQ] .

  obtain s2 where
      M_N1: "C_Match s1 None s2"
    and P_N3: "C_Path s2 [None, None, None] s_deq_post"
    using my_C_Path_ConsE[OF P_N4] .

  obtain s3 where
      M_N2: "C_Match s2 None s3"
    and P_N2: "C_Path s3 [None, None] s_deq_post"
    using my_C_Path_ConsE[OF P_N3] .

  obtain s4 where
      M_N3: "C_Match s3 None s4"
    and P_N1: "C_Path s4 [None] s_deq_post"
    using my_C_Path_ConsE[OF P_N2] .

  obtain s5 where
      M_N4: "C_Match s4 None s5"
    and P_N0: "C_Path s5 [] s_deq_post"
    using my_C_Path_ConsE[OF P_N1] .

  have S5_EQ: "s5 = s_deq_post"
    using P_N0 by (cases rule: C_Path.cases) auto

  have T_N_ALL: "C_Tau_Star s1 s_deq_post"
    using C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N1]
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N2]
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N3] my_C_Match_NoneE[OF M_N4]]]]
          S5_EQ
    by simp

  have T_MID: "C_Tau_Star u_deq_post s_deq_post"
    using C_Tau_Star_trans[OF T_DEQ_POST T_N_ALL] .

  have MID:
    "(((Q_arr s_deq_post 1 = A1) \<and>
       ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
      \<or>
      ((Q_arr s_deq_post 1 = BOT) \<and> program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1))
     \<and>
     (program_counter s_deq_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
      (program_counter s_deq_post P2 = ''E1'' \<longrightarrow> X_var s_deq_post \<noteq> 1) \<and>
      (program_counter s_deq_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_deq_post P2 \<noteq> 1))"
    using Tau_Star_preserves_P1_branch_P2_pending_safe[OF N2 INV_u_deq_post BR_CALL POST_DEQ_SAFE T_MID] .

  have INV_s_deq_post: "system_invariant s_deq_post"
    using TauStar_preserves_INV[OF T_MID INV_u_deq_post] .

  obtain u_ret_pre u_ret_post where
      T_RET_PRE: "C_Tau_Star s_deq_post u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
    and T_RET_POST: "C_Tau_Star u_ret_post sk0"
    using my_C_Match_SomeE[OF M_RET] .

  have PRE_RET:
    "(((Q_arr u_ret_pre 1 = A1) \<and>
       ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))
      \<or>
      ((Q_arr u_ret_pre 1 = BOT) \<and> program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1))
     \<and>
     (program_counter u_ret_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
      (program_counter u_ret_pre P2 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1) \<and>
      (program_counter u_ret_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P2 \<noteq> 1))"
    using Tau_Star_preserves_P1_branch_P2_pending_safe[OF N2 INV_s_deq_post]
          MID T_RET_PRE
    by auto

  have POST_RET:
    "program_counter u_ret_post P2 = ''L0'' \<and>
     (((Q_arr u_ret_post 1 = A1) \<and>
        ((program_counter u_ret_post P1 \<in> {''D1'', ''D2''}) \<or>
         (program_counter u_ret_post P1 = ''D3'' \<and> j_var u_ret_post P1 = 1)))
      \<or>
      ((Q_arr u_ret_post 1 = BOT) \<and> program_counter u_ret_post P1 = ''D4'' \<and> x_var u_ret_post P1 = A1))"
    using C_StepCR_P2_ret_preserves_P1_branch[OF N2 STEP_RET]
          PRE_RET
    by auto

  have INV_u_ret_pre: "system_invariant u_ret_pre"
    using TauStar_preserves_INV[OF T_RET_PRE INV_s_deq_post] .

  have NXT_RET: "Next u_ret_pre u_ret_post"
    using C_StepCR_into_Next[OF STEP_RET] .

  have INV_u_ret_post: "system_invariant u_ret_post"
    using Sys_Inv_Step[OF INV_u_ret_pre NXT_RET] .

  from POST_RET have
      PCP2_POST: "program_counter u_ret_post P2 = ''L0''"
    and BR_POST:
      "((Q_arr u_ret_post 1 = A1) \<and>
         ((program_counter u_ret_post P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter u_ret_post P1 = ''D3'' \<and> j_var u_ret_post P1 = 1)))
       \<or>
       ((Q_arr u_ret_post 1 = BOT) \<and> program_counter u_ret_post P1 = ''D4'' \<and> x_var u_ret_post P1 = A1)"
    by auto

  show ?thesis
    using Tau_Star_preserves_P1_branch[OF N2 INV_u_ret_post PCP2_POST BR_POST T_RET_POST] .
qed

lemma hwq_full_e1_pre_deq_p1_l0_shape:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
  shows "program_counter s_before_deq P1 = ''L0''"
proof -
  have SPLIT:
    "[Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
      Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @
     [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s_a1_ret where
      P_A1: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    and P_TAIL: "C_Path s_a1_ret
        [Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using C_Path_appendE[OF PREFIX[unfolded SPLIT]] by blast

  have SNAP_A1:
    "program_counter s_a1_ret P1 = ''L0'' \<and>
     program_counter s_a1_ret P2 = ''L0'' \<and>
     Q_arr s_a1_ret 1 = A1"
    using hwq_a1_segment_q1_shape[OF N2 INIT P_A1] .

  have XNZ_A1: "X_var s_a1_ret \<noteq> 1"
    using hwq_a1_segment_XNZ[OF N2 INIT P_A1] .

  have SPLIT_TAIL:
    "[Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A2 P2 call), None] @
     [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s_mid where
      P12: "C_Path s_a1_ret [Some (mk_obs enq A2 P2 call), None] s_mid"
    and P34: "C_Path s_mid
         [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]
         s_before_deq"
    using C_Path_appendE[OF P_TAIL[unfolded SPLIT_TAIL]] by blast

  have MID_SNAP:
    "program_counter s_mid P1 = ''L0'' \<and>
     program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s_mid 1 = A1 \<and>
     X_var s_mid \<noteq> 1 \<and>
     (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    using hwq_a2_call_tau_preserves_q1[OF N2 P12 SNAP_A1 XNZ_A1] .

  from MID_SNAP have PC1_0: "program_counter s_mid P1 = ''L0''"
    and P2SET_0: "program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''}"
    and Q1_0: "Q_arr s_mid 1 = A1"
    and XNZ_0: "X_var s_mid \<noteq> 1"
    and I2NZ_0: "(program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    by auto

  obtain s1 where
      M_CALL: "C_Match s_mid (Some (mk_obs enq A3 P1 call)) s1"
    and P_REST1: "C_Path s1 [None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P34] .

  obtain u_call_pre u_call_post where
      TAU_PRE: "C_Tau_Star s_mid u_call_pre"
    and STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A3 P1 call)) u_call_post"
    and TAU_POST: "C_Tau_Star u_call_post s1"
    using my_C_Match_SomeE[OF M_CALL] .

  have PRE_SAFE:
    "program_counter u_call_pre P1 = ''L0'' \<and>
     program_counter u_call_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr u_call_pre 1 = A1 \<and>
     (program_counter u_call_pre P2 = ''E1'' \<longrightarrow> X_var u_call_pre \<noteq> 1) \<and>
     (program_counter u_call_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_pre P2 \<noteq> 1)"
    using hwq_p2_pending_tau_preserves_q1_weak[OF N2 TAU_PRE PC1_0 P2SET_0 _ I2NZ_0 Q1_0]
          XNZ_0
    by auto

  have CALL_SAFE:
    "program_counter u_call_post P1 = ''E1'' \<and>
     (program_counter u_call_post P1 = ''E1'' \<longrightarrow> X_var u_call_post \<noteq> 1) \<and>
     (program_counter u_call_post P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_post P1 \<noteq> 1) \<and>
     program_counter u_call_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_call_post P2 = ''E1'' \<longrightarrow> X_var u_call_post \<noteq> 1) \<and>
     (program_counter u_call_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_post P2 \<noteq> 1) \<and>
     Q_arr u_call_post 1 = A1"
  proof -
    from PRE_SAFE obtain
        PC1_PRE: "program_counter u_call_pre P1 = ''L0''"
      and P2SET_PRE: "program_counter u_call_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and Q1_PRE: "Q_arr u_call_pre 1 = A1"
      and P2E1SAFE_PRE: "(program_counter u_call_pre P2 = ''E1'' \<longrightarrow> X_var u_call_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_call_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_pre P2 \<noteq> 1)"
      by blast

    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto

      have INV_PRE: "system_invariant u_call_pre"
        using C_Sys_L0_enq_vis
        using Sys_L0_def by blast

      have XNZ_PRE: "X_var u_call_pre \<noteq> 1"
      proof
        assume X1: "X_var u_call_pre = 1"
        have S2: "sI2_X_var_Upper_Bound u_call_pre"
          using INV_PRE unfolding system_invariant_def by auto
        have QBOT: "Q_arr u_call_pre 1 = BOT"
          using S2 X1
          unfolding sI2_X_var_Upper_Bound_def
          by auto
        from Q1_PRE QBOT show False
          using BOT_def by linarith
      qed

      from C_Sys_L0_enq_vis pP1 PC1_PRE Q1_PRE P2SET_PRE P2E1SAFE_PRE P2I_SAFE_PRE XNZ_PRE
      show ?thesis
        unfolding Sys_L0_def C_L0_def
                  program_counter_def X_var_def i_var_def Q_arr_def v_var_def V_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  obtain s2 where
      M_N1: "C_Match s1 None s2"
    and P_REST2: "C_Path s2 [None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P_REST1] .

  obtain s3 where
      M_N2: "C_Match s2 None s3"
    and P_REST3: "C_Path s3 [Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P_REST2] .

  obtain s4 where
      M_RET: "C_Match s3 (Some (mk_obs enq A3 P1 ret)) s4"
    and P_EMP: "C_Path s4 [] s_before_deq"
    using my_C_Path_ConsE[OF P_REST3] .

  have S4_EQ: "s4 = s_before_deq"
    using P_EMP by (cases rule: C_Path.cases) auto

  have T1: "C_Tau_Star s1 s2"
    using my_C_Match_NoneE[OF M_N1] .
  have T2: "C_Tau_Star s2 s3"
    using my_C_Match_NoneE[OF M_N2] .
  have T12: "C_Tau_Star s1 s3"
    using C_Tau_Star_trans[OF T1 T2] .
  have T_TOTAL: "C_Tau_Star u_call_post s3"
    using C_Tau_Star_trans[OF TAU_POST T12] .

  have MID_SAFE:
    "Q_arr s3 1 = A1 \<and>
     program_counter s3 P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s3 P1 = ''E1'' \<longrightarrow> X_var s3 \<noteq> 1) \<and>
     (program_counter s3 P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s3 P1 \<noteq> 1) \<and>
     program_counter s3 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s3 P2 = ''E1'' \<longrightarrow> X_var s3 \<noteq> 1) \<and>
     (program_counter s3 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s3 P2 \<noteq> 1)"
    using hwq_two_pending_enq_tau_preserves_q1[OF N2 T_TOTAL]
          CALL_SAFE
    by auto

  obtain u_ret_pre u_ret_post where
      TAU_RET_PRE: "C_Tau_Star s3 u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A3 P1 ret)) u_ret_post"
    and TAU_RET_POST: "C_Tau_Star u_ret_post s4"
    using my_C_Match_SomeE[OF M_RET] .

  have PRE_RET:
    "Q_arr u_ret_pre 1 = A1 \<and>
     program_counter u_ret_pre P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_pre P1 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1) \<and>
     (program_counter u_ret_pre P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P1 \<noteq> 1) \<and>
     program_counter u_ret_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_pre P2 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1) \<and>
     (program_counter u_ret_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P2 \<noteq> 1)"
    using hwq_two_pending_enq_tau_preserves_q1[OF N2 TAU_RET_PRE]
          MID_SAFE
    by auto

  have POST_RET:
    "program_counter u_ret_post P1 = ''L0'' \<and>
     Q_arr u_ret_post 1 = A1 \<and>
     program_counter u_ret_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_post P2 = ''E1'' \<longrightarrow> X_var u_ret_post \<noteq> 1) \<and>
     (program_counter u_ret_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_post P2 \<noteq> 1)"
  proof -
    from PRE_RET obtain
        Q1_PRE: "Q_arr u_ret_pre 1 = A1"
      and P1SET_PRE: "program_counter u_ret_pre P1 \<in> {''E1'', ''E2'', ''E3''}"
      and P1E1SAFE_PRE: "(program_counter u_ret_pre P1 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1)"
      and P1I_SAFE_PRE: "(program_counter u_ret_pre P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P1 \<noteq> 1)"
      and P2SET_PRE: "program_counter u_ret_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and P2E1SAFE_PRE: "(program_counter u_ret_pre P2 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_ret_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P2 \<noteq> 1)"
      by blast

    from STEP_RET show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP1 Q1_PRE P2SET_PRE P2E1SAFE_PRE P2I_SAFE_PRE
      show ?thesis
        unfolding Sys_E3_def C_E3_def
                  program_counter_def Q_arr_def X_var_def i_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have FINAL_SAFE:
    "program_counter s4 P1 = ''L0'' \<and>
     program_counter s4 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s4 1 = A1 \<and>
     (program_counter s4 P2 = ''E1'' \<longrightarrow> X_var s4 \<noteq> 1) \<and>
     (program_counter s4 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s4 P2 \<noteq> 1)"
    using hwq_p2_pending_tau_preserves_q1_weak[OF N2 TAU_RET_POST]
          POST_RET
    by auto

  from FINAL_SAFE S4_EQ show ?thesis
    by simp
qed



(* ========================================================================= *)
(* Branch 4.1. *)
(* ========================================================================= *)
lemma hwq_full_e1_P1_quantum_branch:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
      and INV: "system_invariant sk0"
      and X4: "X_var sk0 = 4"
  shows "(Q_arr sk0 1 = A1 \<and>
          ((program_counter sk0 P1 \<in> {''D1'', ''D2''}) \<or>
           (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1)))
        \<or>
        (Q_arr sk0 1 = BOT \<and> program_counter sk0 P1 = ''D4'' \<and> x_var sk0 P1 = A1)"
proof -
  have SPLIT: "e1_labels =
      ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
        Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
        None, None, Some (mk_obs enq A3 P1 ret)]) @
      ([Some (mk_obs deq BOT P1 call), None, None, None, None] @
       [Some (mk_obs enq A2 P2 ret)])"
    unfolding e1_labels_def by simp

  obtain s_before_deq where
      P_PREFIX:
        "C_Path s0
          [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
           Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
           None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    and P_SUFFIX:
        "C_Path s_before_deq
          ([Some (mk_obs deq BOT P1 call), None, None, None, None] @
           [Some (mk_obs enq A2 P2 ret)]) sk0"
    using C_Path_appendE[OF E1FULL[unfolded SPLIT]]
    by blast

  have PREQ1: "Q_arr s_before_deq 1 = A1"
    using hwq_full_e1_pre_deq_q1_shape[OF N2 INIT P_PREFIX] .

  have P2SAFE0: "P2_pending_A2_safe s_before_deq"
    using hwq_full_e1_pre_deq_p2_safe_shape[OF N2 INIT P_PREFIX] .

  have P2SAFE:
    "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1) \<and>
     (program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1)"
    using P2SAFE0
    unfolding P2_pending_A2_safe_def
    by auto

  have PC1_0: "program_counter s_before_deq P1 = ''L0''"
    using hwq_full_e1_pre_deq_p1_l0_shape[OF N2 INIT P_PREFIX] .

  have RS0: "Reachable_Sys s_before_deq"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] P_PREFIX] .

  have INV0: "system_invariant s_before_deq"
    using Reachable_Sys_system_invariant[OF RS0] .

  show ?thesis
    using hwq_quantum_branch_suffix_from_pre_deq[OF N2 INV0 PC1_0 P_SUFFIX PREQ1 P2SAFE] .
qed


(* Bridge 5: set summaryconcrete *)

(* lvyi *)



lemma hwq_full_e1_pre_deq_only_three_enq_calls:
  assumes INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
  (* Model. prefix,, *)
  shows "\<And>q a sn. EnqCallInHis s_before_deq q a sn \<Longrightarrow> a \<in> {A1, A2, A3}"
proof -
  have SPLIT:
    "[Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
      Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A1 P1 call)] @
     [None, None, Some (mk_obs enq A1 P1 ret)] @
     [Some (mk_obs enq A2 P2 call)] @
     [None] @
     [Some (mk_obs enq A3 P1 call)] @
     [None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s1 s2 s3 s4 s5 where
      P1: "C_Path s0 [Some (mk_obs enq A1 P1 call)] s1"
    and P2: "C_Path s1 [None, None, Some (mk_obs enq A1 P1 ret)] s2"
    and P3: "C_Path s2 [Some (mk_obs enq A2 P2 call)] s3"
    and P4: "C_Path s3 [None] s4"
    and P5: "C_Path s4 [Some (mk_obs enq A3 P1 call)] s5"
    and P6: "C_Path s5 [None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using C_Path_appendE[OF PREFIX[unfolded SPLIT]]
    by (meson C_Path_appendE)

  have HIS1:
    "his_seq s1 = his_seq s0 @ [mk_act enq A1 P1 (s_var s0 P1) call]"
    using C_Path_single_enq_call_history[OF P1] .

  have HIS3:
    "his_seq s3 = his_seq s2 @ [mk_act enq A2 P2 (s_var s2 P2) call]"
    using C_Path_single_enq_call_history[OF P3] .

  have HIS5:
    "his_seq s5 = his_seq s4 @ [mk_act enq A3 P1 (s_var s4 P1) call]"
    using C_Path_single_enq_call_history[OF P5] .

  have NO_ENQ_CALL_P2:
    "\<forall>x\<in>set [None, None, Some (mk_obs enq A1 P1 ret)]. \<forall>p a.
       x \<noteq> Some (mk_obs enq a p call)"
    unfolding mk_obs_def by auto

  have NO_ENQ_CALL_P4:
    "\<forall>x\<in>set [None]. \<forall>p a.
       x \<noteq> Some (mk_obs enq a p call)"
    unfolding mk_obs_def by auto

  have NO_ENQ_CALL_P6:
    "\<forall>x\<in>set [None, None, Some (mk_obs enq A3 P1 ret)]. \<forall>p a.
       x \<noteq> Some (mk_obs enq a p call)"
    unfolding mk_obs_def by auto

  (* 1: 4, sn0 *)
  have P2_KEEP:
    "\<And>q0 a0 sn0. EnqCallInHis s2 q0 a0 sn0 \<longleftrightarrow> EnqCallInHis s1 q0 a0 sn0"
    using C_Path_no_enq_call_preserves_EnqCallInHis[OF P2 NO_ENQ_CALL_P2] by blast

  have P4_KEEP:
    "\<And>q0 a0 sn0. EnqCallInHis s4 q0 a0 sn0 \<longleftrightarrow> EnqCallInHis s3 q0 a0 sn0"
    using C_Path_no_enq_call_preserves_EnqCallInHis[OF P4 NO_ENQ_CALL_P4] by blast

  have P6_KEEP:
    "\<And>q0 a0 sn0. EnqCallInHis s_before_deq q0 a0 sn0 \<longleftrightarrow> EnqCallInHis s5 q0 a0 sn0"
    using C_Path_no_enq_call_preserves_EnqCallInHis[OF P6 NO_ENQ_CALL_P6] by blast

  (* 2: direct 4 *)
  fix q a sn
  assume EC_FINAL: "EnqCallInHis s_before_deq q a sn"

  have EC5: "EnqCallInHis s5 q a sn"
    using EC_FINAL P6_KEEP[of q a sn] by blast

  have EC4:
    "EnqCallInHis s4 q a sn \<or> (q = P1 \<and> a = A3)"
    using EC5 EnqCallInHis_append_enq_call_iff[OF HIS5]
    by auto

  (* 3: alignment, proof - qed by auto *)
  have EC3:
    "EnqCallInHis s3 q a sn \<or> (q = P1 \<and> a = A3)"
    using EC4 P4_KEEP[of q a sn] by auto

  have EC2:
    "EnqCallInHis s2 q a sn \<or> (q = P2 \<and> a = A2) \<or> (q = P1 \<and> a = A3)"
    using EC3 EnqCallInHis_append_enq_call_iff[OF HIS3]
    by auto

  have EC1:
    "EnqCallInHis s1 q a sn \<or> (q = P2 \<and> a = A2) \<or> (q = P1 \<and> a = A3)"
    using EC2 P2_KEEP[of q a sn] by auto

  have EC0:
    "EnqCallInHis s0 q a sn \<or> (q = P1 \<and> a = A1) \<or> (q = P2 \<and> a = A2) \<or> (q = P1 \<and> a = A3)"
    using EC1 EnqCallInHis_append_enq_call_iff[OF HIS1]
    by auto

  have NO0: "\<not> EnqCallInHis s0 q a sn"
    using Init_no_EnqCallInHis[OF INIT] .

  from EC0 NO0 show "a \<in> {A1, A2, A3}"
    by auto
qed


lemma hwq_full_e1_pre_deq_no_A1_in_slots23:
  assumes INV0: "system_invariant s_before_deq"
      and PREQ1: "Q_arr s_before_deq 1 = A1"
  shows "Q_arr s_before_deq 2 \<noteq> A1 \<and> Q_arr s_before_deq 3 \<noteq> A1"
proof -
  (* : extract, system_invariantE unfold *)
  have S8: "sI8_Q_Qback_Sync s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  have S10: "sI10_Qback_Unique_Vals s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  (* Proof step. *)
  have QB1: "Qback_arr s_before_deq 1 = A1"
    using PREQ1 S8
    unfolding sI8_Q_Qback_Sync_def
    by (metis BOT_def zero_neq_one)

  have NO2: "Q_arr s_before_deq 2 \<noteq> A1"
  proof
    assume H: "Q_arr s_before_deq 2 = A1"
    have QB2: "Qback_arr s_before_deq 2 = A1"
      using H S8
      unfolding sI8_Q_Qback_Sync_def
      by (metis BOT_def One_nat_def Zero_not_Suc)
    from S10 QB1 QB2 show False
      unfolding sI10_Qback_Unique_Vals_def
      by (metis BOT_def numeral_eq_one_iff semiring_norm(85)
          zero_neq_one)
  qed

  have NO3: "Q_arr s_before_deq 3 \<noteq> A1"
  proof
    assume H: "Q_arr s_before_deq 3 = A1"
    have QB3: "Qback_arr s_before_deq 3 = A1"
      using H S8
      unfolding sI8_Q_Qback_Sync_def
      by (metis BOT_def zero_neq_one)
    from S10 QB1 QB3 show False
      unfolding sI10_Qback_Unique_Vals_def
      by (metis BOT_def Suc_0_mod_numeral(1,3) numeral_One
          zero_neq_one)
  qed

  show ?thesis
    using NO2 NO3 by auto
qed

(* ========================================================================= *)
(* Core local safeguard: single-step Tau A3 (unchanged P2) *)
(* ========================================================================= *)
lemma C_Tau_preserves_specific_Qback_slot_after_A3_ret:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys s"
      and TAU: "C_Tau s s'"
      and P1L0: "program_counter s P1 = ''L0''"
      and P2SET: "program_counter s P2 \<in> {''E1'', ''E2'', ''E3''}"
      and KVAL: "Qback_arr s k = A3"
  shows "Qback_arr s' k = A3"
proof -
  have INV: "system_invariant s"
    using Reachable_Sys_system_invariant[OF RS] .

  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp

  obtain p where PIN: "p \<in> ProcSet"
    and STEP: "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    using STEP0 by (cases rule: C_StepCR.cases) auto

  have p_cases: "p = P1 \<or> p = P2"
    using PIN N2 by auto

  from p_cases show ?thesis
  proof
    assume pP1: "p = P1"
    from STEP show ?thesis
      using pP1 P1L0
      unfolding Sys_E1_def Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def
                C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def
                T_D2_EnterLoop_def program_counter_def Let_def Qback_arr_def
      by auto
  next
    assume pP2: "p = P2"
    from STEP show ?thesis
    proof (elim disjE)
      assume H: "Sys_E1 p s s'"
      then show ?thesis
        using pP2 KVAL
        unfolding Sys_E1_def C_E1_def Let_def Qback_arr_def
        by auto
    next
      assume H: "Sys_E2 p s s'"
      have S3: "sI3_E2_Slot_Exclusive s"
        using INV unfolding system_invariant_def by auto

      have PCE2: "program_counter s P2 = ''E2''"
        using H pP2
        unfolding Sys_E2_def C_E2_def program_counter_def Let_def
        by auto

      have IK: "i_var s P2 \<noteq> k"
      proof
        assume EQ: "i_var s P2 = k"
        have "Qback_arr s (i_var s P2) = BOT"
          using S3 PCE2
          unfolding sI3_E2_Slot_Exclusive_def
          by auto
        with KVAL EQ show False
          using BOT_def by auto
      qed

      then show ?thesis
        using H pP2 KVAL
        unfolding Sys_E2_def C_E2_def Let_def Qback_arr_def i_var_def
        by auto
    next
      assume H: "Sys_D1 p s s'"
      then show ?thesis
        using pP2 KVAL P2SET
        unfolding Sys_D1_def C_D1_def Let_def Qback_arr_def program_counter_def
        by auto
    next
      assume H: "Sys_D2 p s s'"
      then show ?thesis
        using pP2 KVAL P2SET
        unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def Let_def Qback_arr_def program_counter_def
        by auto
    next
      assume H: "Sys_D3 p s s'"
      then show ?thesis
        using pP2 KVAL P2SET
        unfolding Sys_D3_def C_D3_def Let_def Qback_arr_def program_counter_def
        by auto
    qed
  qed
qed

(* ========================================================================= *)
(* Core inductive propagation: single-stepinvariant guard Tau* *)
(* ========================================================================= *)
lemma C_Tau_Star_preserves_specific_Qback_slot_after_A3_ret:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys s"
      and TAUS: "C_Tau_Star s s'"
      and P1L0: "program_counter s P1 = ''L0''"
      and P2SET: "program_counter s P2 \<in> {''E1'', ''E2'', ''E3''}"
      and KVAL: "Qback_arr s k = A3"
  shows "Qback_arr s' k = A3"
  using TAUS RS P1L0 P2SET KVAL
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have K2: "Qback_arr s2 k = A3"
    using C_Tau_preserves_specific_Qback_slot_after_A3_ret
          [OF N2 step.prems(1) step.hyps(1) step.prems(2) step.prems(3) step.prems(4)] .

have STEP12: "C_StepCR s1 None s2"
  using step.hyps(1) unfolding C_Tau_def by simp

have NXT12: "Next s1 s2"
  using C_StepCR_into_Next[OF STEP12] .

have RS_2: "Reachable_Sys s2"
proof -
  have "Reachable_Sys s1" using step.prems(1) .
  moreover have "Next s1 s2" using NXT12 .
  ultimately show "Reachable_Sys s2"
    by (rule Reachable_Sys.step)
qed

obtain p where PIN: "p \<in> ProcSet"
  and STEPp: "Sys_E1 p s1 s2 \<or> Sys_E2 p s1 s2 \<or> Sys_D1 p s1 s2 \<or> Sys_D2 p s1 s2 \<or> Sys_D3 p s1 s2"
  using STEP12 by (cases rule: C_StepCR.cases) auto

have p_cases: "p = P1 \<or> p = P2"
  using PIN N2 by auto

have P1L0_2: "program_counter s2 P1 = ''L0''"
proof -
  from p_cases show ?thesis
  proof
    assume pP1: "p = P1"
    from STEPp show ?thesis
      using pP1 step.prems(2)
      unfolding Sys_E1_def Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def
                C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def
                T_D2_EnterLoop_def program_counter_def Let_def
      by auto
  next
    assume pP2: "p = P2"
    from STEPp show ?thesis
      using pP2 step.prems(2)
      unfolding Sys_E1_def Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def
                C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def
                T_D2_EnterLoop_def program_counter_def Let_def
      using STEPp hwq_other_proc_preserves_pc program_counter_def
      by auto
  qed
qed

  have P2SET_2: "program_counter s2 P2 \<in> {''E1'', ''E2'', ''E3''}"
    using step.hyps(1) step.prems(3)
    unfolding C_Tau_def
    by (cases rule: C_StepCR.cases)
       (auto simp: Sys_E1_def Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def
                   C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def
                   T_D2_EnterLoop_def program_counter_def Let_def
             split: if_splits)

  show ?case
    using step.IH[OF RS_2 P1L0_2 P2SET_2 K2] .
qed


lemma hwq_a3_segment_qback_final:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and P_A1: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
      and P12: "C_Path s_a1_ret [Some (mk_obs enq A2 P2 call), None] s_mid"
      and TPRE: "C_Tau_Star s_mid u_call_pre"
      and STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A3 P1 call)) u_call_post"
      and TPOST: "C_Tau_Star u_call_post s1"
      and M_N1: "C_Match s1 None s2"
      and M_N2: "C_Match s2 None s3"
      and T_RET_PRE: "C_Tau_Star s3 u_ret_pre"
      and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A3 P1 ret)) u_ret_post"
      and T_RET_POST: "C_Tau_Star u_ret_post s_before_deq"
      and QB_POST: "Qback_arr u_ret_post (i_var u_ret_pre P1) = A3"
      and P1_L0: "program_counter u_ret_post P1 = ''L0''"
  shows "Qback_arr s_before_deq (i_var u_ret_pre P1) = A3"
proof -
  have SNAP_A1:
    "program_counter s_a1_ret P1 = ''L0'' \<and>
     program_counter s_a1_ret P2 = ''L0'' \<and>
     Q_arr s_a1_ret 1 = A1"
    using hwq_a1_segment_q1_shape[OF N2 INIT P_A1] .

  have XNZ_A1: "X_var s_a1_ret \<noteq> 1"
    using hwq_a1_segment_XNZ[OF N2 INIT P_A1] .

  have MID_SNAP:
    "program_counter s_mid P1 = ''L0'' \<and>
     program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s_mid 1 = A1 \<and>
     X_var s_mid \<noteq> 1 \<and>
     (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    using hwq_a2_call_tau_preserves_q1[OF N2 P12 SNAP_A1 XNZ_A1] .

  from MID_SNAP have PC1_0: "program_counter s_mid P1 = ''L0''"
    and P2SET_0: "program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''}"
    and Q1_0: "Q_arr s_mid 1 = A1"
    and XNZ_0: "X_var s_mid \<noteq> 1"
    and I2NZ_0: "(program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    by auto

  have PRE_SAFE:
    "program_counter u_call_pre P1 = ''L0'' \<and>
     program_counter u_call_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr u_call_pre 1 = A1 \<and>
     (program_counter u_call_pre P2 = ''E1'' \<longrightarrow> X_var u_call_pre \<noteq> 1) \<and>
     (program_counter u_call_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_pre P2 \<noteq> 1)"
    using hwq_p2_pending_tau_preserves_q1_weak[OF N2 TPRE PC1_0 P2SET_0 _ I2NZ_0 Q1_0]
          XNZ_0
    by auto

  have CALL_SAFE:
    "program_counter u_call_post P1 = ''E1'' \<and>
     (program_counter u_call_post P1 = ''E1'' \<longrightarrow> X_var u_call_post \<noteq> 1) \<and>
     (program_counter u_call_post P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_post P1 \<noteq> 1) \<and>
     program_counter u_call_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_call_post P2 = ''E1'' \<longrightarrow> X_var u_call_post \<noteq> 1) \<and>
     (program_counter u_call_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_post P2 \<noteq> 1) \<and>
     Q_arr u_call_post 1 = A1"
  proof -
    from PRE_SAFE obtain
        PC1_PRE: "program_counter u_call_pre P1 = ''L0''"
      and P2SET_PRE: "program_counter u_call_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and Q1_PRE: "Q_arr u_call_pre 1 = A1"
      and P2E1SAFE_PRE: "(program_counter u_call_pre P2 = ''E1'' \<longrightarrow> X_var u_call_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_call_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_call_pre P2 \<noteq> 1)"
      by blast

    from STEP_CALL show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_enq_vis p)
      have pP1: "p = P1"
        using C_Sys_L0_enq_vis unfolding mk_obs_def by auto

      have INV_PRE: "system_invariant u_call_pre"
        using C_Sys_L0_enq_vis unfolding Sys_L0_def by blast

      have XNZ_PRE: "X_var u_call_pre \<noteq> 1"
      proof
        assume X1: "X_var u_call_pre = 1"
        have S2: "sI2_X_var_Upper_Bound u_call_pre"
          using INV_PRE unfolding system_invariant_def by auto
        have QBOT: "Q_arr u_call_pre 1 = BOT"
          using S2 X1
          unfolding sI2_X_var_Upper_Bound_def
          by auto
        from Q1_PRE QBOT show False
          using BOT_def by linarith
      qed

      from C_Sys_L0_enq_vis pP1 PC1_PRE Q1_PRE P2SET_PRE P2E1SAFE_PRE P2I_SAFE_PRE XNZ_PRE
      show ?thesis
        unfolding Sys_L0_def C_L0_def
                  program_counter_def X_var_def i_var_def Q_arr_def v_var_def V_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have T1: "C_Tau_Star s1 s2"
    using my_C_Match_NoneE[OF M_N1] .

  have T2: "C_Tau_Star s2 s3"
    using my_C_Match_NoneE[OF M_N2] .

  have T12: "C_Tau_Star s1 s3"
    using C_Tau_Star_trans[OF T1 T2] .

  have T_TOTAL: "C_Tau_Star u_call_post s3"
    using C_Tau_Star_trans[OF TPOST T12] .

  have MID_SAFE:
    "Q_arr s3 1 = A1 \<and>
     program_counter s3 P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s3 P1 = ''E1'' \<longrightarrow> X_var s3 \<noteq> 1) \<and>
     (program_counter s3 P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s3 P1 \<noteq> 1) \<and>
     program_counter s3 P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s3 P2 = ''E1'' \<longrightarrow> X_var s3 \<noteq> 1) \<and>
     (program_counter s3 P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s3 P2 \<noteq> 1)"
    using hwq_two_pending_enq_tau_preserves_q1[OF N2 T_TOTAL] CALL_SAFE
    by auto

  have PRE_RET:
    "Q_arr u_ret_pre 1 = A1 \<and>
     program_counter u_ret_pre P1 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_pre P1 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1) \<and>
     (program_counter u_ret_pre P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P1 \<noteq> 1) \<and>
     program_counter u_ret_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_pre P2 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1) \<and>
     (program_counter u_ret_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P2 \<noteq> 1)"
    using hwq_two_pending_enq_tau_preserves_q1[OF N2 T_RET_PRE] MID_SAFE
    by auto

  have POST_RET:
    "program_counter u_ret_post P1 = ''L0'' \<and>
     Q_arr u_ret_post 1 = A1 \<and>
     program_counter u_ret_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter u_ret_post P2 = ''E1'' \<longrightarrow> X_var u_ret_post \<noteq> 1) \<and>
     (program_counter u_ret_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_post P2 \<noteq> 1)"
  proof -
    from PRE_RET obtain
        Q1_PRE: "Q_arr u_ret_pre 1 = A1"
      and P1SET_PRE: "program_counter u_ret_pre P1 \<in> {''E1'', ''E2'', ''E3''}"
      and P1E1SAFE_PRE: "(program_counter u_ret_pre P1 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1)"
      and P1I_SAFE_PRE: "(program_counter u_ret_pre P1 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P1 \<noteq> 1)"
      and P2SET_PRE: "program_counter u_ret_pre P2 \<in> {''E1'', ''E2'', ''E3''}"
      and P2E1SAFE_PRE: "(program_counter u_ret_pre P2 = ''E1'' \<longrightarrow> X_var u_ret_pre \<noteq> 1)"
      and P2I_SAFE_PRE: "(program_counter u_ret_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_ret_pre P2 \<noteq> 1)"
      by blast

    from STEP_RET show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have pP1: "p = P1"
        unfolding mk_obs_def by auto
      from C_Sys_E3_vis pP1 Q1_PRE P2SET_PRE P2E1SAFE_PRE P2I_SAFE_PRE
      show ?thesis
        unfolding Sys_E3_def C_E3_def
                  program_counter_def Q_arr_def X_var_def i_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have RS_a1: "Reachable_Sys s_a1_ret"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] P_A1] .

  have RS_mid: "Reachable_Sys s_mid"
    using C_Path_reachable[OF RS_a1 P12] .

  have RS_call_pre: "Reachable_Sys u_call_pre"
    using C_Tau_Star_reachable[OF RS_mid TPRE] .

  have NXT_CALL: "Next u_call_pre u_call_post"
    using C_StepCR_into_Next[OF STEP_CALL] .

  have RS_call_post: "Reachable_Sys u_call_post"
    using RS_call_pre NXT_CALL
    by (meson Reachable_Sys.step)

  have RS_s1: "Reachable_Sys s1"
    using C_Tau_Star_reachable[OF RS_call_post TPOST] .

  have RS_s2: "Reachable_Sys s2"
    using C_Tau_Star_reachable[OF RS_s1 T1] .

  have RS_s3: "Reachable_Sys s3"
    using C_Tau_Star_reachable[OF RS_s2 T2] .

  have RS_pre: "Reachable_Sys u_ret_pre"
    using C_Tau_Star_reachable[OF RS_s3 T_RET_PRE] .

  have NXT_RET: "Next u_ret_pre u_ret_post"
    using C_StepCR_into_Next[OF STEP_RET] .

  have RS_post: "Reachable_Sys u_ret_post"
    using RS_pre NXT_RET
    by (meson Reachable_Sys.step)

  have QB_FINAL: "Qback_arr s_before_deq (i_var u_ret_pre P1) = A3"
  proof -
    from POST_RET obtain
      P2SET_POST: "program_counter u_ret_post P2 \<in> {''E1'', ''E2'', ''E3''}"
      by blast

    show ?thesis
      using C_Tau_Star_preserves_specific_Qback_slot_after_A3_ret
              [OF N2 RS_post T_RET_POST P1_L0 P2SET_POST QB_POST] .
  qed

  show ?thesis
    using QB_FINAL .
qed


lemma hwq_full_e1_pre_deq_A3_in_Qback_from_segment:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
      and PREQ1: "Q_arr s_before_deq 1 = A1"
      and P2SAFE:
        "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
         (program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1) \<and>
         (program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1)"
  shows "\<exists>k\<in>{2,3}. Qback_arr s_before_deq k = A3"
proof -
  have SPLIT:
    "[Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
      Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
      None, None, Some (mk_obs enq A3 P1 ret)]
     =
     [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @
     [Some (mk_obs enq A2 P2 call), None] @
     [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]"
    by simp

  obtain s_a1_ret s_mid where
      P_A1: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] s_a1_ret"
    and P12: "C_Path s_a1_ret [Some (mk_obs enq A2 P2 call), None] s_mid"
    and P34: "C_Path s_mid
        [Some (mk_obs enq A3 P1 call), None, None, Some (mk_obs enq A3 P1 ret)]
        s_before_deq"
    using C_Path_appendE[OF PREFIX[unfolded SPLIT]]
    using C_Path_appendE by blast


  have SNAP_A1:
    "program_counter s_a1_ret P1 = ''L0'' \<and>
     program_counter s_a1_ret P2 = ''L0'' \<and>
     Q_arr s_a1_ret 1 = A1"
    using hwq_a1_segment_q1_shape[OF N2 INIT P_A1] .

  have XNZ_A1: "X_var s_a1_ret \<noteq> 1"
    using hwq_a1_segment_XNZ[OF N2 INIT P_A1] .

  have MID_SNAP:
    "program_counter s_mid P1 = ''L0'' \<and>
     program_counter s_mid P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     Q_arr s_mid 1 = A1 \<and>
     X_var s_mid \<noteq> 1 \<and>
     (program_counter s_mid P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_mid P2 \<noteq> 1)"
    using hwq_a2_call_tau_preserves_q1[OF N2 P12 SNAP_A1 XNZ_A1] .

  obtain s1 where
      M_CALL: "C_Match s_mid (Some (mk_obs enq A3 P1 call)) s1"
    and P_REST1: "C_Path s1 [None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P34] .

  obtain u_call_pre u_call_post where
      TPRE: "C_Tau_Star s_mid u_call_pre"
    and STEP_CALL: "C_StepCR u_call_pre (Some (mk_obs enq A3 P1 call)) u_call_post"
    and TPOST: "C_Tau_Star u_call_post s1"
    using my_C_Match_SomeE[OF M_CALL] .

  obtain s2 where
      M_N1: "C_Match s1 None s2"
    and P_REST2: "C_Path s2 [None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P_REST1] .

  obtain s3 where
      M_N2: "C_Match s2 None s3"
    and P_REST3: "C_Path s3 [Some (mk_obs enq A3 P1 ret)] s_before_deq"
    using my_C_Path_ConsE[OF P_REST2] .

  obtain s4 where
      M_RET: "C_Match s3 (Some (mk_obs enq A3 P1 ret)) s4"
    and P_EMP: "C_Path s4 [] s_before_deq"
    using my_C_Path_ConsE[OF P_REST3] .

  have S4_EQ: "s4 = s_before_deq"
    using P_EMP by (cases rule: C_Path.cases) auto

  obtain u_ret_pre u_ret_post where
      T_RET_PRE: "C_Tau_Star s3 u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A3 P1 ret)) u_ret_post"
    and T_RET_POST: "C_Tau_Star u_ret_post s_before_deq"
    using my_C_Match_SomeE[OF M_RET] S4_EQ by blast

  have P_S_MID:
    "C_Path s0
      ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret)] @
       [Some (mk_obs enq A2 P2 call), None]) s_mid"
    using C_Path_append P12 P_A1 by blast

  have RS_mid: "Reachable_Sys s_mid"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] P_S_MID] .

  have RS_s1: "Reachable_Sys s1"
    using C_Match_reachable[OF RS_mid M_CALL] .

  have RS_s2: "Reachable_Sys s2"
    using C_Match_reachable[OF RS_s1 M_N1] .

  have RS_s3: "Reachable_Sys s3"
    using C_Match_reachable[OF RS_s2 M_N2] .

  have RS_pre: "Reachable_Sys u_ret_pre"
    using C_Tau_Star_reachable[OF RS_s3 T_RET_PRE] .

  have INV_pre: "system_invariant u_ret_pre"
    using Reachable_Sys_system_invariant[OF RS_pre] .

  (* 1: extract, system_invariantE *)
  have SI4p: "sI4_E3_Qback_Written u_ret_pre"
    using INV_pre unfolding system_invariant_def by auto
  have S8p: "sI8_Q_Qback_Sync u_ret_pre"
    using INV_pre unfolding system_invariant_def by auto

  have PC_E3: "program_counter u_ret_pre P1 = ''E3''"
  proof -
    from STEP_RET show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      then have "p = P1"
        unfolding mk_obs_def by auto
      with C_Sys_E3_vis show ?thesis
        unfolding Sys_E3_def C_E3_def program_counter_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  have V_PRE: "v_var u_ret_pre P1 = A3"
  proof -
    from STEP_RET show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_E3_vis p)
      (* unfold mk_obs v_var definition, directalignment, unfoldstate *)
      thus ?thesis 
        unfolding mk_obs_def v_var_def 
        by auto
    qed (auto simp: mk_obs_def)
  qed

  have QB_PRE: "Qback_arr u_ret_pre (i_var u_ret_pre P1) = A3"
    using SI4p PC_E3 V_PRE
    unfolding sI4_E3_Qback_Written_def
    by auto

  have I_PRE_LT: "i_var u_ret_pre P1 < X_var u_ret_pre"
    using SI4p PC_E3
    unfolding sI4_E3_Qback_Written_def
    by auto


  (* ======================================================================= *)
  (* : extract STEP_RET (E3) directconcrete *)
  (* ======================================================================= *)
    have QB_PRE_raw:
      "CState.Qback_arr (fst u_ret_pre) (CState.i_var (fst u_ret_pre) P1) = A3"
      using QB_PRE
      unfolding Qback_arr_def i_var_def
      by simp

    have QB_POST: "Qback_arr u_ret_post (i_var u_ret_pre P1) = A3"
    proof -
      from STEP_RET show ?thesis
      proof (cases rule: C_StepCR.cases)
        case (C_Sys_E3_vis p)
        then have pP1: "p = P1"
          unfolding mk_obs_def by auto
        from QB_PRE_raw C_Sys_E3_vis pP1 show ?thesis
          unfolding Sys_E3_def C_E3_def Qback_arr_def i_var_def
          by (auto split: if_splits)
      qed (auto simp: mk_obs_def)
    qed

    have P1_L0: "program_counter u_ret_post P1 = ''L0''"
    proof -
      from STEP_RET show ?thesis
      proof (cases rule: C_StepCR.cases)
        case (C_Sys_E3_vis p)
        then have pP1: "p = P1" unfolding mk_obs_def by auto
        with C_Sys_E3_vis show ?thesis 
          unfolding Sys_E3_def C_E3_def program_counter_def Let_def 
          by (auto split: if_splits)
      qed (auto simp: mk_obs_def)
    qed


  have CREDIT0: "E1_credit s0 = 0"
    using INIT
    unfolding Init_def E1_credit_def program_counter_def
    by auto

  have X0: "X_var s0 = 1"
    using INIT
    unfolding Init_def X_var_def
    by auto

  have SUM3:
    "sum_list
      (map is_enq_call_opt
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)]) = 3"
    unfolding is_enq_call_opt_def is_enq_call_cr_def mk_obs_def
    by simp

  have POT_BEFORE_DEQ:
    "X_var s_before_deq + E1_credit s_before_deq =
     X_var s0 + E1_credit s0 +
     sum_list
      (map is_enq_call_opt
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)])"
    using C_Path_potential_eq[OF N2 PREFIX] .

  have POT_BEFORE_DEQ_4:
    "X_var s_before_deq + E1_credit s_before_deq = 4"
    using POT_BEFORE_DEQ CREDIT0 X0 SUM3
    by simp

  have POT_RET_POST:
    "X_var s_before_deq + E1_credit s_before_deq =
     X_var u_ret_post + E1_credit u_ret_post"
    using C_Tau_Star_potential_eq[OF N2 T_RET_POST]
    by simp

  have POT_STEP_RET:
    "X_var u_ret_post + E1_credit u_ret_post =
     X_var u_ret_pre + E1_credit u_ret_pre"
    using C_StepCR_Vis_potential_eq[OF N2 STEP_RET]
    unfolding is_enq_call_cr_def mk_obs_def
    by simp

  have POT_PRE_4:
    "X_var u_ret_pre + E1_credit u_ret_pre = 4"
    using POT_BEFORE_DEQ_4 POT_RET_POST POT_STEP_RET
    by arith

  have X_LE_4: "X_var u_ret_pre \<le> 4"
    using POT_PRE_4
    unfolding E1_credit_def
    by auto



have QB_FINAL: "Qback_arr s_before_deq (i_var u_ret_pre P1) = A3"
  using hwq_a3_segment_qback_final[OF N2 INIT P_A1 P12 TPRE STEP_CALL TPOST M_N1 M_N2 T_RET_PRE STEP_RET T_RET_POST QB_POST P1_L0] .

have RS_fin: "Reachable_Sys s_before_deq"
  using C_Path_reachable[OF Reachable_Sys.init[OF INIT] PREFIX] .

have INV_fin: "system_invariant s_before_deq"
  using Reachable_Sys_system_invariant[OF RS_fin] .

have S8_fin: "sI8_Q_Qback_Sync s_before_deq"
  using INV_fin unfolding system_invariant_def by auto

have I_NE_1: "i_var u_ret_pre P1 \<noteq> 1"
proof
  assume I1: "i_var u_ret_pre P1 = 1"
  have QB1_fin: "Qback_arr s_before_deq 1 = A1"
    using PREQ1 S8_fin
    unfolding sI8_Q_Qback_Sync_def
    by (metis BOT_def zero_neq_one)
  have "Qback_arr s_before_deq 1 = A3"
    using QB_FINAL I1 by simp
  with QB1_fin show False
    by simp
qed

have I_IN_23: "i_var u_ret_pre P1 \<in> {2,3}"
proof -
  have I_POS: "i_var u_ret_pre P1 > 0"
    using SI4p PC_E3
    unfolding sI4_E3_Qback_Written_def Val_def
    by auto
  from I_PRE_LT X_LE_4 I_POS I_NE_1 show ?thesis
    by auto
qed

  from I_IN_23 QB_FINAL show ?thesis
    by blast
qed

lemma DeqRetInHis_append_non_deq_ret_iff:
  assumes HIS: "his_seq s' = his_seq s @ [e]"
      and NON: "act_name e \<noteq> deq \<or> act_cr e \<noteq> ret"
  shows "DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
  using HIS NON
  unfolding DeqRetInHis_def Model.DeqRetInHis_def
  by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

lemma C_Match_no_deq_ret_preserves_DeqRetInHis:
  assumes MATCH: "C_Match s l s'"
      and NO_DEQ_RET: "\<forall>p a. l \<noteq> Some (mk_obs deq a p ret)"
  shows "DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
  using MATCH
proof (cases rule: C_Match.cases)
  case match_tau
  then have TS: "C_Tau_Star s s'" by auto
  show ?thesis
    using C_Tau_Star_preserves_his_seq[OF TS]
    unfolding DeqRetInHis_def Model.DeqRetInHis_def
    by auto
next
  case match_vis
  then obtain u obs v where
      L_EQ: "l = Some obs"
    and T1: "C_Tau_Star s u"
    and V_STEP: "C_StepCR u (Some obs) v"
    and T2: "C_Tau_Star v s'"
    by auto

  have PRE: "his_seq u = his_seq s"
    using C_Tau_Star_preserves_his_seq[OF T1] .

  have POST: "his_seq s' = his_seq v"
    using C_Tau_Star_preserves_his_seq[OF T2] .

  have PRE_KEEP: "DeqRetInHis u q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
    using PRE
    unfolding DeqRetInHis_def Model.DeqRetInHis_def
    by auto

  have POST_KEEP: "DeqRetInHis s' q a sn \<longleftrightarrow> DeqRetInHis v q a sn"
    using POST
    unfolding DeqRetInHis_def Model.DeqRetInHis_def
    by auto

  have STEP_KEEP: "DeqRetInHis v q a sn \<longleftrightarrow> DeqRetInHis u q a sn"
    using V_STEP
  proof (cases rule: C_StepCR.cases)
    case (C_Sys_L0_enq_vis p)
    have L0STEP: "L0 p u v"
      using C_Sys_L0_enq_vis unfolding L0_def by auto
    have PC_E1: "program_counter v p = ''E1''"
      using C_Sys_L0_enq_vis unfolding Sys_L0_def C_L0_def program_counter_def Let_def
      by (auto split: if_splits)
    have HIS: "his_seq v = his_seq u @ [mk_act enq (V_var u) p (s_var u p) call]"
      using L0_E1_history_append[OF L0STEP PC_E1] .
    have NON: "act_name (mk_act enq (V_var u) p (s_var u p) call) \<noteq> deq \<or>
               act_cr (mk_act enq (V_var u) p (s_var u p) call) \<noteq> ret"
      by (simp add: mk_act_def act_name_def act_cr_def)
    show ?thesis
      using DeqRetInHis_append_non_deq_ret_iff[OF HIS NON] .
  next
    case (C_Sys_L0_deq_vis p)
    have L0STEP: "L0 p u v"
      using C_Sys_L0_deq_vis unfolding L0_def by auto
    have PCD1: "program_counter v p = ''D1''"
      using C_Sys_L0_deq_vis unfolding Sys_L0_def C_L0_def program_counter_def Let_def
      by (auto split: if_splits)
    have HIS: "his_seq v = his_seq u @ [mk_act deq BOT p (s_var u p) call]"
      using L0_D1_history_append[OF L0STEP PCD1] .
    have NON: "act_name (mk_act deq BOT p (s_var u p) call) \<noteq> deq \<or>
               act_cr (mk_act deq BOT p (s_var u p) call) \<noteq> ret"
      by (simp add: mk_act_def act_name_def act_cr_def)
    show ?thesis
      using DeqRetInHis_append_non_deq_ret_iff[OF HIS NON] .
  next
    case (C_Sys_E3_vis p)
    obtain us_mid where
        U3: "U_E3 p (CState.v_var (fst u) p) (s_var u p) (snd u) us_mid"
      and U4: "U_E4 p us_mid (snd v)"
      using C_Sys_E3_vis(2) unfolding Sys_E3_def
      using Sys_E3_def local.C_Sys_E3_vis(3) by blast 
    have HIS: "his_seq v = his_seq u @ [mk_act enq (v_var u p) p (s_var u p) ret]"
      using U3 U4 unfolding his_seq_def v_var_def s_var_def U_E3_def U_E4_def by auto
    have NON: "act_name (mk_act enq (v_var u p) p (s_var u p) ret) \<noteq> deq \<or>
               act_cr (mk_act enq (v_var u p) p (s_var u p) ret) \<noteq> ret"
      by (simp add: mk_act_def act_name_def act_cr_def)
    show ?thesis
      using DeqRetInHis_append_non_deq_ret_iff[OF HIS NON] .
  next
    case (C_Sys_D4_vis p)
    then have "Some obs = Some (mk_obs deq (x_var u p) p ret)"
      unfolding mk_obs_def by auto
    hence "obs = mk_obs deq (x_var u p) p ret" by simp
    with L_EQ have "l = Some (mk_obs deq (x_var u p) p ret)" by simp
    with NO_DEQ_RET show ?thesis by blast
  qed

  from PRE_KEEP STEP_KEEP POST_KEEP show ?thesis
    by blast
qed


lemma C_Path_no_deq_ret_preserves_DeqRetInHis:
  assumes PATH: "C_Path s labs t"
      and NO_DEQ_RET: "\<forall>x\<in>set labs. \<forall>p a. x \<noteq> Some (mk_obs deq a p ret)"
  shows "DeqRetInHis t q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
  using PATH NO_DEQ_RET
proof (induction rule: C_Path.induct)
  case nil
  then show ?case by simp
next
  case (cons s l s1 ls s2)
  have NO_HEAD: "\<forall>p a. l \<noteq> Some (mk_obs deq a p ret)"
    using cons.prems by auto

  have NO_TAIL: "\<forall>x\<in>set ls. \<forall>p a. x \<noteq> Some (mk_obs deq a p ret)"
    using cons.prems by auto

  have HEAD_KEEP: "DeqRetInHis s1 q a sn \<longleftrightarrow> DeqRetInHis s q a sn"
    using C_Match_no_deq_ret_preserves_DeqRetInHis[OF cons.hyps(1) NO_HEAD] .

  have TAIL_KEEP: "DeqRetInHis s2 q a sn \<longleftrightarrow> DeqRetInHis s1 q a sn"
    using cons.IH[OF NO_TAIL] .

  from HEAD_KEEP TAIL_KEEP show ?case
    by blast
qed

lemma Init_no_DeqRetInHis:
  assumes INIT: "Init s0"
  shows "\<not> DeqRetInHis s0 q a sn"
  using INIT
  unfolding DeqRetInHis_def Init_def his_seq_def
  by auto

lemma Reachable_nonL0_in_ProcSet:
  assumes RS: "Reachable_Sys s"
      and NZ: "program_counter s p \<noteq> ''L0''"
  shows "p \<in> ProcSet"
  using RS NZ
proof (induction rule: Reachable_Sys.induct)
  case (init s)
  then show ?case
    unfolding Init_def program_counter_def ProcSet_def
    by auto
next
  case (step s t)
  from step.prems have NZt: "program_counter t p \<noteq> ''L0''" .

  from step.hyps(2) obtain q where
      QIN: "q \<in> ProcSet"
    and NXT:
      "Sys_L0 q s t \<or> Sys_E1 q s t \<or> Sys_E2 q s t \<or> Sys_E3 q s t \<or>
       Sys_D1 q s t \<or> Sys_D2 q s t \<or> Sys_D3 q s t \<or> Sys_D4 q s t"
    unfolding Next_def
    by auto

  show ?case
  proof (cases "p = q")
    case True
    then show ?thesis
      using QIN by simp
  next
    case False
    have PCT: "program_counter t p = program_counter s p"
      using NXT False
      unfolding
        Sys_L0_def Sys_E1_def Sys_E2_def Sys_E3_def
        Sys_D1_def Sys_D2_def Sys_D3_def Sys_D4_def
        C_L0_def C_E1_def C_E2_def C_E3_def
        C_D1_def C_D2_def C_D3_def C_D4_def
        T_D2_EnterLoop_def
        program_counter_def Let_def
      by (auto split: if_splits)

    have "program_counter s p \<noteq> ''L0''"
      using NZt PCT by simp

    then show ?thesis
      using step.IH by blast
  qed
qed

lemma hwq_full_e1_pre_deq_QbackA3_implies_QarrA3:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
      and INV0: "system_invariant s_before_deq"
      and QBK: "Qback_arr s_before_deq k = A3"
      and K23: "k \<in> {2,3}"
  shows "Q_arr s_before_deq k = A3"
proof -
  have TYPEOK: "TypeOK s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  have S8: "sI8_Q_Qback_Sync s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  have H13: "hI13_Qback_Deq_Sync s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  have P1L0: "program_counter s_before_deq P1 = ''L0''"
    using hwq_full_e1_pre_deq_p1_l0_shape[OF N2 INIT PREFIX] .

  have P2SAFE:
    "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''}"
    using hwq_full_e1_pre_deq_p2_safe_shape[OF N2 INIT PREFIX]
    using INIT Init_no_EnqCallInHis
      hI10_Enq_Call_Existence_def
      system_invariant_Init system_invariant_def
    by blast


  have RS0: "Reachable_Sys s_before_deq"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] PREFIX] .

  have NO_D4_A3:
    "\<not> (\<exists>p. program_counter s_before_deq p = ''D4'' \<and> x_var s_before_deq p = A3)"
  proof
    assume H: "\<exists>p. program_counter s_before_deq p = ''D4'' \<and> x_var s_before_deq p = A3"
    then obtain p where
      PD4: "program_counter s_before_deq p = ''D4''"
      and XA3: "x_var s_before_deq p = A3"
      by blast

    have PIN: "p \<in> ProcSet"
      using Reachable_nonL0_in_ProcSet[OF RS0] PD4
      by auto

    have "p = P1 \<or> p = P2"
      using PIN N2 by auto

    then show False
      using PD4 P1L0 P2SAFE by auto
  qed

  (* 1: 4 DeqRetInHis *)
  have NO_DEQ_RET_A3:
    "\<not> (\<exists>p sn. DeqRetInHis s_before_deq p A3 sn)"
  proof
    assume H: "\<exists>p sn. DeqRetInHis s_before_deq p A3 sn"
    then obtain p sn where DR: "DeqRetInHis s_before_deq p A3 sn"
      by blast

    have NO_DEQ_RET_PREFIX:
      "\<forall>x\<in>set
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)].
         \<forall>p a. x \<noteq> Some (mk_obs deq a p ret)"
      unfolding mk_obs_def
      by auto

    (* Auxiliary lemma. *)
    have KEEP:
      "DeqRetInHis s_before_deq p A3 sn \<longleftrightarrow> DeqRetInHis s0 p A3 sn"
      using C_Path_no_deq_ret_preserves_DeqRetInHis[OF PREFIX NO_DEQ_RET_PREFIX] .

    (* Auxiliary lemma. *)
    have INIT0: "\<not> DeqRetInHis s0 p A3 sn"
      using Init_no_DeqRetInHis[OF INIT] .

    from DR KEEP INIT0 show False
      by blast
  qed

  show ?thesis
  proof (cases "Q_arr s_before_deq k = A3")
    case True
    then show ?thesis .
  next
    case False
    have QBOT: "Q_arr s_before_deq k = BOT"
      using S8 QBK False
      unfolding sI8_Q_Qback_Sync_def
      by force

    have A3NZ: "A3 \<noteq> BOT"
      using False QBOT by fastforce

    (* 4: unfold definition, hI13 Model. prefix Unify *)
    have WIT:
      "(\<exists>p. program_counter s_before_deq p = ''D4'' \<and> x_var s_before_deq p = A3) \<or>
       (\<exists>p sn. DeqRetInHis s_before_deq p A3 sn)"
      using H13 QBK QBOT A3NZ
      unfolding hI13_Qback_Deq_Sync_def DeqRetInHis_def Model.DeqRetInHis_def
      by blast

    from WIT NO_D4_A3 NO_DEQ_RET_A3 show ?thesis
      by blast
  qed
qed


lemma hwq_full_e1_pre_deq_A3_in_slots23:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
  shows "A3 \<in> {Q_arr s_before_deq 2, Q_arr s_before_deq 3}"
proof -
  have RS0: "Reachable_Sys s_before_deq"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] PREFIX] .

  have INV0: "system_invariant s_before_deq"
    using Reachable_Sys_system_invariant[OF RS0] .

  have PREQ1: "Q_arr s_before_deq 1 = A1"
    using hwq_full_e1_pre_deq_q1_shape[OF N2 INIT PREFIX] .

  have P2SAFE:
    "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1) \<and>
     (program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1)"
    using hwq_full_e1_pre_deq_p2_safe_shape[OF N2 INIT PREFIX]
    using P2_pending_A2_safe_def by blast 

  obtain k where
      K23: "k \<in> {2,3}"
    and QBK: "Qback_arr s_before_deq k = A3"
    using hwq_full_e1_pre_deq_A3_in_Qback_from_segment[OF N2 INIT PREFIX PREQ1 P2SAFE]
    using P2_pending_A2_safe_def by blast

  have QAK: "Q_arr s_before_deq k = A3"
    using hwq_full_e1_pre_deq_QbackA3_implies_QarrA3[OF N2 INIT PREFIX INV0 QBK K23]
    by blast

  from K23 QAK show ?thesis
    by auto
qed


lemma hwq_full_e1_pre_deq_slots23_seed:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
  shows "Slots23_seed s_before_deq"
proof -
  have PREQ1: "Q_arr s_before_deq 1 = A1"
    using hwq_full_e1_pre_deq_q1_shape[OF N2 INIT PREFIX] .

  have P2SAFE:
    "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1) \<and>
     (program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1)"
    using hwq_full_e1_pre_deq_p2_safe_shape[OF N2 INIT PREFIX]
    using P2_pending_A2_safe_def by blast

  have RS0: "Reachable_Sys s_before_deq"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] PREFIX] .

  have INV0: "system_invariant s_before_deq"
    using Reachable_Sys_system_invariant[OF RS0] .

  (* ========================================================================= *)
  (* 1: extract, system_invariantE *)
  (* ========================================================================= *)
  have S8: "sI8_Q_Qback_Sync s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  have S10: "sI10_Qback_Unique_Vals s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  have H10: "hI10_Enq_Call_Existence s_before_deq"
    using INV0 unfolding system_invariant_def by auto

  have QB1: "Qback_arr s_before_deq 1 = A1"
    using PREQ1 S8
    unfolding sI8_Q_Qback_Sync_def
    by (metis BOT_def zero_neq_one)

  have NO_A1_2: "Q_arr s_before_deq 2 \<noteq> A1"
  proof
    assume Q2A1: "Q_arr s_before_deq 2 = A1"
    have QB2: "Qback_arr s_before_deq 2 = A1"
      using Q2A1 S8
      unfolding sI8_Q_Qback_Sync_def
      using INV0 PREQ1 hwq_full_e1_pre_deq_no_A1_in_slots23
      by blast
    from S10 QB1 QB2 show False
      unfolding sI10_Qback_Unique_Vals_def
      using INV0 PREQ1 Q2A1 hwq_full_e1_pre_deq_no_A1_in_slots23
      by blast
  qed

  have NO_A1_3: "Q_arr s_before_deq 3 \<noteq> A1"
  proof
    assume Q3A1: "Q_arr s_before_deq 3 = A1"
    have QB3: "Qback_arr s_before_deq 3 = A1"
      using Q3A1 S8
      unfolding sI8_Q_Qback_Sync_def
      using INV0 PREQ1 hwq_full_e1_pre_deq_no_A1_in_slots23
      by blast
    from S10 QB1 QB3 show False
      unfolding sI10_Qback_Unique_Vals_def
      using INV0 PREQ1 Q3A1 hwq_full_e1_pre_deq_no_A1_in_slots23
      by blast
  qed

  (* ========================================================================= *)
  (* 2: INIT, note *)
  (* ========================================================================= *)
  note ONLY3 = hwq_full_e1_pre_deq_only_three_enq_calls[OF INIT PREFIX]

  have SUB23: "{Q_arr s_before_deq 2, Q_arr s_before_deq 3} \<subseteq> {BOT, A2, A3}"
  proof
    fix x
    assume HX: "x \<in> {Q_arr s_before_deq 2, Q_arr s_before_deq 3}"
    then have HX_cases:
      "(x = Q_arr s_before_deq 2) \<or> (x = Q_arr s_before_deq 3)"
      by auto

    show "x \<in> {BOT, A2, A3}"
    proof (cases "x = BOT")
      case True
      then show ?thesis by auto
    next
      case False
      then obtain k where
          K23: "k \<in> {2,3}"
        and XK: "Q_arr s_before_deq k = x"
        using HX_cases by auto

      have QBK: "Qback_arr s_before_deq k = x"
        using XK False S8
        unfolding sI8_Q_Qback_Sync_def
        by metis

      (* 1: EnqCallInHis3_def, direct blast extract *)
      obtain p_id sn_num where CALL: "EnqCallInHis s_before_deq p_id x sn_num"
        using H10 QBK
        unfolding hI10_Enq_Call_Existence_def
        by blast

      (* 2: unfold definition, *)
      have X123: "x \<in> {A1, A2, A3}"
        using ONLY3 CALL
        unfolding EnqCallInHis_def Model.EnqCallInHis_def
        by blast

      have XNE1: "x \<noteq> A1"
        using HX_cases NO_A1_2 NO_A1_3 by auto

      from X123 XNE1 show ?thesis
        by auto
    qed
  qed

  have A3IN: "A3 \<in> {Q_arr s_before_deq 2, Q_arr s_before_deq 3}"
    using hwq_full_e1_pre_deq_A3_in_slots23[OF N2 INIT PREFIX] .

  show ?thesis
    unfolding Slots23_seed_def
    using SUB23 A3IN by auto
qed

lemma Tau_preserves_slots23_after_p2_ret_step:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and PCP2: "program_counter s P2 = ''L0''"
      and BR:
        "((Q_arr s 1 = A1) \<and>
           ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
         \<or>
         ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
      and TAU: "C_Tau s s'"
  shows "Q_arr s' 2 = Q_arr s 2 \<and> Q_arr s' 3 = Q_arr s 3"
proof -
  have STEP0: "C_StepCR s None s'"
    using TAU unfolding C_Tau_def by simp

  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP:
      "Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s'"
    by (cases rule: C_StepCR.cases) auto

  have p_cases: "p = P1 \<or> p = P2"
    using PIN N2 by auto

  have p_not_P2: "p \<noteq> P2"
  proof
    assume "p = P2"
    with STEP PCP2 show False
      unfolding Sys_E1_def C_E1_def Sys_E2_def C_E2_def
                Sys_D1_def C_D1_def Sys_D2_def C_D2_def Sys_D3_def C_D3_def
                program_counter_def
      by auto
  qed

  hence pP1: "p = P1"
    using p_cases by auto

from STEP show ?thesis
  proof (elim disjE)
    assume "Sys_E1 p s s'"
    then show ?thesis
      using pP1 BR
      unfolding Sys_E1_def C_E1_def program_counter_def Let_def
      by auto
  next
    assume "Sys_E2 p s s'"
    then show ?thesis
      using pP1 BR
      unfolding Sys_E2_def C_E2_def program_counter_def Let_def
      by auto
  next
    assume "Sys_D1 p s s'"
    then show ?thesis
      using pP1 BR
      unfolding Sys_D1_def C_D1_def program_counter_def Let_def Q_arr_def
      by auto
next
    assume "Sys_D2 p s s'"
    then show ?thesis
      using pP1 BR
      unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def program_counter_def Let_def Q_arr_def
      apply (auto split: if_splits)
      done
  next
    assume "Sys_D3 p s s'"
    then show ?thesis
      using pP1 BR
      unfolding Sys_D3_def C_D3_def program_counter_def Let_def Q_arr_def j_var_def
      by auto
  qed
qed

lemma Tau_Star_preserves_slots23_after_p2_ret:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and PCP2: "program_counter s P2 = ''L0''"
      and BR:
        "((Q_arr s 1 = A1) \<and>
           ((program_counter s P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s P1 = ''D3'' \<and> j_var s P1 = 1)))
         \<or>
         ((Q_arr s 1 = BOT) \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1)"
      and TAUS: "C_Tau_Star s s'"
  shows "Q_arr s' 2 = Q_arr s 2 \<and> Q_arr s' 3 = Q_arr s 3"
proof -
  from TAUS INV PCP2 BR show ?thesis
  proof (induction rule: C_Tau_Star.induct)
    case refl
    then show ?case by simp
  next
    case (step s1 s2 s3)
    have STEP12: "Q_arr s2 2 = Q_arr s1 2 \<and> Q_arr s2 3 = Q_arr s1 3"
      using Tau_preserves_slots23_after_p2_ret_step[OF N2 step.prems(1) step.prems(2) step.prems(3) step.hyps(1)] .

    have STEP0: "C_StepCR s1 None s2"
      using step.hyps(1) unfolding C_Tau_def by simp

    obtain p where PIN: "p \<in> ProcSet"
      and STEPp: "Sys_E1 p s1 s2 \<or> Sys_E2 p s1 s2 \<or> Sys_D1 p s1 s2 \<or> Sys_D2 p s1 s2 \<or> Sys_D3 p s1 s2"
      using STEP0 by (cases rule: C_StepCR.cases) auto

    have pP1: "p = P1"
    proof -
      have "p = P1 \<or> p = P2"
        using PIN N2 by auto
      then show ?thesis
      proof
        assume "p = P1"
        then show ?thesis .
      next
        assume pP2: "p = P2"
        from STEPp show ?thesis
        proof (elim disjE)
          assume H: "Sys_E1 p s1 s2"
          with pP2 step.prems(2) show ?thesis
            unfolding Sys_E1_def C_E1_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_E2 p s1 s2"
          with pP2 step.prems(2) show ?thesis
            unfolding Sys_E2_def C_E2_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_D1 p s1 s2"
          with pP2 step.prems(2) show ?thesis
            unfolding Sys_D1_def C_D1_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_D2 p s1 s2"
          with pP2 step.prems(2) show ?thesis
            unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def program_counter_def Let_def
            by auto
        next
          assume H: "Sys_D3 p s1 s2"
          with pP2 step.prems(2) show ?thesis
            unfolding Sys_D3_def C_D3_def program_counter_def Let_def
            by auto
        qed
      qed
    qed

    have PCP2_2: "program_counter s2 P2 = ''L0''"
      using STEPp pP1 step.prems(2)
      unfolding Sys_E1_def Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def
                C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def
                T_D2_EnterLoop_def program_counter_def Let_def
      by (metis C_Tau_preserves_P2_L0 N2 program_counter_def
          step.hyps(1))

    have NXT: "Next s1 s2"
      using C_StepCR_into_Next[OF STEP0] .

    have INV2: "system_invariant s2"
      using Sys_Inv_Step[OF step.prems(1) NXT] .

    have BR2:
      "((Q_arr s2 1 = A1) \<and>
         ((program_counter s2 P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s2 P1 = ''D3'' \<and> j_var s2 P1 = 1)))
       \<or>
       ((Q_arr s2 1 = BOT) \<and> program_counter s2 P1 = ''D4'' \<and> x_var s2 P1 = A1)"
      using Tau_preserves_P1_branch_step[OF N2 step.prems(1) step.prems(2) step.prems(3) step.hyps(1)] .

    have IH': "Q_arr s3 2 = Q_arr s2 2 \<and> Q_arr s3 3 = Q_arr s2 3"
      using step.IH[OF INV2 PCP2_2 BR2] .

    from STEP12 IH' show ?case
      by auto
  qed
qed

lemma TauStar_preserves_INV:
  assumes TAUS: "C_Tau_Star x y"
      and INV:  "system_invariant x"
  shows "system_invariant y"
  using TAUS INV
proof (induction rule: C_Tau_Star.induct)
  case refl
  then show ?case by simp
next
  case (step s1 s2 s3)
  have STEP0: "C_StepCR s1 None s2"
    using step.hyps(1) unfolding C_Tau_def by simp
  have NXT: "Next s1 s2"
    using C_StepCR_into_Next[OF STEP0] .
  have INV2: "system_invariant s2"
    using Sys_Inv_Step[OF step.prems NXT] .
  show ?case
    using step.IH[OF INV2] .
qed

(* single-step Tau v_var *)
lemma C_Tau_preserves_v_var:
  assumes "C_Tau s t"
  shows "v_var t p = v_var s p"
  using assms unfolding C_Tau_def
  by (cases rule: C_StepCR.cases)
     (auto simp: Sys_E1_def Sys_E2_def Sys_D1_def Sys_D2_def Sys_D3_def
                 C_E1_def C_E2_def C_D1_def C_D2_def C_D3_def
                 T_D2_EnterLoop_def Let_def v_var_def split: if_splits)

(* multi-step Tau_Star v_var (path induction) *)
lemma C_Tau_Star_preserves_v_var:
  assumes "C_Tau_Star s t"
  shows "v_var t p = v_var s p"
  using assms
  by (induction rule: C_Tau_Star.induct) (auto simp: C_Tau_preserves_v_var)

(* Branch 1.1. *)
lemma Tau_preserves_Slots23_seed_step:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and TAU: "C_Tau s t"
      and SAFE: "P2_pending_A2_safe s \<and>
                 ((Q_arr s 1 = A1 \<and> program_counter s P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
                  (Q_arr s 1 = A1 \<and> program_counter s P1 = ''D3'' \<and> j_var s P1 = 1) \<or>
                  (Q_arr s 1 = BOT \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1))"
      and SEED: "Slots23_seed s"
  shows "Slots23_seed t \<and>
         P2_pending_A2_safe t \<and>
         ((Q_arr t 1 = A1 \<and> program_counter t P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
          (Q_arr t 1 = A1 \<and> program_counter t P1 = ''D3'' \<and> j_var t P1 = 1) \<or>
          (Q_arr t 1 = BOT \<and> program_counter t P1 = ''D4'' \<and> x_var t P1 = A1))"
proof -
  have STEP0: "C_StepCR s None t" using TAU unfolding C_Tau_def by simp
  from STEP0 obtain p where PIN: "p \<in> ProcSet"
    and STEP: "Sys_E1 p s t \<or> Sys_E2 p s t \<or> Sys_D1 p s t \<or> Sys_D2 p s t \<or> Sys_D3 p s t"
    by (cases rule: C_StepCR.cases) auto
  have p_cases: "p = P1 \<or> p = P2" using PIN N2 by auto
  have S3: "sI3_E2_Slot_Exclusive s" using INV unfolding system_invariant_def by auto

  from p_cases show ?thesis
  proof
    assume pP1: "p = P1"
    from STEP show ?thesis
    proof (elim disjE)
      assume H: "Sys_E1 p s t" then show ?thesis using pP1 SAFE unfolding Sys_E1_def C_E1_def program_counter_def Let_def by auto
    next
      assume H: "Sys_E2 p s t" then show ?thesis using pP1 SAFE unfolding Sys_E2_def C_E2_def program_counter_def Let_def by auto
    next
      assume H: "Sys_D1 p s t"
      have UNCHANGED: "Q_arr t 1 = Q_arr s 1" "P2_pending_A2_safe t" "Slots23_seed t"
        using H pP1 SAFE SEED unfolding P2_pending_A2_safe_def Slots23_seed_def Sys_D1_def C_D1_def Q_arr_def v_var_def X_var_def i_var_def program_counter_def Let_def by auto
      show ?thesis using H pP1 SAFE UNCHANGED unfolding Sys_D1_def C_D1_def program_counter_def Let_def by auto
    next
      assume H: "Sys_D2 p s t"
      have UNCHANGED: "Q_arr t 1 = Q_arr s 1" "P2_pending_A2_safe t" "Slots23_seed t"
        using H pP1 SAFE SEED unfolding P2_pending_A2_safe_def Slots23_seed_def Sys_D2_def C_D2_def T_D2_EnterLoop_def Q_arr_def v_var_def X_var_def i_var_def program_counter_def Let_def by (auto split: if_splits)
      show ?thesis using H pP1 SAFE UNCHANGED unfolding Sys_D2_def C_D2_def T_D2_EnterLoop_def program_counter_def j_var_def Let_def by (auto split: if_splits)
    next
      assume H: "Sys_D3 p s t"
      have PC_D3: "program_counter s P1 = ''D3''" using H pP1 unfolding Sys_D3_def C_D3_def program_counter_def Let_def by auto
      have J1: "j_var s P1 = 1" using SAFE PC_D3 by auto
      have Q1: "Q_arr s 1 = A1" using SAFE PC_D3 by auto
      
      have UNCHANGED: "P2_pending_A2_safe t" "Slots23_seed t"
        using H pP1 J1 SAFE SEED unfolding P2_pending_A2_safe_def Slots23_seed_def Sys_D3_def C_D3_def Q_arr_def j_var_def v_var_def X_var_def i_var_def program_counter_def Let_def by (auto split: if_splits)
        
      (* Branch 1.3. *)
      show ?thesis using H pP1 SAFE UNCHANGED J1 Q1 
        unfolding Sys_D3_def C_D3_def program_counter_def Q_arr_def j_var_def x_var_def Let_def BOT_def 
        by (auto split: if_splits)
    qed
  next
    assume pP2: "p = P2"
    from STEP show ?thesis
    proof (elim disjE)
      assume H: "Sys_E1 p s t" then show ?thesis using pP2 SAFE SEED unfolding P2_pending_A2_safe_def Sys_E1_def C_E1_def program_counter_def Q_arr_def x_var_def v_var_def X_var_def i_var_def j_var_def Let_def Slots23_seed_def by auto
    next
      assume H: "Sys_E2 p s t"
      have PCE2: "program_counter s P2 = ''E2''" using H pP2 unfolding Sys_E2_def C_E2_def program_counter_def Let_def by auto
      have Q_BOT: "Q_arr s (i_var s P2) = BOT" using S3 PCE2 unfolding sI3_E2_Slot_Exclusive_def by auto
      show ?thesis proof (cases "i_var s P2 = 2 \<or> i_var s P2 = 3")
        case True then show ?thesis using H pP2 SAFE SEED Q_BOT unfolding P2_pending_A2_safe_def Sys_E2_def C_E2_def program_counter_def Q_arr_def x_var_def v_var_def X_var_def i_var_def j_var_def Let_def Slots23_seed_def BOT_def by (auto split: if_splits)
      next
        case False then show ?thesis using H pP2 SAFE SEED unfolding P2_pending_A2_safe_def Sys_E2_def C_E2_def program_counter_def Q_arr_def x_var_def v_var_def X_var_def i_var_def j_var_def Let_def Slots23_seed_def BOT_def by (auto split: if_splits)
      qed
    next
      assume H: "Sys_D1 p s t" then show ?thesis using pP2 SAFE SEED unfolding P2_pending_A2_safe_def Sys_D1_def C_D1_def program_counter_def Q_arr_def x_var_def v_var_def X_var_def i_var_def j_var_def Let_def Slots23_seed_def by auto
    next
      assume H: "Sys_D2 p s t" then show ?thesis using pP2 SAFE SEED unfolding P2_pending_A2_safe_def Sys_D2_def C_D2_def program_counter_def Q_arr_def x_var_def v_var_def X_var_def i_var_def j_var_def T_D2_EnterLoop_def Let_def Slots23_seed_def by (auto split: if_splits)
    next
      assume H: "Sys_D3 p s t" then show ?thesis using pP2 SAFE SEED unfolding P2_pending_A2_safe_def Sys_D3_def C_D3_def program_counter_def Q_arr_def x_var_def v_var_def X_var_def i_var_def j_var_def Let_def Slots23_seed_def by auto
    qed
  qed
qed

(* Core helper 2: multi-step Tau_Star preserve state () *)
lemma Tau_Star_preserves_Slots23_seed_pending:
  assumes N2: "N_Procs = 2"
      and INV: "system_invariant s"
      and TAUS: "C_Tau_Star s t"
      and SAFE: "P2_pending_A2_safe s \<and>
                 ((Q_arr s 1 = A1 \<and> program_counter s P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
                  (Q_arr s 1 = A1 \<and> program_counter s P1 = ''D3'' \<and> j_var s P1 = 1) \<or>
                  (Q_arr s 1 = BOT \<and> program_counter s P1 = ''D4'' \<and> x_var s P1 = A1))"
      and SEED: "Slots23_seed s"
  shows "Slots23_seed t \<and>
         P2_pending_A2_safe t \<and>
         ((Q_arr t 1 = A1 \<and> program_counter t P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
          (Q_arr t 1 = A1 \<and> program_counter t P1 = ''D3'' \<and> j_var t P1 = 1) \<or>
          (Q_arr t 1 = BOT \<and> program_counter t P1 = ''D4'' \<and> x_var t P1 = A1))"
  using TAUS INV SAFE SEED
proof (induction rule: C_Tau_Star.induct)
  case refl then show ?case by simp
next
  case (step s1 s2 s3)
  have NXT: "Next s1 s2" using C_StepCR_into_Next[OF step.hyps(1)[unfolded C_Tau_def, simplified]] .
  have INV2: "system_invariant s2" using Sys_Inv_Step[OF step.prems(1) NXT] .
  have STEP2: "Slots23_seed s2 \<and> P2_pending_A2_safe s2 \<and> 
               ((Q_arr s2 1 = A1 \<and> program_counter s2 P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
                (Q_arr s2 1 = A1 \<and> program_counter s2 P1 = ''D3'' \<and> j_var s2 P1 = 1) \<or>
                (Q_arr s2 1 = BOT \<and> program_counter s2 P1 = ''D4'' \<and> x_var s2 P1 = A1))"
    using Tau_preserves_Slots23_seed_step[OF N2 step.prems(1) step.hyps(1) step.prems(2) step.prems(3)] .
  show ?case using step.IH[OF INV2 STEP2[THEN conjunct2] STEP2[THEN conjunct1]] by simp
qed

(* Helper: Deq Call Q_arr, *)
lemma StepCR_deq_call_preserves_Slots23_seed:
  assumes "C_StepCR s (Some (mk_obs deq BOT p call)) t"
      and "Slots23_seed s"
  shows "Slots23_seed t"
proof -
  from assms(1) have "Q_arr t 2 = Q_arr s 2 \<and> Q_arr t 3 = Q_arr s 3"
    by (cases rule: C_StepCR.cases) 
       (auto simp: mk_obs_def Sys_L0_def C_L0_def Q_arr_def Let_def split: if_splits)
  then show ?thesis using assms(2) unfolding Slots23_seed_def by simp
qed

lemma hwq_suffix_after_deq_call_to_s_deq_post:
  assumes N2: "N_Procs = 2"
      and INV0: "system_invariant s_before_deq"
      and PC1_0: "program_counter s_before_deq P1 = ''L0''"
      and P_DEQ: "C_Path s_before_deq
        [Some (mk_obs deq BOT P1 call), None, None, None, None] s_deq_post"
      and PREQ1: "Q_arr s_before_deq 1 = A1"
      and P2SAFE: "P2_pending_A2_safe s_before_deq"
      and SEED0: "Slots23_seed s_before_deq"
  shows
      "system_invariant s_deq_post"
      (* Branch 1.1. *)
    and "((Q_arr s_deq_post 1 = A1) \<and>
           ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
         \<or>
         ((Q_arr s_deq_post 1 = BOT) \<and>
           program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1)"
    and "P2_pending_A2_safe s_deq_post"
    and "Slots23_seed s_deq_post"
proof -
  obtain s1 where
      M_DEQ: "C_Match s_before_deq (Some (mk_obs deq BOT P1 call)) s1"
    and P_N4: "C_Path s1 [None, None, None, None] s_deq_post"
    using my_C_Path_ConsE[OF P_DEQ] .

  obtain u_deq_pre u_deq_post where
      T_DEQ_PRE:  "C_Tau_Star s_before_deq u_deq_pre"
    and STEP_DEQ: "C_StepCR u_deq_pre (Some (mk_obs deq BOT P1 call)) u_deq_post"
    and T_DEQ_POST:"C_Tau_Star u_deq_post s1"
    using my_C_Match_SomeE[OF M_DEQ] by blast

  have INV_u_deq_pre: "system_invariant u_deq_pre"
    using TauStar_preserves_INV[OF T_DEQ_PRE INV0] .

  (* ----------------------------------------------------------------- *)
  (* Step 1. *)
  (* ----------------------------------------------------------------- *)
  have PRE_DEQ_SAFE:
    "program_counter u_deq_pre P1 = ''L0'' \<and>
     Q_arr u_deq_pre 1 = A1 \<and>
     P2_pending_A2_safe u_deq_pre"
  proof -
    have P2_PARTS:
      "program_counter s_before_deq P2 \<in> {''E1'', ''E2'', ''E3''}"
      "program_counter s_before_deq P2 = ''E1'' \<longrightarrow> X_var s_before_deq \<noteq> 1"
      "program_counter s_before_deq P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_before_deq P2 \<noteq> 1"
      "v_var s_before_deq P2 = A2"
      using P2SAFE unfolding P2_pending_A2_safe_def by auto

    have 1: "program_counter u_deq_pre P1 = ''L0'' \<and> Q_arr u_deq_pre 1 = A1 \<and>
             program_counter u_deq_pre P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
             (program_counter u_deq_pre P2 = ''E1'' \<longrightarrow> X_var u_deq_pre \<noteq> 1) \<and>
             (program_counter u_deq_pre P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_deq_pre P2 \<noteq> 1)"
      using hwq_p2_pending_tau_preserves_q1_weak[OF N2 T_DEQ_PRE PC1_0 P2_PARTS(1) P2_PARTS(2) P2_PARTS(3) PREQ1]
      by auto 

    have 2: "v_var u_deq_pre P2 = A2"
      using C_Tau_Star_preserves_v_var[OF T_DEQ_PRE] P2_PARTS(4) by auto

    show ?thesis using 1 2 unfolding P2_pending_A2_safe_def
      using "1" C_Tau_Star_preserves_v_var P2_PARTS(4) T_DEQ_PRE
      by presburger
  qed

  (* ----------------------------------------------------------------- *)
  (* Step 2.1. *)
  (* ----------------------------------------------------------------- *)
  have BR_CALL:
    "((Q_arr u_deq_post 1 = A1) \<and>
       ((program_counter u_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter u_deq_post P1 = ''D3'' \<and> j_var u_deq_post P1 = 1)))
     \<or>
     ((Q_arr u_deq_post 1 = BOT) \<and> program_counter u_deq_post P1 = ''D4'' \<and> x_var u_deq_post P1 = A1)"
  proof -
    from PRE_DEQ_SAFE obtain PC1_PRE: "program_counter u_deq_pre P1 = ''L0''"
                          and Q1_PRE:  "Q_arr u_deq_pre 1 = A1" by blast
    from STEP_DEQ show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_deq_vis p)
      then have pP1: "p = P1" unfolding mk_obs_def by auto
      from C_Sys_L0_deq_vis pP1 PC1_PRE Q1_PRE show ?thesis
        unfolding Sys_L0_def C_L0_def program_counter_def Q_arr_def j_var_def x_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  (* ----------------------------------------------------------------- *)
  (* Step 3.2. *)
  (* ----------------------------------------------------------------- *)
  have POST_DEQ_SAFE: "P2_pending_A2_safe u_deq_post"
  proof -
    from PRE_DEQ_SAFE have P2SAFE_PRE: "P2_pending_A2_safe u_deq_pre" by blast
    from STEP_DEQ show ?thesis
    proof (cases rule: C_StepCR.cases)
      case (C_Sys_L0_deq_vis p)
      then have pP1: "p = P1" unfolding mk_obs_def by auto
      from C_Sys_L0_deq_vis pP1 P2SAFE_PRE show ?thesis
        unfolding Sys_L0_def C_L0_def P2_pending_A2_safe_def
                  program_counter_def X_var_def i_var_def v_var_def Let_def
        by (auto split: if_splits)
    qed (auto simp: mk_obs_def)
  qed

  (* ----------------------------------------------------------------- *)
  (* Step 4. *)
  (* ----------------------------------------------------------------- *)
  have NXT_DEQ: "Next u_deq_pre u_deq_post" using C_StepCR_into_Next[OF STEP_DEQ] .
  have INV_u_deq_post: "system_invariant u_deq_post" using Sys_Inv_Step[OF INV_u_deq_pre NXT_DEQ] .

  obtain s2 where M_N1: "C_Match s1 None s2" and P_N3: "C_Path s2 [None, None, None] s_deq_post" using my_C_Path_ConsE[OF P_N4] .
  obtain s3 where M_N2: "C_Match s2 None s3" and P_N2: "C_Path s3 [None, None] s_deq_post" using my_C_Path_ConsE[OF P_N3] .
  obtain s4 where M_N3: "C_Match s3 None s4" and P_N1: "C_Path s4 [None] s_deq_post" using my_C_Path_ConsE[OF P_N2] .
  obtain s5 where M_N4: "C_Match s4 None s5" and P_N0: "C_Path s5 [] s_deq_post" using my_C_Path_ConsE[OF P_N1] .

  have S5_EQ: "s5 = s_deq_post" using P_N0 by (cases rule: C_Path.cases) auto

  have T_N_ALL: "C_Tau_Star s1 s_deq_post"
    using C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N1]
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N2]
          C_Tau_Star_trans[OF my_C_Match_NoneE[OF M_N3] my_C_Match_NoneE[OF M_N4]]]] S5_EQ by simp

  have T_MID: "C_Tau_Star u_deq_post s_deq_post" using C_Tau_Star_trans[OF T_DEQ_POST T_N_ALL] .

  (* ----------------------------------------------------------------- *)
  (* Step 5.1.2. *)
  (* ----------------------------------------------------------------- *)
  have MID_BRANCH_SAFE_P1:
    "((Q_arr s_deq_post 1 = A1) \<and>
       ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
     \<or>
     ((Q_arr s_deq_post 1 = BOT) \<and> program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1)"
  and MID_BRANCH_SAFE_P2: "P2_pending_A2_safe s_deq_post"
  proof -
    have POST_DEQ_SAFE_OLD:
      "program_counter u_deq_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
       (program_counter u_deq_post P2 = ''E1'' \<longrightarrow> X_var u_deq_post \<noteq> 1) \<and>
       (program_counter u_deq_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var u_deq_post P2 \<noteq> 1)"
      using POST_DEQ_SAFE unfolding P2_pending_A2_safe_def by blast

    have OLD_MID:
      "(((Q_arr s_deq_post 1 = A1) \<and>
         ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
        \<or>
        ((Q_arr s_deq_post 1 = BOT) \<and> program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1))
       \<and>
       (program_counter s_deq_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
        (program_counter s_deq_post P2 = ''E1'' \<longrightarrow> X_var s_deq_post \<noteq> 1) \<and>
        (program_counter s_deq_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_deq_post P2 \<noteq> 1))"
      using Tau_Star_preserves_P1_branch_P2_pending_safe[OF N2 INV_u_deq_post BR_CALL POST_DEQ_SAFE_OLD T_MID] .

    show "((Q_arr s_deq_post 1 = A1) \<and> ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or> (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1))) \<or> ((Q_arr s_deq_post 1 = BOT) \<and> program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1)"
      using OLD_MID by blast

    have V_POST: "v_var u_deq_post P2 = A2" using POST_DEQ_SAFE unfolding P2_pending_A2_safe_def by blast
    have V_END: "v_var s_deq_post P2 = A2" using C_Tau_Star_preserves_v_var[OF T_MID] V_POST by auto

    show "P2_pending_A2_safe s_deq_post" unfolding P2_pending_A2_safe_def using OLD_MID V_END by blast
  qed

  (* ----------------------------------------------------------------- *)
  (* Step 6.23. *)
  (* ----------------------------------------------------------------- *)
  have SAFE_PRE_SEED: "P2_pending_A2_safe s_before_deq \<and>
                 ((Q_arr s_before_deq 1 = A1 \<and> program_counter s_before_deq P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
                  (Q_arr s_before_deq 1 = A1 \<and> program_counter s_before_deq P1 = ''D3'' \<and> j_var s_before_deq P1 = 1) \<or>
                  (Q_arr s_before_deq 1 = BOT \<and> program_counter s_before_deq P1 = ''D4'' \<and> x_var s_before_deq P1 = A1))"
    using P2SAFE PC1_0 PREQ1 by auto

  have SEED_u_deq_pre: "Slots23_seed u_deq_pre"
    using Tau_Star_preserves_Slots23_seed_pending[OF N2 INV0 T_DEQ_PRE SAFE_PRE_SEED SEED0] by blast

  have SEED_u_deq_post: "Slots23_seed u_deq_post"
    using StepCR_deq_call_preserves_Slots23_seed[OF STEP_DEQ SEED_u_deq_pre] .

  have SAFE_POST_SEED: "P2_pending_A2_safe u_deq_post \<and>
                 ((Q_arr u_deq_post 1 = A1 \<and> program_counter u_deq_post P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
                  (Q_arr u_deq_post 1 = A1 \<and> program_counter u_deq_post P1 = ''D3'' \<and> j_var u_deq_post P1 = 1) \<or>
                  (Q_arr u_deq_post 1 = BOT \<and> program_counter u_deq_post P1 = ''D4'' \<and> x_var u_deq_post P1 = A1))"
    using POST_DEQ_SAFE BR_CALL by auto

  have SEED_deq_post: "Slots23_seed s_deq_post"
    using Tau_Star_preserves_Slots23_seed_pending[OF N2 INV_u_deq_post T_MID SAFE_POST_SEED SEED_u_deq_post] by blast

  have INV_s_deq_post: "system_invariant s_deq_post" using TauStar_preserves_INV[OF T_MID INV_u_deq_post] .

  (* ----------------------------------------------------------------- *)
  (* Step 7.4. *)
  (* ----------------------------------------------------------------- *)
  show "system_invariant s_deq_post" using INV_s_deq_post .

  show "((Q_arr s_deq_post 1 = A1) \<and>
         ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
       \<or>
       ((Q_arr s_deq_post 1 = BOT) \<and>
         program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1)"
    using MID_BRANCH_SAFE_P1 .

  show "P2_pending_A2_safe s_deq_post" using MID_BRANCH_SAFE_P2 .

  show "Slots23_seed s_deq_post" using SEED_deq_post .
qed


lemma hwq_pending_suffix_to_ret_pre:
  assumes N2: "N_Procs = 2"
      and INV_s_deq_post: "system_invariant s_deq_post"
      (* Branch 1. *)
      and P1_BRANCH_SAFE:
        "((Q_arr s_deq_post 1 = A1) \<and>
           ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
         \<or>
         ((Q_arr s_deq_post 1 = BOT) \<and> program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1)"
      and P2_SAFE: "P2_pending_A2_safe s_deq_post"
      and SEED_deq_post: "Slots23_seed s_deq_post"
      and T_RET_PRE: "C_Tau_Star s_deq_post u_ret_pre"
  shows
      "system_invariant u_ret_pre"
    and "((Q_arr u_ret_pre 1 = A1) \<and>
           ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))
         \<or>
         ((Q_arr u_ret_pre 1 = BOT) \<and> program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1)"
    and "P2_pending_A2_safe u_ret_pre"
    and "Slots23_seed u_ret_pre"
proof -
  (* Step 1. *)
  have INV_u_ret_pre: "system_invariant u_ret_pre"
    using TauStar_preserves_INV[OF T_RET_PRE INV_s_deq_post] .

  (* ----------------------------------------------------------------- *)
  (* Step 2.1. *)
  (* ----------------------------------------------------------------- *)
  have OLD_P2_SAFE:
    "program_counter s_deq_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
     (program_counter s_deq_post P2 = ''E1'' \<longrightarrow> X_var s_deq_post \<noteq> 1) \<and>
     (program_counter s_deq_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_deq_post P2 \<noteq> 1)"
    using P2_SAFE unfolding P2_pending_A2_safe_def by blast

  have OLD_MID_BRANCH_SAFE:
    "(((Q_arr s_deq_post 1 = A1) \<and>
       ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
     \<or>
     ((Q_arr s_deq_post 1 = BOT) \<and> program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1))
     \<and>
     (program_counter s_deq_post P2 \<in> {''E1'', ''E2'', ''E3''} \<and>
      (program_counter s_deq_post P2 = ''E1'' \<longrightarrow> X_var s_deq_post \<noteq> 1) \<and>
      (program_counter s_deq_post P2 \<in> {''E2'', ''E3''} \<longrightarrow> i_var s_deq_post P2 \<noteq> 1))"
    using P1_BRANCH_SAFE OLD_P2_SAFE by blast

  have STRICT_P1_BRANCH_POST:
    "((Q_arr u_ret_pre 1 = A1) \<and>
       ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))
     \<or>
     ((Q_arr u_ret_pre 1 = BOT) \<and> program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1)"
    using Tau_Star_preserves_P1_branch_P2_pending_safe[OF N2 INV_s_deq_post P1_BRANCH_SAFE OLD_P2_SAFE T_RET_PRE] 
    by blast

  (* ----------------------------------------------------------------- *)
  (* Step 3.2. *)
  (* ----------------------------------------------------------------- *)
  have SEED_HELPER_INPUT: 
    "P2_pending_A2_safe s_deq_post \<and>
     ((Q_arr s_deq_post 1 = A1 \<and> program_counter s_deq_post P1 \<in> {''L0'', ''D1'', ''D2''}) \<or>
      (Q_arr s_deq_post 1 = A1 \<and> program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1) \<or>
      (Q_arr s_deq_post 1 = BOT \<and> program_counter s_deq_post P1 = ''D4'' \<and> x_var s_deq_post P1 = A1))"
    using P2_SAFE P1_BRANCH_SAFE by auto

  have SEED_AND_P2_SAFE_POST:
    "Slots23_seed u_ret_pre \<and> P2_pending_A2_safe u_ret_pre"
    using Tau_Star_preserves_Slots23_seed_pending[OF N2 INV_s_deq_post T_RET_PRE SEED_HELPER_INPUT SEED_deq_post] 
    by blast

  (* ----------------------------------------------------------------- *)
  (* Step 4. *)
  (* ----------------------------------------------------------------- *)
  show "system_invariant u_ret_pre" 
    using INV_u_ret_pre .
    
  show "((Q_arr u_ret_pre 1 = A1) \<and>
           ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))
         \<or>
         ((Q_arr u_ret_pre 1 = BOT) \<and> program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1)"
    using STRICT_P1_BRANCH_POST .
    
  show "P2_pending_A2_safe u_ret_pre"
    using SEED_AND_P2_SAFE_POST by blast
    
  show "Slots23_seed u_ret_pre"
    using SEED_AND_P2_SAFE_POST by blast
qed

(* lvyi *)

lemma hwq_ret_pre_common_facts:
  assumes N2: "N_Procs = 2"
      and INV_u_ret_pre: "system_invariant u_ret_pre"
      and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
      and T_RET_POST: "C_Tau_Star u_ret_post sk0"
      and X4: "X_var sk0 = 4"
      and PRE_RET_P2: "P2_pending_A2_safe u_ret_pre"
      and SEED_RET_PRE: "Slots23_seed u_ret_pre"
  shows
    "program_counter u_ret_pre P2 = ''E3''"
    "v_var u_ret_pre P2 = A2"
    "i_var u_ret_pre P2 \<in> {2,3}"
    "Q_arr u_ret_pre (i_var u_ret_pre P2) = A2 \<or>
     Q_arr u_ret_pre (i_var u_ret_pre P2) = BOT"
    "Q_arr u_ret_pre (i_var u_ret_pre P2) \<noteq> A3"
    "A3 \<in> {Q_arr u_ret_pre 2, Q_arr u_ret_pre 3}"
proof -
  from STEP_RET obtain p where
      PIN: "p \<in> ProcSet"
    and E3VIS: "Sys_E3 p u_ret_pre u_ret_post"
    and LAB: "mk_obs enq A2 p ret = mk_obs enq A2 P2 ret"
    by (cases rule: C_StepCR.cases) (auto simp: mk_obs_def)

  have pP2: "p = P2"
    using LAB unfolding mk_obs_def by auto

  have PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
    using E3VIS pP2
    unfolding Sys_E3_def C_E3_def program_counter_def Let_def
    by (auto split: if_splits)

  have V_PRE2: "v_var u_ret_pre P2 = A2"
    using PRE_RET_P2
    unfolding P2_pending_A2_safe_def
    by auto

  have SI4_pre: "sI4_E3_Qback_Written u_ret_pre"
    using INV_u_ret_pre
    unfolding system_invariant_def
    by auto

  have X_POST_EQ: "X_var u_ret_post = X_var u_ret_pre"
    using E3VIS pP2
    unfolding Sys_E3_def C_E3_def X_var_def Let_def
    by (auto split: if_splits)

  have X_POST_LE4: "X_var u_ret_post \<le> 4"
    using C_Tau_Star_X_var_mono[OF T_RET_POST] X4
    by auto

  have X_PRE_LE4: "X_var u_ret_pre \<le> 4"
    using X_POST_EQ X_POST_LE4 by simp

  have I_POS: "i_var u_ret_pre P2 > 0"
    using SI4_pre PC_E3_P2
    unfolding sI4_E3_Qback_Written_def Val_def
    by auto

  have I_LT_X: "i_var u_ret_pre P2 < X_var u_ret_pre"
    using SI4_pre PC_E3_P2
    unfolding sI4_E3_Qback_Written_def
    by auto

  have I_NE1: "i_var u_ret_pre P2 \<noteq> 1"
    using PRE_RET_P2 PC_E3_P2
    unfolding P2_pending_A2_safe_def
    by auto

  have I_IN_23: "i_var u_ret_pre P2 \<in> {2,3}"
    using I_POS I_LT_X I_NE1 X_PRE_LE4
    by auto

  have SLOT_A2_or_BOT:
    "Q_arr u_ret_pre (i_var u_ret_pre P2) = A2 \<or>
     Q_arr u_ret_pre (i_var u_ret_pre P2) = BOT"
    using SI4_pre PC_E3_P2 V_PRE2
    unfolding sI4_E3_Qback_Written_def
    by auto

  have SLOT_NOT_A3:
    "Q_arr u_ret_pre (i_var u_ret_pre P2) \<noteq> A3"
    using SLOT_A2_or_BOT
    using BOT_def by presburger

  from SEED_RET_PRE have A3IN:
    "A3 \<in> {Q_arr u_ret_pre 2, Q_arr u_ret_pre 3}"
    unfolding Slots23_seed_def
    by auto

  show "program_counter u_ret_pre P2 = ''E3''"
    using PC_E3_P2 .
  show "v_var u_ret_pre P2 = A2"
    using V_PRE2 .
  show "i_var u_ret_pre P2 \<in> {2,3}"
    using I_IN_23 .
  show "Q_arr u_ret_pre (i_var u_ret_pre P2) = A2 \<or>
        Q_arr u_ret_pre (i_var u_ret_pre P2) = BOT"
    using SLOT_A2_or_BOT .
  show "Q_arr u_ret_pre (i_var u_ret_pre P2) \<noteq> A3"
    using SLOT_NOT_A3 .
  show "A3 \<in> {Q_arr u_ret_pre 2, Q_arr u_ret_pre 3}"
    using A3IN .
qed


lemma hwq_ret_pre_bot_implies_d4_or_deqret_A2:
  assumes INV: "system_invariant s"
      and PRE_RET_P2: "P2_pending_A2_safe s"
      and PC_E3_P2: "program_counter s P2 = ''E3''"
      and QBOT: "Q_arr s (i_var s P2) = BOT"
  shows
    "(\<exists>p. program_counter s p = ''D4'' \<and> x_var s p = A2) \<or>
     (\<exists>p sn. DeqRetInHis s p A2 sn)"
proof -
  have SI4: "sI4_E3_Qback_Written s"
    using INV unfolding system_invariant_def by auto

  have H13: "hI13_Qback_Deq_Sync s"
    using INV unfolding system_invariant_def by auto

  have V2: "v_var s P2 = A2"
    using PRE_RET_P2 unfolding P2_pending_A2_safe_def by auto

  have QB_ACTIVE: "Qback_arr s (i_var s P2) = A2"
    using SI4 PC_E3_P2 V2
    unfolding sI4_E3_Qback_Written_def
    by auto

  have A2_NZ: "A2 \<noteq> BOT"
    by (simp add: BOT_def)

  have EXK: "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = A2"
    using QBOT QB_ACTIVE by blast

  from H13 A2_NZ EXK show ?thesis
    unfolding hI13_Qback_Deq_Sync_def
    by blast
qed


lemma hwq_two_proc_cases_from_D4:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys s"
      and PD4: "program_counter s p = ''D4''"
  shows "p = P1 \<or> p = P2"
proof -
  have PIN: "p \<in> ProcSet"
    using Reachable_nonL0_in_ProcSet[OF RS] PD4 by auto
  thus ?thesis
    using N2
    unfolding ProcSet_def 
    by auto
qed


lemma hwq_ret_pre_no_D4_A2_D12:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and BR12:
        "(Q_arr u_ret_pre 1 = A1) \<and>
         (program_counter u_ret_pre P1 \<in> {''D1'', ''D2''})"
      and PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
  shows
    "\<not> (\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2)"
proof
  assume H: "\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2"
  then obtain p where
      PD4: "program_counter u_ret_pre p = ''D4''"
    and XA2: "x_var u_ret_pre p = A2"
    by blast

  have "p = P1 \<or> p = P2"
    using hwq_two_proc_cases_from_D4[OF N2 RS PD4] .

  then show False
  proof
    assume pP1: "p = P1"
    from BR12 PD4 pP1 show False by auto
  next
    assume pP2: "p = P2"
    from PC_E3_P2 PD4 pP2 show False by auto
  qed
qed


lemma hwq_ret_pre_no_D4_A2_D3j1:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and BRD3:
        "(Q_arr u_ret_pre 1 = A1) \<and>
         program_counter u_ret_pre P1 = ''D3'' \<and>
         j_var u_ret_pre P1 = 1"
      and PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
  shows
    "\<not> (\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2)"
proof
  assume H: "\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2"
  then obtain p where
      PD4: "program_counter u_ret_pre p = ''D4''"
    and XA2: "x_var u_ret_pre p = A2"
    by blast

  have "p = P1 \<or> p = P2"
    using hwq_two_proc_cases_from_D4[OF N2 RS PD4] .

  then show False
  proof
    assume pP1: "p = P1"
    from BRD3 PD4 pP1 show False by auto
  next
    assume pP2: "p = P2"
    from PC_E3_P2 PD4 pP2 show False by auto
  qed
qed


lemma hwq_ret_pre_no_D4_A2_D4A1:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and BRD4:
        "(Q_arr u_ret_pre 1 = BOT) \<and>
         program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1"
      and PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
  shows
    "\<not> (\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2)"
proof
  assume H: "\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2"
  then obtain p where
      PD4: "program_counter u_ret_pre p = ''D4''"
    and XA2: "x_var u_ret_pre p = A2"
    by blast

  have "p = P1 \<or> p = P2"
    using hwq_two_proc_cases_from_D4[OF N2 RS PD4] .

  then show False
  proof
    assume pP1: "p = P1"
    have A1A2_NE: "A1 \<noteq> A2"
      by simp
    from BRD4 XA2 pP1 A1A2_NE show False by auto
  next
    assume pP2: "p = P2"
    from PC_E3_P2 PD4 pP2 show False by auto
  qed
qed


lemma hwq_ret_pre_active_slot_not_bot_D12:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and INV: "system_invariant u_ret_pre"
      and BR12:
        "(Q_arr u_ret_pre 1 = A1) \<and>
         (program_counter u_ret_pre P1 \<in> {''D1'', ''D2''})"
      and PRE_RET_P2: "P2_pending_A2_safe u_ret_pre"
      and PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
      and NO_DEQ_RET_A2: "\<not> (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
  shows "Q_arr u_ret_pre (i_var u_ret_pre P2) \<noteq> BOT"
proof
  assume QBOT: "Q_arr u_ret_pre (i_var u_ret_pre P2) = BOT"

  have WIT:
    "(\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2) \<or>
     (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
    using hwq_ret_pre_bot_implies_d4_or_deqret_A2[OF INV PRE_RET_P2 PC_E3_P2 QBOT] .

  have NO_D4_A2:
    "\<not> (\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2)"
    using hwq_ret_pre_no_D4_A2_D12[OF N2 RS BR12 PC_E3_P2] .

  from WIT NO_D4_A2 NO_DEQ_RET_A2 show False
    by blast
qed


lemma hwq_ret_pre_active_slot_not_bot_D3j1:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and INV: "system_invariant u_ret_pre"
      and BRD3:
        "(Q_arr u_ret_pre 1 = A1) \<and>
         program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1"
      and PRE_RET_P2: "P2_pending_A2_safe u_ret_pre"
      and PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
      and NO_DEQ_RET_A2: "\<not> (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
  shows "Q_arr u_ret_pre (i_var u_ret_pre P2) \<noteq> BOT"
proof
  assume QBOT: "Q_arr u_ret_pre (i_var u_ret_pre P2) = BOT"

  have WIT:
    "(\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2) \<or>
     (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
    using hwq_ret_pre_bot_implies_d4_or_deqret_A2[OF INV PRE_RET_P2 PC_E3_P2 QBOT] .

  have NO_D4_A2:
    "\<not> (\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2)"
    using hwq_ret_pre_no_D4_A2_D3j1[OF N2 RS BRD3 PC_E3_P2] .

  from WIT NO_D4_A2 NO_DEQ_RET_A2 show False
    by blast
qed


lemma hwq_ret_pre_active_slot_not_bot_D4A1:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and INV: "system_invariant u_ret_pre"
      and BRD4:
        "(Q_arr u_ret_pre 1 = BOT) \<and>
         program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1"
      and PRE_RET_P2: "P2_pending_A2_safe u_ret_pre"
      and PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
      and NO_DEQ_RET_A2: "\<not> (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
  shows "Q_arr u_ret_pre (i_var u_ret_pre P2) \<noteq> BOT"
proof
  assume QBOT: "Q_arr u_ret_pre (i_var u_ret_pre P2) = BOT"

  have WIT:
    "(\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2) \<or>
     (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
    using hwq_ret_pre_bot_implies_d4_or_deqret_A2[OF INV PRE_RET_P2 PC_E3_P2 QBOT] .

  have NO_D4_A2:
    "\<not> (\<exists>p. program_counter u_ret_pre p = ''D4'' \<and> x_var u_ret_pre p = A2)"
    using hwq_ret_pre_no_D4_A2_D4A1[OF N2 RS BRD4 PC_E3_P2] .

  from WIT NO_D4_A2 NO_DEQ_RET_A2 show False
    by blast
qed


lemma hwq_ret_pre_active_slot_not_bot:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and INV_u_ret_pre: "system_invariant u_ret_pre"
      and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
      and T_RET_POST: "C_Tau_Star u_ret_post sk0"
      and X4: "X_var sk0 = 4"
      and PRE_RET_P1:
        "((Q_arr u_ret_pre 1 = A1) \<and>
           ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))
         \<or>
         ((Q_arr u_ret_pre 1 = BOT) \<and> program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1)"
      and PRE_RET_P2: "P2_pending_A2_safe u_ret_pre"
      and SEED_RET_PRE: "Slots23_seed u_ret_pre"
      and NO_DEQ_RET_A2: "\<not> (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
  shows "Q_arr u_ret_pre (i_var u_ret_pre P2) = A2"
proof -
  have PC_E3_P2: "program_counter u_ret_pre P2 = ''E3''"
    using hwq_ret_pre_common_facts
      [OF N2 INV_u_ret_pre STEP_RET T_RET_POST X4 PRE_RET_P2 SEED_RET_PRE]
    by blast

  have SLOT_A2_or_BOT:
    "Q_arr u_ret_pre (i_var u_ret_pre P2) = A2 \<or>
     Q_arr u_ret_pre (i_var u_ret_pre P2) = BOT"
    using hwq_ret_pre_common_facts
      [OF N2 INV_u_ret_pre STEP_RET T_RET_POST X4 PRE_RET_P2 SEED_RET_PRE]
    by blast

have SLOT_NOT_BOT:
  "Q_arr u_ret_pre (i_var u_ret_pre P2) \<noteq> BOT"
proof -
  from PRE_RET_P1 show ?thesis
  proof
    assume BR12:
      "((Q_arr u_ret_pre 1 = A1) \<and>
         ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))"

    have BR12_cases:
      "((Q_arr u_ret_pre 1 = A1) \<and>
         program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
       ((Q_arr u_ret_pre 1 = A1) \<and>
         program_counter u_ret_pre P1 = ''D3'' \<and>
         j_var u_ret_pre P1 = 1)"
      using BR12 by auto

    from BR12_cases show ?thesis
    proof
      assume BRD12:
        "(Q_arr u_ret_pre 1 = A1) \<and>
         program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}"
      show ?thesis
        using hwq_ret_pre_active_slot_not_bot_D12
          [OF N2 RS INV_u_ret_pre BRD12 PRE_RET_P2 PC_E3_P2 NO_DEQ_RET_A2] .
    next
      assume BRD3:
        "(Q_arr u_ret_pre 1 = A1) \<and>
         program_counter u_ret_pre P1 = ''D3'' \<and>
         j_var u_ret_pre P1 = 1"
      show ?thesis
        using hwq_ret_pre_active_slot_not_bot_D3j1
          [OF N2 RS INV_u_ret_pre BRD3 PRE_RET_P2 PC_E3_P2 NO_DEQ_RET_A2] .
    qed
  next
    assume BRD4:
      "(Q_arr u_ret_pre 1 = BOT) \<and>
       program_counter u_ret_pre P1 = ''D4'' \<and>
       x_var u_ret_pre P1 = A1"
    show ?thesis
      using hwq_ret_pre_active_slot_not_bot_D4A1
        [OF N2 RS INV_u_ret_pre BRD4 PRE_RET_P2 PC_E3_P2 NO_DEQ_RET_A2] .
  qed
qed

  from SLOT_A2_or_BOT SLOT_NOT_BOT show ?thesis
    by auto
qed


lemma hwq_p2_ret_collapse_from_seed:
  assumes N2: "N_Procs = 2"
      and RS: "Reachable_Sys u_ret_pre"
      and INV_u_ret_pre: "system_invariant u_ret_pre"
      and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
      and T_RET_POST: "C_Tau_Star u_ret_post sk0"
      and X4: "X_var sk0 = 4"
      and PRE_RET_P1:
        "((Q_arr u_ret_pre 1 = A1) \<and>
           ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
            (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))
         \<or>
         ((Q_arr u_ret_pre 1 = BOT) \<and> program_counter u_ret_pre P1 = ''D4'' \<and> x_var u_ret_pre P1 = A1)"
      and PRE_RET_P2: "P2_pending_A2_safe u_ret_pre"
      and SEED_RET_PRE: "Slots23_seed u_ret_pre"
      and NO_DEQ_RET_A2: "\<not> (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
  shows "{Q_arr u_ret_pre 2, Q_arr u_ret_pre 3} = {A2, A3}"
proof -
  have SLOT_A2:
    "Q_arr u_ret_pre (i_var u_ret_pre P2) = A2"
    using hwq_ret_pre_active_slot_not_bot
      [OF N2 RS INV_u_ret_pre STEP_RET T_RET_POST X4
          PRE_RET_P1 PRE_RET_P2 SEED_RET_PRE NO_DEQ_RET_A2] .

  have I23: "i_var u_ret_pre P2 \<in> {2,3}"
    using hwq_ret_pre_common_facts
      [OF N2 INV_u_ret_pre STEP_RET T_RET_POST X4 PRE_RET_P2 SEED_RET_PRE]
    by blast

  have A2_NE_A3: "A2 \<noteq> A3"
    by simp

  from SEED_RET_PRE have A3IN:
    "A3 \<in> {Q_arr u_ret_pre 2, Q_arr u_ret_pre 3}"
    unfolding Slots23_seed_def by auto

  show ?thesis
  proof (cases "i_var u_ret_pre P2 = 2")
    case True
    hence Q2: "Q_arr u_ret_pre 2 = A2"
      using SLOT_A2 by simp

    have Q3: "Q_arr u_ret_pre 3 = A3"
    proof -
      from A3IN have "A3 = Q_arr u_ret_pre 2 \<or> A3 = Q_arr u_ret_pre 3"
        by auto
      with Q2 A2_NE_A3 show ?thesis
        by auto
    qed

    from Q2 Q3 show ?thesis
      by auto
  next
    case False
    with I23 have I3: "i_var u_ret_pre P2 = 3"
      by auto

    hence Q3: "Q_arr u_ret_pre 3 = A2"
      using SLOT_A2 by simp

    have Q2: "Q_arr u_ret_pre 2 = A3"
    proof -
      from A3IN have "A3 = Q_arr u_ret_pre 2 \<or> A3 = Q_arr u_ret_pre 3"
        by auto
      with Q3 A2_NE_A3 show ?thesis
        by auto
    qed

    from Q2 Q3 show ?thesis
      by auto
  qed
qed

lemma hwq_p2_ret_preserves_slots23:
  assumes STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
  shows "program_counter u_ret_post P2 = ''L0'' \<and>
         Q_arr u_ret_post 2 = Q_arr u_ret_pre 2 \<and>
         Q_arr u_ret_post 3 = Q_arr u_ret_pre 3"
proof -
  from STEP_RET show ?thesis
  proof (cases rule: C_StepCR.cases)
    case (C_Sys_E3_vis p)
    then have pP2: "p = P2"
      unfolding mk_obs_def by auto

    have PCP2_POST: "program_counter u_ret_post P2 = ''L0''"
      using C_Sys_E3_vis pP2
      unfolding Sys_E3_def C_E3_def program_counter_def Let_def
      by (auto split: if_splits)

    have Q2_EQ: "Q_arr u_ret_post 2 = Q_arr u_ret_pre 2"
      using C_Sys_E3_vis pP2
      unfolding Sys_E3_def C_E3_def Q_arr_def Let_def
      by (auto split: if_splits)

    have Q3_EQ: "Q_arr u_ret_post 3 = Q_arr u_ret_pre 3"
      using C_Sys_E3_vis pP2
      unfolding Sys_E3_def C_E3_def Q_arr_def Let_def
      by (auto split: if_splits)

    from PCP2_POST Q2_EQ Q3_EQ show ?thesis
      by simp
  qed (auto simp: mk_obs_def)
qed



lemma hwq_slots23_suffix_from_pre_deq:
  assumes N2: "N_Procs = 2"
      and RS0: "Reachable_Sys s_before_deq"
      and INV0: "system_invariant s_before_deq"
      and PC1_0: "program_counter s_before_deq P1 = ''L0''"
      and PATH:
        "C_Path s_before_deq
          ([Some (mk_obs deq BOT P1 call), None, None, None, None] @
           [Some (mk_obs enq A2 P2 ret)]) sk0"
      and PREQ1: "Q_arr s_before_deq 1 = A1"
      and P2SAFE: "P2_pending_A2_safe s_before_deq"
      and X4: "X_var sk0 = 4"
      and SEED0: "Slots23_seed s_before_deq"
      and NO_DEQ_RET_A2_0:
        "\<not> (\<exists>p sn. DeqRetInHis s_before_deq p A2 sn)"
  shows "{Q_arr sk0 2, Q_arr sk0 3} = {A2, A3}"
proof -
  obtain s_deq_post where
      P_DEQ: "C_Path s_before_deq
                [Some (mk_obs deq BOT P1 call), None, None, None, None]
                s_deq_post"
    and M_RET: "C_Match s_deq_post (Some (mk_obs enq A2 P2 ret)) sk0"
    using C_Path_snocE[OF PATH] by blast

  have RS_s_deq_post: "Reachable_Sys s_deq_post"
    using C_Path_reachable[OF RS0 P_DEQ] .

  have INV_s_deq_post: "system_invariant s_deq_post"
    and MID_BRANCH_SAFE:
      "((Q_arr s_deq_post 1 = A1) \<and>
         ((program_counter s_deq_post P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter s_deq_post P1 = ''D3'' \<and> j_var s_deq_post P1 = 1)))
       \<or>
       ((Q_arr s_deq_post 1 = BOT) \<and>
        program_counter s_deq_post P1 = ''D4'' \<and>
        x_var s_deq_post P1 = A1)"
    and P2SAFE_deq_post: "P2_pending_A2_safe s_deq_post"
    and SEED_deq_post: "Slots23_seed s_deq_post"
    using hwq_suffix_after_deq_call_to_s_deq_post
      [OF N2 INV0 PC1_0 P_DEQ PREQ1 P2SAFE SEED0]
    by blast+

  obtain u_ret_pre u_ret_post where
      T_RET_PRE: "C_Tau_Star s_deq_post u_ret_pre"
    and STEP_RET: "C_StepCR u_ret_pre (Some (mk_obs enq A2 P2 ret)) u_ret_post"
    and T_RET_POST: "C_Tau_Star u_ret_post sk0"
    using my_C_Match_SomeE[OF M_RET] by blast

  have RS_u_ret_pre: "Reachable_Sys u_ret_pre"
    using C_Tau_Star_reachable[OF RS_s_deq_post T_RET_PRE] .

  have INV_u_ret_pre: "system_invariant u_ret_pre"
    and PRE_RET_P1:
      "((Q_arr u_ret_pre 1 = A1) \<and>
         ((program_counter u_ret_pre P1 \<in> {''D1'', ''D2''}) \<or>
          (program_counter u_ret_pre P1 = ''D3'' \<and> j_var u_ret_pre P1 = 1)))
       \<or>
       ((Q_arr u_ret_pre 1 = BOT) \<and>
        program_counter u_ret_pre P1 = ''D4'' \<and>
        x_var u_ret_pre P1 = A1)"
    and PRE_RET_P2: "P2_pending_A2_safe u_ret_pre"
    and SEED_RET_PRE: "Slots23_seed u_ret_pre"
    using hwq_pending_suffix_to_ret_pre
      [OF N2 INV_s_deq_post MID_BRANCH_SAFE P2SAFE_deq_post SEED_deq_post T_RET_PRE]
    by blast+

  have NO_DEQ_RET_A2_s_deq_post:
    "\<not> (\<exists>p sn. DeqRetInHis s_deq_post p A2 sn)"
  proof
    assume H: "\<exists>p sn. DeqRetInHis s_deq_post p A2 sn"
    then obtain p sn where DR_POST: "DeqRetInHis s_deq_post p A2 sn"
      by blast

    have NO_DEQ_RET_P_DEQ:
      "\<forall>x\<in>set [Some (mk_obs deq BOT P1 call), None, None, None, None].
         \<forall>p a. x \<noteq> Some (mk_obs deq a p ret)"
      unfolding mk_obs_def
      by auto

    have KEEP:
      "DeqRetInHis s_deq_post p A2 sn \<longleftrightarrow> DeqRetInHis s_before_deq p A2 sn"
      using C_Path_no_deq_ret_preserves_DeqRetInHis[OF P_DEQ NO_DEQ_RET_P_DEQ] .

    from DR_POST KEEP NO_DEQ_RET_A2_0 show False
      by blast
  qed

  have NO_DEQ_RET_A2_u_ret_pre:
    "\<not> (\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn)"
  proof
    assume H: "\<exists>p sn. DeqRetInHis u_ret_pre p A2 sn"
    then obtain p sn where DR_PRE: "DeqRetInHis u_ret_pre p A2 sn"
      by blast

    have HIS_EQ: "his_seq u_ret_pre = his_seq s_deq_post"
      using C_Tau_Star_preserves_his_seq[OF T_RET_PRE]
      by simp

    have KEEP:
      "DeqRetInHis u_ret_pre p A2 sn \<longleftrightarrow> DeqRetInHis s_deq_post p A2 sn"
      using HIS_EQ
      unfolding DeqRetInHis_def Model.DeqRetInHis_def
      by auto

    from DR_PRE KEEP NO_DEQ_RET_A2_s_deq_post show False
      by blast
  qed

  have Q23_PRE:
    "{Q_arr u_ret_pre 2, Q_arr u_ret_pre 3} = {A2, A3}"
    using hwq_p2_ret_collapse_from_seed
      [OF N2 RS_u_ret_pre INV_u_ret_pre STEP_RET T_RET_POST X4
          PRE_RET_P1 PRE_RET_P2 SEED_RET_PRE NO_DEQ_RET_A2_u_ret_pre] .

  have RET_PRES:
    "program_counter u_ret_post P2 = ''L0'' \<and>
     Q_arr u_ret_post 2 = Q_arr u_ret_pre 2 \<and>
     Q_arr u_ret_post 3 = Q_arr u_ret_pre 3"
    using hwq_p2_ret_preserves_slots23[OF STEP_RET] .

  from RET_PRES have
      PCP2_POST: "program_counter u_ret_post P2 = ''L0''"
    and Q2_POST_EQ: "Q_arr u_ret_post 2 = Q_arr u_ret_pre 2"
    and Q3_POST_EQ: "Q_arr u_ret_post 3 = Q_arr u_ret_pre 3"
    by auto

  have Q23_POST:
    "{Q_arr u_ret_post 2, Q_arr u_ret_post 3} = {A2, A3}"
    using Q23_PRE Q2_POST_EQ Q3_POST_EQ
    by auto

  have NXT_RET: "Next u_ret_pre u_ret_post"
    using C_StepCR_into_Next[OF STEP_RET] .

  have INV_u_ret_post: "system_invariant u_ret_post"
    using Sys_Inv_Step[OF INV_u_ret_pre NXT_RET] .

  have BR_POST:
    "((Q_arr u_ret_post 1 = A1) \<and>
       ((program_counter u_ret_post P1 \<in> {''D1'', ''D2''}) \<or>
        (program_counter u_ret_post P1 = ''D3'' \<and> j_var u_ret_post P1 = 1)))
     \<or>
     ((Q_arr u_ret_post 1 = BOT) \<and>
      program_counter u_ret_post P1 = ''D4'' \<and>
      x_var u_ret_post P1 = A1)"
    using C_StepCR_P2_ret_preserves_P1_branch[OF N2 STEP_RET PRE_RET_P1]
    by auto

  have Q23_FINAL_EQ:
    "Q_arr sk0 2 = Q_arr u_ret_post 2 \<and>
     Q_arr sk0 3 = Q_arr u_ret_post 3"
    using Tau_Star_preserves_slots23_after_p2_ret
      [OF N2 INV_u_ret_post PCP2_POST BR_POST T_RET_POST] .

  from Q23_POST Q23_FINAL_EQ show ?thesis
    by auto
qed

lemma hwq_full_e1_pre_deq_no_deq_ret_A2:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and PREFIX: "C_Path s0
        [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
         Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
         None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
  shows "\<not> (\<exists>p sn. DeqRetInHis s_before_deq p A2 sn)"
proof
  assume H: "\<exists>p sn. DeqRetInHis s_before_deq p A2 sn"
  then obtain p sn where DR: "DeqRetInHis s_before_deq p A2 sn"
    by blast

  have NO_DEQ_RET_PREFIX:
    "\<forall>x\<in>set
      [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
       Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
       None, None, Some (mk_obs enq A3 P1 ret)].
       \<forall>p a. x \<noteq> Some (mk_obs deq a p ret)"
    unfolding mk_obs_def
    by auto

  have KEEP:
    "DeqRetInHis s_before_deq p A2 sn \<longleftrightarrow> DeqRetInHis s0 p A2 sn"
    using C_Path_no_deq_ret_preserves_DeqRetInHis[OF PREFIX NO_DEQ_RET_PREFIX] .

  have INIT0: "\<not> DeqRetInHis s0 p A2 sn"
    using Init_no_DeqRetInHis[OF INIT] .

  from DR KEEP INIT0 show False
    by blast
qed

(* lvyi *)

(* Bridge 5: set summaryconcrete *)
lemma hwq_full_e1_quantum_set_shape:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
      and INV: "system_invariant sk0"
      and X4: "X_var sk0 = 4"
  shows "{Q_arr sk0 2, Q_arr sk0 3} = {A2, A3}"
proof -
  have SPLIT: "e1_labels =
      ([Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
        Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
        None, None, Some (mk_obs enq A3 P1 ret)]) @
      ([Some (mk_obs deq BOT P1 call), None, None, None, None] @
       [Some (mk_obs enq A2 P2 ret)])"
    unfolding e1_labels_def by simp

  obtain s_before_deq where
      P_PREFIX:
        "C_Path s0
          [Some (mk_obs enq A1 P1 call), None, None, Some (mk_obs enq A1 P1 ret),
           Some (mk_obs enq A2 P2 call), None, Some (mk_obs enq A3 P1 call),
           None, None, Some (mk_obs enq A3 P1 ret)] s_before_deq"
    and P_SUFFIX:
        "C_Path s_before_deq
          ([Some (mk_obs deq BOT P1 call), None, None, None, None] @
           [Some (mk_obs enq A2 P2 ret)]) sk0"
    using C_Path_appendE[OF E1FULL[unfolded SPLIT]]
    by blast

  have PREQ1: "Q_arr s_before_deq 1 = A1"
    using hwq_full_e1_pre_deq_q1_shape[OF N2 INIT P_PREFIX] .

  have P2SAFE: "P2_pending_A2_safe s_before_deq"
    using hwq_full_e1_pre_deq_p2_safe_shape[OF N2 INIT P_PREFIX] .

  have PC1_0: "program_counter s_before_deq P1 = ''L0''"
    using hwq_full_e1_pre_deq_p1_l0_shape[OF N2 INIT P_PREFIX] .

  have RS0: "Reachable_Sys s_before_deq"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] P_PREFIX] .

  have INV0: "system_invariant s_before_deq"
    using Reachable_Sys_system_invariant[OF RS0] .

  have SEED0: "Slots23_seed s_before_deq"
    using hwq_full_e1_pre_deq_slots23_seed[OF N2 INIT P_PREFIX] .

  have NO_DEQ_RET_A2_0:
    "\<not> (\<exists>p sn. DeqRetInHis s_before_deq p A2 sn)"
    using hwq_full_e1_pre_deq_no_deq_ret_A2[OF N2 INIT P_PREFIX] .

  show ?thesis
    using hwq_slots23_suffix_from_pre_deq
      [OF N2 RS0 INV0 PC1_0 P_SUFFIX PREQ1 P2SAFE X4 SEED0 NO_DEQ_RET_A2_0] .
qed



lemma hwq_full_e1_reaches_quantum_shape:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
  shows "E1_HWQ_quantum_shape sk0"
proof -
  have RS: "Reachable_Sys sk0"
    using C_Path_reachable[OF Reachable_Sys.init[OF INIT] E1FULL] .

  have INV: "system_invariant sk0"
    using Reachable_Sys_system_invariant[OF RS] .

  (* 1: P2 () *)
  have P2_DONE: "program_counter sk0 P2 = ''L0''"
    using hwq_full_e1_P2_DONE[OF N2 INIT E1FULL] .

  (* 2: X_var () *)
  have X4: "X_var sk0 = 4"
    using hwq_full_e1_X4[OF N2 INIT E1FULL INV] .

  (* 3: P1 *)
  have HPD: "HasPendingDeq sk0 P1"
    using hwq_full_e1_pending_deq_P1[OF N2 INIT E1FULL INV X4] .

  (* 4: P1 local branch state *)
  have P1_BRANCH:
    "(Q_arr sk0 1 = A1 \<and>
      ((program_counter sk0 P1 \<in> {''D1'', ''D2''}) \<or>
       (program_counter sk0 P1 = ''D3'' \<and> j_var sk0 P1 = 1)))
     \<or>
     (Q_arr sk0 1 = BOT \<and> program_counter sk0 P1 = ''D4'' \<and> x_var sk0 P1 = A1)"
    using hwq_full_e1_P1_quantum_branch[OF N2 INIT E1FULL INV X4] .

  (* 5: set summary *)
  have QSET23: "{Q_arr sk0 2, Q_arr sk0 3} = {A2, A3}"
    using hwq_full_e1_quantum_set_shape[OF N2 INIT E1FULL INV X4] .

  (* final:, automatic Quantum Shape *)
  show ?thesis
    unfolding E1_HWQ_quantum_shape_def
    using INV X4 P2_DONE HPD P1_BRANCH QSET23
    by auto
qed



lemma hwq_prefix_quantum_shape_from_matched_e1:
  assumes N2: "N_Procs = 2"
      and INIT: "Init s0"
      and E1FULL: "C_Path s0 e1_labels sk0"
  shows "E1_HWQ_quantum_shape sk0"
  using hwq_full_e1_reaches_quantum_shape[OF N2 INIT E1FULL] .


lemma T_Path_snocE_aux:
  assumes PATH: "T_Path s (xs @ [l]) t"
  shows "\<exists>u. T_Path s xs u \<and> T_StepCR u l t"
using PATH
proof (induction xs arbitrary: s t)
  case Nil
  then have P: "T_Path s [l] t"
    by simp
  then obtain s1 where
      STEP: "T_StepCR s l s1"
    and NIL: "T_Path s1 [] t"
    by (cases rule: T_Path.cases) auto
  from NIL have "t = s1"
    by (cases rule: T_Path.cases) auto
  with STEP have "T_StepCR s l t"
    by simp
  moreover have "T_Path s [] s"
    by (rule T_Path.nil)
  ultimately show ?case
    by blast
next
  case (Cons a xs)
  then have P: "T_Path s (a # (xs @ [l])) t"
    by simp
  then obtain s1 where
      STEP: "T_StepCR s a s1"
    and REST: "T_Path s1 (xs @ [l]) t"
    by (cases rule: T_Path.cases) auto
  from Cons.IH[OF REST] obtain u where
      PREF: "T_Path s1 xs u"
    and LAST: "T_StepCR u l t"
    by blast
  have "T_Path s (a # xs) u"
    using STEP PREF
    by (rule T_Path.cons)
  with LAST show ?case
    by blast
qed

lemma T_Path_snocE:
  assumes PATH: "T_Path s (xs @ [l]) t"
  obtains u where "T_Path s xs u" and "T_StepCR u l t"
  using T_Path_snocE_aux[OF PATH]
  by blast


subsection \<open>Main theorem\<close>

theorem TSQ_not_forward_simulated_by_HWQ_2proc:
  assumes N2: "N_Procs = 2"
  shows "\<not> (\<exists>R. FW_Sim_CR R)"
proof
  assume H: "\<exists>R. FW_Sim_CR R"
  then obtain R where SIM: "FW_Sim_CR R"
    by blast

  from tsq_e1_exists_2proc[OF N2]
  obtain t0 tk where
      TINIT: "T_Init t0"
    and TPREFIX: "T_Path t0 e1_labels tk"
    and E1TSQ: "E1_TSQ_shape tk"
    by blast

  have INVK: "TSQ_State_Inv_Plus tk"
    using T_Path_TSQ_State_Inv_Plus[OF TINIT TPREFIX] .

  obtain tm where
      TPRE: "T_Path t0 e1_pre_labels tm"
    and TLAST: "T_StepCR tm (Some (mk_obs enq A2 P2 ret)) tk"
    using T_Path_snocE[OF TPREFIX[unfolded e1_labels_split]]
    by blast

  from TLAST obtain p where
      PIN: "p \<in> ProcSet"
    and E3RET: "T_E3 p tm tk"
    and LABRET: "mk_obs enq (t_v tm p) p ret = mk_obs enq A2 P2 ret"
    by (cases rule: T_StepCR.cases) (auto simp: mk_obs_def)

  have pP2: "p = P2"
    using LABRET
    unfolding mk_obs_def
    by auto

  have PC2K: "t_pc tk P2 = ''TL0''"
    using E3RET pP2
    unfolding T_E3_def
    by auto

  from FW_Sim_CR_from_init[OF SIM TINIT TPREFIX]
  obtain s0 sk where
      SINIT: "Init s0"
    and CPREFIX: "C_Path s0 e1_labels sk"
    and RELK: "R tk sk"
    by blast

  have E1HWQ_quant: "E1_HWQ_quantum_shape sk"
    using hwq_prefix_quantum_shape_from_matched_e1[OF N2 SINIT CPREFIX] .

  from tsq_e2_from_e1[OF N2 E1TSQ INVK]
  obtain t2 where TE2: "T_Path tk e2_labels t2"
    by blast

  from tsq_e3_from_e1[OF N2 E1TSQ INVK PC2K]
  obtain t3 where TE3: "T_Path tk e3_labels t3"
    by blast

  obtain s2 where CE2: "C_Path sk e2_labels s2"
    using FW_Sim_CR_path[OF SIM RELK TE2] by blast

  obtain s3 where CE3: "C_Path sk e3_labels s3"
    using FW_Sim_CR_path[OF SIM RELK TE3] by blast

  have E1HWQ_relaxed: "E1_HWQ_relaxed_shape sk"
    using collapse_quantum_to_relaxed[OF N2 E1HWQ_quant CE2] .

  from hwq_no_common_match_from_e1[OF N2 E1HWQ_relaxed CE2 CE3]
  show False .
qed

end
