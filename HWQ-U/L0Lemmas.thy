theory L0Lemmas
  imports
    Main
    "HOL-Library.Multiset"
    Model
    PureLib
    StateLib
    DeqLib
    EnqLib
    D3Lemmas
begin

definition L0 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "L0 p s s' \<longleftrightarrow> Sys_L0 p s s'"

definition L0_E1_update_state :: "SysState \<Rightarrow> nat \<Rightarrow> SysState" where
  "L0_E1_update_state s p \<equiv>
     (let cs = fst s; us = snd s in
       (cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''E1'' else CState.c_program_counter cs x),
             V_var := CState.V_var cs + 1,
             v_var := (\<lambda>x. if x = p then CState.V_var cs else CState.v_var cs x) \<rparr>,
        us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter us x),
            u_his_seq := u_his_seq us @ [mk_act enq (CState.V_var cs) p (UState.S_var us p) call] \<rparr>))"

definition L0_D1_update_state :: "SysState \<Rightarrow> nat \<Rightarrow> SysState" where
  "L0_D1_update_state s p \<equiv>
     (let cs = fst s; us = snd s in
       (cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D1'' else CState.c_program_counter cs x) \<rparr>,
        us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us x),
            u_his_seq := u_his_seq us @ [mk_act deq BOT p (UState.S_var us p) call] \<rparr>))"

lemma L0_pc_cases:
  assumes STEP: "L0 p s s'"
  shows "program_counter s' p = ''E1'' \<or> program_counter s' p = ''D1''"
  using STEP
  unfolding L0_def Sys_L0_def C_L0_def program_counter_def
  by (auto simp: Let_def split: if_splits)

lemma L0_E1_update:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''E1''"
  shows "s' = L0_E1_update_state s p"
proof -
  have pc_E1: "CState.c_program_counter (fst s') p = ''E1''"
    using PC unfolding program_counter_def by simp
  have fst_eq:
    "fst s' =
      (fst s)\<lparr> c_program_counter := (\<lambda>x. if x = p then ''E1'' else CState.c_program_counter (fst s) x),
                V_var := CState.V_var (fst s) + 1,
                v_var := (\<lambda>x. if x = p then CState.V_var (fst s) else CState.v_var (fst s) x) \<rparr>"
    using STEP PC
    unfolding L0_def Sys_L0_def C_L0_def program_counter_def
    by (auto simp: Let_def split: if_splits)

  obtain us_mid where
    mid_E: "U_L0_E p (snd s) us_mid" and
    mid_E1: "U_E1 p (CState.V_var (fst s)) (s_var s p) us_mid (snd s')"
    using STEP pc_E1
    unfolding L0_def Sys_L0_def
    by auto

  have us_mid_def:
    "us_mid =
      (snd s)\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UE1'' else u_program_counter (snd s) x) \<rparr>"
    using mid_E unfolding U_L0_E_def by auto

  have snd_eq:
    "snd s' =
      (snd s)\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter (snd s) x),
                u_his_seq := u_his_seq (snd s) @ [mk_act enq (CState.V_var (fst s)) p (s_var s p) call] \<rparr>"
    using mid_E1 us_mid_def
    unfolding U_E1_def
    by (simp add: fun_eq_iff)

show ?thesis
  using fst_eq snd_eq
  unfolding L0_E1_update_state_def s_var_def
  by (simp add: Let_def prod_eq_iff)
qed

lemma L0_D1_update:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''D1''"
  shows "s' = L0_D1_update_state s p"
proof -
  have pc_D1: "CState.c_program_counter (fst s') p = ''D1''"
    using PC unfolding program_counter_def by simp
  have fst_eq:
    "fst s' =
      (fst s)\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D1'' else CState.c_program_counter (fst s) x) \<rparr>"
    using STEP PC
    unfolding L0_def Sys_L0_def C_L0_def program_counter_def
    by (auto simp: Let_def split: if_splits)

  obtain us_mid where
    mid_D: "U_L0_D p (snd s) us_mid" and
    mid_D1: "U_D1 p (s_var s p) us_mid (snd s')"
    using STEP pc_D1
    unfolding L0_def Sys_L0_def
    by auto

  have us_mid_def:
    "us_mid =
      (snd s)\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD1'' else u_program_counter (snd s) x) \<rparr>"
    using mid_D unfolding U_L0_D_def by auto

  have snd_eq:
    "snd s' =
      (snd s)\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter (snd s) x),
                u_his_seq := u_his_seq (snd s) @ [mk_act deq BOT p (s_var s p) call] \<rparr>"
    using mid_D1 us_mid_def
    unfolding U_D1_def
    by (simp add: fun_eq_iff)

show ?thesis
  using fst_eq snd_eq
  unfolding L0_D1_update_state_def s_var_def
  by (simp add: Let_def prod_eq_iff)
qed

lemma L0_E1_state:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''E1''"
  shows "s' = L0_E1_update_state s p"
  using L0_E1_update[OF STEP PC] .

lemma L0_D1_state:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''D1''"
  shows "s' = L0_D1_update_state s p"
  using L0_D1_update[OF STEP PC] .

lemma L0_E1_history_append:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''E1''"
  shows "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
proof -
  have s'_def: "s' = L0_E1_update_state s p"
    using L0_E1_state[OF STEP PC] .
  show ?thesis
    using s'_def
    unfolding L0_E1_update_state_def his_seq_def V_var_def s_var_def
    by (simp add: Let_def)
qed

lemma L0_D1_history_append:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''D1''"
  shows "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
proof -
  have s'_def: "s' = L0_D1_update_state s p"
    using L0_D1_state[OF STEP PC] .
  show ?thesis
    using s'_def
    unfolding L0_D1_update_state_def his_seq_def s_var_def
    by (simp add: Let_def)
qed

lemma L0_E1_lin_unchanged:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''E1''"
  shows "lin_seq s' = lin_seq s"
proof -
  have s'_def: "s' = L0_E1_update_state s p"
    using L0_E1_state[OF STEP PC] .
  show ?thesis
    using s'_def
    unfolding L0_E1_update_state_def lin_seq_def
    by (simp add: Let_def)
qed

lemma L0_D1_lin_unchanged:
  assumes STEP: "L0 p s s'"
  assumes PC: "program_counter s' p = ''D1''"
  shows "lin_seq s' = lin_seq s"
proof -
  have s'_def: "s' = L0_D1_update_state s p"
    using L0_D1_state[OF STEP PC] .
  show ?thesis
    using s'_def
    unfolding L0_D1_update_state_def lin_seq_def
    by (simp add: Let_def)
qed

lemma L0_no_match_ret_no_HB_from:
  assumes NORET: "\<forall>k<length H. \<not> match_ret H k op"
  shows "\<not> HB H op x"
proof
  assume hb: "HB H op x"

  obtain kr kc where
    kr_lt_kc: "kr < kc"
    and mr: "match_ret H kr op"
    and mc: "match_call H kc x"
    using hb
    unfolding HB_def
    by metis

  have kr_lt_H:
    "kr < length H"
    using mr
    unfolding match_ret_def
    by simp

  show False
    using NORET kr_lt_H mr
    by blast
qed


lemma L0_HB_consistent_append_no_ret:
  assumes HBc: "HB_consistent L H"
  assumes NORET: "\<forall>k<length H. \<not> match_ret H k op"
  shows "HB_consistent (L @ [op]) H"
proof (rule HB_consistent_append)
  show "HB_consistent L H"
    using HBc .
next
  show "\<forall>x\<in>set L. \<not> HB H op x"
    using L0_no_match_ret_no_HB_from[OF NORET]
    by blast
next
  show "\<not> HB H op op"
    using L0_no_match_ret_no_HB_from[OF NORET] .
qed


lemma L0_all_lin_called_from_lI1:
  assumes LI1: "lI1_Op_Sets_Equivalence s"
  shows "\<forall>a\<in>set (lin_seq s). OpCalledInHis (his_seq s) a"
proof
  fix a
  assume a_in: "a \<in> set (lin_seq s)"

  have a_oplin:
    "a \<in> OPLin s"
    using a_in unfolding OPLin_def by simp

  have cases:
    "a \<in> OP_A_enq s \<or> a \<in> OP_A_deq s \<or> a \<in> OP_B_enq s"
    using LI1 a_oplin
    unfolding lI1_Op_Sets_Equivalence_def
    by blast

  thus "OpCalledInHis (his_seq s) a"
  proof
    assume "a \<in> OP_A_enq s"
    then obtain qq vv sn where
      a_eq: "a = mk_op enq vv qq sn"
      and call: "EnqCallInHis s qq vv sn"
      unfolding OP_A_enq_def by blast

    show ?thesis
      using EnqCallInHis_imp_OpCalledInHis[OF call]
      unfolding a_eq by simp
  next
    assume rest: "a \<in> OP_A_deq s \<or> a \<in> OP_B_enq s"
    thus ?thesis
    proof
      assume "a \<in> OP_A_deq s"

      hence name_deq: "op_name a = deq"
        and call: "DeqCallInHis s (op_pid a) (op_ssn a)"
        unfolding OP_A_deq_def
        by auto

      have a_mk:
        "mk_op deq (op_val a) (op_pid a) (op_ssn a) = a"
        using name_deq
        by (cases a)
           (simp add: mk_op_def op_name_def op_val_def op_pid_def op_ssn_def)

      have called_mk:
        "OpCalledInHis (his_seq s)
           (mk_op deq (op_val a) (op_pid a) (op_ssn a))"
        using DeqCallInHis_imp_OpCalledInHis[OF call, of "op_val a"] .

      show ?thesis
        using called_mk a_mk
        by simp
    next
      assume "a \<in> OP_B_enq s"
      then obtain qq vv sn where
        a_eq: "a = mk_op enq vv qq sn"
        and call: "EnqCallInHis s qq vv sn"
        unfolding OP_B_enq_def by blast

      show ?thesis
        using EnqCallInHis_imp_OpCalledInHis[OF call]
        unfolding a_eq by simp
    qed
  qed
qed

lemma hI21_enq_ret_obtain_call:
  assumes H21: "hI21_Ret_Implies_Call s"
  assumes k_lt: "k < length (his_seq s)"
  assumes name_enq: "act_name (his_seq s ! k) = enq"
  assumes cr_ret: "act_cr (his_seq s ! k) = ret"
  obtains tm where
    "tm < k"
    "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k)"
    "act_name (his_seq s ! tm) = act_name (his_seq s ! k)"
    "act_cr (his_seq s ! tm) = call"
    "act_val (his_seq s ! tm) = act_val (his_seq s ! k)"
proof -
  have raw:
    "\<exists>tm<k.
       act_pid (his_seq s ! tm) = act_pid (his_seq s ! k) \<and>
       act_name (his_seq s ! tm) = act_name (his_seq s ! k) \<and>
       act_cr (his_seq s ! tm) = call \<and>
       (if act_name (his_seq s ! k) = enq
        then act_val (his_seq s ! tm) = act_val (his_seq s ! k)
        else act_val (his_seq s ! tm) = BOT)"
    using H21 k_lt cr_ret
    unfolding hI21_Ret_Implies_Call_def
    by blast

  then obtain tm where
    tm_lt: "tm < k"
    and pid_eq:
      "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k)"
    and name_eq:
      "act_name (his_seq s ! tm) = act_name (his_seq s ! k)"
    and cr_call:
      "act_cr (his_seq s ! tm) = call"
    and val_eq_if:
      "(if act_name (his_seq s ! k) = enq
        then act_val (his_seq s ! tm) = act_val (his_seq s ! k)
        else act_val (his_seq s ! tm) = BOT)"
    by blast

  have val_eq:
    "act_val (his_seq s ! tm) = act_val (his_seq s ! k)"
    using val_eq_if name_enq
    by simp

  show ?thesis
    using that[OF tm_lt pid_eq name_eq cr_call val_eq] .
qed

lemma hI7_His_WF_append_call:
  assumes WF: "hI7_His_WF s"
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes CALL: "act_cr e = call"
  shows "hI7_His_WF s'"
proof -
  show ?thesis
    unfolding hI7_His_WF_def
  proof (intro allI impI)
    fix k
    assume K: "k < length (his_seq s')"
    let ?e_ret = "his_seq s' ! k"
    have CORE:
      "act_cr ?e_ret = ret \<longrightarrow>
       (\<exists>j<k.
          let e_call = his_seq s' ! j in
          act_pid e_call = act_pid ?e_ret \<and>
          act_ssn e_call = act_ssn ?e_ret \<and>
          act_name e_call = act_name ?e_ret \<and>
          act_cr e_call = call \<and>
          (if act_name ?e_ret = enq
           then act_val e_call = act_val ?e_ret
           else act_val e_call = BOT))"
    proof
      assume RET: "act_cr ?e_ret = ret"
      let ?n = "length (his_seq s)"
      have LEN: "length (his_seq s') = Suc ?n"
        using HIS by simp
      show "\<exists>j<k.
              let e_call = his_seq s' ! j in
              act_pid e_call = act_pid ?e_ret \<and>
              act_ssn e_call = act_ssn ?e_ret \<and>
              act_name e_call = act_name ?e_ret \<and>
              act_cr e_call = call \<and>
              (if act_name ?e_ret = enq
               then act_val e_call = act_val ?e_ret
               else act_val e_call = BOT)"
      proof (cases "k < ?n")
        case True
        have K_EQ: "?e_ret = his_seq s ! k"
          using HIS True by (simp add: nth_append)
        have RET_OLD: "act_cr (his_seq s ! k) = ret"
          using RET K_EQ by simp
        have STEP:
          "let e_ret = his_seq s ! k in
             act_cr e_ret = ret \<longrightarrow>
             (\<exists>j<k.
                let e_call = his_seq s ! j in
                act_pid e_call = act_pid e_ret \<and>
                act_ssn e_call = act_ssn e_ret \<and>
                act_name e_call = act_name e_ret \<and>
                act_cr e_call = call \<and>
                (if act_name e_ret = enq
                 then act_val e_call = act_val e_ret
                 else act_val e_call = BOT))"
          using WF True
          unfolding hI7_His_WF_def
          by blast
        have OLD:
          "\<exists>j<k.
             let e_call = his_seq s ! j in
             act_pid e_call = act_pid (his_seq s ! k) \<and>
             act_ssn e_call = act_ssn (his_seq s ! k) \<and>
             act_name e_call = act_name (his_seq s ! k) \<and>
             act_cr e_call = call \<and>
             (if act_name (his_seq s ! k) = enq
              then act_val e_call = act_val (his_seq s ! k)
              else act_val e_call = BOT)"
          using STEP RET_OLD
          unfolding Let_def
          by blast
        then obtain j where
          JLT: "j < k" and
          JPROP:
            "let e_call = his_seq s ! j in
             act_pid e_call = act_pid (his_seq s ! k) \<and>
             act_ssn e_call = act_ssn (his_seq s ! k) \<and>
             act_name e_call = act_name (his_seq s ! k) \<and>
             act_cr e_call = call \<and>
             (if act_name (his_seq s ! k) = enq
              then act_val e_call = act_val (his_seq s ! k)
              else act_val e_call = BOT)"
          by blast
        have J_OLD: "j < ?n"
          using JLT True by linarith
        have J_EQ: "his_seq s' ! j = his_seq s ! j"
          using HIS J_OLD by (simp add: nth_append)
        show ?thesis
        proof (rule exI[where x = j], intro conjI)
          show "j < k"
            using JLT .
          show "let e_call = his_seq s' ! j in
                  act_pid e_call = act_pid ?e_ret \<and>
                  act_ssn e_call = act_ssn ?e_ret \<and>
                  act_name e_call = act_name ?e_ret \<and>
                  act_cr e_call = call \<and>
                  (if act_name ?e_ret = enq
                   then act_val e_call = act_val ?e_ret
                   else act_val e_call = BOT)"
            using JPROP J_EQ K_EQ
            unfolding Let_def
            by simp
        qed
      next
        case False
        then have K_LAST: "k = ?n"
          using K LEN by linarith
        have E_LAST: "?e_ret = e"
          using HIS K_LAST by simp
        have False
          using CALL RET E_LAST by simp
        then show ?thesis
          by blast
      qed
    qed
    show "let e_ret = his_seq s' ! k in
            act_cr e_ret = ret \<longrightarrow>
            (\<exists>j<k.
               let e_call = his_seq s' ! j in
               act_pid e_call = act_pid e_ret \<and>
               act_ssn e_call = act_ssn e_ret \<and>
               act_name e_call = act_name e_ret \<and>
               act_cr e_call = call \<and>
               (if act_name e_ret = enq
                then act_val e_call = act_val e_ret
                else act_val e_call = BOT))"
      using CORE by simp
  qed
qed

lemma hI21_Ret_Implies_Call_append_call:
  assumes H13: "hI21_Ret_Implies_Call s"
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes CALL: "act_cr e = call"
  shows "hI21_Ret_Implies_Call s'"
proof -
  show ?thesis
    unfolding hI21_Ret_Implies_Call_def
  proof (intro allI impI)
    fix k
    assume K: "k < length (his_seq s')"
    assume RET: "act_cr (his_seq s' ! k) = ret"
    let ?n = "length (his_seq s)"
    have LEN: "length (his_seq s') = Suc ?n"
      using HIS by simp
    show "\<exists>tm<k.
            act_pid (his_seq s' ! tm) = act_pid (his_seq s' ! k) \<and>
            act_name (his_seq s' ! tm) = act_name (his_seq s' ! k) \<and>
            act_cr (his_seq s' ! tm) = call \<and>
            (if act_name (his_seq s' ! k) = enq
             then act_val (his_seq s' ! tm) = act_val (his_seq s' ! k)
             else act_val (his_seq s' ! tm) = BOT)"
    proof (cases "k < ?n")
      case True
      have K_EQ: "his_seq s' ! k = his_seq s ! k"
        using HIS True by (simp add: nth_append)
      have RET_OLD: "act_cr (his_seq s ! k) = ret"
        using RET K_EQ by simp
      have H13_K:
        "\<forall>i<length (his_seq s).
           act_cr (his_seq s ! i) = ret \<longrightarrow>
           (\<exists>tm<i.
              act_pid (his_seq s ! tm) = act_pid (his_seq s ! i) \<and>
              act_name (his_seq s ! tm) = act_name (his_seq s ! i) \<and>
              act_cr (his_seq s ! tm) = call \<and>
              (if act_name (his_seq s ! i) = enq
               then act_val (his_seq s ! tm) = act_val (his_seq s ! i)
               else act_val (his_seq s ! tm) = BOT))"
        using H13
        unfolding hI21_Ret_Implies_Call_def
        by simp
      have STEP0:
        "act_cr (his_seq s ! k) = ret \<longrightarrow>
         (\<exists>tm<k.
            act_pid (his_seq s ! tm) = act_pid (his_seq s ! k) \<and>
            act_name (his_seq s ! tm) = act_name (his_seq s ! k) \<and>
            act_cr (his_seq s ! tm) = call \<and>
            (if act_name (his_seq s ! k) = enq
             then act_val (his_seq s ! tm) = act_val (his_seq s ! k)
             else act_val (his_seq s ! tm) = BOT))"
        using H13_K True
        by blast
      have OLD_RAW:
        "\<exists>tm<k.
           act_pid (his_seq s ! tm) = act_pid (his_seq s ! k) \<and>
           act_name (his_seq s ! tm) = act_name (his_seq s ! k) \<and>
           act_cr (his_seq s ! tm) = call \<and>
           (if act_name (his_seq s ! k) = enq
            then act_val (his_seq s ! tm) = act_val (his_seq s ! k)
            else act_val (his_seq s ! tm) = BOT)"
        using STEP0 RET_OLD
        by (rule mp)
      then obtain tm where
        TM: "tm < k" and
        TM_PROP:
          "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k) \<and>
           act_name (his_seq s ! tm) = act_name (his_seq s ! k) \<and>
           act_cr (his_seq s ! tm) = call \<and>
           (if act_name (his_seq s ! k) = enq
            then act_val (his_seq s ! tm) = act_val (his_seq s ! k)
            else act_val (his_seq s ! tm) = BOT)"
        by blast
      have TM_OLD: "tm < ?n"
        using TM True by linarith
      have TM_EQ: "his_seq s' ! tm = his_seq s ! tm"
        using HIS TM_OLD by (simp add: nth_append)
      show "\<exists>tm<k.
              act_pid (his_seq s' ! tm) = act_pid (his_seq s' ! k) \<and>
              act_name (his_seq s' ! tm) = act_name (his_seq s' ! k) \<and>
              act_cr (his_seq s' ! tm) = call \<and>
              (if act_name (his_seq s' ! k) = enq
               then act_val (his_seq s' ! tm) = act_val (his_seq s' ! k)
               else act_val (his_seq s' ! tm) = BOT)"
      proof (rule exI[where x = tm])
        show "tm < k \<and>
              act_pid (his_seq s' ! tm) = act_pid (his_seq s' ! k) \<and>
              act_name (his_seq s' ! tm) = act_name (his_seq s' ! k) \<and>
              act_cr (his_seq s' ! tm) = call \<and>
              (if act_name (his_seq s' ! k) = enq
               then act_val (his_seq s' ! tm) = act_val (his_seq s' ! k)
               else act_val (his_seq s' ! tm) = BOT)"
          using TM TM_PROP TM_EQ K_EQ
          by simp
      qed
    next
      case False
      then have K_LAST: "k = ?n"
        using K LEN by linarith
      have K_IS_E: "his_seq s' ! k = e"
        using HIS K_LAST by simp
      have False
        using K_IS_E CALL RET by simp
      then show "\<exists>tm<k.
                   act_pid (his_seq s' ! tm) = act_pid (his_seq s' ! k) \<and>
                   act_name (his_seq s' ! tm) = act_name (his_seq s' ! k) \<and>
                   act_cr (his_seq s' ! tm) = call \<and>
                   (if act_name (his_seq s' ! k) = enq
                    then act_val (his_seq s' ! tm) = act_val (his_seq s' ! k)
                    else act_val (his_seq s' ! tm) = BOT)"
        by blast
    qed
  qed
qed

lemma hI20_Enq_Val_Valid_append_enq_call:
  assumes H12: "hI20_Enq_Val_Valid s"
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes ENQ: "act_name e = enq"
  assumes CALL: "act_cr e = call"
  assumes VAL: "act_val e \<in> Val"
  shows "hI20_Enq_Val_Valid s'"
  using H12 HIS ENQ CALL VAL
  unfolding hI20_Enq_Val_Valid_def
  by (auto simp: nth_append split: if_splits nat.splits)

lemma hI20_Enq_Val_Valid_append_non_enq:
  assumes H12: "hI20_Enq_Val_Valid s"
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes NON: "act_name e ~= enq"
  shows "hI20_Enq_Val_Valid s'"
  using H12 HIS NON
  unfolding hI20_Enq_Val_Valid_def
  by (auto simp: nth_append split: if_splits nat.splits)

lemma hI8_Val_Unique_append_non_enq_call:
  assumes UNI: "hI8_Val_Unique s"
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes NON: "act_name e ~= enq | act_cr e ~= call"
  shows "hI8_Val_Unique s'"
  using UNI HIS NON
  unfolding hI8_Val_Unique_def
  by (auto simp: nth_append split: if_splits nat.splits)

lemma hI8_Val_Unique_append_enq_call_if_fresh:
  assumes UNI: "hI8_Val_Unique s"
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes ENQ: "act_name e = enq"
  assumes CALL: "act_cr e = call"
  assumes FRESH:
    "\<forall>k < length (his_seq s).
      ~ (act_name (his_seq s ! k) = enq &
         act_cr (his_seq s ! k) = call &
         act_val (his_seq s ! k) = act_val e)"
  shows "hI8_Val_Unique s'"
proof -
  let ?n = "length (his_seq s)"
  have LEN: "length (his_seq s') = Suc ?n"
    using HIS by simp
  have NTH_OLD: "\<And>k. k < ?n \<Longrightarrow> his_seq s' ! k = his_seq s ! k"
    using HIS by (simp add: nth_append)
  have UNI_CORE:
    "\<forall>x<?n. \<forall>y<?n.
      act_name (his_seq s ! x) = enq &
      act_name (his_seq s ! y) = enq &
      act_cr (his_seq s ! x) = call &
      act_cr (his_seq s ! y) = call &
      act_val (his_seq s ! x) = act_val (his_seq s ! y)
      --> x = y"
    using UNI unfolding hI8_Val_Unique_def by auto

  have MAIN:
    "\<And>i j.
      i < length (his_seq s') \<Longrightarrow>
      j < length (his_seq s') \<Longrightarrow>
      act_name (his_seq s' ! i) = enq \<Longrightarrow>
      act_name (his_seq s' ! j) = enq \<Longrightarrow>
      act_cr (his_seq s' ! i) = call \<Longrightarrow>
      act_cr (his_seq s' ! j) = call \<Longrightarrow>
      act_val (his_seq s' ! i) = act_val (his_seq s' ! j) \<Longrightarrow>
      i = j"
  proof -
    fix i j
    assume I: "i < length (his_seq s')"
    assume J: "j < length (his_seq s')"
    assume EI: "act_name (his_seq s' ! i) = enq"
    assume EJ: "act_name (his_seq s' ! j) = enq"
    assume CI: "act_cr (his_seq s' ! i) = call"
    assume CJ: "act_cr (his_seq s' ! j) = call"
    assume VEQ: "act_val (his_seq s' ! i) = act_val (his_seq s' ! j)"
    have I_LE: "i <= ?n" using I LEN by linarith
    have J_LE: "j <= ?n" using J LEN by linarith
    consider (i_last) "i = ?n" | (i_old) "i < ?n"
      using I_LE by linarith
    then show "i = j"
    proof cases
      case i_last
      have I_LAST: "his_seq s' ! i = e" using HIS I i_last by simp
      have I_VAL: "act_val (his_seq s' ! i) = act_val e" using I_LAST by simp
      consider (j_last) "j = ?n" | (j_old) "j < ?n"
        using J_LE by linarith
      then show ?thesis
      proof cases
        case j_last
        from i_last j_last show ?thesis by simp
      next
        case j_old
        have J_OLD_EQ: "his_seq s' ! j = his_seq s ! j" using NTH_OLD j_old by simp
        have J_ENQ_CALL:
          "act_name (his_seq s ! j) = enq &
           act_cr (his_seq s ! j) = call &
           act_val (his_seq s ! j) = act_val e"
          using EJ CJ VEQ I_VAL J_OLD_EQ by auto
        from FRESH j_old J_ENQ_CALL show ?thesis by blast
      qed
    next
      case i_old
      have I_OLD_EQ: "his_seq s' ! i = his_seq s ! i" using NTH_OLD i_old by simp
      consider (j_last) "j = ?n" | (j_old) "j < ?n"
        using J_LE by linarith
      then show ?thesis
      proof cases
        case j_last
        have J_LAST: "his_seq s' ! j = e" using HIS J j_last by simp
        have J_VAL: "act_val (his_seq s' ! j) = act_val e" using J_LAST by simp
        have I_ENQ_CALL:
          "act_name (his_seq s ! i) = enq &
           act_cr (his_seq s ! i) = call &
           act_val (his_seq s ! i) = act_val e"
          using EI CI VEQ J_VAL I_OLD_EQ by auto
        from FRESH i_old I_ENQ_CALL show ?thesis by blast
      next
        case j_old
        have J_OLD_EQ: "his_seq s' ! j = his_seq s ! j" using NTH_OLD j_old by simp
        have EI_OLD: "act_name (his_seq s ! i) = enq" using EI I_OLD_EQ by simp
        have EJ_OLD: "act_name (his_seq s ! j) = enq" using EJ J_OLD_EQ by simp
        have CI_OLD: "act_cr (his_seq s ! i) = call" using CI I_OLD_EQ by simp
        have CJ_OLD: "act_cr (his_seq s ! j) = call" using CJ J_OLD_EQ by simp
        have VEQ_OLD: "act_val (his_seq s ! i) = act_val (his_seq s ! j)"
          using VEQ I_OLD_EQ J_OLD_EQ by simp
        from UNI_CORE i_old j_old EI_OLD EJ_OLD CI_OLD CJ_OLD VEQ_OLD
        show ?thesis by blast
      qed
    qed
  qed
  show ?thesis
    unfolding hI8_Val_Unique_def
    using MAIN by blast
qed


lemma L0_step_facts:
  assumes STEP: "L0 p s s'"
  shows "program_counter s p = ''L0''"
    and "Simulate_PC s'"
  using STEP
  unfolding L0_def Sys_L0_def C_L0_def program_counter_def
  by auto


lemma EnqCallInHis_append_enq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act enq v p sn0 call]"
  shows "EnqCallInHis s' q a sn \<longleftrightarrow> EnqCallInHis s q a sn \<or> (q = p \<and> a = v \<and> sn = sn0)"
  using HIS
  unfolding EnqCallInHis_def
  by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

lemma EnqCallInHis_append_deq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act deq BOT p sn0 call]"
  shows "Model.EnqCallInHis s' q a sn \<longleftrightarrow> Model.EnqCallInHis s q a sn"
  using HIS
  unfolding Model.EnqCallInHis_def
  by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

lemma EnqRetInHis_append_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes CALL: "act_cr e = call"
  shows "Model.EnqRetInHis s' q a sn \<longleftrightarrow> Model.EnqRetInHis s q a sn"
  using HIS CALL
  unfolding Model.EnqRetInHis_def
  by auto

lemma DeqRetInHis_append_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes CALL: "act_cr e = call"
  shows "Model.DeqRetInHis s' q a sn \<longleftrightarrow> Model.DeqRetInHis s q a sn"
  using HIS CALL
  unfolding Model.DeqRetInHis_def
  by auto

lemma DeqCallInHis_append_enq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act enq v p sn0 call]"
  shows "Model.DeqCallInHis s' q sn \<longleftrightarrow> Model.DeqCallInHis s q sn"
  using HIS
  unfolding Model.DeqCallInHis_def
  by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

lemma DeqCallInHis_append_deq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act deq BOT p sn0 call]"
  shows "Model.DeqCallInHis s' q sn \<longleftrightarrow> Model.DeqCallInHis s q sn \<or> (q = p \<and> sn = sn0)"
  using HIS
  unfolding Model.DeqCallInHis_def
  by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)

lemma HasPendingEnq_append_enq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act enq v p (s_var s p) call]"
  assumes SN: "s_var s' q = s_var s q"
  shows "HasPendingEnq s' q a \<longleftrightarrow>
         HasPendingEnq s q a \<or>
         (q = p \<and> a = v \<and>
          (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = q \<and> act_ssn e = s_var s q \<and> act_cr e = ret)))"
proof -
  have call_eq:
    "Model.EnqCallInHis s' q a (s_var s' q) \<longleftrightarrow>
     Model.EnqCallInHis s q a (s_var s q) \<or> (q = p \<and> a = v)"
  proof
    assume new_call: "Model.EnqCallInHis s' q a (s_var s' q)"
    then obtain e where
      e_in: "e \<in> set (his_seq s')"
      and e_props:
        "act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_name e = enq \<and> act_cr e = call \<and> act_val e = a"
      unfolding Model.EnqCallInHis_def by blast
    from HIS e_in have e_cases:
      "e = mk_act enq v p (s_var s p) call \<or> e \<in> set (his_seq s)"
      by auto
    from e_cases show "Model.EnqCallInHis s q a (s_var s q) \<or> (q = p \<and> a = v)"
    proof
      assume e_new: "e = mk_act enq v p (s_var s p) call"
      with e_props SN show ?thesis
        by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    next
      assume e_old: "e \<in> set (his_seq s)"
      have e_props_old:
        "act_pid e = q \<and> act_ssn e = s_var s q \<and> act_name e = enq \<and> act_cr e = call \<and> act_val e = a"
        using e_props SN by simp
      have exists_old:
        "\<exists>x \<in> set (his_seq s).
           act_pid x = q \<and> act_ssn x = s_var s q \<and> act_name x = enq \<and> act_cr x = call \<and> act_val x = a"
        using e_old e_props_old by blast
      have "Model.EnqCallInHis s q a (s_var s q)"
        using exists_old
        unfolding Model.EnqCallInHis_def .
      then show ?thesis by simp
    qed
  next
    assume old_or_new: "Model.EnqCallInHis s q a (s_var s q) \<or> (q = p \<and> a = v)"
    from old_or_new show "Model.EnqCallInHis s' q a (s_var s' q)"
    proof
      assume old_call: "Model.EnqCallInHis s q a (s_var s q)"
      then obtain e where
        e_in: "e \<in> set (his_seq s)"
        and e_props:
          "act_pid e = q \<and> act_ssn e = s_var s q \<and> act_name e = enq \<and> act_cr e = call \<and> act_val e = a"
        unfolding Model.EnqCallInHis_def by blast
      have "e \<in> set (his_seq s')"
        using HIS e_in by auto
      moreover have
        "act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_name e = enq \<and> act_cr e = call \<and> act_val e = a"
        using e_props SN by simp
      ultimately have exists_new:
        "\<exists>x \<in> set (his_seq s').
           act_pid x = q \<and> act_ssn x = s_var s' q \<and> act_name x = enq \<and> act_cr x = call \<and> act_val x = a"
        by blast
      show "Model.EnqCallInHis s' q a (s_var s' q)"
        using exists_new
        unfolding Model.EnqCallInHis_def .
    next
      assume new_call: "q = p \<and> a = v"
      have evt_in: "mk_act enq v p (s_var s p) call \<in> set (his_seq s')"
        using HIS by auto
      have evt_props:
        "act_pid (mk_act enq v p (s_var s p) call) = q \<and>
         act_ssn (mk_act enq v p (s_var s p) call) = s_var s' q \<and>
         act_name (mk_act enq v p (s_var s p) call) = enq \<and>
         act_cr (mk_act enq v p (s_var s p) call) = call \<and>
         act_val (mk_act enq v p (s_var s p) call) = a"
        using new_call SN
        by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      have exists_new_call:
        "\<exists>x \<in> set (his_seq s').
           act_pid x = q \<and> act_ssn x = s_var s' q \<and> act_name x = enq \<and> act_cr x = call \<and> act_val x = a"
        using evt_in evt_props by blast
      show "Model.EnqCallInHis s' q a (s_var s' q)"
        using exists_new_call
        unfolding Model.EnqCallInHis_def .
    qed
  qed
  have ret_eq:
    "(\<forall>e \<in> set (his_seq s'). \<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)) \<longleftrightarrow>
     (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = q \<and> act_ssn e = s_var s q \<and> act_cr e = ret))"
    using HIS SN
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_cr_def)
  show ?thesis
    unfolding HasPendingEnq_def Let_def
    using call_eq ret_eq by blast
qed

lemma L0_no_ret_at_current_ssn:
  assumes hI2_SSN_Bounds_s: "hI2_SSN_Bounds s"
  assumes PC_L0: "program_counter s p = ''L0''"
  shows "\<forall>e \<in> set (his_seq s). \<not> (act_pid e = p \<and> act_ssn e = s_var s p \<and> act_cr e = ret)"
proof (intro ballI notI)
  fix e
  assume e_in: "e \<in> set (his_seq s)"
  assume e_bad: "act_pid e = p \<and> act_ssn e = s_var s p \<and> act_cr e = ret"
  then have pid_eq: "act_pid e = p"
    and ssn_eq: "act_ssn e = s_var s p"
    by auto
  from hI2_SSN_Bounds_s have ai11:
    "\<forall>pa. \<forall>ev \<in> set (his_seq s).
       act_pid ev = pa \<longrightarrow>
       (act_ssn ev \<le> s_var s pa \<and>
        (program_counter s pa = ''L0'' \<longrightarrow> act_ssn ev < s_var s pa))"
    unfolding hI2_SSN_Bounds_def .
  from ai11 e_in pid_eq have "act_ssn e < s_var s p"
    using PC_L0 by blast
  with ssn_eq show False
    by simp
qed

lemma OPLin_deq_not_current_ssn_at_L0:
  assumes lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
  assumes hI2_SSN_Bounds_s: "hI2_SSN_Bounds s"
  assumes PC_L0: "program_counter s p = ''L0''"
  assumes in_oplin: "act \<in> OPLin s"
  assumes deq_act: "op_name act = deq"
  assumes pid_p: "op_pid act = p"
  shows "op_ssn act \<noteq> s_var s p"
proof -
  have in_union: "act \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_Op_Sets_Equivalence_s in_oplin
    unfolding lI1_Op_Sets_Equivalence_def
    by auto
  have in_op_a_deq: "act \<in> OP_A_deq s"
    using in_union deq_act
    unfolding OP_A_enq_def OP_A_deq_def OP_B_enq_def
    by (auto simp: mk_op_def op_name_def op_val_def op_pid_def op_ssn_def)
  then have deq_call: "Model.DeqCallInHis s (op_pid act) (op_ssn act)"
    unfolding OP_A_deq_def
    by auto
  then obtain e where
    e_in: "e \<in> set (his_seq s)"
    and e_pid: "act_pid e = op_pid act"
    and e_ssn: "act_ssn e = op_ssn act"
    and e_deq: "act_name e = deq"
    and e_call: "act_cr e = call"
    unfolding Model.DeqCallInHis_def
    by auto
  have e_pid_p: "act_pid e = p"
    using e_pid pid_p by simp
  from hI2_SSN_Bounds_s have ai11:
    "\<forall>pa. \<forall>ev \<in> set (his_seq s).
       act_pid ev = pa \<longrightarrow>
       (act_ssn ev \<le> s_var s pa \<and>
        (program_counter s pa = ''L0'' \<longrightarrow> act_ssn ev < s_var s pa))"
    unfolding hI2_SSN_Bounds_def .
  have ai11_p:
    "\<forall>ev \<in> set (his_seq s).
       act_pid ev = p \<longrightarrow>
       (act_ssn ev \<le> s_var s p \<and>
        (program_counter s p = ''L0'' \<longrightarrow> act_ssn ev < s_var s p))"
    using ai11 by blast
  have "act_ssn e < s_var s p"
    using ai11_p e_in e_pid_p PC_L0
    by blast
  then show ?thesis
    using e_ssn by auto
qed

lemma HasPendingEnq_append_deq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
  assumes SN: "s_var s' q = s_var s q"
  shows "HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a"
proof -
  have call_eq:
    "Model.EnqCallInHis s' q a (s_var s' q) \<longleftrightarrow> Model.EnqCallInHis s q a (s_var s q)"
    using HIS SN
    unfolding Model.EnqCallInHis_def
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  have ret_eq:
    "(\<forall>e \<in> set (his_seq s'). \<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)) \<longleftrightarrow>
     (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = q \<and> act_ssn e = s_var s q \<and> act_cr e = ret))"
    using HIS SN
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_cr_def)
  show ?thesis
    unfolding HasPendingEnq_def Let_def
    using call_eq ret_eq by blast
qed

lemma hI9_Deq_Ret_Unique_append_call_event_simple:
  assumes H1: "hI9_Deq_Ret_Unique s"
  assumes HIS: "his_seq s' = his_seq s @ [e]"
  assumes CALL: "act_cr e = call"
  shows "hI9_Deq_Ret_Unique s'"
  using H1 HIS CALL
  unfolding hI9_Deq_Ret_Unique_def
  by (auto simp: Let_def nth_append split: if_splits nat.splits)

lemma L0_E1_fresh:
  assumes hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
  assumes PC_L0: "program_counter s p = ''L0''"
  shows "\<forall>k < length (his_seq s).
           \<not> (act_name (his_seq s ! k) = enq \<and>
              act_cr (his_seq s ! k) = call \<and>
              act_val (his_seq s ! k) = V_var s)"
proof (intro allI impI notI)
  fix k
  assume k_lt: "k < length (his_seq s)"
  assume ecv:
    "act_name (his_seq s ! k) = enq \<and>
     act_cr (his_seq s ! k) = call \<and>
     act_val (his_seq s ! k) = V_var s"
  have "act_val (his_seq s ! k) < V_var s"
    using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s k_lt] ecv
    by auto
  with ecv show False
    by simp
qed

lemma L0_E1_qback_fresh:
  assumes hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
  assumes TypeOK_s: "TypeOK s"
  shows "\<forall>k. Qback_arr s k \<noteq> V_var s"
proof
  fix k
  have qback_cases: "Qback_arr s k = BOT \<or> Qback_arr s k < V_var s"
    using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s, of k] .
  have v_positive: "V_var s \<in> Val"
    using TypeOK_s unfolding TypeOK_def by auto
  then have v_not_bot: "V_var s \<noteq> BOT"
    unfolding Val_def BOT_def by auto
  show "Qback_arr s k \<noteq> V_var s"
  proof
    assume eq: "Qback_arr s k = V_var s"
    from qback_cases show False
    proof
      assume "Qback_arr s k = BOT"
      with eq v_not_bot show False by simp
    next
      assume "Qback_arr s k < V_var s"
      with eq show False by simp
    qed
  qed
qed

lemma HasPendingDeq_append_enq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act enq v p (s_var s p) call]"
  assumes SN: "s_var s' q = s_var s q"
  shows "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
proof -
  have call_eq:
    "Model.DeqCallInHis s' q (s_var s' q) \<longleftrightarrow> Model.DeqCallInHis s q (s_var s q)"
    using HIS SN
    unfolding Model.DeqCallInHis_def
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  have ret_eq:
    "(\<forall>e \<in> set (his_seq s'). \<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)) \<longleftrightarrow>
     (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = q \<and> act_ssn e = s_var s q \<and> act_cr e = ret))"
    using HIS SN
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_cr_def)
  show ?thesis
    unfolding HasPendingDeq_def Let_def
    using call_eq ret_eq by blast
qed

lemma HasPendingDeq_append_deq_call_other_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
  assumes q_ne_p: "q \<noteq> p"
  assumes SN: "s_var s' q = s_var s q"
  shows "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
proof -
  have call_eq:
    "Model.DeqCallInHis s' q (s_var s' q) \<longleftrightarrow> Model.DeqCallInHis s q (s_var s q)"
    using HIS q_ne_p SN
    unfolding Model.DeqCallInHis_def
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  have ret_eq:
    "(\<forall>e \<in> set (his_seq s'). \<not> (act_pid e = q \<and> act_ssn e = s_var s' q \<and> act_cr e = ret)) \<longleftrightarrow>
     (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = q \<and> act_ssn e = s_var s q \<and> act_cr e = ret))"
    using HIS SN
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_cr_def)
  show ?thesis
    unfolding HasPendingDeq_def Let_def
    using call_eq ret_eq by blast
qed


lemma hI23_Deq_Call_Ret_Balanced_append_enq_call_if_balanced_deq:
  assumes HI15: "hI23_Deq_Call_Ret_Balanced s"
  assumes BALANCED:
    "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
     length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
  assumes HIS: "his_seq s' = his_seq s @ [mk_act enq v p (s_var s p) call]"
  shows "hI23_Deq_Call_Ret_Balanced s'"
proof (unfold hI23_Deq_Call_Ret_Balanced_def, intro allI impI)
  fix q k
  let ?n = "length (his_seq s)"
  let ?evt = "mk_act enq v p (s_var s p) call"
  assume k_le': "k \<le> length (his_seq s')"
  have len': "length (his_seq s') = Suc ?n"
    using HIS by simp
  show "let q_his = filter (\<lambda>e. act_pid e = q) (take k (his_seq s')) in
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
          (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
  proof (cases "k \<le> ?n")
    case True
    have old_prop:
      "let q_his = filter (\<lambda>e. act_pid e = q) (take k (his_seq s)) in
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
         (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
      using HI15 True
      unfolding hI23_Deq_Call_Ret_Balanced_def
      by blast
    have take_eq: "take k (his_seq s') = take k (his_seq s)"
      using HIS True by simp
    show ?thesis
      using old_prop take_eq
      by simp
  next
    case False
    with k_le' len' have k_full: "k = Suc ?n"
      by linarith
    have old_prop_q:
      "let q_his = filter (\<lambda>e. act_pid e = q) (his_seq s) in
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
         (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
    proof -
      from HI15 have
        "let q_his = filter (\<lambda>e. act_pid e = q) (take (length (his_seq s)) (his_seq s)) in
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
           (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
        unfolding hI23_Deq_Call_Ret_Balanced_def
        by blast
      then show ?thesis
        by simp
    qed
    show ?thesis
    proof (cases "q = p")
      case False
      have qhis_eq:
        "filter (\<lambda>e. act_pid e = q) (take k (his_seq s')) =
         filter (\<lambda>e. act_pid e = q) (his_seq s)"
        using HIS k_full False
        by (simp add: mk_act_def act_pid_def)
      show ?thesis
        using old_prop_q qhis_eq
        by simp
    next
      case True
      let ?q_his = "filter (\<lambda>e. act_pid e = p) (his_seq s)"
      let ?C = "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) ?q_his)"
      let ?R = "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) ?q_his)"
      have old_prop_p:
        "let q_his = filter (\<lambda>e. act_pid e = p) (his_seq s) in
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
           (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
        using old_prop_q True
        by simp
      have old_bounds:
        "?R \<le> ?C \<and> ?C - ?R \<le> 1 \<and>
         (?q_his \<noteq> [] \<and> act_cr (last ?q_his) = call \<and> act_name (last ?q_his) \<noteq> deq \<longrightarrow> ?C = ?R)"
        using old_prop_p by (simp add: Let_def)
      have counts_eq: "?C = ?R"
        using BALANCED by simp
      show ?thesis
        using old_bounds counts_eq HIS k_full True
        by (simp add: mk_act_def act_pid_def act_name_def act_cr_def)
    qed
  qed
qed

lemma hI23_Deq_Call_Ret_Balanced_append_deq_call_if_balanced_deq:
  assumes HI15: "hI23_Deq_Call_Ret_Balanced s"
  assumes BALANCED:
    "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
     length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
  assumes HIS: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
  shows "hI23_Deq_Call_Ret_Balanced s'"
proof (unfold hI23_Deq_Call_Ret_Balanced_def, intro allI impI)
  fix q k
  let ?n = "length (his_seq s)"
  assume k_le': "k \<le> length (his_seq s')"
  have len': "length (his_seq s') = Suc ?n"
    using HIS by simp
  show "let q_his = filter (\<lambda>e. act_pid e = q) (take k (his_seq s')) in
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
          (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
  proof (cases "k \<le> ?n")
    case True
    have old_prop:
      "let q_his = filter (\<lambda>e. act_pid e = q) (take k (his_seq s)) in
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
         (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
      using HI15 True
      unfolding hI23_Deq_Call_Ret_Balanced_def
      by blast
    have take_eq: "take k (his_seq s') = take k (his_seq s)"
      using HIS True by simp
    show ?thesis
      using old_prop take_eq
      by simp
  next
    case False
    with k_le' len' have k_full: "k = Suc ?n"
      by linarith
    have old_prop_q:
      "let q_his = filter (\<lambda>e. act_pid e = q) (his_seq s) in
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
         length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
         (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
          length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
    proof -
      from HI15 have
        "let q_his = filter (\<lambda>e. act_pid e = q) (take (length (his_seq s)) (his_seq s)) in
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
           (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
        unfolding hI23_Deq_Call_Ret_Balanced_def
        by blast
      then show ?thesis
        by simp
    qed
    show ?thesis
    proof (cases "q = p")
      case False
      have qhis_eq:
        "filter (\<lambda>e. act_pid e = q) (take k (his_seq s')) =
         filter (\<lambda>e. act_pid e = q) (his_seq s)"
        using HIS k_full False
        by (simp add: mk_act_def act_pid_def)
      show ?thesis
        using old_prop_q qhis_eq
        by simp
    next
      case True
      let ?q_his = "filter (\<lambda>e. act_pid e = p) (his_seq s)"
      let ?C = "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) ?q_his)"
      let ?R = "length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) ?q_his)"
      have old_prop_p:
        "let q_his = filter (\<lambda>e. act_pid e = p) (his_seq s) in
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) -
           length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>
           (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow>
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) =
            length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))"
        using old_prop_q True
        by (simp add: Let_def)
      have old_bounds:
        "?R \<le> ?C \<and> ?C - ?R \<le> 1 \<and>
         (?q_his \<noteq> [] \<and> act_cr (last ?q_his) = call \<and> act_name (last ?q_his) \<noteq> deq \<longrightarrow> ?C = ?R)"
        using old_prop_p
        by (simp add: Let_def)
      have counts_eq: "?C = ?R"
        using BALANCED by simp
      show ?thesis
        using old_bounds counts_eq HIS k_full True
        by (simp add: mk_act_def act_pid_def act_name_def act_cr_def)
    qed
  qed
qed

lemma HB_EnqRetCall_append_enq_call_other_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act enq v p (s_var s p) call]"
  assumes b_ne_v: "b \<noteq> v"
  shows "HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
proof
  assume hb': "HB_EnqRetCall s' a b"
  then obtain p1 p2 sn1 sn2 k1 k2 where
    order: "k1 < k2"
    and mret: "match_ret (his_seq s') k1 (mk_op enq a p1 sn1)"
    and mcall: "match_call (his_seq s') k2 (mk_op enq b p2 sn2)"
    unfolding HB_EnqRetCall_def HB_Act_def HB_def
    by blast
  let ?n = "length (his_seq s)"
  have len': "length (his_seq s') = Suc ?n"
    using HIS by simp
  have k2_len': "k2 < length (his_seq s')"
    using mcall unfolding match_call_def by simp
  have k2_old: "k2 < ?n"
  proof (rule ccontr)
    assume "\<not> k2 < ?n"
    with k2_len' len' have k2_last: "k2 = ?n"
      by linarith
    have last_nth: "his_seq s' ! k2 = mk_act enq v p (s_var s p) call"
      using HIS k2_last by simp
    have b_eq: "b = v"
      using mcall last_nth
      unfolding match_call_def Let_def mk_op_def mk_act_def
      by (auto simp: act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                     op_name_def op_pid_def op_val_def op_ssn_def)
    have p2_eq: "p2 = p"
      using mcall last_nth
      unfolding match_call_def Let_def mk_op_def mk_act_def
      by (auto simp: act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                     op_name_def op_pid_def op_val_def op_ssn_def)
    have sn2_eq: "sn2 = s_var s p"
      using mcall last_nth
      unfolding match_call_def Let_def mk_op_def mk_act_def
      by (auto simp: act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                     op_name_def op_pid_def op_val_def op_ssn_def)
    have same_act: "mk_op enq b p2 sn2 = mk_op enq v p (s_var s p)"
      using b_eq p2_eq sn2_eq
      by (simp add: mk_op_def)
    then show False
      using same_act b_ne_v
      by (simp add: mk_op_def op_val_def)
  qed
  have k1_old: "k1 < ?n"
    using order(1) k2_old by linarith
  have mret_old: "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
    using HIS mret k1_old
    unfolding match_ret_def
    by (simp add: Let_def nth_append)
  have mcall_old: "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
    using HIS mcall k2_old
    unfolding match_call_def
    by (simp add: Let_def nth_append)
  show "HB_EnqRetCall s a b"
    unfolding HB_EnqRetCall_def HB_Act_def HB_def
    using order mret_old mcall_old
    by blast
next
  assume hb: "HB_EnqRetCall s a b"
  then obtain p1 p2 sn1 sn2 k1 k2 where
    order: "k1 < k2"
    and mret: "match_ret (his_seq s) k1 (mk_op enq a p1 sn1)"
    and mcall: "match_call (his_seq s) k2 (mk_op enq b p2 sn2)"
    unfolding HB_EnqRetCall_def HB_Act_def HB_def
    by blast
  have mret_new: "match_ret (his_seq s') k1 (mk_op enq a p1 sn1)"
    using HIS mret
    unfolding match_ret_def
    by (simp add: Let_def nth_append)
  have mcall_new: "match_call (his_seq s') k2 (mk_op enq b p2 sn2)"
    using HIS mcall
    unfolding match_call_def
    by (simp add: Let_def nth_append)
  show "HB_EnqRetCall s' a b"
    unfolding HB_EnqRetCall_def HB_Act_def HB_def
    using order mret_new mcall_new
    by blast
qed

lemma HB_Act_append_enq_call_other_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act enq v p (s_var s p) call]"
  assumes ACT2_NE: "act2 \<noteq> mk_op enq v p (s_var s p)"
  shows "HB_Act s' act1 act2 \<longleftrightarrow> HB_Act s act1 act2"
proof
  assume hb': "HB_Act s' act1 act2"
  then obtain k1 k2 where
    order: "k1 < k2"
    and mret: "match_ret (his_seq s') k1 act1"
    and mcall: "match_call (his_seq s') k2 act2"
    unfolding HB_Act_def HB_def
    by blast
  let ?n = "length (his_seq s)"
  have len': "length (his_seq s') = Suc ?n"
    using HIS by simp
  have k2_len': "k2 < length (his_seq s')"
    using mcall unfolding match_call_def by simp
  have k2_old: "k2 < ?n"
  proof (rule ccontr)
    assume "\<not> k2 < ?n"
    with k2_len' len' have k2_last: "k2 = ?n"
      by linarith
    have last_nth: "his_seq s' ! k2 = mk_act enq v p (s_var s p) call"
      using HIS k2_last by simp
    have act2_eq: "act2 = mk_op enq v p (s_var s p)"
      using mcall last_nth
      unfolding match_call_def Let_def mk_op_def mk_act_def
      by (cases act2)
         (auto simp: act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                     op_name_def op_pid_def op_val_def op_ssn_def)
    with ACT2_NE show False by contradiction
  qed
  have k1_old: "k1 < ?n"
    using order(1) k2_old by linarith
  have mret_old: "match_ret (his_seq s) k1 act1"
    using HIS mret k1_old
    unfolding match_ret_def
    by (simp add: Let_def nth_append)
  have mcall_old: "match_call (his_seq s) k2 act2"
    using HIS mcall k2_old
    unfolding match_call_def
    by (simp add: Let_def nth_append)
  show "HB_Act s act1 act2"
    unfolding HB_Act_def HB_def
    using order mret_old mcall_old
    by blast
next
  assume hb: "HB_Act s act1 act2"
  then obtain k1 k2 where
    order: "k1 < k2"
    and mret: "match_ret (his_seq s) k1 act1"
    and mcall: "match_call (his_seq s) k2 act2"
    unfolding HB_Act_def HB_def
    by blast
  have mret_new: "match_ret (his_seq s') k1 act1"
    using HIS mret
    unfolding match_ret_def
    by (simp add: Let_def nth_append)
  have mcall_new: "match_call (his_seq s') k2 act2"
    using HIS mcall
    unfolding match_call_def
    by (simp add: Let_def nth_append)
  show "HB_Act s' act1 act2"
    unfolding HB_Act_def HB_def
    using order mret_new mcall_new
    by blast
qed



lemma HB_Act_append_deq_call_other_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
  assumes ACT2_SAFE: "op_name act2 \<noteq> deq \<or> op_pid act2 \<noteq> p \<or> op_ssn act2 \<noteq> s_var s p"
  shows "HB_Act s' act1 act2 \<longleftrightarrow> HB_Act s act1 act2"
proof
  assume hb': "HB_Act s' act1 act2"
  then obtain k1 k2 where
    order: "k1 < k2"
    and mret: "match_ret (his_seq s') k1 act1"
    and mcall: "match_call (his_seq s') k2 act2"
    unfolding HB_Act_def HB_def
    by blast
  let ?n = "length (his_seq s)"
  have len': "length (his_seq s') = Suc ?n"
    using HIS by simp
  have k2_len': "k2 < length (his_seq s')"
    using mcall unfolding match_call_def by simp
  have k2_old: "k2 < ?n"
  proof (rule ccontr)
    assume "\<not> k2 < ?n"
    with k2_len' len' have k2_last: "k2 = ?n"
      by linarith
    have last_nth: "his_seq s' ! k2 = mk_act deq BOT p (s_var s p) call"
      using HIS k2_last by simp
    have act2_deq: "op_name act2 = deq"
      using mcall last_nth
      unfolding match_call_def Let_def mk_act_def
      by (cases act2)
         (auto simp: act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                     op_name_def op_pid_def op_val_def op_ssn_def)
    have act2_pid: "op_pid act2 = p"
      using mcall last_nth
      unfolding match_call_def Let_def mk_act_def
      by (cases act2)
         (auto simp: act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                     op_name_def op_pid_def op_val_def op_ssn_def)
    have act2_ssn: "op_ssn act2 = s_var s p"
      using mcall last_nth
      unfolding match_call_def Let_def mk_act_def
      by (cases act2)
         (auto simp: act_name_def act_pid_def act_val_def act_ssn_def act_cr_def
                     op_name_def op_pid_def op_val_def op_ssn_def)
    from ACT2_SAFE act2_deq act2_pid act2_ssn show False
      by blast
  qed
  have k1_old: "k1 < ?n"
    using order(1) k2_old by linarith
  have mret_old: "match_ret (his_seq s) k1 act1"
    using HIS mret k1_old
    unfolding match_ret_def
    by (simp add: Let_def nth_append)
  have mcall_old: "match_call (his_seq s) k2 act2"
    using HIS mcall k2_old
    unfolding match_call_def
    by (simp add: Let_def nth_append)
  show "HB_Act s act1 act2"
    unfolding HB_Act_def HB_def
    using order mret_old mcall_old
    by blast
next
  assume hb: "HB_Act s act1 act2"
  then obtain k1 k2 where
    order: "k1 < k2"
    and mret: "match_ret (his_seq s) k1 act1"
    and mcall: "match_call (his_seq s) k2 act2"
    unfolding HB_Act_def HB_def
    by blast
  have mret_new: "match_ret (his_seq s') k1 act1"
    using HIS mret
    unfolding match_ret_def
    by (simp add: Let_def nth_append)
  have mcall_new: "match_call (his_seq s') k2 act2"
    using HIS mcall
    unfolding match_call_def
    by (simp add: Let_def nth_append)
  show "HB_Act s' act1 act2"
    unfolding HB_Act_def HB_def
    using order mret_new mcall_new
    by blast
qed

lemma HB_EnqRetCall_append_deq_call_iff:
  assumes HIS: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
  shows "HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
proof
  assume hb': "HB_EnqRetCall s' a b"
  then obtain p1 p2 sn1 sn2 where
    hbact': "HB_Act s' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    unfolding HB_EnqRetCall_def
    by blast
  have act2_safe:
    "op_name (mk_op enq b p2 sn2) \<noteq> deq \<or>
     op_pid (mk_op enq b p2 sn2) \<noteq> p \<or>
     op_ssn (mk_op enq b p2 sn2) \<noteq> s_var s p"
    by (simp add: mk_op_def op_name_def op_pid_def op_ssn_def)
  have "HB_Act s' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) \<longleftrightarrow>
        HB_Act s (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    using HB_Act_append_deq_call_other_iff[OF HIS act2_safe] .
  then have hbact: "HB_Act s (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    using hbact' by blast
  show "HB_EnqRetCall s a b"
    unfolding HB_EnqRetCall_def
    using hbact
    by blast
next
  assume hb: "HB_EnqRetCall s a b"
  then obtain p1 p2 sn1 sn2 where
    hbact: "HB_Act s (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    unfolding HB_EnqRetCall_def
    by blast
  have act2_safe:
    "op_name (mk_op enq b p2 sn2) \<noteq> deq \<or>
     op_pid (mk_op enq b p2 sn2) \<noteq> p \<or>
     op_ssn (mk_op enq b p2 sn2) \<noteq> s_var s p"
    by (simp add: mk_op_def op_name_def op_pid_def op_ssn_def)
  have "HB_Act s' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2) \<longleftrightarrow>
        HB_Act s (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    using HB_Act_append_deq_call_other_iff[OF HIS act2_safe] .
  then have hbact': "HB_Act s' (mk_op enq a p1 sn1) (mk_op enq b p2 sn2)"
    using hbact by blast
  show "HB_EnqRetCall s' a b"
    unfolding HB_EnqRetCall_def
    using hbact'
    by blast
qed

(* Proof note. Related symbols: hI3_L0_E_Phase_Bounds, L0, E1, D1.
*)
lemma hI3_L0_E_Phase_Bounds_L0_to_E1:
  assumes hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
  assumes pc_L0: "program_counter s p = ''L0''"
  assumes s'_def: "s' = L0_E1_update_state s p"
  shows "hI3_L0_E_Phase_Bounds s'"
proof -
  (* Step 1: extract the required facts. Related symbols: i_var, j_var. *)
  have pc_eq: "program_counter s' q = (if q = p then ''E1'' else program_counter s q)" for q
    using s'_def
    unfolding L0_E1_update_state_def program_counter_def
    by (auto simp: Let_def)
  have his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    using s'_def
    unfolding L0_E1_update_state_def his_seq_def V_var_def s_var_def
    by (simp add: Let_def)
  have ssn_eq: "s_var s' q = s_var s q" for q
    using s'_def
    unfolding L0_E1_update_state_def s_var_def
    by (auto simp: Let_def)
  have qback_eq: "Qback_arr s' k = Qback_arr s k" for k
    using s'_def
    unfolding L0_E1_update_state_def Qback_arr_def
    by (auto simp: Let_def)
  have v_eq: "v_var s' q = (if q = p then V_var s else v_var s q)" for q
    using s'_def
    unfolding L0_E1_update_state_def v_var_def V_var_def
    by (auto simp: Let_def)
  have V_suc: "V_var s' = Suc (V_var s)"
    using s'_def
    unfolding L0_E1_update_state_def V_var_def
    by (auto simp: Let_def)

  show ?thesis
  proof (rule hI3_L0_E_Phase_BoundsI)
    (* --------------------------------------------------------------------- *)
    (* Clause 1 of the invariant preservation proof. Related symbols: L0. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>q. program_counter s' q = ''L0'' \<longrightarrow> (\<forall>a. \<not> HasPendingEnq s' q a) \<and> \<not> HasPendingDeq s' q"
    proof (intro allI impI)
      fix q
      assume qL0: "program_counter s' q = ''L0''"
      have q_ne_p: "q \<noteq> p"
        using qL0 pc_eq by auto
      have old_L0: "program_counter s q = ''L0''"
        using qL0 pc_eq q_ne_p by simp
      from hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s old_L0] have old_none:
        "(\<forall>a. \<not> HasPendingEnq s q a) \<and> \<not> HasPendingDeq s q" .
      moreover have "HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a" for a
        using HasPendingEnq_append_enq_call_iff[OF his_eq ssn_eq[of q]] q_ne_p by auto
      moreover have "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
        using HasPendingDeq_append_enq_call_iff[OF his_eq ssn_eq[of q]] .
      ultimately show "(\<forall>a. \<not> HasPendingEnq s' q a) \<and> \<not> HasPendingDeq s' q"
        by auto
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 2 of the invariant preservation proof. Related symbols: L0. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>q. program_counter s' q = ''L0'' \<longrightarrow>
          length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s')) =
          length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s'))"
    proof (intro allI impI)
      fix q
      assume qL0: "program_counter s' q = ''L0''"
      have q_ne_p: "q \<noteq> p"
        using qL0 pc_eq by auto
      have old_L0: "program_counter s q = ''L0''"
        using qL0 pc_eq q_ne_p by simp
      have old_bal:
        "length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
         length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
        using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s old_L0] .
      show "length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s')) =
            length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s'))"
        using old_bal his_eq q_ne_p
        by (auto simp: mk_act_def act_pid_def act_name_def act_cr_def)
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 3 of the invariant preservation proof. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>q. program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longrightarrow> v_var s' q < V_var s'"
    proof (intro allI impI)
      fix q
      assume q_E: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
      show "v_var s' q < V_var s'"
      proof (cases "q = p")
        case True
        (* Extract the required witnesses and facts. *)
        have "v_var s' p = V_var s" using v_eq True by simp
        also have "... < Suc (V_var s)" by simp
        also have "... = V_var s'" using V_suc by simp
        finally show ?thesis using True by simp
      next
        case False
        (* Enqueue-side reasoning. *)
        have old_E: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" using q_E pc_eq False by auto
        have old_lt: "v_var s q < V_var s" using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s old_E] .
        have "v_var s' q = v_var s q" using v_eq False by simp
        also have "... < V_var s" using old_lt by simp
        also have "... < V_var s'" using V_suc by simp
        finally show ?thesis by simp
      qed
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 4 of the invariant preservation proof. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>k<length (his_seq s'). act_name (his_seq s' ! k) = enq \<and> act_cr (his_seq s' ! k) = call \<longrightarrow> act_val (his_seq s' ! k) < V_var s'"
    proof (intro allI impI)
      fix k
      assume k_lt: "k < length (his_seq s')"
      assume ec: "act_name (his_seq s' ! k) = enq \<and> act_cr (his_seq s' ! k) = call"
      let ?n = "length (his_seq s)"
      have len': "length (his_seq s') = Suc ?n"
        using his_eq by simp
      show "act_val (his_seq s' ! k) < V_var s'"
      proof (cases "k < ?n")
        case True
        have old_nth: "his_seq s' ! k = his_seq s ! k"
          using his_eq True by (simp add: nth_append)
        have old_ec:
          "act_name (his_seq s ! k) = enq \<and> act_cr (his_seq s ! k) = call"
          using ec old_nth by auto
        have old_lt: "act_val (his_seq s ! k) < V_var s"
          using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s True] old_ec
          by auto
        show ?thesis
          using old_lt V_suc old_nth by simp
      next
        case False
        with k_lt len' have k_last: "k = ?n"
          by linarith
        (* Reasoning about appending one history or sequence element. *)
        have "his_seq s' ! k = mk_act enq (V_var s) p (s_var s p) call"
          using his_eq k_last by simp
        then have "act_val (his_seq s' ! k) = V_var s"
          by (simp add: mk_act_def act_val_def)
        also have "... < V_var s'" using V_suc by simp
        finally show ?thesis by simp
      qed
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 5 of the invariant preservation proof. Related symbols: Qback. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>k. Qback_arr s' k = BOT \<or> Qback_arr s' k < V_var s'"
    proof (intro allI)
      fix k
      have old_qback: "Qback_arr s k = BOT \<or> Qback_arr s k < V_var s"
        using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s, of k] .
      show "Qback_arr s' k = BOT \<or> Qback_arr s' k < V_var s'"
        using old_qback qback_eq[of k] V_suc by auto
    qed
  qed
qed

lemma hI3_L0_E_Phase_Bounds_L0_to_D1:
  assumes hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
  assumes pc_L0: "program_counter s p = ''L0''"
  assumes s'_def: "s' = L0_D1_update_state s p"
  shows "hI3_L0_E_Phase_Bounds s'"
proof -
  (* Step 1: extract the required facts. *)
  have pc_eq: "program_counter s' q = (if q = p then ''D1'' else program_counter s q)" for q
    using s'_def
    unfolding L0_D1_update_state_def program_counter_def
    by (auto simp: Let_def)
  have his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    using s'_def
    unfolding L0_D1_update_state_def his_seq_def s_var_def
    by (simp add: Let_def)
  have ssn_eq: "s_var s' q = s_var s q" for q
    using s'_def
    unfolding L0_D1_update_state_def s_var_def
    by (auto simp: Let_def)
  have qback_eq: "Qback_arr s' k = Qback_arr s k" for k
    using s'_def
    unfolding L0_D1_update_state_def Qback_arr_def
    by (auto simp: Let_def)
  have v_eq: "v_var s' q = v_var s q" for q
    using s'_def
    unfolding L0_D1_update_state_def v_var_def
    by (auto simp: Let_def)
  have V_eq: "V_var s' = V_var s"
    using s'_def
    unfolding L0_D1_update_state_def V_var_def
    by (auto simp: Let_def)

  show ?thesis
  proof (rule hI3_L0_E_Phase_BoundsI)
    (* --------------------------------------------------------------------- *)
    (* Clause 1 of the invariant preservation proof. Related symbols: L0. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>q. program_counter s' q = ''L0'' \<longrightarrow> (\<forall>a. \<not> HasPendingEnq s' q a) \<and> \<not> HasPendingDeq s' q"
    proof (intro allI impI)
      fix q
      assume qL0: "program_counter s' q = ''L0''"
      have q_ne_p: "q \<noteq> p"
        using qL0 pc_eq by auto
      have old_L0: "program_counter s q = ''L0''"
        using qL0 pc_eq q_ne_p by simp
      from hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s old_L0] have old_none:
        "(\<forall>a. \<not> HasPendingEnq s q a) \<and> \<not> HasPendingDeq s q" .
      moreover have "HasPendingEnq s' q a \<longleftrightarrow> HasPendingEnq s q a" for a
        using HasPendingEnq_append_deq_call_iff[OF his_eq ssn_eq[of q]] by simp
      moreover have "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
        using HasPendingDeq_append_deq_call_other_iff[OF his_eq q_ne_p ssn_eq[of q]] .
      ultimately show "(\<forall>a. \<not> HasPendingEnq s' q a) \<and> \<not> HasPendingDeq s' q"
        by auto
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 2 of the invariant preservation proof. Related symbols: L0. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>q. program_counter s' q = ''L0'' \<longrightarrow>
          length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s')) =
          length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s'))"
    proof (intro allI impI)
      fix q
      assume qL0: "program_counter s' q = ''L0''"
      have q_ne_p: "q \<noteq> p"
        using qL0 pc_eq by auto
      have old_L0: "program_counter s q = ''L0''"
        using qL0 pc_eq q_ne_p by simp
      have old_bal:
        "length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
         length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
        using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s old_L0] .
      show "length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s')) =
            length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s'))"
        using old_bal his_eq q_ne_p
        by (auto simp: mk_act_def act_pid_def act_name_def act_cr_def)
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 3 of the invariant preservation proof. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>q. program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longrightarrow> v_var s' q < V_var s'"
    proof (intro allI impI)
      fix q
      assume q_E: "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
      (* State-transition reasoning. Related symbols: D1. *)
      have q_ne_p: "q \<noteq> p" using q_E pc_eq by auto
      have old_E: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}" using q_E pc_eq q_ne_p by auto
      have old_lt: "v_var s q < V_var s" using hI3_L0_E_Phase_Bounds_E_v_var_lt[OF hI3_L0_E_Phase_Bounds_s old_E] .

      show "v_var s' q < V_var s'"
        using old_lt v_eq V_eq by simp
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 4 of the invariant preservation proof. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>k<length (his_seq s'). act_name (his_seq s' ! k) = enq \<and> act_cr (his_seq s' ! k) = call \<longrightarrow> act_val (his_seq s' ! k) < V_var s'"
    proof (intro allI impI)
      fix k
      assume k_lt: "k < length (his_seq s')"
      assume ec: "act_name (his_seq s' ! k) = enq \<and> act_cr (his_seq s' ! k) = call"
      let ?n = "length (his_seq s)"
      have len': "length (his_seq s') = Suc ?n"
        using his_eq by simp
      show "act_val (his_seq s' ! k) < V_var s'"
      proof (cases "k < ?n")
        case True
        have old_nth: "his_seq s' ! k = his_seq s ! k"
          using his_eq True by (simp add: nth_append)
        have old_ec:
          "act_name (his_seq s ! k) = enq \<and> act_cr (his_seq s ! k) = call"
          using ec old_nth by auto
        have old_lt: "act_val (his_seq s ! k) < V_var s"
          using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s True] old_ec
          by auto
        show ?thesis
          using old_lt V_eq old_nth by simp
      next
        case False
        with k_lt len' have k_last: "k = ?n"
          by linarith
        (* Reasoning about appending one history or sequence element. *)
        have last_nth: "his_seq s' ! k = mk_act deq BOT p (s_var s p) call"
          using his_eq k_last by simp
        have False
          using last_nth ec
          unfolding mk_act_def act_name_def act_cr_def
          by simp
        then show ?thesis by simp
      qed
    qed

    (* --------------------------------------------------------------------- *)
    (* Clause 5 of the invariant preservation proof. Related symbols: Qback. *)
    (* --------------------------------------------------------------------- *)
    show "\<forall>k. Qback_arr s' k = BOT \<or> Qback_arr s' k < V_var s'"
    proof (intro allI)
      fix k
      have old_qback: "Qback_arr s k = BOT \<or> Qback_arr s k < V_var s"
        using hI3_L0_E_Phase_Bounds_qback_cases[OF hI3_L0_E_Phase_Bounds_s, of k] .
      show "Qback_arr s' k = BOT \<or> Qback_arr s' k < V_var s'"
        using old_qback qback_eq[of k] V_eq by auto
    qed
  qed
qed


(* SourceL0Proof.thy / L0_preserves_invariant / E1 / hI5_SSN_Unique_s'. *)
(* Original locationoriginal file 563-654 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_ssn_unique:
  fixes s s' :: SysState and p :: nat
  assumes hI5_SSN_Unique_s: "hI5_SSN_Unique s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and ai11_p:
      "\<forall>ev \<in> set (his_seq s).
         act_pid ev = p \<longrightarrow>
         (act_ssn ev \<le> s_var s p \<and>
          (program_counter s p = ''L0'' \<longrightarrow> act_ssn ev < s_var s p))"
    and pc_L0: "program_counter s p = ''L0''"
  shows "hI5_SSN_Unique s'"
proof (unfold hI5_SSN_Unique_def, intro allI impI)
  fix i j
  assume i_lt: "i < length (his_seq s')" and j_lt: "j < length (his_seq s')"
  assume props_raw:
    "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j) \<and>
     act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j) \<and>
     act_cr (his_seq s' ! i) = act_cr (his_seq s' ! j)"
  let ?L = "length (his_seq s)"
  have len': "length (his_seq s') = Suc ?L"
    using his_eq by simp
  have pid_eq:
    "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
    and ssn_eq:
    "act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j)"
    and cr_eq:
    "act_cr (his_seq s' ! i) = act_cr (his_seq s' ! j)"
    using props_raw by auto
  consider (both_old) "i < ?L" "j < ?L"
    | (i_old_j_new) "i < ?L" "j = ?L"
    | (i_new_j_old) "i = ?L" "j < ?L"
    | (both_new) "i = ?L" "j = ?L"
    using i_lt j_lt len' by linarith
  then show "i = j"
  proof cases
    case both_old
    have pid_old: "act_pid (his_seq s ! i) = act_pid (his_seq s ! j)"
      using pid_eq both_old his_eq
      by (simp add: nth_append)
    have ssn_old: "act_ssn (his_seq s ! i) = act_ssn (his_seq s ! j)"
      using ssn_eq both_old his_eq
      by (simp add: nth_append)
    have cr_old: "act_cr (his_seq s ! i) = act_cr (his_seq s ! j)"
      using cr_eq both_old his_eq
      by (simp add: nth_append)
    from hI5_SSN_Unique_s[unfolded hI5_SSN_Unique_def, rule_format, OF both_old(1) both_old(2)]
      pid_old ssn_old cr_old
    show ?thesis
      by blast
  next
    case i_old_j_new
    have j_new: "his_seq s' ! j = mk_act enq (V_var s) p (s_var s p) call"
      using his_eq i_old_j_new by (simp add: nth_append)
    then have pid_j: "act_pid (his_seq s' ! j) = p"
      and ssn_j: "act_ssn (his_seq s' ! j) = s_var s p"
      and cr_j: "act_cr (his_seq s' ! j) = call"
      by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)
    from pid_eq ssn_eq cr_eq pid_j ssn_j cr_j have
      pid_i': "act_pid (his_seq s' ! i) = p"
      and ssn_i': "act_ssn (his_seq s' ! i) = s_var s p"
      and cr_i': "act_cr (his_seq s' ! i) = call"
      by simp_all
    have i_old: "his_seq s' ! i = his_seq s ! i"
      using his_eq i_old_j_new by (simp add: nth_append)
    have i_in: "his_seq s ! i \<in> set (his_seq s)"
      using i_old_j_new by simp
    have pid_i: "act_pid (his_seq s ! i) = p"
      using pid_i' i_old by simp
    have "act_ssn (his_seq s ! i) < s_var s p"
      using ai11_p i_in pid_i pc_L0
      by blast
    then show ?thesis
      using ssn_i' i_old by simp
  next
    case i_new_j_old
    have i_new: "his_seq s' ! i = mk_act enq (V_var s) p (s_var s p) call"
      using his_eq i_new_j_old by (simp add: nth_append)
    then have pid_i: "act_pid (his_seq s' ! i) = p"
      and ssn_i: "act_ssn (his_seq s' ! i) = s_var s p"
      and cr_i: "act_cr (his_seq s' ! i) = call"
      by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)
    from pid_eq ssn_eq cr_eq pid_i ssn_i cr_i have
      pid_j': "act_pid (his_seq s' ! j) = p"
      and ssn_j': "act_ssn (his_seq s' ! j) = s_var s p"
      and cr_j': "act_cr (his_seq s' ! j) = call"
      by simp_all
    have j_old: "his_seq s' ! j = his_seq s ! j"
      using his_eq i_new_j_old by (simp add: nth_append)
    have j_in: "his_seq s ! j \<in> set (his_seq s)"
      using i_new_j_old by simp
    have pid_j: "act_pid (his_seq s ! j) = p"
      using pid_j' j_old by simp
    have "act_ssn (his_seq s ! j) < s_var s p"
      using ai11_p j_in pid_j pc_L0
      by blast
    then show ?thesis
      using ssn_j' j_old by simp
  next
    case both_new
    then show ?thesis by simp
  qed
qed

(* SourceL0Proof.thy / L0_preserves_invariant / E1 / hI14_Pending_Enq_Qback_Exclusivity_s'. *)
(* Original locationoriginal file 878-948 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_pending_enq_qback_exclusive:
  fixes s s' :: SysState and p :: nat
  assumes hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and ssn_eq_E1: "\<And>q. s_var s' q = s_var s q"
    and pc_eq_E1: "\<And>q. program_counter s' q = (if q = p then ''E1'' else program_counter s q)"
    and qback_eq_E1: "\<And>k. Qback_arr s' k = Qback_arr s k"
    and i_eq_E1: "\<And>q. i_var s' q = i_var s q"
    and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and pc_L0: "program_counter s p = ''L0''"
    and TypeOK_s: "TypeOK s"
  shows "hI14_Pending_Enq_Qback_Exclusivity s'"
proof (unfold hI14_Pending_Enq_Qback_Exclusivity_def, intro conjI allI impI)
  fix q a
  assume hq': "HasPendingEnq s' q a \<and> program_counter s' q \<in> {''E2'', ''E3''}"
  then have pend': "HasPendingEnq s' q a"
    and pc_oldish: "program_counter s' q \<in> {''E2'', ''E3''}"
    by auto
  have q_ne_p: "q \<noteq> p"
    using pc_oldish pc_eq_E1[of q] by auto
  have pend: "HasPendingEnq s q a"
    using HasPendingEnq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] pend' q_ne_p
    by auto
  have pc_old: "program_counter s q \<in> {''E2'', ''E3''}"
    using pc_oldish q_ne_p pc_eq_E1[of q] by auto
  have old_no_qback: "\<not> (\<exists>k. Qback_arr s k = a \<and> k \<noteq> i_var s q)"
    using hI14_Pending_Enq_Qback_Exclusivity_s pend pc_old
    unfolding hI14_Pending_Enq_Qback_Exclusivity_def by auto
  show "\<not> (\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q)"
  proof
    assume "\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q"
    then obtain k where
      qback_k': "Qback_arr s' k = a"
      and ki_ne': "k \<noteq> i_var s' q"
      by blast
    have "Qback_arr s k = a \<and> k \<noteq> i_var s q"
      using qback_k' ki_ne' qback_eq_E1[of k] i_eq_E1[of q] by simp
    then show False
      using old_no_qback by blast
  qed
next
  fix q a
  assume hq': "HasPendingEnq s' q a \<and> program_counter s' q = ''E1''"
  then have pend': "HasPendingEnq s' q a"
    and pcE1': "program_counter s' q = ''E1''"
    by auto
  show "\<not> (\<exists>k. Qback_arr s' k = a)"
  proof (cases "q = p")
    case True
    have pending_cases: "HasPendingEnq s q a \<or> a = V_var s"
      using HasPendingEnq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] pend' True
      by auto
    have no_old_pending_p: "\<forall>x. \<not> HasPendingEnq s p x"
      using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s pc_L0]
      by auto
    show ?thesis
    proof (cases "a = V_var s")
      case True
      have fresh_qback: "\<forall>k. Qback_arr s k \<noteq> V_var s"
        using L0_E1_qback_fresh[OF hI3_L0_E_Phase_Bounds_s TypeOK_s] .
      show ?thesis
        using True fresh_qback qback_eq_E1 by auto
    next
      case False
      with pending_cases True no_old_pending_p have False
        by auto
      then show ?thesis by simp
    qed
  next
    case False
    have pc_old: "program_counter s q = ''E1''"
      using pcE1' False pc_eq_E1[of q] by auto
    have pend: "HasPendingEnq s q a"
      using HasPendingEnq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] pend' False
      by auto
    have old_no_qback: "\<not> (\<exists>k. Qback_arr s k = a)"
      using hI14_Pending_Enq_Qback_Exclusivity_s pend pc_old
      unfolding hI14_Pending_Enq_Qback_Exclusivity_def by auto
    show ?thesis
      using old_no_qback qback_eq_E1 by auto
  qed
qed

(* SourceL0Proof.thy / L0_preserves_invariant / E1 / hI30_Ticket_HB_Immunity_s'. *)
(* Original locationoriginal file 1302-1388 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_ticket_hb_immune:
  fixes s s' :: SysState and p :: nat
  assumes hI30_Ticket_HB_Immunity_s: "hI30_Ticket_HB_Immunity s"
    and pc_eq_E1: "\<And>q. program_counter s' q = (if q = p then ''E1'' else program_counter s q)"
    and InQBack_eq_E1: "\<And>a. InQBack s' a \<longleftrightarrow> InQBack s a"
    and v_eq_E1: "\<And>q. v_var s' q = (if q = p then V_var s else v_var s q)"
    and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and Idx_eq_E1: "\<And>a. Idx s' a = Idx s a"
    and i_eq_E1: "\<And>q. i_var s' q = i_var s q"
  shows "hI30_Ticket_HB_Immunity s'"
proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI)
  fix b u
  assume prem':
    "program_counter s' u \<in> {''E2'', ''E3''} \<and>
     InQBack s' b \<and> b \<noteq> BOT \<and>
     b \<noteq> v_var s' u \<and> HB_EnqRetCall s' b (v_var s' u)"
  have u_ne_p: "u \<noteq> p"
    using prem' pc_eq_E1[of u]
    by auto

  have pc_old: "program_counter s u \<in> {''E2'', ''E3''}"
    using prem' u_ne_p pc_eq_E1[of u]
    by auto

  have inq_old: "InQBack s b"
    using prem' InQBack_eq_E1[of b]
    by auto

  have b_not_bot_old: "b \<noteq> BOT"
    using prem'
    by auto

  have neq_old: "b \<noteq> v_var s u"
    using prem' u_ne_p v_eq_E1[of u]
    by auto

  (* HB stability argument. Related symbols: V_var, HB. *)
  have neq_fresh_u: "v_var s u \<noteq> V_var s"
  proof
    assume eq_fresh: "v_var s u = V_var s"
    have pend_u: "HasPendingEnq s u (v_var s u)"
      using hI1_E_Phase_Pending_Enq_s pc_old
      unfolding hI1_E_Phase_Pending_Enq_def
      by blast
    have call_u: "Model.EnqCallInHis s u (v_var s u) (s_var s u)"
      using pend_u
      unfolding HasPendingEnq_def Let_def
      by blast
    then obtain e where
      e_in: "e \<in> set (his_seq s)"
      and e_props:
        "act_pid e = u \<and> act_ssn e = s_var s u \<and>
         act_name e = enq \<and> act_cr e = call \<and> act_val e = v_var s u"
      unfolding Model.EnqCallInHis_def
      by blast
    then obtain k where
      k_lt: "k < length (his_seq s)" and
      kth: "his_seq s ! k = e"
      by (meson in_set_conv_nth)
    (* Use the relevant invariant, lemma, or hypothesis. Related symbols: hI3_L0_E_Phase_Bounds, V_var. *)
    have lt_fresh: "act_val (his_seq s ! k) < V_var s"
      using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s k_lt] kth e_props
      by auto
    with kth e_props eq_fresh show False
      by auto
  qed

  have hb_eq:
    "HB_EnqRetCall s' b (v_var s u) \<longleftrightarrow> HB_EnqRetCall s b (v_var s u)"
    using HB_EnqRetCall_append_enq_call_other_iff[OF his_eq neq_fresh_u, of b] .

  have hb_old: "HB_EnqRetCall s b (v_var s u)"
  proof -
    have "HB_EnqRetCall s' b (v_var s u)"
      using prem' u_ne_p
      by (simp add: v_eq_E1[of u])
    with hb_eq show ?thesis
      by blast
  qed

  have old_prem:
    "program_counter s u \<in> {''E2'', ''E3''} \<and>
     InQBack s b \<and> b \<noteq> BOT \<and>
     b \<noteq> v_var s u \<and> HB_EnqRetCall s b (v_var s u)"
    using pc_old inq_old b_not_bot_old neq_old hb_old
    by blast

  have old_idx: "Idx s b < i_var s u"
    using hI30_Ticket_HB_Immunity_s old_prem
    unfolding hI30_Ticket_HB_Immunity_def
    by blast

  show "Idx s' b < i_var s' u"
    using old_idx u_ne_p Idx_eq_E1[of b] i_eq_E1[of u]
    by simp
qed

lemma L0_E1_op_sets_equiv:
  fixes s s' :: SysState and p :: nat
  assumes lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
    and SetA_eq_E1: "SetA s' = SetA s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and fresh_not_SetA: "V_var s \<notin> SetA s"
    and SetB_eq_E1: "SetB s' = SetB s"
    and fresh_not_TypeB: "\<not> TypeB s (V_var s)"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
  shows "lI1_Op_Sets_Equivalence s'"
proof -
  have op_a_enq_eq: "OP_A_enq s' = OP_A_enq s"
  proof (rule subset_antisym)
    show "OP_A_enq s' \<subseteq> OP_A_enq s"
    proof
      fix x
      assume xin: "x \<in> OP_A_enq s'"
      then obtain q a sn where
        xdef: "x = mk_op enq a q sn"
        and aA': "a \<in> SetA s'"
        and enq': "Model.EnqCallInHis s' q a sn"
        unfolding OP_A_enq_def by blast
      have aA: "a \<in> SetA s"
        using aA' SetA_eq_E1 by simp
      have a_ne: "a \<noteq> V_var s"
        using aA fresh_not_SetA by auto
      have enq: "Model.EnqCallInHis s q a sn"
        using enq' his_eq a_ne
        unfolding Model.EnqCallInHis_def
        by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      show "x \<in> OP_A_enq s"
        using xdef aA enq unfolding OP_A_enq_def by blast
    qed
  next
    show "OP_A_enq s \<subseteq> OP_A_enq s'"
    proof
      fix x
      assume xin: "x \<in> OP_A_enq s"
      then obtain q a sn where
        xdef: "x = mk_op enq a q sn"
        and aA: "a \<in> SetA s"
        and enq: "Model.EnqCallInHis s q a sn"
        unfolding OP_A_enq_def by blast
      have aA': "a \<in> SetA s'"
        using aA SetA_eq_E1 by simp
      have enq': "Model.EnqCallInHis s' q a sn"
        using enq his_eq
        unfolding Model.EnqCallInHis_def
        by auto
      show "x \<in> OP_A_enq s'"
        using xdef aA' enq' unfolding OP_A_enq_def by blast
    qed
  qed

  have op_a_deq_eq: "OP_A_deq s' = OP_A_deq s"
    using SetA_eq_E1 DeqCallInHis_append_enq_call_iff[OF his_eq] lin_seq_eq
    unfolding OP_A_deq_def OPLin_def by auto

  have op_b_enq_eq: "OP_B_enq s' = OP_B_enq s"
  proof (rule subset_antisym)
    show "OP_B_enq s' \<subseteq> OP_B_enq s"
    proof
      fix x
      assume xin: "x \<in> OP_B_enq s'"
      then obtain q a sn where
        xdef: "x = mk_op enq a q sn"
        and aB': "a \<in> SetB s'"
        and enq': "Model.EnqCallInHis s' q a sn"
        unfolding OP_B_enq_def by blast
      have aB: "a \<in> SetB s"
        using aB' SetB_eq_E1 by simp
      have a_ne: "a \<noteq> V_var s"
      proof
        assume a_eq: "a = V_var s"
        from aB have "TypeB s a"
          unfolding SetB_def by auto
        with a_eq fresh_not_TypeB show False
          by simp
      qed
      have enq: "Model.EnqCallInHis s q a sn"
        using enq' his_eq a_ne
        unfolding Model.EnqCallInHis_def
        by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      show "x \<in> OP_B_enq s"
        using xdef aB enq unfolding OP_B_enq_def by blast
    qed
  next
    show "OP_B_enq s \<subseteq> OP_B_enq s'"
    proof
      fix x
      assume xin: "x \<in> OP_B_enq s"
      then obtain q a sn where
        xdef: "x = mk_op enq a q sn"
        and aB: "a \<in> SetB s"
        and enq: "Model.EnqCallInHis s q a sn"
        unfolding OP_B_enq_def by blast
      have aB': "a \<in> SetB s'"
        using aB SetB_eq_E1 by simp
      have enq': "Model.EnqCallInHis s' q a sn"
        using enq his_eq
        unfolding Model.EnqCallInHis_def
        by auto
      show "x \<in> OP_B_enq s'"
        using xdef aB' enq' unfolding OP_B_enq_def by blast
    qed
  qed

  show ?thesis
    using lI1_Op_Sets_Equivalence_s lin_seq_eq op_a_enq_eq op_a_deq_eq op_b_enq_eq
    unfolding lI1_Op_Sets_Equivalence_def OPLin_def by simp
qed

lemma L0_E1_deq_result_exclusive:
  fixes s s' :: SysState and p :: nat
  assumes hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and pc_eq_E1: "\<And>q. program_counter s' q = (if q = p then ''E1'' else program_counter s q)"
    and x_eq_E1: "\<And>q. x_var s' q = x_var s q"
    and qarr_eq_E1: "\<And>k. Q_arr s' k = Q_arr s k"
    and ssn_eq_E1: "\<And>q. s_var s' q = s_var s q"
    and pc_L0: "program_counter s p = ''L0''"
  shows "hI15_Deq_Result_Exclusivity s'"
proof -
  (* Reasoning about appending one history or sequence element. *)
  have deq_ret_eq: "\<And>q a sn. Model.DeqRetInHis s' q a sn \<longleftrightarrow> Model.DeqRetInHis s q a sn"
    using DeqRetInHis_append_call_iff[of s' s "mk_act enq (V_var s) p (s_var s p) call"]
    using his_eq by (simp add: mk_act_def act_cr_def)

  (* State-transition reasoning. Related symbols: L0, E1, D4. *)
  have d4_eq: "\<And>q. (program_counter s' q = ''D4'') \<longleftrightarrow> (program_counter s q = ''D4'')"
    using pc_eq_E1 pc_L0 by auto

  show ?thesis
    unfolding hI15_Deq_Result_Exclusivity_def
  proof (intro conjI)
    (* ================================================================= *)
    (* Branch 1 of the proof. *)
    (* ================================================================= *)
    show "\<forall>a p1 p2. a \<in> Val \<longrightarrow> p1 \<noteq> p2 \<longrightarrow>
          \<not> (((\<exists>sn1. Model.DeqRetInHis s' p1 a sn1) \<or> program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a) \<and>
             ((\<exists>sn2. Model.DeqRetInHis s' p2 a sn2) \<or> program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a))"
    proof (intro allI impI)
      fix a p1 p2 :: nat
      assume "a \<in> Val" "p1 \<noteq> p2"

      (* State-transition reasoning. Related symbols: p1. *)
      have "((\<exists>sn1. Model.DeqRetInHis s' p1 a sn1) \<or> program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a) \<longleftrightarrow>
            ((\<exists>sn1. Model.DeqRetInHis s p1 a sn1) \<or> program_counter s p1 = ''D4'' \<and> x_var s p1 = a)"
        using deq_ret_eq[of p1 a] d4_eq[of p1] x_eq_E1[of p1]
        by simp

      (* State-transition reasoning. Related symbols: p2. *)
      moreover have "((\<exists>sn2. Model.DeqRetInHis s' p2 a sn2) \<or> program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a) \<longleftrightarrow>
                     ((\<exists>sn2. Model.DeqRetInHis s p2 a sn2) \<or> program_counter s p2 = ''D4'' \<and> x_var s p2 = a)"
        using deq_ret_eq[of p2 a] d4_eq[of p2] x_eq_E1[of p2] by simp

      (* State-transition reasoning. *)
      ultimately show "\<not> (((\<exists>sn1. Model.DeqRetInHis s' p1 a sn1) \<or> program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a) \<and>
                         ((\<exists>sn2. Model.DeqRetInHis s' p2 a sn2) \<or> program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a))"
        using hI15_Deq_Result_Exclusivity_s \<open>a \<in> Val\<close> \<open>p1 \<noteq> p2\<close>
        unfolding hI15_Deq_Result_Exclusivity_def by auto
    qed

    (* ================================================================= *)
    (* Branch 2 of the proof. Related symbols: Q_arr. *)
    (* ================================================================= *)
    show "\<forall>q a k. a \<in> Val \<longrightarrow> HasPendingDeq s' q \<longrightarrow> \<not> (x_var s' q = a \<and> Q_arr s' k = a)"
    proof (intro allI impI)
      fix q a k
      assume "a \<in> Val" "HasPendingDeq s' q"
      hence "HasPendingDeq s q"
        using HasPendingDeq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] by simp
      thus "\<not> (x_var s' q = a \<and> Q_arr s' k = a)"
        using hI15_Deq_Result_Exclusivity_s \<open>a \<in> Val\<close>
        unfolding hI15_Deq_Result_Exclusivity_def
        using x_eq_E1[of q] qarr_eq_E1[of k] by auto
    qed

    (* ================================================================= *)
    (* Branch 3 of the proof. Related symbols: Q_arr. *)
    (* ================================================================= *)
    show "\<forall>q a. a \<in> Val \<longrightarrow> (\<exists>sn. Model.DeqRetInHis s' q a sn) \<longrightarrow> (\<forall>k. Q_arr s' k \<noteq> a)"
      using hI15_Deq_Result_Exclusivity_s deq_ret_eq qarr_eq_E1
      unfolding hI15_Deq_Result_Exclusivity_def
      by auto
  qed
qed

(* SourceL0Proof.thy / L0_preserves_invariant / E1 / hI25_Enq_Call_Ret_Balanced_s'. *)
(* Original locationoriginal file 1356-1512 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_enq_call_ret_balanced:
  fixes s s' :: SysState and p :: nat
  assumes hI25_Enq_Call_Ret_Balanced_s: "hI25_Enq_Call_Ret_Balanced s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and pc_eq_E1: "\<And>q. program_counter s' q = (if q = p then ''E1'' else program_counter s q)"
    and pc_L0: "program_counter s p = ''L0''"
  shows "hI25_Enq_Call_Ret_Balanced s'"
    proof (unfold hI25_Enq_Call_Ret_Balanced_def, intro allI impI)
      fix q k
      let ?n = "length (his_seq s)"
      assume k_le': "k \<le> length (his_seq s')"
      have len': "length (his_seq s') = Suc ?n"
        using his_eq by simp
      show "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')) in
              let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
              let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
              n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
              (k = length (his_seq s') \<longrightarrow>
                (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1))"
      proof (cases "k \<le> ?n")
        case True
        have take_eq: "take k (his_seq s') = take k (his_seq s)"
          using his_eq True by simp
        have k_ne_len': "k \<noteq> length (his_seq s')"
          using True len' by linarith
        show ?thesis
        proof -
          let ?p_his_old = "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s))"
          let ?n_call_old = "length (filter (\<lambda>e. act_cr e = call) ?p_his_old)"
          let ?n_ret_old = "length (filter (\<lambda>e. act_cr e = ret) ?p_his_old)"
          have old_prop_raw:
            "?n_call_old \<ge> ?n_ret_old \<and> ?n_call_old - ?n_ret_old \<le> 1 \<and>
             (k = length (his_seq s) \<longrightarrow>
               (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> ?n_call_old - ?n_ret_old = 1))"
            using hI25_Enq_Call_Ret_Balanced_s True
            unfolding hI25_Enq_Call_Ret_Balanced_def Let_def
            by blast
          have old_bounds:
            "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s)) in
               let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
               let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
               n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1"
            using old_prop_raw
            unfolding Let_def
            by simp
          have bounds:
            "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')) in
               let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
               let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
               n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1"
            using old_bounds take_eq
            unfolding Let_def
            by simp
          then show ?thesis
            using k_ne_len'
            by simp
        qed
      next
        case False
        with k_le' len' have k_full: "k = Suc ?n"
          by linarith
        let ?p_his_old = "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (his_seq s)"
        let ?n_call_old = "length (filter (\<lambda>e. act_cr e = call) ?p_his_old)"
        let ?n_ret_old = "length (filter (\<lambda>e. act_cr e = ret) ?p_his_old)"
        have old_prop_q_raw:
          "?n_call_old \<ge> ?n_ret_old \<and> ?n_call_old - ?n_ret_old \<le> 1 \<and>
           (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> ?n_call_old - ?n_ret_old = 1)"
        proof -
          from hI25_Enq_Call_Ret_Balanced_s have
            "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take (length (his_seq s)) (his_seq s)) in
               let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
               let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
               n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
               (length (his_seq s) = length (his_seq s) \<longrightarrow>
                 (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1))"
            unfolding hI25_Enq_Call_Ret_Balanced_def by blast
          then show ?thesis
            unfolding Let_def
            by simp
        qed
        have old_prop_q:
          "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (his_seq s) in
             let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
             let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
             n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
             (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1)"
          using old_prop_q_raw
          unfolding Let_def
          by simp
        show ?thesis
        proof (cases "q = p")
          case False
          have qhis_eq:
            "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')) =
             filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (his_seq s)"
            using his_eq k_full False
            by (simp add: mk_act_def act_pid_def act_name_def)
          have pc_eq:
            "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow>
             program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
            using False pc_eq_E1[of q]
            by simp
          show ?thesis
          proof -
            have raw':
              "?n_call_old \<ge> ?n_ret_old \<and> ?n_call_old - ?n_ret_old \<le> 1 \<and>
               (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> ?n_call_old - ?n_ret_old = 1)"
              using old_prop_q_raw pc_eq
              by simp
            have n_call_eq:
              "length (filter (\<lambda>e. act_cr e = call)
                 (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')))) = ?n_call_old"
              using qhis_eq
              by simp
            have n_ret_eq:
              "length (filter (\<lambda>e. act_cr e = ret)
                 (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')))) = ?n_ret_old"
              using qhis_eq
              by simp
            have k_eq_len': "k = length (his_seq s')"
              using k_full len'
              by simp
            then show ?thesis
              using raw' n_call_eq n_ret_eq
              unfolding Let_def
              by simp
          qed
        next
          case True
          let ?q_his = "filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (his_seq s)"
          let ?C = "length (filter (\<lambda>e. act_cr e = call) ?q_his)"
          let ?R = "length (filter (\<lambda>e. act_cr e = ret) ?q_his)"
          have old_bounds:
            "?C \<ge> ?R \<and> ?C - ?R \<le> 1 \<and>
             (program_counter s p \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> ?C - ?R = 1)"
            using old_prop_q_raw True
            by simp
          have diff_ne_1: "?C - ?R \<noteq> 1"
            using old_bounds pc_L0 by simp
          have counts_eq: "?C = ?R"
          proof (cases "?C = ?R")
            case True
            then show ?thesis .
          next
            case False
            from old_bounds have r_le_c: "?R \<le> ?C"
              by simp
            from old_bounds have diff_le_1: "?C - ?R \<le> 1"
              by simp
            from False r_le_c have r_lt_c: "?R < ?C"
              by linarith
            with diff_le_1 have c_suc_r: "?C = Suc ?R"
              by arith
            then have "?C - ?R = 1"
              by simp
            with diff_ne_1 show ?thesis
              by contradiction
          qed
          show ?thesis
            using his_eq k_full True counts_eq pc_eq_E1[of p]
            by (simp add: mk_act_def act_pid_def act_name_def act_cr_def)
        qed
      qed
    qed

(* SourceL0Proof.thy / L0_preserves_invariant / E1 / hI28_Fresh_Enq_Immunity_s'. *)
(* Original locationoriginal file 1599-1718 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_fresh_enq_immune:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and v_eq_E1: "\<And>q. v_var s' q = (if q = p then V_var s else v_var s q)"
    and hI28_Fresh_Enq_Immunity_s: "hI28_Fresh_Enq_Immunity s"
    and pc_eq_E1: "\<And>q. program_counter s' q = (if q = p then ''E1'' else program_counter s q)"
    and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s"
    and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s"
    and fresh_not_SetA: "V_var s \<notin> SetA s"
    and fresh_not_SetB: "V_var s \<notin> SetB s"
  shows "hI28_Fresh_Enq_Immunity s'"
    proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI notI)
      fix u q a sn
      assume prem':
        "program_counter s' u \<in> {''E1'', ''E2''} \<and> v_var s' u = a \<and> a \<noteq> BOT"
      assume deq': "Model.DeqRetInHis s' q a sn"

      (* ========================================================================= *)
      (* State-transition reasoning. Related symbols: step_facts. *)
      (* ========================================================================= *)
      have step_facts:
        "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
        "v_var s' p = V_var s"
        using his_eq apply auto[1]
        by (simp add: v_eq_E1)

      show False
      proof (cases "u = p")
        case False
        (* ------------------------------------------------------------------------- *)
        (* State-transition reasoning. *)
        (* ------------------------------------------------------------------------- *)
        have pc_old: "program_counter s u \<in> {''E1'', ''E2''}"
          using prem' False pc_eq_E1[of u] by auto
        have v_old: "v_var s u = a"
          using prem' False v_eq_E1[of u] by auto

        (* Reasoning about appending one history or sequence element. *)
        have deq_old: "Model.DeqRetInHis s q a sn"
        proof -
          from deq' obtain e where "e \<in> set (his_seq s')"
            (* Key proof fix. Related symbols: act_ssn. *)
            and e_props: "act_pid e = q" "act_ssn e = sn" "act_name e = deq" "act_cr e = ret" "act_val e = a"
            unfolding Model.DeqRetInHis_def by blast

          (* Set, cardinality, and uniqueness reasoning. *)
          have "e \<in> set (his_seq s)"
            using \<open>e \<in> set (his_seq s')\<close> step_facts e_props
            by (auto simp: mk_act_def act_name_def)

          thus ?thesis using e_props unfolding Model.DeqRetInHis_def by blast
        qed

        from hI28_Fresh_Enq_Immunity_s pc_old v_old deq_old show False
          unfolding hI28_Fresh_Enq_Immunity_def
          using prem' by blast

      next
        case True
        (* ------------------------------------------------------------------------- *)
        (* Ticket-counter freshness and ordering reasoning. Related symbols: V_var. *)
        (* ------------------------------------------------------------------------- *)
        have a_eq: "a = V_var s"
          using prem' True step_facts by auto

        have deq_old: "Model.DeqRetInHis s q (V_var s) sn"
        proof -
          from deq' obtain e where "e \<in> set (his_seq s')"
            (* Key proof fix. Related symbols: act_ssn. *)
            and e_props: "act_pid e = q" "act_ssn e = sn" "act_name e = deq" "act_cr e = ret" "act_val e = V_var s"
            unfolding Model.DeqRetInHis_def a_eq by blast

          have "e \<in> set (his_seq s)"
            using \<open>e \<in> set (his_seq s')\<close> step_facts e_props
            by (auto simp: mk_act_def act_name_def)

          thus ?thesis using e_props unfolding Model.DeqRetInHis_def by blast
        qed

        (* ========================================================================= *)
        (* Use the relevant invariant, lemma, or hypothesis. *)
        (* ========================================================================= *)
        have False
        proof -
          (* Happens-before reasoning. Related symbols: deq_old, lI3_HB_Ret_Lin_Sync. *)
          from deq_old obtain e_ret_deq where e_ret_deq: "e_ret_deq \<in> set (his_seq s)"
            "act_name e_ret_deq = deq" "act_cr e_ret_deq = ret" "act_val e_ret_deq = V_var s"
            unfolding DeqRetInHis_def by blast
          then obtain k_deq where k_deq: "k_deq < length (lin_seq s)"
            "lin_seq s ! k_deq = mk_op deq (V_var s) (act_pid e_ret_deq) (act_ssn e_ret_deq)"
            using lI3_HB_Ret_Lin_Sync_s unfolding lI3_HB_Ret_Lin_Sync_def
            using DeqRetInHis_def by blast

          (* Step 2: use the available invariant or hypothesis. Related symbols: lI4_FIFO_Semantics. *)
          (* Proof-automation note. *)
          have op_deq: "op_name (lin_seq s ! k_deq) = deq"
            using k_deq(2) by (simp add: mk_op_def op_name_def)
          have val_deq: "op_val (lin_seq s ! k_deq) = V_var s"
            using k_deq(2) by (simp add: mk_op_def op_val_def)

          (* Dequeue-side reasoning. Related symbols: op_deq. *)
          from lI4_FIFO_Semantics_s k_deq(1) op_deq obtain k_enq where k_enq: "k_enq < k_deq"
            and enq: "op_name (lin_seq s ! k_enq) = enq"
            and val_enq_eq: "op_val (lin_seq s ! k_enq) = op_val (lin_seq s ! k_deq)"
            unfolding lI4_FIFO_Semantics_def lI4_FIFO_Semantics_list_def Let_def by blast

          (* Ticket-counter freshness and ordering reasoning. Related symbols: V_var. *)
          have val_enq: "op_val (lin_seq s ! k_enq) = V_var s"
            using val_enq_eq val_deq by simp

          have k_enq_len: "k_enq < length (lin_seq s)" using k_enq k_deq(1) by simp

          (* Step 3: use the available invariant or hypothesis. *)
          (* Enqueue-side reasoning. Related symbols: SetA, SetB. *)
          have "lin_seq s ! k_enq \<in> set (lin_seq s)"
            using k_enq_len by (rule nth_mem)
          then have "op_val (lin_seq s ! k_enq) \<in> SetA s \<union> SetB s"
            using enq lin_seq_enq_in_sets
            by (simp add: INV)

          (* Ticket-counter freshness and ordering reasoning. Related symbols: V_var. *)
          then have "V_var s \<in> SetA s \<union> SetB s"
            using val_enq by simp

          (* Proof note. *)
          with fresh_not_SetA fresh_not_SetB show False
            by blast
        qed
        then show False by simp
      qed
    qed

(* SourceL0Proof.thy / L0_preserves_invariant / E1 / hI29_E2_Scanner_Immunity_s'. *)
(* Original locationoriginal file 1721-1827 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_e2_scanner_immune:
  fixes s s' :: SysState and p :: nat
  assumes hI29_E2_Scanner_Immunity_s: "hI29_E2_Scanner_Immunity s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and ssn_eq_E1: "\<And>q. s_var s' q = s_var s q"
    and pc_eq_E1: "\<And>q. program_counter s' q = (if q = p then ''E1'' else program_counter s q)"
    and InQBack_eq_E1: "\<And>a. InQBack s' a \<longleftrightarrow> InQBack s a"
    and TypeB_eq_E1: "\<And>a. TypeB s' a \<longleftrightarrow> TypeB s a"
    and Idx_eq_E1: "\<And>a. Idx s' a = Idx s a"
    and j_eq_E1: "\<And>q. j_var s' q = j_var s q"
    and i_eq_E1: "\<And>q. i_var s' q = i_var s q"
    and l_eq_E1: "\<And>q. l_var s' q = l_var s q"
    and v_eq_E1: "\<And>q. v_var s' q = (if q = p then V_var s else v_var s q)"
    and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s"
    and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and pc_L0: "program_counter s p = ''L0''"
    and pc_D3_eq_E1: "\<And>q. (program_counter s' q = ''D3'') \<longleftrightarrow> (program_counter s q = ''D3'')"
  shows "hI29_E2_Scanner_Immunity s'"
    proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI notI)
      fix u a q
      assume prem':
        "program_counter s' u = ''E2'' \<and>
         InQBack s' a \<and> TypeB s' a \<and>
         HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
         Idx s' a < j_var s' q \<and> j_var s' q \<le> i_var s' u \<and> i_var s' u < l_var s' q"
      assume hb': "HB_EnqRetCall s' a (v_var s' u)"

      have u_ne_p: "u \<noteq> p"
        using prem' pc_eq_E1[of u]
        by auto

      have pc_u_old: "program_counter s u = ''E2''"
        using prem' u_ne_p pc_eq_E1[of u]
        by auto

      have inq_old: "InQBack s a"
        using prem' InQBack_eq_E1[of a]
        by auto

      have type_old: "TypeB s a"
        using prem' TypeB_eq_E1[of a]
        by auto

      have pend_old: "HasPendingDeq s q"
        using prem' HasPendingDeq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]]
        by auto

      have pc_q_old: "program_counter s q = ''D3''"
      proof (cases "q = p")
        case True
        then have "program_counter s q = ''L0''"
          using pc_L0 by simp
        with prem' True show ?thesis
          using pc_D3_eq_E1[of q] by auto
      next
        case False
        with prem' show ?thesis
          using pc_D3_eq_E1[of q] by auto
      qed

      have idx_old: "Idx s a < j_var s q"
        using prem' Idx_eq_E1[of a] j_eq_E1[of q]
        by auto

      have ji_old: "j_var s q \<le> i_var s u"
        using prem' j_eq_E1[of q] i_eq_E1[of u] u_ne_p
        by auto

      have il_old: "i_var s u < l_var s q"
        using prem' i_eq_E1[of u] l_eq_E1[of q] u_ne_p
        by auto

      have old_prem:
        "program_counter s u = ''E2'' \<and>
         InQBack s a \<and> TypeB s a \<and>
         HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and>
         Idx s a < j_var s q \<and> j_var s q \<le> i_var s u \<and> i_var s u < l_var s q"
        using pc_u_old inq_old type_old pend_old pc_q_old idx_old ji_old il_old
        by blast

      have hb'_oldarg: "HB_EnqRetCall s' a (v_var s u)"
        using hb' u_ne_p
        by (simp add: v_eq_E1[of u])

      have hb_old: "HB_EnqRetCall s a (v_var s u)"
      proof -
        have neq_fresh: "v_var s u \<noteq> V_var s"
        proof
          assume eq_fresh: "v_var s u = V_var s"
          have cur_enq: "Model.EnqCallInHis s u (V_var s) (s_var s u)"
            using hI10_Enq_Call_Existence_s pc_u_old eq_fresh
            unfolding hI10_Enq_Call_Existence_def
            by auto
          then obtain e where
            e_in: "e \<in> set (his_seq s)"
            and e_props:
              "act_pid e = u \<and> act_ssn e = s_var s u \<and>
               act_name e = enq \<and> act_cr e = call \<and> act_val e = V_var s"
            unfolding Model.EnqCallInHis_def
            by blast
          then obtain k where
            k_lt: "k < length (his_seq s)" and
            kth: "his_seq s ! k = e"
            by (meson in_set_conv_nth)
          have no_fresh_call:
            "\<forall>k < length (his_seq s).
               \<not> (act_name (his_seq s ! k) = enq \<and>
                  act_cr (his_seq s ! k) = call \<and>
                  act_val (his_seq s ! k) = V_var s)"
            using L0_E1_fresh[OF hI3_L0_E_Phase_Bounds_s pc_L0] .
          from no_fresh_call[rule_format, OF k_lt] kth e_props
          show False
            by auto
        qed
        have hb_eq:
          "HB_EnqRetCall s' a (v_var s u) \<longleftrightarrow> HB_EnqRetCall s a (v_var s u)"
          using HB_EnqRetCall_append_enq_call_other_iff[OF his_eq neq_fresh] .
        from hb_eq hb'_oldarg show ?thesis
          by blast
      qed

      from hI29_E2_Scanner_Immunity_s old_prem hb_old show False
        unfolding hI29_E2_Scanner_Immunity_def
        by blast
    qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / D3Witness_eq_D1. *)
(* Original locationoriginal file 1670-1751 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_d3_witness_eq:
  fixes s s' :: SysState and a :: nat
  assumes pc_D3_eq_D1: "\<And>q. (program_counter s' q = ''D3'') \<longleftrightarrow> (program_counter s q = ''D3'')"
    and Idx_eq_D1: "\<And>a. Idx s' a = Idx s a"
    and j_eq_D1: "\<And>q. j_var s' q = j_var s q"
    and l_eq_D1: "\<And>q. l_var s' q = l_var s q"
    and D3Block_eq_D1:
      "\<And>pa a. (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT) \<longleftrightarrow>
                (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)"
  shows
    "(\<exists>pa. program_counter s' pa = ''D3'' \<and>
          j_var s' pa \<le> Idx s' a \<and> Idx s' a < l_var s' pa \<and>
          (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)) \<longleftrightarrow>
     (\<exists>pa. program_counter s pa = ''D3'' \<and>
          j_var s pa \<le> Idx s a \<and> Idx s a < l_var s pa \<and>
          (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT))"
proof
  assume ex':
    "\<exists>pa. program_counter s' pa = ''D3'' \<and>
          j_var s' pa \<le> Idx s' a \<and> Idx s' a < l_var s' pa \<and>
          (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)"
  then show
    "\<exists>pa. program_counter s pa = ''D3'' \<and>
          j_var s pa \<le> Idx s a \<and> Idx s a < l_var s pa \<and>
          (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)"
  proof (elim exE conjE)
    fix pa
    assume paD3': "program_counter s' pa = ''D3''"
    assume jle': "j_var s' pa \<le> Idx s' a"
    assume ilt': "Idx s' a < l_var s' pa"
    assume block': "\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
    have paD3: "program_counter s pa = ''D3''"
      using paD3' pc_D3_eq_D1[of pa] by simp
    have jle: "j_var s pa \<le> Idx s a"
      using jle' Idx_eq_D1[of a] j_eq_D1[of pa] by simp
    have ilt: "Idx s a < l_var s pa"
      using ilt' Idx_eq_D1[of a] l_eq_D1[of pa] by simp
    have block: "\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT"
      using D3Block_eq_D1[of pa a] block' by simp
    have old_ex:
      "\<exists>pb. program_counter s pb = ''D3'' \<and>
            j_var s pb \<le> Idx s a \<and> Idx s a < l_var s pb \<and>
            (\<forall>k. j_var s pb \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)"
    proof (intro exI[of _ pa])
      show "program_counter s pa = ''D3'' \<and>
            j_var s pa \<le> Idx s a \<and> Idx s a < l_var s pa \<and>
            (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)"
        using paD3 jle ilt block by simp
    qed
    from old_ex show "\<exists>pa. program_counter s pa = ''D3'' \<and>
                        j_var s pa \<le> Idx s a \<and> Idx s a < l_var s pa \<and>
                        (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)" .
  qed
next
  assume ex:
    "\<exists>pa. program_counter s pa = ''D3'' \<and>
          j_var s pa \<le> Idx s a \<and> Idx s a < l_var s pa \<and>
          (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)"
  then show
    "\<exists>pa. program_counter s' pa = ''D3'' \<and>
          j_var s' pa \<le> Idx s' a \<and> Idx s' a < l_var s' pa \<and>
          (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)"
  proof (elim exE conjE)
    fix pa
    assume paD3: "program_counter s pa = ''D3''"
    assume jle: "j_var s pa \<le> Idx s a"
    assume ilt: "Idx s a < l_var s pa"
    assume block: "\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT"
    have paD3': "program_counter s' pa = ''D3''"
      using paD3 pc_D3_eq_D1[of pa] by simp
    have jle': "j_var s' pa \<le> Idx s' a"
      using jle Idx_eq_D1[of a] j_eq_D1[of pa] by simp
    have ilt': "Idx s' a < l_var s' pa"
      using ilt Idx_eq_D1[of a] l_eq_D1[of pa] by simp
    have block': "\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
      using D3Block_eq_D1[of pa a] block by simp
    have new_ex:
      "\<exists>pb. program_counter s' pb = ''D3'' \<and>
            j_var s' pb \<le> Idx s' a \<and> Idx s' a < l_var s' pb \<and>
            (\<forall>k. j_var s' pb \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)"
    proof (intro exI[of _ pa])
      show "program_counter s' pa = ''D3'' \<and>
            j_var s' pa \<le> Idx s' a \<and> Idx s' a < l_var s' pa \<and>
            (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)"
        using paD3' jle' ilt' block' by simp
    qed
    from new_ex show "\<exists>pa. program_counter s' pa = ''D3'' \<and>
                        j_var s' pa \<le> Idx s' a \<and> Idx s' a < l_var s' pa \<and>
                        (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)" .
  qed
qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / TypeBT_eq_D1. *)
(* Original locationoriginal file 1792-1883 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_typebt_eq:
  fixes s s' :: SysState and a :: nat
  assumes TypeB_eq_D1: "\<And>a. TypeB s' a \<longleftrightarrow> TypeB s a"
    and InQBack_eq_D1: "\<And>a. InQBack s' a \<longleftrightarrow> InQBack s a"
    and PrefixBOT_eq_D1: "\<And>a. (\<forall>k<Idx s' a. Q_arr s' k = BOT) \<longleftrightarrow> (\<forall>k<Idx s a. Q_arr s k = BOT)"
    and D3Witness_eq_D1:
      "\<And>a. ((\<exists>pa. program_counter s' pa = ''D3'' \<and>
                 j_var s' pa \<le> Idx s' a \<and> Idx s' a < l_var s' pa \<and>
                 (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)) \<longleftrightarrow>
                (\<exists>pa. program_counter s pa = ''D3'' \<and>
                 j_var s pa \<le> Idx s a \<and> Idx s a < l_var s pa \<and>
                 (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)))"
  shows "TypeBT s' a \<longleftrightarrow> TypeBT s a"
proof
  assume bt': "TypeBT s' a"
  have bt'_parts:
    "TypeB s' a \<and> InQBack s' a \<and>
     ((\<forall>k<Idx s' a. Q_arr s' k = BOT) \<or>
      (\<exists>p. program_counter s' p = ''D3'' \<and>
           j_var s' p \<le> Idx s' a \<and> Idx s' a < l_var s' p \<and>
           (\<forall>k. j_var s' p \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)))"
    using bt' unfolding TypeBT_def by simp
  have tb': "TypeB s' a"
    using bt'_parts by blast
  have inq': "InQBack s' a"
    using bt'_parts by blast
  have rest':
    "(\<forall>k<Idx s' a. Q_arr s' k = BOT) \<or>
     (\<exists>p. program_counter s' p = ''D3'' \<and>
          j_var s' p \<le> Idx s' a \<and> Idx s' a < l_var s' p \<and>
          (\<forall>k. j_var s' p \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT))"
    using bt'_parts by blast
  have tb: "TypeB s a"
    using TypeB_eq_D1[of a] tb' by simp
  have inq: "InQBack s a"
    using InQBack_eq_D1[of a] inq' by simp
  have rest:
    "(\<forall>k<Idx s a. Q_arr s k = BOT) \<or>
     (\<exists>p. program_counter s p = ''D3'' \<and>
          j_var s p \<le> Idx s a \<and> Idx s a < l_var s p \<and>
          (\<forall>k. j_var s p \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT))"
  proof -
    from rest' show ?thesis
    proof
      assume 1: "\<forall>k<Idx s' a. Q_arr s' k = BOT"
      then show ?thesis
        using PrefixBOT_eq_D1[of a] by simp
    next
      assume 2:
        "\<exists>p. program_counter s' p = ''D3'' \<and>
             j_var s' p \<le> Idx s' a \<and> Idx s' a < l_var s' p \<and>
             (\<forall>k. j_var s' p \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)"
      then show ?thesis
        using D3Witness_eq_D1[of a] by simp
    qed
  qed
  show "TypeBT s a"
    using tb inq rest unfolding TypeBT_def by blast
next
  assume bt: "TypeBT s a"
  have bt_parts:
    "TypeB s a \<and> InQBack s a \<and>
     ((\<forall>k<Idx s a. Q_arr s k = BOT) \<or>
      (\<exists>p. program_counter s p = ''D3'' \<and>
           j_var s p \<le> Idx s a \<and> Idx s a < l_var s p \<and>
           (\<forall>k. j_var s p \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)))"
    using bt unfolding TypeBT_def by simp
  have tb: "TypeB s a"
    using bt_parts by blast
  have inq: "InQBack s a"
    using bt_parts by blast
  have rest:
    "(\<forall>k<Idx s a. Q_arr s k = BOT) \<or>
     (\<exists>p. program_counter s p = ''D3'' \<and>
          j_var s p \<le> Idx s a \<and> Idx s a < l_var s p \<and>
          (\<forall>k. j_var s p \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT))"
    using bt_parts by blast
  have tb': "TypeB s' a"
    using TypeB_eq_D1[of a] tb by simp
  have inq': "InQBack s' a"
    using InQBack_eq_D1[of a] inq by simp
  have rest':
    "(\<forall>k<Idx s' a. Q_arr s' k = BOT) \<or>
     (\<exists>p. program_counter s' p = ''D3'' \<and>
          j_var s' p \<le> Idx s' a \<and> Idx s' a < l_var s' p \<and>
          (\<forall>k. j_var s' p \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT))"
  proof -
    from rest show ?thesis
    proof
      assume 1: "\<forall>k<Idx s a. Q_arr s k = BOT"
      then show ?thesis
        using PrefixBOT_eq_D1[of a] by simp
    next
      assume 2:
        "\<exists>p. program_counter s p = ''D3'' \<and>
             j_var s p \<le> Idx s a \<and> Idx s a < l_var s p \<and>
             (\<forall>k. j_var s p \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)"
      then show ?thesis
        using D3Witness_eq_D1[of a] by simp
    qed
  qed
  show "TypeBT s' a"
    using tb' inq' rest' unfolding TypeBT_def by blast
qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / hI5_SSN_Unique_s'. *)
(* Original locationoriginal file 2097-2188 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_ssn_unique:
  fixes s s' :: SysState and p :: nat
  assumes hI5_SSN_Unique_s: "hI5_SSN_Unique s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and ai11_p:
      "\<forall>ev \<in> set (his_seq s).
         act_pid ev = p \<longrightarrow>
         (act_ssn ev \<le> s_var s p \<and>
          (program_counter s p = ''L0'' \<longrightarrow> act_ssn ev < s_var s p))"
    and pc_L0: "program_counter s p = ''L0''"
  shows "hI5_SSN_Unique s'"
proof (unfold hI5_SSN_Unique_def, intro allI impI)
  fix i j
  assume i_lt: "i < length (his_seq s')" and j_lt: "j < length (his_seq s')"
  assume props_raw:
    "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j) \<and>
     act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j) \<and>
     act_cr (his_seq s' ! i) = act_cr (his_seq s' ! j)"
  let ?L = "length (his_seq s)"
  have len': "length (his_seq s') = Suc ?L"
    using his_eq by simp
  have pid_eq:
    "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
    and ssn_eq:
    "act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j)"
    and cr_eq:
    "act_cr (his_seq s' ! i) = act_cr (his_seq s' ! j)"
    using props_raw by auto
  consider (both_old) "i < ?L" "j < ?L"
    | (i_old_j_new) "i < ?L" "j = ?L"
    | (i_new_j_old) "i = ?L" "j < ?L"
    | (both_new) "i = ?L" "j = ?L"
    using i_lt j_lt len' by linarith
  then show "i = j"
  proof cases
    case both_old
    have pid_old: "act_pid (his_seq s ! i) = act_pid (his_seq s ! j)"
      using pid_eq both_old his_eq
      by (simp add: nth_append)
    have ssn_old: "act_ssn (his_seq s ! i) = act_ssn (his_seq s ! j)"
      using ssn_eq both_old his_eq
      by (simp add: nth_append)
    have cr_old: "act_cr (his_seq s ! i) = act_cr (his_seq s ! j)"
      using cr_eq both_old his_eq
      by (simp add: nth_append)
    from hI5_SSN_Unique_s[unfolded hI5_SSN_Unique_def, rule_format, OF both_old(1) both_old(2)]
      pid_old ssn_old cr_old
    show ?thesis
      by blast
  next
    case i_old_j_new
    have j_new: "his_seq s' ! j = mk_act deq BOT p (s_var s p) call"
      using his_eq i_old_j_new by (simp add: nth_append)
    then have pid_j: "act_pid (his_seq s' ! j) = p"
      and ssn_j: "act_ssn (his_seq s' ! j) = s_var s p"
      and cr_j: "act_cr (his_seq s' ! j) = call"
      by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)
    from pid_eq ssn_eq cr_eq pid_j ssn_j cr_j have
      pid_i': "act_pid (his_seq s' ! i) = p"
      and ssn_i': "act_ssn (his_seq s' ! i) = s_var s p"
      and cr_i': "act_cr (his_seq s' ! i) = call"
      by simp_all
    have i_old: "his_seq s' ! i = his_seq s ! i"
      using his_eq i_old_j_new by (simp add: nth_append)
    have i_in: "his_seq s ! i \<in> set (his_seq s)"
      using i_old_j_new by simp
    have pid_i: "act_pid (his_seq s ! i) = p"
      using pid_i' i_old by simp
    have "act_ssn (his_seq s ! i) < s_var s p"
      using ai11_p i_in pid_i pc_L0
      by blast
    then show ?thesis
      using ssn_i' i_old by simp
  next
    case i_new_j_old
    have i_new: "his_seq s' ! i = mk_act deq BOT p (s_var s p) call"
      using his_eq i_new_j_old by (simp add: nth_append)
    then have pid_i: "act_pid (his_seq s' ! i) = p"
      and ssn_i: "act_ssn (his_seq s' ! i) = s_var s p"
      and cr_i: "act_cr (his_seq s' ! i) = call"
      by (simp_all add: mk_act_def act_pid_def act_ssn_def act_cr_def)
    from pid_eq ssn_eq cr_eq pid_i ssn_i cr_i have
      pid_j': "act_pid (his_seq s' ! j) = p"
      and ssn_j': "act_ssn (his_seq s' ! j) = s_var s p"
      and cr_j': "act_cr (his_seq s' ! j) = call"
      by simp_all
    have j_old: "his_seq s' ! j = his_seq s ! j"
      using his_eq i_new_j_old by (simp add: nth_append)
    have j_in: "his_seq s ! j \<in> set (his_seq s)"
      using i_new_j_old by simp
    have pid_j: "act_pid (his_seq s ! j) = p"
      using pid_j' j_old by simp
    have "act_ssn (his_seq s ! j) < s_var s p"
      using ai11_p j_in pid_j pc_L0
      by blast
    then show ?thesis
      using ssn_j' j_old by simp
  next
    case both_new
    then show ?thesis by simp
  qed
qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / hI27_Pending_PC_Sync_s'. *)
(* Original locationoriginal file 2741-2817 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_pending_pc_sync:
  fixes s s' :: SysState and p :: nat
  assumes hI27_Pending_PC_Sync_s: "hI27_Pending_PC_Sync s"
    and pc_eq_D1: "\<And>q. program_counter s' q = (if q = p then ''D1'' else program_counter s q)"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and ssn_eq_D1: "\<And>q. s_var s' q = s_var s q"
    and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and pc_L0: "program_counter s p = ''L0''"
    and v_eq_D1: "\<And>q. v_var s' q = v_var s q"
  shows "hI27_Pending_PC_Sync s'"
proof (unfold hI27_Pending_PC_Sync_def, intro conjI allI impI)
  fix q
  assume pend': "HasPendingDeq s' q"
  show "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
  proof (cases "q = p")
    case True
    then show ?thesis
      using pc_eq_D1[of q]
      by auto
  next
    case False
    have pend_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
      using HasPendingDeq_append_deq_call_other_iff[OF his_eq False ssn_eq_D1[of q]] .
    have pend_old: "HasPendingDeq s q"
      using pend' pend_eq by blast
    have pc_old: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using hI27_Pending_PC_Sync_s pend_old
      unfolding hI27_Pending_PC_Sync_def
      by blast
    show ?thesis
      using pc_old pc_eq_D1[of q] False
      by auto
  qed
next
  fix q
  assume pend': "HasPendingEnq s' q (v_var s' q)"
  show "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
  proof (cases "q = p")
    case True
    have pc_q_L0: "program_counter s q = ''L0''"
      using True pc_L0 by simp
    have no_pend_old: "\<not> HasPendingEnq s q (v_var s' q)"
      using hI3_L0_E_Phase_Bounds_L0_pending[OF hI3_L0_E_Phase_Bounds_s pc_q_L0] by blast
    have pend_eq: "HasPendingEnq s' q (v_var s' q) \<longleftrightarrow> HasPendingEnq s q (v_var s' q)"
      using HasPendingEnq_append_deq_call_iff[OF his_eq ssn_eq_D1[of q]] by simp
    have "\<not> HasPendingEnq s' q (v_var s' q)"
      using no_pend_old pend_eq by simp
    with pend' show ?thesis
      by contradiction
  next
    case False
    have vv_eq: "v_var s' q = v_var s q"
      using v_eq_D1[of q] False by simp
    have pend_eq: "HasPendingEnq s' q (v_var s q) \<longleftrightarrow> HasPendingEnq s q (v_var s q)"
      using HasPendingEnq_append_deq_call_iff[OF his_eq ssn_eq_D1[of q]] by simp
    have pend_old': "HasPendingEnq s' q (v_var s q)"
      using pend' vv_eq by simp
    have pend_old: "HasPendingEnq s q (v_var s q)"
      using pend_old' pend_eq by blast
    have pc_old: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
      using hI27_Pending_PC_Sync_s pend_old
      unfolding hI27_Pending_PC_Sync_def
      by blast
    show ?thesis
      using pc_old pc_eq_D1[of q] False
      by auto
  qed
qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / hI28_Fresh_Enq_Immunity_s'. *)
(* Original locationoriginal file 2819-2893 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_fresh_enq_immune:
  fixes s s' :: SysState and p :: nat
  assumes hI28_Fresh_Enq_Immunity_s: "hI28_Fresh_Enq_Immunity s"
    and pc_eq_D1: "\<And>q. program_counter s' q = (if q = p then ''D1'' else program_counter s q)"
    and v_eq_D1: "\<And>q. v_var s' q = v_var s q"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
  shows "hI28_Fresh_Enq_Immunity s'"
proof (unfold hI28_Fresh_Enq_Immunity_def, intro allI impI notI)
  fix u :: nat and q :: nat and a :: nat and sn :: nat
  assume prem':
    "program_counter s' u \<in> {''E1'', ''E2''} \<and> v_var s' u = a \<and> a \<noteq> BOT"
  assume deq': "Model.DeqRetInHis s' q a sn"

  have u_ne_p: "u \<noteq> p"
    using prem' pc_eq_D1[of u]
    by auto

  have pc_old: "program_counter s u \<in> {''E1'', ''E2''}"
    using prem' u_ne_p pc_eq_D1[of u]
    by auto

  have v_old: "v_var s u = a"
    using prem' u_ne_p v_eq_D1[of u]
    by auto

  have deq_old: "Model.DeqRetInHis s q a sn"
  proof -
    obtain e where
      e_in: "e \<in> set (his_seq s')"
      and e_props:
        "act_pid e = q \<and> act_ssn e = sn \<and>
         act_name e = deq \<and> act_cr e = ret \<and> act_val e = a"
      using deq'
      unfolding Model.DeqRetInHis_def
      by blast
    have e_old: "e \<in> set (his_seq s)"
    proof -
      from e_in have "e \<in> set (his_seq s) \<or> e = mk_act deq BOT p (s_var s p) call"
        using his_eq
        by auto
      then show ?thesis
      proof
        assume "e \<in> set (his_seq s)"
        then show ?thesis .
      next
        assume "e = mk_act deq BOT p (s_var s p) call"
        with e_props show ?thesis
          by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      qed
    qed
    show ?thesis
      using e_old e_props
      unfolding Model.DeqRetInHis_def
      by blast
  qed

  have False
  proof -
    have old_no: "\<not> Model.DeqRetInHis s q a sn"
    proof
      assume deq_old: "Model.DeqRetInHis s q a sn"
      have "program_counter s u \<in> {''E1'', ''E2''}"
        using pc_old .
      moreover have "v_var s u = a"
        using v_old .
      moreover have "a \<noteq> BOT"
        using prem'
        by auto
      moreover note deq_old
      ultimately show False
        using hI28_Fresh_Enq_Immunity_s
        unfolding hI28_Fresh_Enq_Immunity_def
        by blast
    qed
    moreover have "Model.DeqRetInHis s q a sn"
      using deq_old .
    ultimately show False
      by contradiction
  qed
  then show False .
qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / lI3_HB_Ret_Lin_Sync_s'. *)
(* Original locationoriginal file 3028-3119 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_hb_ret_lin_sync:
  fixes s s' :: SysState and p :: nat
  assumes lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
    and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s"
    and pc_L0: "program_counter s p = ''L0''"
  shows "lI3_HB_Ret_Lin_Sync s'"
proof -
  have part1:
    "\<forall>k1 k2. k1 < length (lin_seq s') \<and> k2 < length (lin_seq s') \<and>
             HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2) \<longrightarrow> k1 < k2"
  proof (intro allI impI)
    fix k1 k2
    assume prem':
      "k1 < length (lin_seq s') \<and> k2 < length (lin_seq s') \<and>
       HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2)"
    then have k1_lt: "k1 < length (lin_seq s')" and k2_lt: "k2 < length (lin_seq s')"
      and hb': "HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2)"
      by auto
    have k1_old: "k1 < length (lin_seq s)" and k2_old: "k2 < length (lin_seq s)"
      using k1_lt k2_lt lin_seq_eq by simp_all
    have act2_safe:
      "op_name (lin_seq s ! k2) \<noteq> deq \<or>
       op_pid (lin_seq s ! k2) \<noteq> p \<or>
       op_ssn (lin_seq s ! k2) \<noteq> s_var s p"
    proof (cases "op_name (lin_seq s ! k2) = deq")
      case False
      then show ?thesis by simp
    next
      case True
      have deq2: "op_name (lin_seq s ! k2) = deq"
        using True .
      show ?thesis
      proof (cases "op_pid (lin_seq s ! k2) = p")
        case False
        then show ?thesis by simp
      next
        case True
        have pid2: "op_pid (lin_seq s ! k2) = p"
          using True .
        have in_oplin: "lin_seq s ! k2 \<in> OPLin s"
          using k2_old unfolding OPLin_def by simp
        have ssn_ne: "op_ssn (lin_seq s ! k2) \<noteq> s_var s p"
          using OPLin_deq_not_current_ssn_at_L0[OF lI1_Op_Sets_Equivalence_s hI2_SSN_Bounds_s pc_L0 in_oplin deq2 pid2]
          by simp
        then show ?thesis by simp
      qed
    qed
    have hb'_oldseq: "HB_Act s' (lin_seq s ! k1) (lin_seq s ! k2)"
      using hb' lin_seq_eq by simp
    have "HB_Act s' (lin_seq s ! k1) (lin_seq s ! k2) \<longleftrightarrow>
          HB_Act s (lin_seq s ! k1) (lin_seq s ! k2)"
      using HB_Act_append_deq_call_other_iff[OF his_eq act2_safe] .
    then have hb_old: "HB_Act s (lin_seq s ! k1) (lin_seq s ! k2)"
      using hb'_oldseq by blast
    from lI3_HB_Ret_Lin_Sync_s k1_old k2_old hb_old show "k1 < k2"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
  qed
  have part2:
    "\<forall>q a sn. Model.EnqRetInHis s' q a sn \<longrightarrow>
       (\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op enq a q sn)"
  proof (intro allI impI)
    fix q :: nat and a :: nat and sn :: nat
    assume enqret': "Model.EnqRetInHis s' q a sn"
    have enqret: "Model.EnqRetInHis s q a sn"
      using enqret' his_eq
      unfolding Model.EnqRetInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    from lI3_HB_Ret_Lin_Sync_s enqret obtain k where
      k_lt: "k < length (lin_seq s)"
      and act_eq: "lin_seq s ! k = mk_op enq a q sn"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
    show "\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op enq a q sn"
      using k_lt act_eq lin_seq_eq
      by auto
  qed
  have part3:
    "\<forall>q a sn. Model.DeqRetInHis s' q a sn \<longrightarrow>
       (\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op deq a q sn)"
  proof (intro allI impI)
    fix q :: nat and a :: nat and sn :: nat
    assume deqret': "Model.DeqRetInHis s' q a sn"
    have deqret: "Model.DeqRetInHis s q a sn"
      using deqret' his_eq
      unfolding Model.DeqRetInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    from lI3_HB_Ret_Lin_Sync_s deqret obtain k where
      k_lt: "k < length (lin_seq s)"
      and act_eq: "lin_seq s ! k = mk_op deq a q sn"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
    show "\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op deq a q sn"
      using k_lt act_eq lin_seq_eq
      by auto
  qed
  show ?thesis
    unfolding lI3_HB_Ret_Lin_Sync_def
    using part1 part2 part3 by blast
qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / hI15_Deq_Result_Exclusivity_s'. *)
(* Original locationoriginal file 3329-3513 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_deq_result_exclusive:
  fixes s s' :: SysState and p :: nat
  assumes hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and pc_eq_D1: "\<And>q. program_counter s' q = (if q = p then ''D1'' else program_counter s q)"
    and x_eq_D1: "\<And>q. x_var s' q = x_var s q"
    and qarr_eq_D1: "\<And>k. Q_arr s' k = Q_arr s k"
    and ssn_eq_D1: "\<And>q. s_var s' q = s_var s q"
    and pc_L0: "program_counter s p = ''L0''"
    and sI11_x_var_Scope_s: "sI11_x_var_Scope s"
  shows "hI15_Deq_Result_Exclusivity s'"
    proof -
      have hI15_Deq_Result_Exclusivity_part2_old:
        "\<forall>q a k. a \<in> Val \<longrightarrow> HasPendingDeq s q \<longrightarrow> \<not> (x_var s q = a \<and> Q_arr s k = a)"
        using hI15_Deq_Result_Exclusivity_s
        unfolding hI15_Deq_Result_Exclusivity_def
        by blast

      have hI15_Deq_Result_Exclusivity_part3_old:
        "\<forall>q a. a \<in> Val \<longrightarrow> (\<exists>sn. Model.DeqRetInHis s q a sn) \<longrightarrow> (\<forall>k. Q_arr s k \<noteq> a)"
        using hI15_Deq_Result_Exclusivity_s
        unfolding hI15_Deq_Result_Exclusivity_def
        by (elim conjE, blast)

      have part1:
        "\<forall>a p1 p2. a \<in> Val \<longrightarrow> p1 \<noteq> p2 \<longrightarrow>
          \<not> (((\<exists>sn1. Model.DeqRetInHis s' p1 a sn1) \<or> (program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a)) \<and>
             ((\<exists>sn2. Model.DeqRetInHis s' p2 a sn2) \<or> (program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a)))"
      proof (intro allI impI)
        fix a :: nat and p1 :: nat and p2 :: nat
        assume a_val: "a \<in> Val"
        assume p_ne: "p1 \<noteq> p2"
        show "\<not> (((\<exists>sn1. Model.DeqRetInHis s' p1 a sn1) \<or> (program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a)) \<and>
                 ((\<exists>sn2. Model.DeqRetInHis s' p2 a sn2) \<or> (program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a)))"
        proof
          assume both':
            "(((\<exists>sn1. Model.DeqRetInHis s' p1 a sn1) \<or> (program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a)) \<and>
              ((\<exists>sn2. Model.DeqRetInHis s' p2 a sn2) \<or> (program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a)))"

          have deqret_eq1:
            "(\<exists>sn1. Model.DeqRetInHis s' p1 a sn1) \<longleftrightarrow> (\<exists>sn1. Model.DeqRetInHis s p1 a sn1)"
          proof
            assume "\<exists>sn1. Model.DeqRetInHis s' p1 a sn1"
            then show "\<exists>sn1. Model.DeqRetInHis s p1 a sn1"
              using his_eq
              unfolding Model.DeqRetInHis_def
              by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
          next
            assume "\<exists>sn1. Model.DeqRetInHis s p1 a sn1"
            then show "\<exists>sn1. Model.DeqRetInHis s' p1 a sn1"
              using his_eq
              unfolding Model.DeqRetInHis_def
              by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
          qed

          have deqret_eq2:
            "(\<exists>sn2. Model.DeqRetInHis s' p2 a sn2) \<longleftrightarrow> (\<exists>sn2. Model.DeqRetInHis s p2 a sn2)"
          proof
            assume "\<exists>sn2. Model.DeqRetInHis s' p2 a sn2"
            then show "\<exists>sn2. Model.DeqRetInHis s p2 a sn2"
              using his_eq
              unfolding Model.DeqRetInHis_def
              by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
          next
            assume "\<exists>sn2. Model.DeqRetInHis s p2 a sn2"
            then show "\<exists>sn2. Model.DeqRetInHis s' p2 a sn2"
              using his_eq
              unfolding Model.DeqRetInHis_def
              by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
          qed

          have d4_eq1:
            "(program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a) \<longleftrightarrow>
             (program_counter s p1 = ''D4'' \<and> x_var s p1 = a)"
          proof
            assume h: "program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a"
            then have "program_counter s p1 = ''D4''"
              using pc_eq_D1[of p1] by (cases "p1 = p") auto
            moreover from h have "x_var s p1 = a"
              using x_eq_D1[of p1] by simp
            ultimately show "program_counter s p1 = ''D4'' \<and> x_var s p1 = a"
              by simp
          next
            assume h: "program_counter s p1 = ''D4'' \<and> x_var s p1 = a"
            then have "p1 \<noteq> p"
              using pc_L0 by auto
            with h show "program_counter s' p1 = ''D4'' \<and> x_var s' p1 = a"
              using pc_eq_D1[of p1] x_eq_D1[of p1] by auto
          qed

          have d4_eq2:
            "(program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a) \<longleftrightarrow>
             (program_counter s p2 = ''D4'' \<and> x_var s p2 = a)"
          proof
            assume h: "program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a"
            then have "program_counter s p2 = ''D4''"
              using pc_eq_D1[of p2] by (cases "p2 = p") auto
            moreover from h have "x_var s p2 = a"
              using x_eq_D1[of p2] by simp
            ultimately show "program_counter s p2 = ''D4'' \<and> x_var s p2 = a"
              by simp
          next
            assume h: "program_counter s p2 = ''D4'' \<and> x_var s p2 = a"
            then have "p2 \<noteq> p"
              using pc_L0 by auto
            with h show "program_counter s' p2 = ''D4'' \<and> x_var s' p2 = a"
              using pc_eq_D1[of p2] x_eq_D1[of p2] by auto
          qed

          have both_old:
            "(((\<exists>sn1. Model.DeqRetInHis s p1 a sn1) \<or> (program_counter s p1 = ''D4'' \<and> x_var s p1 = a)) \<and>
              ((\<exists>sn2. Model.DeqRetInHis s p2 a sn2) \<or> (program_counter s p2 = ''D4'' \<and> x_var s p2 = a)))"
            using both' deqret_eq1 deqret_eq2 d4_eq1 d4_eq2
            by blast

          have hI15_Deq_Result_Exclusivity_part1_raw:
            "\<forall>a p1 p2. a \<in> Val \<longrightarrow> p1 \<noteq> p2 \<longrightarrow>
              \<not> (((\<exists>sn1. Model.DeqRetInHis s p1 a sn1) \<or> (program_counter s p1 = ''D4'' \<and> x_var s p1 = a)) \<and>
                 ((\<exists>sn2. Model.DeqRetInHis s p2 a sn2) \<or> (program_counter s p2 = ''D4'' \<and> x_var s p2 = a)))"
            using hI15_Deq_Result_Exclusivity_s
            unfolding hI15_Deq_Result_Exclusivity_def
            by (elim conjE, blast)

          from hI15_Deq_Result_Exclusivity_part1_raw a_val p_ne both_old show False
            by blast
        qed
      qed

      have part2:
        "\<forall>q a k. a \<in> Val \<longrightarrow> HasPendingDeq s' q \<longrightarrow> \<not> (x_var s' q = a \<and> Q_arr s' k = a)"
      proof (intro allI impI)
        fix q :: nat and a :: nat and k :: nat
        assume a_val: "a \<in> Val"
        assume pend': "HasPendingDeq s' q"
        show "\<not> (x_var s' q = a \<and> Q_arr s' k = a)"
        proof (cases "q = p")
          case True
          (* Use the relevant invariant, lemma, or hypothesis. Related symbols: sI11_x_var_Scope, L0, x_var, BOT. *)
          have "program_counter s p = ''L0''" using pc_L0 by simp
          hence "program_counter s p \<noteq> ''D4''" by simp
          hence "x_var s p = BOT" using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def by blast
          hence x_bot: "x_var s' q = BOT"
            using True x_eq_D1[of q] by simp
          then show ?thesis
            using a_val
            by (auto simp: BOT_def Val_def)
        next
          case False
          have pend_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
            using HasPendingDeq_append_deq_call_other_iff[OF his_eq False ssn_eq_D1[of q]] .
          have pend: "HasPendingDeq s q"
            using pend' pend_eq by blast
          have old_no: "\<not> (x_var s q = a \<and> Q_arr s k = a)"
            using hI15_Deq_Result_Exclusivity_part2_old a_val pend by blast
          show ?thesis
            using old_no x_eq_D1[of q] qarr_eq_D1[of k] by auto
        qed
      qed

      have part3:
        "\<forall>q a. a \<in> Val \<longrightarrow> (\<exists>sn. Model.DeqRetInHis s' q a sn) \<longrightarrow> (\<forall>k. Q_arr s' k \<noteq> a)"
      proof (rule allI)
        fix q :: nat
        show "\<forall>a. a \<in> Val \<longrightarrow> (\<exists>sn. Model.DeqRetInHis s' q a sn) \<longrightarrow> (\<forall>k. Q_arr s' k \<noteq> a)"
        proof (rule allI)
          fix a :: nat
          show "a \<in> Val \<longrightarrow> (\<exists>sn. Model.DeqRetInHis s' q a sn) \<longrightarrow> (\<forall>k. Q_arr s' k \<noteq> a)"
          proof (rule impI)
            assume a_val: "a \<in> Val"
            show "(\<exists>sn. Model.DeqRetInHis s' q a sn) \<longrightarrow> (\<forall>k. Q_arr s' k \<noteq> a)"
            proof (rule impI)
              assume deq': "\<exists>sn. Model.DeqRetInHis s' q a sn"
              have deq_old: "\<exists>sn. Model.DeqRetInHis s q a sn"
                using deq' his_eq
                unfolding Model.DeqRetInHis_def
                by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
              have old_no: "\<forall>k. Q_arr s k \<noteq> a"
                using hI15_Deq_Result_Exclusivity_part3_old a_val deq_old by blast
              show "\<forall>k. Q_arr s' k \<noteq> a"
              proof (rule allI)
                fix k :: nat
                have "Q_arr s k \<noteq> a"
                  using old_no by blast
                then show "Q_arr s' k \<noteq> a"
                  using qarr_eq_D1[of k] by auto
              qed
            qed
          qed
        qed
      qed

      show ?thesis
        unfolding hI15_Deq_Result_Exclusivity_def
        using part1 part2 part3
        by blast
    qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / hI25_Enq_Call_Ret_Balanced_s'. *)
(* Original locationoriginal file 3733-3896 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_enq_call_ret_balanced:
  fixes s s' :: SysState and p :: nat
  assumes hI25_Enq_Call_Ret_Balanced_s: "hI25_Enq_Call_Ret_Balanced s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and pc_eq_D1: "\<And>q. program_counter s' q = (if q = p then ''D1'' else program_counter s q)"
    and pc_L0: "program_counter s p = ''L0''"
  shows "hI25_Enq_Call_Ret_Balanced s'"
    proof (unfold hI25_Enq_Call_Ret_Balanced_def, intro allI impI)
      fix q k
      let ?n = "length (his_seq s)"
      assume k_le': "k \<le> length (his_seq s')"
      have len': "length (his_seq s') = Suc ?n"
        using his_eq by simp
      show "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')) in
              let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
              let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
              n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
              (k = length (his_seq s') \<longrightarrow>
                (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1))"
      proof (cases "k \<le> ?n")
        case True
        have take_eq: "take k (his_seq s') = take k (his_seq s)"
          using his_eq True by simp
        have k_ne_len': "k \<noteq> length (his_seq s')"
          using True len' by linarith
        show ?thesis
        proof -
          let ?p_his_old = "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s))"
          let ?n_call_old = "length (filter (\<lambda>e. act_cr e = call) ?p_his_old)"
          let ?n_ret_old = "length (filter (\<lambda>e. act_cr e = ret) ?p_his_old)"
          have old_prop_raw:
            "?n_call_old \<ge> ?n_ret_old \<and> ?n_call_old - ?n_ret_old \<le> 1 \<and>
             (k = length (his_seq s) \<longrightarrow>
               (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> ?n_call_old - ?n_ret_old = 1))"
            using hI25_Enq_Call_Ret_Balanced_s True
            unfolding hI25_Enq_Call_Ret_Balanced_def Let_def
            by blast
          have old_bounds:
            "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s)) in
               let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
               let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
               n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1"
            using old_prop_raw
            unfolding Let_def
            by simp
          have bounds:
            "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')) in
               let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
               let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
               n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1"
            using old_bounds take_eq
            unfolding Let_def
            by simp
          then show ?thesis
            using k_ne_len'
            by simp
        qed
      next
        case False
        with k_le' len' have k_full: "k = Suc ?n"
          by linarith
        let ?p_his_old = "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (his_seq s)"
        let ?n_call_old = "length (filter (\<lambda>e. act_cr e = call) ?p_his_old)"
        let ?n_ret_old = "length (filter (\<lambda>e. act_cr e = ret) ?p_his_old)"
        have old_prop_q_raw:
          "?n_call_old \<ge> ?n_ret_old \<and> ?n_call_old - ?n_ret_old \<le> 1 \<and>
           (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> ?n_call_old - ?n_ret_old = 1)"
        proof -
          from hI25_Enq_Call_Ret_Balanced_s have
            "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take (length (his_seq s)) (his_seq s)) in
               let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
               let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
               n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
               (length (his_seq s) = length (his_seq s) \<longrightarrow>
                 (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1))"
            unfolding hI25_Enq_Call_Ret_Balanced_def by blast
          then show ?thesis
            unfolding Let_def
            by simp
        qed
        have old_prop_q:
          "let p_his = filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (his_seq s) in
             let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
             let n_ret = length (filter (\<lambda>e. act_cr e = ret) p_his) in
             n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
             (program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1)"
          using old_prop_q_raw
          unfolding Let_def
          by simp
        show ?thesis
        proof (cases "q = p")
          case False
          have qhis_eq:
            "filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')) =
             filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (his_seq s)"
            using his_eq k_full False
            by (simp add: mk_act_def act_pid_def act_name_def)
          have pc_eq:
            "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow>
             program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
            using False pc_eq_D1[of q]
            by simp
          show ?thesis
          proof -
            have raw':
              "?n_call_old \<ge> ?n_ret_old \<and> ?n_call_old - ?n_ret_old \<le> 1 \<and>
               (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> ?n_call_old - ?n_ret_old = 1)"
              using old_prop_q_raw pc_eq
              by simp
            have n_call_eq:
              "length (filter (\<lambda>e. act_cr e = call)
                 (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')))) = ?n_call_old"
              using qhis_eq
              by simp
            have n_ret_eq:
              "length (filter (\<lambda>e. act_cr e = ret)
                 (filter (\<lambda>e. act_pid e = q \<and> act_name e = enq) (take k (his_seq s')))) = ?n_ret_old"
              using qhis_eq
              by simp
            have k_eq_len': "k = length (his_seq s')"
              using k_full len'
              by simp
            then show ?thesis
              using raw' n_call_eq n_ret_eq
              unfolding Let_def
              by simp
          qed
        next
          case True
          have pc_not_e123: "program_counter s p \<notin> {''E1'', ''E2'', ''E3''}"
            using pc_L0 by simp
          have diff_ne_1: "?n_call_old - ?n_ret_old \<noteq> 1"
            using old_prop_q_raw pc_not_e123 True
            by simp
          have qhis_eq:
            "filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (take k (his_seq s')) =
             filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (his_seq s)"
            using his_eq k_full
            by (simp add: mk_act_def act_pid_def act_name_def)
          have n_call_eq:
            "length (filter (\<lambda>e. act_cr e = call)
               (filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (take k (his_seq s')))) = ?n_call_old"
            using qhis_eq True by simp
          have n_ret_eq:
            "length (filter (\<lambda>e. act_cr e = ret)
               (filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (take k (his_seq s')))) = ?n_ret_old"
            using qhis_eq True by simp
          have k_eq_len': "k = length (his_seq s')"
            using k_full len' by simp
          have pc_p_D1: "program_counter s' p = ''D1''"
            using pc_eq_D1[of p]
            by simp
          have bounds_old: "?n_ret_old \<le> ?n_call_old \<and> ?n_call_old - ?n_ret_old \<le> 1"
            using old_prop_q_raw
            by simp
          have bounds_new:
            "let n_call = length (filter (\<lambda>e. act_cr e = call)
                (filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (take k (his_seq s')))) in
             let n_ret = length (filter (\<lambda>e. act_cr e = ret)
                (filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (take k (his_seq s')))) in
             n_ret \<le> n_call \<and> n_call - n_ret \<le> 1"
            using bounds_old n_call_eq n_ret_eq
            unfolding Let_def
            by simp
          show ?thesis
            using bounds_new diff_ne_1 n_call_eq n_ret_eq k_eq_len' True pc_p_D1
            unfolding Let_def
            by simp
        qed
      qed
    qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / lI1_Op_Sets_Equivalence_s'. *)
(* Original locationoriginal file 4204-4391 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_op_sets_equiv:
  fixes s s' :: SysState and p :: nat
  assumes lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
    and SetA_eq_D1: "SetA s' = SetA s"
    and SetB_eq_D1: "SetB s' = SetB s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
  shows "lI1_Op_Sets_Equivalence s'"
      proof -
        have op_a_enq_eq: "OP_A_enq s' = OP_A_enq s"
        proof
          show "OP_A_enq s' \<subseteq> OP_A_enq s"
          proof
            fix x
            assume xin: "x \<in> OP_A_enq s'"
            then obtain q a sn where
              xdef: "x = mk_op enq a q sn"
              and aA': "a \<in> SetA s'"
              and enq': "Model.EnqCallInHis s' q a sn"
              unfolding OP_A_enq_def by blast
            have aA: "a \<in> SetA s"
              using aA' SetA_eq_D1 by simp
            have enq: "Model.EnqCallInHis s q a sn"
              using enq' his_eq
              unfolding Model.EnqCallInHis_def
              by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
            show "x \<in> OP_A_enq s"
              using xdef aA enq unfolding OP_A_enq_def by blast
          qed
        next
          show "OP_A_enq s \<subseteq> OP_A_enq s'"
          proof
            fix x
            assume xin: "x \<in> OP_A_enq s"
            then obtain q a sn where
              xdef: "x = mk_op enq a q sn"
              and aA: "a \<in> SetA s"
              and enq: "Model.EnqCallInHis s q a sn"
              unfolding OP_A_enq_def by blast
            have aA': "a \<in> SetA s'"
              using aA SetA_eq_D1 by simp
            have enq': "Model.EnqCallInHis s' q a sn"
              using enq his_eq
              unfolding Model.EnqCallInHis_def
              by auto
            show "x \<in> OP_A_enq s'"
              using xdef aA' enq' unfolding OP_A_enq_def by blast
          qed
        qed
        have op_a_deq_eq: "OP_A_deq s' = OP_A_deq s"
        proof
          show "OP_A_deq s' \<subseteq> OP_A_deq s"
          proof
            fix x
            assume xin: "x \<in> OP_A_deq s'"
            have xlin': "x \<in> OPLin s'"
              using xin unfolding OP_A_deq_def by blast
            have xdeq: "op_name x = deq"
              using xin unfolding OP_A_deq_def by blast
            have xA': "op_val x \<in> SetA s'"
              using xin unfolding OP_A_deq_def by blast
            have xdeq': "Model.DeqCallInHis s' (op_pid x) (op_ssn x)"
              using xin unfolding OP_A_deq_def by blast
            obtain op a q sn where
              xsplit: "x = mk_op op a q sn"
              by (cases x) (auto simp: mk_op_def)
            have op_deq: "op = deq"
              using xdeq xsplit by (simp add: mk_op_def op_name_def)
            have xdef: "x = mk_op deq a q sn"
              using xsplit op_deq by simp
            have aA': "a \<in> SetA s'"
              using xA' xdef by (simp add: mk_op_def op_val_def)
            have lin': "mk_op deq a q sn \<in> OPLin s'"
              using xlin' xdef by simp
            have deq': "Model.DeqCallInHis s' q sn"
              using xdeq' xdef by (simp add: mk_op_def op_pid_def op_ssn_def)
            have aA: "a \<in> SetA s"
              using aA' SetA_eq_D1 by simp
            have lin: "mk_op deq a q sn \<in> OPLin s"
              using lin' lin_seq_eq unfolding OPLin_def by simp
            show "x \<in> OP_A_deq s"
            proof (cases "q = p")
              case False
              have deq: "Model.DeqCallInHis s q sn"
                using deq' his_eq False
                unfolding Model.DeqCallInHis_def
                by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
              have in_op: "mk_op deq a q sn \<in> OP_A_deq s"
                using aA lin deq
                unfolding OP_A_deq_def
                by (auto simp: mk_op_def op_name_def op_pid_def op_val_def op_ssn_def)
              show ?thesis
                using in_op xdef by simp
            next
              case True
              have not_a_enq: "mk_op deq a q sn \<notin> OP_A_enq s"
                unfolding OP_A_enq_def
                by (auto simp: mk_op_def)
              have not_b_enq: "mk_op deq a q sn \<notin> OP_B_enq s"
                unfolding OP_B_enq_def
                by (auto simp: mk_op_def)
              have "mk_op deq a q sn \<in> OP_A_deq s"
                using lI1_Op_Sets_Equivalence_s lin not_a_enq not_b_enq
                unfolding lI1_Op_Sets_Equivalence_def
                by blast
              then show ?thesis
                using xdef by simp
            qed
          qed
        next
          show "OP_A_deq s \<subseteq> OP_A_deq s'"
          proof
            fix x
            assume xin: "x \<in> OP_A_deq s"
            have xlin: "x \<in> OPLin s"
              using xin unfolding OP_A_deq_def by blast
            have xdeq: "op_name x = deq"
              using xin unfolding OP_A_deq_def by blast
            have xA: "op_val x \<in> SetA s"
              using xin unfolding OP_A_deq_def by blast
            have xdeq0: "Model.DeqCallInHis s (op_pid x) (op_ssn x)"
              using xin unfolding OP_A_deq_def by blast
            obtain op a q sn where
              xsplit: "x = mk_op op a q sn"
              by (cases x) (auto simp: mk_op_def)
            have op_deq: "op = deq"
              using xdeq xsplit by (simp add: mk_op_def op_name_def)
            have xdef: "x = mk_op deq a q sn"
              using xsplit op_deq by simp
            have aA: "a \<in> SetA s"
              using xA xdef by (simp add: mk_op_def op_val_def)
            have lin: "mk_op deq a q sn \<in> OPLin s"
              using xlin xdef by simp
            have deq: "Model.DeqCallInHis s q sn"
              using xdeq0 xdef by (simp add: mk_op_def op_pid_def op_ssn_def)
            have aA': "a \<in> SetA s'"
              using aA SetA_eq_D1 by simp
            have lin': "mk_op deq a q sn \<in> OPLin s'"
              using lin lin_seq_eq unfolding OPLin_def by simp
            have deq': "Model.DeqCallInHis s' q sn"
              using deq his_eq
              unfolding Model.DeqCallInHis_def
              by auto
            have in_op: "mk_op deq a q sn \<in> OP_A_deq s'"
              using aA' lin' deq'
              unfolding OP_A_deq_def
              by (auto simp: mk_op_def op_name_def op_pid_def op_val_def op_ssn_def)
            show "x \<in> OP_A_deq s'"
              using in_op xdef by simp
          qed
        qed
        have op_b_enq_eq: "OP_B_enq s' = OP_B_enq s"
        proof
          show "OP_B_enq s' \<subseteq> OP_B_enq s"
          proof
            fix x
            assume xin: "x \<in> OP_B_enq s'"
            then obtain q a sn where
              xdef: "x = mk_op enq a q sn"
              and aB': "a \<in> SetB s'"
              and enq': "Model.EnqCallInHis s' q a sn"
              unfolding OP_B_enq_def by blast
            have aB: "a \<in> SetB s"
              using aB' SetB_eq_D1 by simp
            have enq: "Model.EnqCallInHis s q a sn"
              using enq' his_eq
              unfolding Model.EnqCallInHis_def
              by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
            show "x \<in> OP_B_enq s"
              using xdef aB enq unfolding OP_B_enq_def by blast
          qed
        next
          show "OP_B_enq s \<subseteq> OP_B_enq s'"
          proof
            fix x
            assume xin: "x \<in> OP_B_enq s"
            then obtain q a sn where
              xdef: "x = mk_op enq a q sn"
              and aB: "a \<in> SetB s"
              and enq: "Model.EnqCallInHis s q a sn"
              unfolding OP_B_enq_def by blast
            have aB': "a \<in> SetB s'"
              using aB SetB_eq_D1 by simp
            have enq': "Model.EnqCallInHis s' q a sn"
              using enq his_eq
              unfolding Model.EnqCallInHis_def
              by auto
            show "x \<in> OP_B_enq s'"
              using xdef aB' enq' unfolding OP_B_enq_def by blast
          qed
        qed

      show ?thesis
        using lI1_Op_Sets_Equivalence_s lin_seq_eq op_a_enq_eq op_a_deq_eq op_b_enq_eq
        unfolding lI1_Op_Sets_Equivalence_def OPLin_def by simp
    qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / lI9_D1_D2_Deq_Returned_s'. *)
(* Original locationoriginal file 4605-4792 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_d12_deq_returned:
  fixes s s' :: SysState and p :: nat
  assumes lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s"
    and pc_eq_D1: "\<And>q. program_counter s' q = (if q = p then ''D1'' else program_counter s q)"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s"
    and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s"
    and hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s"
    and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s"
    and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s"
    and pc_L0: "program_counter s p = ''L0''"
  shows "lI9_D1_D2_Deq_Returned s'"
    proof (unfold lI9_D1_D2_Deq_Returned_def, intro allI impI)
      fix q k
      assume pc_D12': "program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2''"
        and k_lt': "k < length (lin_seq s')"
        and act_match': "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
      have k_lt: "k < length (lin_seq s)"
        using k_lt' lin_seq_eq by simp
      have act_match: "op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q"
        using act_match' lin_seq_eq by simp
      show "Model.DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
      proof (cases "q = p")
        case False
        have pc_D12: "program_counter s q = ''D1'' \<or> program_counter s q = ''D2''"
          using False pc_D12' pc_eq_D1[of q]
          by simp
        have deq_old:
          "Model.DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
          using lI9_D1_D2_Deq_Returned_s pc_D12 k_lt act_match
          unfolding lI9_D1_D2_Deq_Returned_def
          by blast
        show ?thesis
          using deq_old his_eq lin_seq_eq
          unfolding Model.DeqRetInHis_def
          by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      next
        case True
        let ?a = "op_val (lin_seq s ! k)"
        let ?sn = "op_ssn (lin_seq s ! k)"
        have act_in: "lin_seq s ! k \<in> OPLin s"
          using k_lt unfolding OPLin_def by simp
        have not_a_enq: "lin_seq s ! k \<notin> OP_A_enq s"
          using act_match
          unfolding OP_A_enq_def
          by (auto simp: mk_op_def op_name_def)
        have not_b_enq: "lin_seq s ! k \<notin> OP_B_enq s"
          using act_match
          unfolding OP_B_enq_def
          by (auto simp: mk_op_def op_name_def)
        have in_op_a_deq: "lin_seq s ! k \<in> OP_A_deq s"
          using lI1_Op_Sets_Equivalence_s act_in not_a_enq not_b_enq
          unfolding lI1_Op_Sets_Equivalence_def
          by blast
        have aA: "?a \<in> SetA s"
          using in_op_a_deq
          unfolding OP_A_deq_def
          by simp
        have deq_call: "Model.DeqCallInHis s p ?sn"
          using in_op_a_deq act_match True
          unfolding OP_A_deq_def
          by simp
        have a_val: "?a \<in> Val"
          using aA unfolding SetA_def by simp
        have a_ne_bot: "?a \<noteq> BOT"
          using a_val unfolding Val_def BOT_def by auto
        have inqback: "InQBack s ?a"
          using aA unfolding SetA_def TypeA_def by auto
        have not_qhas: "\<not> QHas s ?a"
          using aA unfolding SetA_def TypeA_def by auto
        from inqback obtain m where qback_m: "Qback_arr s m = ?a"
          using inqback unfolding InQBack_def by auto
        have qarr_bot_or_eq: "Q_arr s m = Qback_arr s m \<or> Q_arr s m = BOT"
          using sI8_Q_Qback_Sync_s unfolding sI8_Q_Qback_Sync_def by blast
        have qarr_ne: "Q_arr s m \<noteq> ?a"
          using not_qhas qback_m unfolding QHas_def by blast
        have qarr_m: "Q_arr s m = BOT"
        proof -
          from qarr_bot_or_eq show ?thesis
          proof
            assume eq1: "Q_arr s m = Qback_arr s m"
            have "Q_arr s m = ?a"
              using eq1 qback_m by simp
            with qarr_ne show ?thesis
              by contradiction
          next
            assume eq2: "Q_arr s m = BOT"
            show ?thesis
              using eq2 .
          qed
        qed
        have queue_wit: "\<exists>m. Q_arr s m = BOT \<and> Qback_arr s m = ?a"
          using qarr_m qback_m by blast
        from hI13_Qback_Deq_Sync_s a_ne_bot queue_wit obtain q0 where old_wit:
          "(program_counter s q0 = ''D4'' \<and> x_var s q0 = ?a) \<or> (\<exists>sn0. Model.DeqRetInHis s q0 ?a sn0)"
          unfolding hI13_Qback_Deq_Sync_def by blast
        have k_in_deqidx: "k \<in> DeqIdxs s ?a"
          using k_lt act_match
          unfolding DeqIdxs_def
          by simp
        have deqidx_card: "card (DeqIdxs s ?a) = 1"
          using lI2_Op_Cardinality_s aA
          unfolding lI2_Op_Cardinality_def
          by blast
        have deq_old: "Model.DeqRetInHis s p ?a ?sn"
        proof -
          from old_wit show ?thesis
          proof
            assume old_d4: "program_counter s q0 = ''D4'' \<and> x_var s q0 = ?a"
            then have q0_D4: "program_counter s q0 = ''D4''"
              and xq0: "x_var s q0 = ?a"
              by auto
            have q0_ne_p: "q0 \<noteq> p"
              using q0_D4 pc_L0 by auto
            have old_in0: "mk_op deq (x_var s q0) q0 (s_var s q0) \<in> set (lin_seq s)"
              using lI6_D4_Deq_Linearized_s q0_D4
              unfolding lI6_D4_Deq_Linearized_def
              by blast
            have old_in: "mk_op deq ?a q0 (s_var s q0) \<in> set (lin_seq s)"
              using old_in0 xq0
              by simp
            then obtain k0 where
              k0_lt: "k0 < length (lin_seq s)"
              and act_eq0: "lin_seq s ! k0 = mk_op deq ?a q0 (s_var s q0)"
              by (metis in_set_conv_nth)
            have k0_in_deqidx: "k0 \<in> DeqIdxs s ?a"
              using k0_lt act_eq0
              unfolding DeqIdxs_def
              by (simp add: mk_op_def op_name_def op_val_def)
            obtain kk where kk_def: "DeqIdxs s ?a = {kk}"
              using deqidx_card by (metis card_1_singletonE)
            have kk_eq_k: "kk = k"
              using k_in_deqidx kk_def by simp
            have k0_eq_k: "k0 = k"
              using k0_in_deqidx kk_def kk_eq_k by simp
            have actk_eq0: "lin_seq s ! k = mk_op deq ?a q0 (s_var s q0)"
              using act_eq0 k0_eq_k by simp
            have pidk: "op_pid (lin_seq s ! k) = p"
              using act_match True by simp
            have "op_pid (mk_op deq ?a q0 (s_var s q0)) = p"
              using actk_eq0 pidk by simp
            then have "q0 = p"
              by (simp add: mk_op_def op_pid_def)
            with q0_ne_p show ?thesis
              by contradiction
          next
            assume old_ret: "\<exists>sn0. Model.DeqRetInHis s q0 ?a sn0"
            then obtain sn0 where ret0: "Model.DeqRetInHis s q0 ?a sn0"
              by blast
            from lI3_HB_Ret_Lin_Sync_s ret0 obtain k0 where
              k0_lt: "k0 < length (lin_seq s)"
              and act_eq0: "lin_seq s ! k0 = mk_op deq ?a q0 sn0"
              unfolding lI3_HB_Ret_Lin_Sync_def
              by blast
            have k0_in_deqidx: "k0 \<in> DeqIdxs s ?a"
              using k0_lt act_eq0
              unfolding DeqIdxs_def
              by (simp add: mk_op_def op_name_def op_val_def)
            obtain kk where kk_def: "DeqIdxs s ?a = {kk}"
              using deqidx_card by (metis card_1_singletonE)
            have kk_eq_k: "kk = k"
              using k_in_deqidx kk_def by simp
            have k0_eq_k: "k0 = k"
              using k0_in_deqidx kk_def kk_eq_k by simp
            have q0_eq_p: "q0 = p"
            proof -
              have actk_eq0: "lin_seq s ! k = mk_op deq ?a q0 sn0"
                using act_eq0 k0_eq_k by simp
              have pidk: "op_pid (lin_seq s ! k) = p"
                using act_match True by simp
              have "op_pid (mk_op deq ?a q0 sn0) = p"
                using actk_eq0 pidk by simp
              then show ?thesis
                by (simp add: mk_op_def op_pid_def)
            qed
            have sn0_eq: "sn0 = ?sn"
            proof -
              have actk_eq0: "lin_seq s ! k = mk_op deq ?a q0 sn0"
                using act_eq0 k0_eq_k by simp
              have ssnk: "op_ssn (lin_seq s ! k) = ?sn"
                by simp
              have "op_ssn (mk_op deq ?a q0 sn0) = ?sn"
                using actk_eq0 ssnk by simp
              then show ?thesis
                by (simp add: mk_op_def op_ssn_def)
            qed
            show ?thesis
              using ret0 q0_eq_p sn0_eq
              by simp
          qed
        qed
        have deq_old_q:
          "Model.DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
          using deq_old True by simp
        show ?thesis
          using deq_old_q his_eq lin_seq_eq
          unfolding Model.DeqRetInHis_def
          by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      qed
    qed

(* SourceL0Proof.thy / L0_preserves_invariant / E1 / hI22_Deq_Local_Pattern_s'. *)
(* Original locationoriginal file 925-990 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_deq_local_pattern:
  fixes s s' :: SysState and p :: nat
  assumes hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and qarr_eq_E1: "\<And>k. Q_arr s' k = Q_arr s k"
    and qback_eq_E1: "\<And>k. Qback_arr s' k = Qback_arr s k"
    and x_eq_E1: "\<And>q. x_var s' q = x_var s q"
  shows "hI22_Deq_Local_Pattern s'"
proof (unfold hI22_Deq_Local_Pattern_def, intro allI impI)
  fix q :: nat and a :: nat and sn :: nat
  assume prem':
    "(\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a \<and> (\<forall>r. x_var s' r \<noteq> a)) \<and>
     Model.DeqRetInHis s' q a sn"
  then obtain k where
    qbot': "Q_arr s' k = BOT"
    and qback': "Qback_arr s' k = a"
    and xnone': "\<forall>r. x_var s' r \<noteq> a"
    and deq': "Model.DeqRetInHis s' q a sn"
    by blast
  have queue_old: "\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a \<and> (\<forall>r. x_var s r \<noteq> a)"
    using qbot' qback' xnone' qarr_eq_E1[of k] qback_eq_E1[of k] x_eq_E1
    by auto
  have deq_old: "Model.DeqRetInHis s q a sn"
    using deq' his_eq
    unfolding Model.DeqRetInHis_def
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  from hI22_Deq_Local_Pattern_s queue_old deq_old have old_wit:
    "let p_his = filter (\<lambda>e. act_pid e = q) (his_seq s) in
       \<exists>i<length p_his. p_his ! i = mk_act deq a q sn ret \<and>
         (i > 0 \<and> p_his ! (i - 1) = mk_act deq BOT q sn call)"
    unfolding hI22_Deq_Local_Pattern_def by blast
    have old_wit':
      "\<exists>i<length (filter (\<lambda>e. act_pid e = q) (his_seq s)).
         (filter (\<lambda>e. act_pid e = q) (his_seq s)) ! i = mk_act deq a q sn ret \<and>
         (i > 0 \<and> (filter (\<lambda>e. act_pid e = q) (his_seq s)) ! (i - 1) = mk_act deq BOT q sn call)"
      using old_wit by (simp add: Let_def)
    have filt_form:
      "filter (\<lambda>e. act_pid e = q) (his_seq s') =
       filter (\<lambda>e. act_pid e = q) (his_seq s) @
       (if q = p then [mk_act enq (V_var s) p (s_var s p) call] else [])"
      using his_eq by (simp add: mk_act_def act_pid_def)
    show "let p_his = filter (\<lambda>e. act_pid e = q) (his_seq s') in
            \<exists>i<length p_his. p_his ! i = mk_act deq a q sn ret \<and>
              (i > 0 \<and> p_his ! (i - 1) = mk_act deq BOT q sn call)"
    proof -
      from old_wit' obtain i where
        i_lt: "i < length (filter (\<lambda>e. act_pid e = q) (his_seq s))"
        and i_props:
          "(filter (\<lambda>e. act_pid e = q) (his_seq s)) ! i = mk_act deq a q sn ret \<and>
           (i > 0 \<and> (filter (\<lambda>e. act_pid e = q) (his_seq s)) ! (i - 1) = mk_act deq BOT q sn call)"
        by blast
      have i_lt_new:
        "i < length (filter (\<lambda>e. act_pid e = q) (his_seq s'))"
        using i_lt filt_form by simp
      have nth_i_new:
        "(filter (\<lambda>e. act_pid e = q) (his_seq s')) ! i = mk_act deq a q sn ret"
        using i_lt i_props filt_form by (auto simp: nth_append)
      have nth_prev_new:
        "i > 0 \<and> (filter (\<lambda>e. act_pid e = q) (his_seq s')) ! (i - 1) = mk_act deq BOT q sn call"
        using i_lt i_props filt_form by (auto simp: nth_append)
      show ?thesis
      proof -
        let ?p_his = "filter (\<lambda>e. act_pid e = q) (his_seq s')"
        have "?p_his ! i = mk_act deq a q sn ret \<and>
              (i > 0 \<and> ?p_his ! (i - 1) = mk_act deq BOT q sn call)"
          using nth_i_new nth_prev_new by simp
        then have "\<exists>i<length ?p_his. ?p_his ! i = mk_act deq a q sn ret \<and>
                     (i > 0 \<and> ?p_his ! (i - 1) = mk_act deq BOT q sn call)"
          using i_lt_new by blast
        then show ?thesis
          by simp
      qed
    qed
  qed

(* SourceL0Proof.thy / L0_preserves_invariant / E1 / lI3_HB_Ret_Lin_Sync_s'. *)
(* Original locationoriginal file 1176-1244 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_hb_ret_lin_sync:
  fixes s s' :: SysState and p :: nat
  assumes lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s"
    and lin_seq_eq: "lin_seq s' = lin_seq s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
    and fresh_not_OPLin: "mk_op enq (V_var s) p (s_var s p) \<notin> OPLin s"
  shows "lI3_HB_Ret_Lin_Sync s'"
proof -
  have part1:
    "\<forall>k1 k2. k1 < length (lin_seq s') \<and> k2 < length (lin_seq s') \<and>
             HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2) \<longrightarrow> k1 < k2"
  proof (intro allI impI)
    fix k1 k2
    assume prem':
      "k1 < length (lin_seq s') \<and> k2 < length (lin_seq s') \<and>
       HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2)"
    then have k1_lt: "k1 < length (lin_seq s')" and k2_lt: "k2 < length (lin_seq s')"
      and hb': "HB_Act s' (lin_seq s' ! k1) (lin_seq s' ! k2)"
      by auto
    have k1_old: "k1 < length (lin_seq s)" and k2_old: "k2 < length (lin_seq s)"
      using k1_lt k2_lt lin_seq_eq by simp_all
    have act2_in_old: "lin_seq s ! k2 \<in> OPLin s"
      unfolding OPLin_def using k2_old by (metis nth_mem)
    have act2_ne: "lin_seq s ! k2 \<noteq> mk_op enq (V_var s) p (s_var s p)"
    proof
      assume eq: "lin_seq s ! k2 = mk_op enq (V_var s) p (s_var s p)"
      then have "mk_op enq (V_var s) p (s_var s p) \<in> OPLin s"
        using act2_in_old by simp
      with fresh_not_OPLin show False
        by contradiction
    qed
    have hb_old: "HB_Act s (lin_seq s ! k1) (lin_seq s ! k2)"
      using HB_Act_append_enq_call_other_iff[OF his_eq act2_ne] hb' lin_seq_eq by simp
    from lI3_HB_Ret_Lin_Sync_s k1_old k2_old hb_old show "k1 < k2"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
  qed
  have part2:
    "\<forall>q a sn. Model.EnqRetInHis s' q a sn \<longrightarrow>
       (\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op enq a q sn)"
  proof (intro allI impI)
    fix q :: nat and a :: nat and sn :: nat
    assume enqret': "Model.EnqRetInHis s' q a sn"
    have enqret: "Model.EnqRetInHis s q a sn"
      using enqret' his_eq
      unfolding Model.EnqRetInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    from lI3_HB_Ret_Lin_Sync_s enqret obtain k where
      k_lt: "k < length (lin_seq s)"
      and act_eq: "lin_seq s ! k = mk_op enq a q sn"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
    show "\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op enq a q sn"
      using k_lt act_eq lin_seq_eq
      by auto
  qed
  have part3:
    "\<forall>q a sn. Model.DeqRetInHis s' q a sn \<longrightarrow>
       (\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op deq a q sn)"
  proof (intro allI impI)
    fix q :: nat and a :: nat and sn :: nat
    assume deqret': "Model.DeqRetInHis s' q a sn"
    have deqret: "Model.DeqRetInHis s q a sn"
      using deqret' his_eq
      unfolding Model.DeqRetInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    from lI3_HB_Ret_Lin_Sync_s deqret obtain k where
      k_lt: "k < length (lin_seq s)"
      and act_eq: "lin_seq s ! k = mk_op deq a q sn"
      unfolding lI3_HB_Ret_Lin_Sync_def by blast
    show "\<exists>k < length (lin_seq s'). lin_seq s' ! k = mk_op deq a q sn"
      using k_lt act_eq lin_seq_eq
      by auto
  qed
  show ?thesis
    unfolding lI3_HB_Ret_Lin_Sync_def
    using part1 part2 part3 by blast
qed

lemma L0_D1_qback_deq_sync:
  fixes s s' :: SysState and p :: nat
  assumes hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s"
    and qarr_eq_D1: "\<And>k. Q_arr s' k = Q_arr s k"
    and qback_eq_D1: "\<And>k. Qback_arr s' k = Qback_arr s k"
    and pc_L0: "program_counter s p = ''L0''"
    and pc_eq_D1: "\<And>q. program_counter s' q = (if q = p then ''D1'' else program_counter s q)"
    and x_eq_D1: "\<And>q. x_var s' q = x_var s q"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
  shows "hI13_Qback_Deq_Sync s'"
proof -
  (* Reasoning about appending one history or sequence element. *)
  have deq_ret_eq: "\<And>pa a sn. Model.DeqRetInHis s' pa a sn \<longleftrightarrow> Model.DeqRetInHis s pa a sn"
    using DeqRetInHis_append_call_iff[of s' s "mk_act deq BOT p (s_var s p) call"]
    using his_eq by (simp add: mk_act_def act_cr_def)

  (* State-transition reasoning. Related symbols: L0, D1, D4. *)
  have d4_eq: "\<And>pa. (program_counter s' pa = ''D4'') \<longleftrightarrow> (program_counter s pa = ''D4'')"
    using pc_eq_D1 pc_L0 by auto

  (* Use the relevant invariant, lemma, or hypothesis. *)
  show ?thesis
    using hI13_Qback_Deq_Sync_s
    unfolding hI13_Qback_Deq_Sync_def
    using qarr_eq_D1 qback_eq_D1 x_eq_D1 d4_eq deq_ret_eq
    by auto
qed

lemma L0_D1_deq_local_pattern:
  fixes s s' :: SysState and p :: nat
  assumes hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and qarr_eq_D1: "\<And>k. Q_arr s' k = Q_arr s k"
    and qback_eq_D1: "\<And>k. Qback_arr s' k = Qback_arr s k"
    and x_eq_D1: "\<And>q. x_var s' q = x_var s q"
  shows "hI22_Deq_Local_Pattern s'"
proof (unfold hI22_Deq_Local_Pattern_def, intro allI impI)
  (* Proof note. *)
  fix q a sn :: nat
  assume prem':
    "(\<exists>k. Q_arr s' k = BOT \<and> Qback_arr s' k = a \<and> (\<forall>r. x_var s' r \<noteq> a)) \<and>
     Model.DeqRetInHis s' q a sn"

  (* Step 1 of the proof. *)
  have prem_s: "(\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a \<and> (\<forall>r. x_var s r \<noteq> a)) \<and>
                Model.DeqRetInHis s q a sn"
    using prem' qarr_eq_D1 qback_eq_D1 x_eq_D1
    using DeqRetInHis_append_call_iff[of s' s "mk_act deq BOT p (s_var s p) call"] his_eq
    by (auto simp: mk_act_def act_cr_def)

  (* Step 2: use the available invariant or hypothesis. *)
  let ?old_his = "filter (\<lambda>e. act_pid e = q) (his_seq s)"
  let ?new_his = "filter (\<lambda>e. act_pid e = q) (his_seq s')"

  have old_wit: "\<exists>i<length ?old_his. ?old_his ! i = mk_act deq a q sn ret \<and>
                                     (i > 0 \<and> ?old_his ! (i - 1) = mk_act deq BOT q sn call)"
    using hI22_Deq_Local_Pattern_s prem_s
    unfolding hI22_Deq_Local_Pattern_def Let_def by blast

  then obtain i where i_len: "i < length ?old_his"
    and i_ret: "?old_his ! i = mk_act deq a q sn ret"
    and i_call: "i > 0 \<and> ?old_his ! (i - 1) = mk_act deq BOT q sn call"
    by blast

  (* Step 3: prove the required intermediate property. *)
  have his_filt: "?new_his = ?old_his @ (if q = p then [mk_act deq BOT p (s_var s p) call] else [])"
    using his_eq by (simp add: act_pid_def mk_act_def)

  have new_len: "i < length ?new_his"
    using i_len his_filt by simp

  have new_ret: "?new_his ! i = mk_act deq a q sn ret"
    using i_len i_ret his_filt by (simp add: nth_append)

  have new_call: "i > 0 \<and> ?new_his ! (i - 1) = mk_act deq BOT q sn call"
    using i_len i_call his_filt
    by (simp add: nth_append_cases(1))

  (* Step 4 of the proof. *)
  show "let p_his = ?new_his in
          \<exists>i<length p_his. p_his ! i = mk_act deq a q sn ret \<and>
            (i > 0 \<and> p_his ! (i - 1) = mk_act deq BOT q sn call)"
    unfolding Let_def
    using new_len new_ret new_call by blast
qed

(* SourceL0Proof.thy / L0_preserves_invariant / D1 / hI29_E2_Scanner_Immunity_s'. *)
(* Original locationoriginal file 2514-2582 approximate line range. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_e2_scanner_immune:
  fixes s s' :: SysState and p :: nat
  assumes hI29_E2_Scanner_Immunity_s: "hI29_E2_Scanner_Immunity s"
    and his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
    and ssn_eq_D1: "\<And>q. s_var s' q = s_var s q"
    and pc_eq_D1: "\<And>q. program_counter s' q = (if q = p then ''D1'' else program_counter s q)"
    and InQBack_eq_D1: "\<And>a. InQBack s' a \<longleftrightarrow> InQBack s a"
    and TypeB_eq_D1: "\<And>a. TypeB s' a \<longleftrightarrow> TypeB s a"
    and Idx_eq_D1: "\<And>a. Idx s' a = Idx s a"
    and j_eq_D1: "\<And>q. j_var s' q = j_var s q"
    and i_eq_D1: "\<And>q. i_var s' q = i_var s q"
    and l_eq_D1: "\<And>q. l_var s' q = l_var s q"
    and v_eq_D1: "\<And>q. v_var s' q = v_var s q"
    and pc_L0: "program_counter s p = ''L0''"
    and pc_D3_eq_D1: "\<And>q. program_counter s' q = ''D3'' \<longleftrightarrow> program_counter s q = ''D3''"
  shows "hI29_E2_Scanner_Immunity s'"
proof (unfold hI29_E2_Scanner_Immunity_def, intro allI impI notI)
  fix u a q
  assume prem':
    "program_counter s' u = ''E2'' \<and>
     InQBack s' a \<and> TypeB s' a \<and>
     HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
     Idx s' a < j_var s' q \<and> j_var s' q \<le> i_var s' u \<and> i_var s' u < l_var s' q"
  assume hb': "HB_EnqRetCall s' a (v_var s' u)"
  have u_ne_p: "u \<noteq> p"
    using prem' pc_eq_D1[of u]
    by auto
  have pc_u_old: "program_counter s u = ''E2''"
    using prem' u_ne_p pc_eq_D1[of u]
    by auto
  have inq_old: "InQBack s a"
    using prem' InQBack_eq_D1[of a]
    by auto
  have type_old: "TypeB s a"
    using prem' TypeB_eq_D1[of a]
    by auto
  have pend_old: "HasPendingDeq s q"
  proof (cases "q = p")
    case True
    have "program_counter s' q = ''D1''"
      using True pc_eq_D1[of q]
      by simp
    moreover have "program_counter s' q = ''D3''"
      using prem'
      by auto
    ultimately show ?thesis
      by simp
  next
    case False
    have pend_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
      using HasPendingDeq_append_deq_call_other_iff[OF his_eq False ssn_eq_D1[of q]] .
    from prem' pend_eq show ?thesis
      by blast
  qed
  have pc_q_old: "program_counter s q = ''D3''"
  proof (cases "q = p")
    case True
    then have "program_counter s q = ''L0''"
      using pc_L0 by simp
    with prem' True show ?thesis
      using pc_eq_D1[of q] by auto
  next
    case False
    with prem' show ?thesis
      using pc_D3_eq_D1[of q] by auto
  qed
  have bounds_old:
    "Idx s a < j_var s q \<and> j_var s q \<le> i_var s u \<and> i_var s u < l_var s q"
    using prem' u_ne_p Idx_eq_D1[of a] j_eq_D1[of q] i_eq_D1[of u] l_eq_D1[of q]
    by auto
  have old_prem:
    "program_counter s u = ''E2'' \<and>
     InQBack s a \<and> TypeB s a \<and>
     HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and>
     Idx s a < j_var s q \<and> j_var s q \<le> i_var s u \<and> i_var s u < l_var s q"
    using pc_u_old inq_old type_old pend_old pc_q_old bounds_old
    by blast
  have hb_old: "HB_EnqRetCall s a (v_var s u)"
    using hb' u_ne_p
          HB_EnqRetCall_append_deq_call_iff[OF his_eq, of a "v_var s u"]
    by (simp add: v_eq_D1[of u])
  from hI29_E2_Scanner_Immunity_s old_prem hb_old show False
    unfolding hI29_E2_Scanner_Immunity_def
    by blast
qed

(* ================================================================== *)
(* USpec helper lemmas for L0 history-call append                       *)
(* ================================================================== *)

lemma L0_OpCalledInHis_append_call_old:
  assumes OLD: "OpCalledInHis H a"
  shows "OpCalledInHis (H @ [e]) a"
proof -
  from OLD obtain k where mc: "match_call H k a"
    unfolding OpCalledInHis_def by blast
  have "match_call (H @ [e]) k a"
    using mc unfolding match_call_def Let_def
    by (simp add: nth_append)
  thus ?thesis
    unfolding OpCalledInHis_def by blast
qed

lemma L0_HB_append_call_no_new_match:
  assumes CALL: "act_cr e = call"
  assumes NOMATCH: "\<not> match_call (H @ [e]) (length H) b"
  shows "HB (H @ [e]) a b = HB H a b"
proof
  assume hb: "HB (H @ [e]) a b"
  then obtain k1 k2 where
    k12: "k1 < k2" and mr: "match_ret (H @ [e]) k1 a" and mc: "match_call (H @ [e]) k2 b"
    unfolding HB_def by blast
  have k1_old: "k1 < length H"
  proof (rule ccontr)
    assume "\<not> k1 < length H"
    hence k1_last: "k1 = length H"
      using mr unfolding match_ret_def by simp
    hence "act_cr ((H @ [e]) ! k1) = call"
      using CALL by (simp add: nth_append)
    moreover have "act_cr ((H @ [e]) ! k1) = ret"
      using mr unfolding match_ret_def Let_def by auto
    ultimately show False by simp
  qed
  have k2_old: "k2 < length H"
  proof (rule ccontr)
    assume "\<not> k2 < length H"
    hence k2_last: "k2 = length H"
      using mc unfolding match_call_def by simp
    hence "match_call (H @ [e]) (length H) b"
      using mc by simp
    with NOMATCH show False by contradiction
  qed
  have mr_old: "match_ret H k1 a"
    using mr k1_old unfolding match_ret_def Let_def by (simp add: nth_append)
  have mc_old: "match_call H k2 b"
    using mc k2_old unfolding match_call_def Let_def by (simp add: nth_append)
  show "HB H a b"
    unfolding HB_def using k12 mr_old mc_old by blast
next
  assume hb: "HB H a b"
  then obtain k1 k2 where
    k12: "k1 < k2" and mr: "match_ret H k1 a" and mc: "match_call H k2 b"
    unfolding HB_def by blast
  have mr_new: "match_ret (H @ [e]) k1 a"
    using mr unfolding match_ret_def Let_def by (simp add: nth_append)
  have mc_new: "match_call (H @ [e]) k2 b"
    using mc unfolding match_call_def Let_def by (simp add: nth_append)
  show "HB (H @ [e]) a b"
    unfolding HB_def using k12 mr_new mc_new by blast
qed

lemma L0_USpec_GenLin_append_call_no_new_match:
  assumes CALL: "act_cr e = call"
  assumes GEN: "USpec_GenLin H S oid L"
  assumes NOMATCH: "\<forall>b\<in>set L. \<not> match_call (H @ [e]) (length H) b"
  shows "USpec_GenLin (H @ [e]) S oid L"
proof -
  have calls: "\<forall>a\<in>set L. OpCalledInHis (H @ [e]) a"
    using GEN L0_OpCalledInHis_append_call_old unfolding USpec_GenLin_def by blast
  have hb: "HB_consistent L (H @ [e])"
  proof (unfold HB_consistent_def, intro allI impI)
    fix k1 k2
    assume pre: "k1 < length L \<and> k2 < length L \<and> HB (H @ [e]) (L ! k1) (L ! k2)"
    hence k2_lt: "k2 < length L" and hb_new: "HB (H @ [e]) (L ! k1) (L ! k2)"
      by simp_all
    have no_last: "\<not> match_call (H @ [e]) (length H) (L ! k2)"
      using NOMATCH k2_lt by simp
    have hb_old: "HB H (L ! k1) (L ! k2)"
      using hb_new L0_HB_append_call_no_new_match[OF CALL no_last, of "L ! k1"] by simp
    show "k1 < k2"
      using GEN pre hb_old unfolding USpec_GenLin_def HB_consistent_def by blast
  qed
  show ?thesis
    using GEN calls hb unfolding USpec_GenLin_def by blast
qed

lemma L0_match_call_last_enq_call:
  "match_call (H @ [mk_act enq v p sn call]) (length H) (mk_op enq v p sn)"
  unfolding match_call_def Let_def
  by (simp add: nth_append mk_act_def mk_op_def act_name_def act_pid_def act_ssn_def act_val_def act_cr_def op_name_def op_pid_def op_ssn_def op_val_def)

lemma L0_match_call_last_deq_call:
  "match_call (H @ [mk_act deq BOT p sn call]) (length H) (mk_op deq v p sn)"
  unfolding match_call_def Let_def
  by (simp add: nth_append mk_act_def mk_op_def act_name_def act_pid_def act_ssn_def act_val_def act_cr_def op_name_def op_pid_def op_ssn_def op_val_def)

lemma L0_OpCalledInHis_last_enq_call:
  "OpCalledInHis (H @ [mk_act enq v p sn call]) (mk_op enq v p sn)"
  using L0_match_call_last_enq_call[of H v p sn]
  unfolding OpCalledInHis_def by blast

lemma L0_OpCalledInHis_last_deq_call:
  "OpCalledInHis (H @ [mk_act deq BOT p sn call]) (mk_op deq v p sn)"
  using L0_match_call_last_deq_call[of H p sn v]
  unfolding OpCalledInHis_def by blast




(* Source of the lifted proof block: L0Proof.thy, L0_preserves_invariant, E1. *)
(* Original source location: approximately lines 1, 1. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_E1_preserves_invariant_branch:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "L0 p s s'"
  assumes True: "program_counter s' p = ''E1''"
  shows "system_invariant s'"
proof -
  note bridge_defs =
    program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def
    i_var_def j_var_def l_var_def x_var_def v_var_def
    s_var_def lin_seq_def his_seq_def

  (* Prove the required intermediate property. Related symbols: system_invariant. *)
  have Simulate_PC_s: "Simulate_PC s"
    and TypeOK_s: "TypeOK s"
    and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s"
    and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s" and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s" and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s"
    and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s" and sI11_x_var_Scope_s: "sI11_x_var_Scope s" and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s"
    and hI4_X_var_Lin_Sync_s: "hI4_X_var_Lin_Sync s"
    and hI7_His_WF_s: "hI7_His_WF s"
    and hI5_SSN_Unique_s: "hI5_SSN_Unique s"
    and hI6_SSN_Order_s: "hI6_SSN_Order s"
    and hI8_Val_Unique_s: "hI8_Val_Unique s"
    and hI9_Deq_Ret_Unique_s: "hI9_Deq_Ret_Unique s" and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" and hI11_Enq_Ret_Existence_s: "hI11_Enq_Ret_Existence s" and hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s"
    and hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s" and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" and hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s" and hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s"
    and hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s" and hI18_Idx_Order_No_Rev_HB_s: "hI18_Idx_Order_No_Rev_HB s" and hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s"
    and hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" and hI21_Ret_Implies_Call_s: "hI21_Ret_Implies_Call s" and hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s" and hI23_Deq_Call_Ret_Balanced_s: "hI23_Deq_Call_Ret_Balanced s"
    and hI24_HB_Implies_Idx_Order_s: "hI24_HB_Implies_Idx_Order s" and hI25_Enq_Call_Ret_Balanced_s: "hI25_Enq_Call_Ret_Balanced s" and hI26_DeqRet_D4_Mutex_s: "hI26_DeqRet_D4_Mutex s"
    and hI27_Pending_PC_Sync_s: "hI27_Pending_PC_Sync s"
    and hI28_Fresh_Enq_Immunity_s: "hI28_Fresh_Enq_Immunity s"
    and hI29_E2_Scanner_Immunity_s: "hI29_E2_Scanner_Immunity s"
    and hI30_Ticket_HB_Immunity_s: "hI30_Ticket_HB_Immunity s"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s"
    and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" and lI5_SA_Prefix_s: "lI5_SA_Prefix s"
    and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" and lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" and lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s"
    and lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s" and lI10_D4_Enq_Deq_HB_s: "lI10_D4_Enq_Deq_HB s" and lI11_D4_Deq_Unique_s: "lI11_D4_Deq_Unique s"
    and uI1_USpec_EffOps_Lin_s: "uI1_USpec_EffOps_Lin s"
    and uI2_USpec_E1UE2_s: "uI2_USpec_E1UE2 s"
    and uI3_USpec_D3UD2_s: "uI3_USpec_D3UD2 s"
    and di_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  have pc_L0: "program_counter s p = ''L0''"
    and Simulate_PC_s': "Simulate_PC s'"
    using L0_step_facts[OF STEP] by auto
    have s'_def: "s' = L0_E1_update_state s p"
      using L0_E1_state[OF STEP True] .
    have his_eq: "his_seq s' = his_seq s @ [mk_act enq (V_var s) p (s_var s p) call]"
      using L0_E1_history_append[OF STEP True] .
    have ssn_eq_E1: "s_var s' q = s_var s q" for q
      using s'_def
      unfolding L0_E1_update_state_def s_var_def
      by (auto simp: Let_def)
    have lin_seq_eq: "lin_seq s' = lin_seq s"
      using L0_E1_lin_unchanged[OF STEP True] .
    have pc_eq_E1: "program_counter s' q = (if q = p then ''E1'' else program_counter s q)" for q
      using s'_def
      unfolding L0_E1_update_state_def program_counter_def
      by (auto simp: Let_def)
    have v_eq_E1: "v_var s' q = (if q = p then V_var s else v_var s q)" for q
      using s'_def
      unfolding L0_E1_update_state_def v_var_def V_var_def
      by (auto simp: Let_def)
    have qarr_eq_E1: "Q_arr s' k = Q_arr s k" for k
      using s'_def
      unfolding L0_E1_update_state_def Q_arr_def
      by (auto simp: Let_def)
    have qback_eq_E1: "Qback_arr s' k = Qback_arr s k" for k
      using s'_def
      unfolding L0_E1_update_state_def Qback_arr_def
      by (auto simp: Let_def)
    have l_eq_E1: "l_var s' q = l_var s q" for q
      using s'_def
      unfolding L0_E1_update_state_def l_var_def
      by (auto simp: Let_def)
    have j_eq_E1: "j_var s' q = j_var s q" for q
      using s'_def
      unfolding L0_E1_update_state_def j_var_def
      by (auto simp: Let_def)
    have i_eq_E1: "i_var s' q = i_var s q" for q
      using s'_def
      unfolding L0_E1_update_state_def i_var_def
      by (auto simp: Let_def)
    have x_eq_E1: "x_var s' q = x_var s q" for q
      using s'_def
      unfolding L0_E1_update_state_def x_var_def
      by (auto simp: Let_def)
    have QHas_eq_E1: "QHas s' a \<longleftrightarrow> QHas s a" for a
      unfolding QHas_def
      using qarr_eq_E1 by auto
    have InQBack_eq_E1: "InQBack s' a \<longleftrightarrow> InQBack s a" for a
      unfolding InQBack_def
      using qback_eq_E1 by auto
    have AtIdx_eq_E1: "AtIdx s' a k \<longleftrightarrow> AtIdx s a k" for a k
      unfolding AtIdx_def
      using qback_eq_E1 by auto
    have Idx_eq_E1: "Idx s' a = Idx s a" for a
      unfolding Idx_def AtIdx_def
      using qback_eq_E1 by simp
    have pc_D3_eq_E1: "(program_counter s' q = ''D3'') \<longleftrightarrow> (program_counter s q = ''D3'')" for q
      using pc_eq_E1[of q] pc_L0 by auto
    have TypeB_eq_E1: "TypeB s' a \<longleftrightarrow> TypeB s a" for a
    proof -
      have e2_eq:
        "(\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = a) \<longleftrightarrow>
         (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = a)"
      proof
        assume "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = a"
        then obtain q where
          qE2': "program_counter s' q = ''E2''"
          and qv': "v_var s' q = a"
          by blast
        show "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = a"
        proof (cases "q = p")
          case True
          with qE2' pc_eq_E1[of q] show ?thesis by simp
        next
          case False
          with qE2' qv' pc_eq_E1[of q] v_eq_E1[of q] show ?thesis
            by auto
        qed
      next
        assume "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = a"
        then obtain q where
          qE2: "program_counter s q = ''E2''"
          and qv: "v_var s q = a"
          by blast
        show "\<exists>q. program_counter s' q = ''E2'' \<and> v_var s' q = a"
        proof (cases "q = p")
          case True
          with pc_L0 qE2 show ?thesis by simp
        next
          case False
          with qE2 qv pc_eq_E1[of q] v_eq_E1[of q] show ?thesis
            by auto
        qed
      qed
      show ?thesis
        unfolding TypeB_def
        using QHas_eq_E1[of a] e2_eq
        by simp
    qed
    have TypeA_eq_E1: "TypeA s' a \<longleftrightarrow> TypeA s a" for a
      unfolding TypeA_def
      using InQBack_eq_E1[of a] QHas_eq_E1[of a]
      by simp
    have SetA_eq_E1: "SetA s' = SetA s"
      unfolding SetA_def using TypeA_eq_E1 by auto
    have SetB_eq_E1: "SetB s' = SetB s"
      unfolding SetB_def using TypeB_eq_E1 by auto
    have TypeBT_eq_E1: "TypeBT s' a \<longleftrightarrow> TypeBT s a" for a
      unfolding TypeBT_def
      using TypeB_eq_E1[of a] InQBack_eq_E1[of a] Idx_eq_E1[of a]
            qarr_eq_E1 pc_D3_eq_E1 j_eq_E1 l_eq_E1
      by auto
    have TypeBO_eq_E1: "TypeBO s' a \<longleftrightarrow> TypeBO s a" for a
      unfolding TypeBO_def
      using TypeB_eq_E1[of a] TypeBT_eq_E1[of a]
      by simp
    have SetBT_eq_E1: "SetBT s' = SetBT s"
      unfolding SetBT_def using TypeBT_eq_E1 by auto
    have SetBO_eq_E1: "SetBO s' = SetBO s"
      unfolding SetBO_def using TypeBO_eq_E1 by auto
    have fresh_not_inQBack: "\<not> InQBack s (V_var s)"
      using L0_E1_qback_fresh[OF hI3_L0_E_Phase_Bounds_s TypeOK_s]
      unfolding InQBack_def by auto
    have fresh_not_SetBT: "V_var s \<notin> SetBT s"
      unfolding SetBT_def TypeBT_def
      using fresh_not_inQBack by auto
    have fresh_not_TypeA: "\<not> TypeA s (V_var s)"
      unfolding TypeA_def using fresh_not_inQBack by auto
    have fresh_not_SetA: "V_var s \<notin> SetA s"
      unfolding SetA_def using fresh_not_TypeA by auto
    have fresh_not_QHas: "\<not> QHas s (V_var s)"
    proof
      assume "QHas s (V_var s)"
      then obtain k where qhas_k: "Q_arr s k = V_var s"
        unfolding QHas_def by blast
      from sI8_Q_Qback_Sync_s have qarr_cases: "Q_arr s k = Qback_arr s k \<or> Q_arr s k = BOT"
        unfolding sI8_Q_Qback_Sync_def by auto
      have v_not_bot: "V_var s \<noteq> BOT"
        using TypeOK_s unfolding TypeOK_def Val_def BOT_def by auto
      from qarr_cases show False
      proof
        assume "Q_arr s k = Qback_arr s k"
        with qhas_k have "Qback_arr s k = V_var s"
          by simp
        with L0_E1_qback_fresh[OF hI3_L0_E_Phase_Bounds_s TypeOK_s] show False
          by blast
      next
        assume "Q_arr s k = BOT"
        with qhas_k v_not_bot show False
          by simp
      qed
    qed

    have fresh_not_TypeB: "\<not> TypeB s (V_var s)"
    proof
      assume fresh_TypeB: "TypeB s (V_var s)"
      then have qhas_or_e2:
        "QHas s (V_var s) \<or> (\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = V_var s)"
        unfolding TypeB_def by auto
      thus False
      proof
        assume "QHas s (V_var s)"
        with fresh_not_QHas show False by contradiction
      next
        assume "\<exists>q. program_counter s q = ''E2'' \<and> v_var s q = V_var s"
        then obtain q where qE2: "program_counter s q = ''E2''" and qv: "v_var s q = V_var s"
          by blast
       have cur_enq: "Model.EnqCallInHis s q (V_var s) (s_var s q)"
  using hI10_Enq_Call_Existence_s qE2 qv
  unfolding hI10_Enq_Call_Existence_def
  by auto
then obtain e where
  e_in: "e \<in> set (his_seq s)"
  and e_props:
    "act_pid e = q \<and> act_ssn e = s_var s q \<and> act_name e = enq \<and> act_cr e = call \<and> act_val e = V_var s"
  unfolding Model.EnqCallInHis_def
  by blast
have e_index: "\<exists>k<length (his_seq s). his_seq s ! k = e"
  using e_in by (simp add: in_set_conv_nth)
then obtain k where
  k_lt: "k < length (his_seq s)"
  and e_nth: "his_seq s ! k = e"
  by blast
have old_lt_imp:
  "act_name (his_seq s ! k) = enq \<and> act_cr (his_seq s ! k) = call \<longrightarrow>
   act_val (his_seq s ! k) < V_var s"
  using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s k_lt]
  by blast
have old_lt: "act_val e < V_var s"
  using old_lt_imp e_props e_nth
  by simp
with e_props show False
  by auto
qed
qed
have fresh_not_SetB: "V_var s \<notin> SetB s"
  unfolding SetB_def using fresh_not_TypeB by auto
have fresh_not_TypeB_E1: "\<not> TypeB s' (V_var s)"
  using fresh_not_TypeB TypeB_eq_E1[of "V_var s"] by simp
have fresh_not_enq_call_cur:
  "\<not> Model.EnqCallInHis s p (V_var s) (s_var s p)"
proof
  assume cur_enq: "Model.EnqCallInHis s p (V_var s) (s_var s p)"
  then obtain e where
    e_in: "e \<in> set (his_seq s)"
    and e_props:
      "act_pid e = p \<and> act_ssn e = s_var s p \<and> act_name e = enq \<and> act_cr e = call \<and> act_val e = V_var s"
    unfolding Model.EnqCallInHis_def
    by blast
  have e_index: "\<exists>k<length (his_seq s). his_seq s ! k = e"
    using e_in by (simp add: in_set_conv_nth)
  then obtain k where
    k_lt: "k < length (his_seq s)"
    and e_nth: "his_seq s ! k = e"
    by blast
  have old_lt_imp:
    "act_name (his_seq s ! k) = enq \<and> act_cr (his_seq s ! k) = call \<longrightarrow>
     act_val (his_seq s ! k) < V_var s"
    using hI3_L0_E_Phase_Bounds_hist_call_lt[OF hI3_L0_E_Phase_Bounds_s k_lt]
    by blast
  have old_lt: "act_val e < V_var s"
    using old_lt_imp e_props e_nth
    by simp
  with e_props show False
    by auto
qed
have fresh_not_OP_A_enq: "mk_op enq (V_var s) p (s_var s p) \<notin> OP_A_enq s"
  using fresh_not_SetA fresh_not_enq_call_cur
  unfolding OP_A_enq_def mk_op_def SetA_def
  by (simp add: op_val_def)
have fresh_not_OP_A_deq: "mk_op enq (V_var s) p (s_var s p) \<notin> OP_A_deq s"
  unfolding OP_A_deq_def mk_op_def
  by (simp add: op_name_def)
have fresh_not_OP_B_enq: "mk_op enq (V_var s) p (s_var s p) \<notin> OP_B_enq s"
  using fresh_not_SetB fresh_not_enq_call_cur
  unfolding OP_B_enq_def mk_op_def SetB_def
  by (simp add: op_val_def)
have fresh_not_OPLin: "mk_op enq (V_var s) p (s_var s p) \<notin> OPLin s"
proof
  assume in_oplin: "mk_op enq (V_var s) p (s_var s p) \<in> OPLin s"
  have in_union: "mk_op enq (V_var s) p (s_var s p) \<in> OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s"
    using lI1_Op_Sets_Equivalence_s in_oplin
    unfolding lI1_Op_Sets_Equivalence_def
    by auto
  with fresh_not_OP_A_enq fresh_not_OP_A_deq fresh_not_OP_B_enq show False
    by auto
qed
    have TypeOK_s': "TypeOK s'"
      using TypeOK_s s'_def
      unfolding TypeOK_def L0_E1_update_state_def V_var_def
      by (auto simp: Let_def bridge_defs Val_def BOT_def)

    have sI1_Zero_Index_BOT_s': "sI1_Zero_Index_BOT s'"
      using sI1_Zero_Index_BOT_s s'_def
      unfolding sI1_Zero_Index_BOT_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI2_X_var_Upper_Bound_s': "sI2_X_var_Upper_Bound s'"
      using sI2_X_var_Upper_Bound_s s'_def
      unfolding sI2_X_var_Upper_Bound_def L0_E1_update_state_def V_var_def
      by (auto simp: Let_def bridge_defs Val_def BOT_def)

    have sI3_E2_Slot_Exclusive_s': "sI3_E2_Slot_Exclusive s'"
      using sI3_E2_Slot_Exclusive_s pc_L0 s'_def
      unfolding sI3_E2_Slot_Exclusive_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI4_E3_Qback_Written_s': "sI4_E3_Qback_Written s'"
      using sI4_E3_Qback_Written_s pc_L0 s'_def
      unfolding sI4_E3_Qback_Written_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI5_D2_Local_Bound_s': "sI5_D2_Local_Bound s'"
      using sI5_D2_Local_Bound_s pc_L0 s'_def
      unfolding sI5_D2_Local_Bound_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI6_D3_Scan_Pointers_s': "sI6_D3_Scan_Pointers s'"
      using sI6_D3_Scan_Pointers_s pc_L0 s'_def
      unfolding sI6_D3_Scan_Pointers_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI7_D4_Deq_Result_s': "sI7_D4_Deq_Result s'"
      using sI7_D4_Deq_Result_s pc_L0 s'_def
      unfolding sI7_D4_Deq_Result_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have hI3_L0_E_Phase_Bounds_s': "hI3_L0_E_Phase_Bounds s'"
      using hI3_L0_E_Phase_Bounds_L0_to_E1[OF hI3_L0_E_Phase_Bounds_s pc_L0 s'_def] .

    have sI8_Q_Qback_Sync_s': "sI8_Q_Qback_Sync s'"
      using sI8_Q_Qback_Sync_s s'_def
      unfolding sI8_Q_Qback_Sync_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI9_Qback_Discrepancy_E3_s': "sI9_Qback_Discrepancy_E3 s'"
      using sI9_Qback_Discrepancy_E3_s s'_def
      unfolding sI9_Qback_Discrepancy_E3_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI10_Qback_Unique_Vals_s': "sI10_Qback_Unique_Vals s'"
      using sI10_Qback_Unique_Vals_s s'_def
      unfolding sI10_Qback_Unique_Vals_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have hI2_SSN_Bounds_s': "hI2_SSN_Bounds s'"
    proof -
      show ?thesis
      proof (unfold hI2_SSN_Bounds_def, intro allI ballI impI)
        fix q e
        assume e_in': "e \<in> set (his_seq s')"
        assume e_pid_q: "act_pid e = q"
        let ?new = "mk_act enq (V_var s) p (s_var s p) call"
        have e_old_or_new: "e \<in> set (his_seq s) \<or> e = ?new"
          using his_eq e_in' by auto
        show "act_ssn e \<le> s_var s' q \<and> (program_counter s' q = ''L0'' \<longrightarrow> act_ssn e < s_var s' q)"
        proof (cases "e \<in> set (his_seq s)")
          case True
          then have old_bound:
            "act_ssn e \<le> s_var s q \<and>
             (program_counter s q = ''L0'' \<longrightarrow> act_ssn e < s_var s q)"
            using hI2_SSN_Bounds_s e_pid_q unfolding hI2_SSN_Bounds_def by blast
          have le_old: "act_ssn e \<le> s_var s' q"
            using old_bound ssn_eq_E1[of q] by simp
          have strict_old: "program_counter s' q = ''L0'' \<longrightarrow> act_ssn e < s_var s' q"
          proof
            assume qL0': "program_counter s' q = ''L0''"
            have q_ne_p: "q \<noteq> p"
              using qL0' pc_eq_E1[of q] by auto
            have old_pc: "program_counter s q = ''L0''"
              using qL0' q_ne_p pc_eq_E1[of q] by simp
            from old_bound old_pc have "act_ssn e < s_var s q"
              by blast
            with ssn_eq_E1[of q] show "act_ssn e < s_var s' q"
              by simp
          qed
          show ?thesis
            using le_old strict_old
            by simp
        next
          case False
          with e_old_or_new have e_new: "e = ?new"
            by auto
          have q_eq_p: "q = p"
            using e_pid_q e_new
            by (simp add: mk_act_def act_pid_def)
          have le_new: "act_ssn e \<le> s_var s' q"
            using e_new q_eq_p ssn_eq_E1[of q]
            by (simp add: mk_act_def act_ssn_def)
          have not_L0: "program_counter s' q = ''L0'' \<Longrightarrow> False"
            using q_eq_p pc_eq_E1[of p]
            by simp
          show ?thesis
            using le_new not_L0 by blast
        qed
      qed
    qed

    have sI11_x_var_Scope_s': "sI11_x_var_Scope s'"
    proof (unfold sI11_x_var_Scope_def, intro allI impI)
      fix q
      assume q_pc': "program_counter s' q \<noteq> ''D4''"
      show "x_var s' q = BOT"
      proof (cases "q = p")
        case True
        (* State-transition reasoning. Related symbols: L0, D4, x_var, BOT. *)
        have qL0: "program_counter s q = ''L0''"
          using pc_L0 True by simp
        hence "program_counter s q \<noteq> ''D4''"
          by simp
        hence "x_var s q = BOT"
          using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def by blast
        (* State-transition reasoning. Related symbols: E1, x_var, BOT. *)
        then show ?thesis
          using True s'_def
          unfolding L0_E1_update_state_def bridge_defs
          by (auto simp: Let_def)
      next
        case False
        (* Proof note. Related symbols: x_var. *)
        have pc_eq: "program_counter s q = program_counter s' q"
          using False s'_def
          unfolding L0_E1_update_state_def bridge_defs
          by (auto simp: Let_def)
        then have q_pc: "program_counter s q \<noteq> ''D4''"
          using q_pc' by simp
        have "x_var s q = BOT"
          using sI11_x_var_Scope_s q_pc
          unfolding sI11_x_var_Scope_def
          by blast
        then show ?thesis
          using False s'_def
          unfolding L0_E1_update_state_def bridge_defs
          by (auto simp: Let_def)
      qed
    qed

    have hI1_E_Phase_Pending_Enq_s': "hI1_E_Phase_Pending_Enq s'"
    proof (unfold hI1_E_Phase_Pending_Enq_def, intro allI impI)
      fix q
      assume qpc': "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
      show "HasPendingEnq s' q (v_var s' q)"
      proof (cases "q = p")
        case True
        have vv: "v_var s' q = V_var s"
          using True v_eq_E1[of q]
          by simp
        have no_ret_cur_p:
          "\<forall>e \<in> set (his_seq s). \<not> (act_pid e = p \<and> act_ssn e = s_var s p \<and> act_cr e = ret)"
          using L0_no_ret_at_current_ssn[OF hI2_SSN_Bounds_s pc_L0] .
        have rhs:
          "HasPendingEnq s p (V_var s) \<or>
           (p = p \<and> V_var s = V_var s \<and>
            (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = p \<and> act_ssn e = s_var s p \<and> act_cr e = ret)))"
          using no_ret_cur_p by simp
        have "HasPendingEnq s' p (V_var s)"
          using HasPendingEnq_append_enq_call_iff[OF his_eq ssn_eq_E1[of p]] rhs
          by blast
        with True vv show ?thesis
          by simp
      next
        case False
        have qpc: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
          using qpc' False pc_eq_E1[of q]
          by auto
        have old_pend: "HasPendingEnq s q (v_var s q)"
          using hI1_E_Phase_Pending_Enq_s qpc
          unfolding hI1_E_Phase_Pending_Enq_def
          by blast
        have vv: "v_var s' q = v_var s q"
          using False v_eq_E1[of q]
          by simp
        have "HasPendingEnq s' q (v_var s q)"
          using HasPendingEnq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] old_pend False
          by auto
        with vv show ?thesis
          by simp
      qed
    qed

    have sI12_D3_Scanned_Prefix_s': "sI12_D3_Scanned_Prefix s'"
    proof (unfold sI12_D3_Scanned_Prefix_def, intro allI impI)
      fix pa k
      assume paD3': "program_counter s' pa = ''D3''"
      assume k_lt': "k < j_var s' pa"
      have pa_ne_p: "pa \<noteq> p"
      proof
        assume "pa = p"
        with paD3' pc_eq_E1[of p] show False by simp
      qed
      have paD3: "program_counter s pa = ''D3''"
        using paD3' pa_ne_p pc_eq_E1[of pa] by simp
      have k_lt: "k < j_var s pa"
        using k_lt' j_eq_E1[of pa] by simp
      from sI12_D3_Scanned_Prefix_s paD3 have old_sI12_D3_Scanned_Prefix:
        "\<forall>k < j_var s pa. Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
        unfolding sI12_D3_Scanned_Prefix_def by blast
      hence "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
        using k_lt by blast
      thus "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
        using qarr_eq_E1[of k] TypeB_eq_E1[of "Q_arr s k"]
        by simp
    qed

    have hI4_X_var_Lin_Sync_s': "hI4_X_var_Lin_Sync s'"
    proof -
      have x_eq: "X_var s' = X_var s"
        using s'_def
        unfolding L0_E1_update_state_def X_var_def
        by (auto simp: Let_def bridge_defs)
      have cnt_eq: "LinEnqCount s' (length (lin_seq s')) = LinEnqCount s (length (lin_seq s))"
        using lin_seq_eq
        unfolding LinEnqCount_def lin_seq_def
        by (simp add: bridge_defs)
      have pc_E2_eq: "\<And>q. program_counter s' q = ''E2'' \<longleftrightarrow> program_counter s q = ''E2''"
        using pc_eq_E1 pc_L0 by auto
      have slots_eq: "E2SlotCount s' = E2SlotCount s"
        apply (rule E2SlotCount_cong)
        using x_eq apply simp
        using pc_E2_eq apply simp
        using i_eq_E1 apply simp
        done
      show ?thesis
        using hI4_X_var_Lin_Sync_s x_eq cnt_eq slots_eq
        unfolding hI4_X_var_Lin_Sync_def
        by simp
    qed



    have hI7_His_WF_s': "hI7_His_WF s'"
      using hI7_His_WF_append_call[OF hI7_His_WF_s his_eq]
      by (simp add: mk_act_def act_cr_def)

    have hI8_Val_Unique_s': "hI8_Val_Unique s'"
      using hI8_Val_Unique_append_enq_call_if_fresh[OF hI8_Val_Unique_s his_eq]
      using L0_E1_fresh[OF hI3_L0_E_Phase_Bounds_s pc_L0]
      by (auto simp: mk_act_def act_name_def act_cr_def act_val_def)

    have ai11_p:
      "\<forall>ev \<in> set (his_seq s).
         act_pid ev = p \<longrightarrow>
         (act_ssn ev \<le> s_var s p \<and>
          (program_counter s p = ''L0'' \<longrightarrow> act_ssn ev < s_var s p))"
      using hI2_SSN_Bounds_s
      unfolding hI2_SSN_Bounds_def
      by blast

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_ssn_unique. *)
    have hI5_SSN_Unique_s': "hI5_SSN_Unique s'"
      using L0_E1_ssn_unique[
        OF hI5_SSN_Unique_s his_eq ai11_p pc_L0
      ] .

    have hI6_SSN_Order_s': "hI6_SSN_Order s'"
    proof (unfold hI6_SSN_Order_def, intro allI impI)
      fix i j
      assume i_lt: "i < length (his_seq s')" and j_lt: "j < length (his_seq s')"
      assume props_raw: "i < j \<and> act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
      let ?L = "length (his_seq s)"
      have len': "length (his_seq s') = Suc ?L"
        using his_eq by simp
      have ij: "i < j"
        and pid_eq: "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
        using props_raw by auto
      consider (both_old) "j < ?L"
        | (i_old_j_new) "i < ?L" "j = ?L"
        using i_lt j_lt ij len' by linarith
      then show
        "act_ssn (his_seq s' ! i) < act_ssn (his_seq s' ! j) \<or>
         (act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j) \<and>
          act_cr (his_seq s' ! i) = call \<and> act_cr (his_seq s' ! j) = ret)"
      proof cases
        case both_old
        have i_old: "i < length (his_seq s)"
          using both_old ij by linarith
        have i_old_eq: "his_seq s' ! i = his_seq s ! i"
          using his_eq i_old
          by (simp add: nth_append)
        have j_old_eq: "his_seq s' ! j = his_seq s ! j"
          using his_eq both_old
          by (simp add: nth_append)
        have pid_old: "act_pid (his_seq s ! i) = act_pid (his_seq s ! j)"
          using pid_eq i_old_eq j_old_eq
          by simp
        have old_order:
          "act_ssn (his_seq s ! i) < act_ssn (his_seq s ! j) \<or>
           (act_ssn (his_seq s ! i) = act_ssn (his_seq s ! j) \<and>
            act_cr (his_seq s ! i) = call \<and> act_cr (his_seq s ! j) = ret)"
          using hI6_SSN_Order_s[unfolded hI6_SSN_Order_def, rule_format, OF i_old both_old]
            ij pid_old
          by blast
        then show ?thesis
          using old_order i_old_eq j_old_eq
          by simp
      next
        case i_old_j_new
        have j_new: "his_seq s' ! j = mk_act enq (V_var s) p (s_var s p) call"
          using his_eq i_old_j_new by (simp add: nth_append)
        then have pid_j: "act_pid (his_seq s' ! j) = p"
          and ssn_j: "act_ssn (his_seq s' ! j) = s_var s p"
          by (simp_all add: mk_act_def act_pid_def act_ssn_def)
        have i_old: "his_seq s' ! i = his_seq s ! i"
          using his_eq i_old_j_new by (simp add: nth_append)
        have i_in: "his_seq s ! i \<in> set (his_seq s)"
          using i_old_j_new by simp
        have pid_i: "act_pid (his_seq s ! i) = p"
          using pid_eq pid_j i_old by simp
        have "act_ssn (his_seq s ! i) < s_var s p"
          using ai11_p i_in pid_i pc_L0
          by blast
        then show ?thesis
          using i_old ssn_j by simp
      qed
    qed

    have hI9_Deq_Ret_Unique_s': "hI9_Deq_Ret_Unique s'"
      using hI9_Deq_Ret_Unique_append_call_event_simple[OF hI9_Deq_Ret_Unique_s his_eq]
      by (simp add: mk_act_def act_cr_def)

   have hI10_Enq_Call_Existence_s': "hI10_Enq_Call_Existence s'"
proof (unfold hI10_Enq_Call_Existence_def, intro conjI)
  show "\<forall>q a. (program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' q = a) \<longrightarrow>
              Model.EnqCallInHis s' q a (s_var s' q)"
  proof (intro allI impI)
    fix q a
    assume pcv': "program_counter s' q \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' q = a"
    have pend': "HasPendingEnq s' q a"
      using hI1_E_Phase_Pending_Enq_s' pcv'
      unfolding hI1_E_Phase_Pending_Enq_def
      by blast
    then show "Model.EnqCallInHis s' q a (s_var s' q)"
      unfolding HasPendingEnq_def Let_def
      by blast
  qed
  show "\<forall>a. a \<in> Val \<and> (\<exists>k. Qback_arr s' k = a) \<longrightarrow>
            (\<exists>q sn. Model.EnqCallInHis s' q a sn)"
  proof (intro allI impI)
    fix a
    assume PRE: "a \<in> Val \<and> (\<exists>k. Qback_arr s' k = a)"
    then have A_VAL: "a \<in> Val" and qb': "\<exists>k. Qback_arr s' k = a"
      by blast+
    have qb_old: "\<exists>k. Qback_arr s k = a"
      using qb' qback_eq_E1
      by auto
    then obtain q sn where old_enq: "Model.EnqCallInHis s q a sn"
      using hI10_Enq_Call_Existence_s A_VAL
      unfolding hI10_Enq_Call_Existence_def
      by blast
    have new_enq: "Model.EnqCallInHis s' q a sn"
      using old_enq his_eq
      unfolding Model.EnqCallInHis_def
      by auto
    show "\<exists>q sn. Model.EnqCallInHis s' q a sn"
      using new_enq by blast
  qed
qed

have hI11_Enq_Ret_Existence_s': "hI11_Enq_Ret_Existence s'"
proof (unfold hI11_Enq_Ret_Existence_def, intro allI impI)
  fix q a sn
  assume cond':
    "((program_counter s' q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' q \<noteq> a \<or> s_var s' q \<noteq> sn) \<and>
      (\<exists>k. Qback_arr s' k = a) \<and>
      Model.EnqCallInHis s' q a sn)"
  have qback_old: "\<exists>k. Qback_arr s k = a"
    using cond' qback_eq_E1 by auto
  have a_ne_fresh: "a \<noteq> V_var s"
    using qback_old L0_E1_qback_fresh[OF hI3_L0_E_Phase_Bounds_s TypeOK_s]
    by blast
  have old_guard: "program_counter s q \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s q \<noteq> a \<or> s_var s q \<noteq> sn"
  proof (cases "q = p")
    case True
    with pc_L0 show ?thesis by simp
  next
    case False
    with cond' pc_eq_E1[of q] v_eq_E1[of q] ssn_eq_E1[of q] show ?thesis by auto
  qed
  have old_enq: "Model.EnqCallInHis s q a sn"
  proof -
    have enq': "Model.EnqCallInHis s' q a sn"
      using cond'
      by simp
    have disj: "Model.EnqCallInHis s q a sn \<or> (q = p \<and> a = V_var s \<and> sn = s_var s p)"
      using enq' his_eq
      unfolding Model.EnqCallInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    from disj show ?thesis
    proof
      assume "Model.EnqCallInHis s q a sn"
      then show ?thesis .
    next
      assume "q = p \<and> a = V_var s \<and> sn = s_var s p"
      with a_ne_fresh show ?thesis
        by simp
    qed
  qed
  have old_ret: "Model.EnqRetInHis s q a sn"
    using hI11_Enq_Ret_Existence_s old_guard qback_old old_enq
    unfolding hI11_Enq_Ret_Existence_def
    by blast
  have ret_iff: "Model.EnqRetInHis s' q a sn \<longleftrightarrow> Model.EnqRetInHis s q a sn"
    using his_eq
    unfolding Model.EnqRetInHis_def
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  show "Model.EnqRetInHis s' q a sn"
    using ret_iff old_ret
    by blast
qed

    have hI12_D_Phase_Pending_Deq_s': "hI12_D_Phase_Pending_Deq s'"
    proof (unfold hI12_D_Phase_Pending_Deq_def, intro allI impI)
      fix q
      assume qD': "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      have q_ne_p: "q \<noteq> p"
        using qD' pc_eq_E1[of q] by auto
      have qD: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
        using qD' q_ne_p pc_eq_E1[of q] by simp
      have pending_old: "HasPendingDeq s q"
        using hI12_D_Phase_Pending_Deq_s qD unfolding hI12_D_Phase_Pending_Deq_def by blast
      have pending_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
        using HasPendingDeq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] .
      show "HasPendingDeq s' q"
        using pending_old pending_eq by blast
    qed

    have hI13_Qback_Deq_Sync_s': "hI13_Qback_Deq_Sync s'"
  proof -
    (* Reasoning about appending one history or sequence element. *)
    have deq_ret_eq: "\<And>q a sn. Model.DeqRetInHis s' q a sn \<longleftrightarrow> Model.DeqRetInHis s q a sn"
      using DeqRetInHis_append_call_iff[of s' s "mk_act enq (V_var s) p (s_var s p) call"]
      using his_eq by (simp add: mk_act_def act_cr_def)

    (* State-transition reasoning. Related symbols: L0, E1, D4. *)
    have d4_eq: "\<And>q. (program_counter s' q = ''D4'') \<longleftrightarrow> (program_counter s q = ''D4'')"
      using pc_eq_E1 pc_L0 by auto

    (* Use the relevant invariant, lemma, or hypothesis. *)
    show ?thesis
      using hI13_Qback_Deq_Sync_s
      unfolding hI13_Qback_Deq_Sync_def
      using qarr_eq_E1 qback_eq_E1 x_eq_E1 d4_eq deq_ret_eq
      by auto
  qed

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_pending_enq_qback_exclusive. *)
    have hI14_Pending_Enq_Qback_Exclusivity_s': "hI14_Pending_Enq_Qback_Exclusivity s'"
      using L0_E1_pending_enq_qback_exclusive[
        OF hI14_Pending_Enq_Qback_Exclusivity_s his_eq ssn_eq_E1 pc_eq_E1 qback_eq_E1 i_eq_E1
           hI3_L0_E_Phase_Bounds_s pc_L0 TypeOK_s
      ] .

(* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
(* Prove the required intermediate property. Related symbols: L0_E1_deq_result_exclusive. *)
have hI15_Deq_Result_Exclusivity_s': "hI15_Deq_Result_Exclusivity s'"
  using L0_E1_deq_result_exclusive[
    OF hI15_Deq_Result_Exclusivity_s his_eq pc_eq_E1 x_eq_E1 qarr_eq_E1 ssn_eq_E1 pc_L0
  ] .

    have hI16_BO_BT_No_HB_s': "hI16_BO_BT_No_HB s'"
    proof (unfold hI16_BO_BT_No_HB_def, intro allI impI)
      fix a b
      assume ab': "a \<in> SetBO s' \<and> b \<in> SetBT s'"
      have a_old: "a \<in> SetBO s"
        and b_old: "b \<in> SetBT s"
        using SetBO_eq_E1 SetBT_eq_E1 ab' by auto
      have b_ne: "b \<noteq> V_var s"
        using b_old fresh_not_SetBT by auto
      have old_no: "\<not> HB_EnqRetCall s a b"
        using hI16_BO_BT_No_HB_s a_old b_old unfolding hI16_BO_BT_No_HB_def by blast
      have hb_eq: "HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
        using HB_EnqRetCall_append_enq_call_other_iff[OF his_eq b_ne] .
      show "\<not> HB_EnqRetCall s' a b"
        using old_no hb_eq
        by blast
    qed

    have hI17_BT_BT_No_HB_s': "hI17_BT_BT_No_HB s'"
    proof (unfold hI17_BT_BT_No_HB_def, intro allI impI)
      fix a b
      assume ab': "a \<in> SetBT s' \<and> b \<in> SetBT s'"
      have a_old: "a \<in> SetBT s"
        and b_old: "b \<in> SetBT s"
        using SetBT_eq_E1 ab' by auto
      have b_ne: "b \<noteq> V_var s"
        using b_old fresh_not_SetBT by auto
      have old_no: "\<not> HB_EnqRetCall s a b"
        using hI17_BT_BT_No_HB_s a_old b_old unfolding hI17_BT_BT_No_HB_def by blast
      have hb_eq: "HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
        using HB_EnqRetCall_append_enq_call_other_iff[OF his_eq b_ne] .
      show "\<not> HB_EnqRetCall s' a b"
        using old_no hb_eq
        by blast
    qed

    have hI18_Idx_Order_No_Rev_HB_s': "hI18_Idx_Order_No_Rev_HB s'"
    proof (unfold hI18_Idx_Order_No_Rev_HB_def, intro allI impI)
      fix a b
      assume prem': "InQBack s' a \<and> InQBack s' b \<and> Idx s' a < Idx s' b"
      have inq_a: "InQBack s a" and inq_b: "InQBack s b"
        using prem' InQBack_eq_E1 by auto
      have idx_old: "Idx s a < Idx s b"
        using prem' Idx_eq_E1[of a] Idx_eq_E1[of b] by simp
      have a_ne: "a \<noteq> V_var s"
        using inq_a fresh_not_inQBack by auto
      have old_no: "\<not> HB_EnqRetCall s b a"
        using hI18_Idx_Order_No_Rev_HB_s inq_a inq_b idx_old unfolding hI18_Idx_Order_No_Rev_HB_def by blast
      have hb_eq: "HB_EnqRetCall s' b a \<longleftrightarrow> HB_EnqRetCall s b a"
        using HB_EnqRetCall_append_enq_call_other_iff[OF his_eq a_ne] .
      show "\<not> HB_EnqRetCall s' b a"
        using old_no hb_eq
        by blast
    qed

have hI19_Scanner_Catches_Later_Enq_s': "hI19_Scanner_Catches_Later_Enq s'"
proof (unfold hI19_Scanner_Catches_Later_Enq_def, intro allI impI)
  fix a b
  assume prem':
    "InQBack s' a \<and> InQBack s' b \<and> TypeB s' a \<and> TypeB s' b \<and> Idx s' a < Idx s' b \<and>
     (\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
          Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q)"
  have inq_a': "InQBack s' a" and inq_b': "InQBack s' b"
    using prem' by auto
  have type_a': "TypeB s' a" and type_b': "TypeB s' b"
    using prem' by auto
  have type_a: "TypeB s a" and type_b: "TypeB s b"
    using type_a' type_b' TypeB_eq_E1 by auto
  have inq_a: "InQBack s a" and inq_b: "InQBack s b"
    using inq_a' inq_b' qback_eq_E1
    unfolding InQBack_def
    by auto
  have idx_old: "Idx s a < Idx s b"
    using prem' Idx_eq_E1[of a] Idx_eq_E1[of b] by simp
  have d3_block_old:
    "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and>
         Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
  proof -
    from prem' obtain q where
      pend': "HasPendingDeq s' q"
      and qD3': "program_counter s' q = ''D3''"
      and bounds':
        "Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q"
      by blast
    have "HasPendingDeq s q"
      using HasPendingDeq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] pend'
      by simp
    moreover have "program_counter s q = ''D3''"
      using qD3' pc_D3_eq_E1[of q] by simp
    moreover have "Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
      using bounds' Idx_eq_E1[of a] Idx_eq_E1[of b] j_eq_E1[of q] l_eq_E1[of q]
      by simp
    ultimately show ?thesis
      by blast
  qed
  have b_ne: "b \<noteq> V_var s"
    using type_b' fresh_not_TypeB_E1 by auto
  have old_no: "\<not> HB_EnqRetCall s a b"
    using hI19_Scanner_Catches_Later_Enq_s inq_a inq_b type_a type_b idx_old d3_block_old
    unfolding hI19_Scanner_Catches_Later_Enq_def
    by blast
  have hb_eq: "HB_EnqRetCall s' a b \<longleftrightarrow> HB_EnqRetCall s a b"
    using HB_EnqRetCall_append_enq_call_other_iff[OF his_eq b_ne] .
  show "\<not> HB_EnqRetCall s' a b"
    using old_no hb_eq
    by blast
qed

    have hI20_Enq_Val_Valid_s': "hI20_Enq_Val_Valid s'"
      using hI20_Enq_Val_Valid_append_enq_call[OF hI20_Enq_Val_Valid_s his_eq] TypeOK_s
      unfolding TypeOK_def V_var_def
      by (auto simp: mk_act_def act_name_def act_cr_def act_val_def TypeOK_def Val_def bridge_defs)

    have hI21_Ret_Implies_Call_s': "hI21_Ret_Implies_Call s'"
      using hI21_Ret_Implies_Call_append_call[OF hI21_Ret_Implies_Call_s his_eq]
      by (simp add: mk_act_def act_cr_def)

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_deq_local_pattern. *)
    have hI22_Deq_Local_Pattern_s': "hI22_Deq_Local_Pattern s'"
      using L0_E1_deq_local_pattern[
        OF hI22_Deq_Local_Pattern_s his_eq qarr_eq_E1 qback_eq_E1 x_eq_E1
      ] .

    have deq_balanced_p:
      "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
       length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
      using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s pc_L0] .
    have hI23_Deq_Call_Ret_Balanced_s': "hI23_Deq_Call_Ret_Balanced s'"
      using hI23_Deq_Call_Ret_Balanced_append_enq_call_if_balanced_deq[OF hI23_Deq_Call_Ret_Balanced_s deq_balanced_p his_eq] .

    have hI24_HB_Implies_Idx_Order_s': "hI24_HB_Implies_Idx_Order s'"
    proof (unfold hI24_HB_Implies_Idx_Order_def, intro allI impI)
      fix u1 u2 v1 v2 idx1 idx2 sn1 sn2
      assume pre:
        "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1) \<and>
         CState.Q_arr (fst s') idx1 = v1 \<and>
         CState.Q_arr (fst s') idx2 = v2"
      have hb': "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
        using pre by simp
      have q1': "CState.Q_arr (fst s') idx1 = v1"
        using pre by simp
      have q2': "CState.Q_arr (fst s') idx2 = v2"
        using pre by simp
      have q1: "CState.Q_arr (fst s) idx1 = v1"
        using q1' qarr_eq_E1[of idx1]
        unfolding Q_arr_def by simp
      have q2: "CState.Q_arr (fst s) idx2 = v2"
        using q2' qarr_eq_E1[of idx2]
        unfolding Q_arr_def by simp
      have v1_ne_fresh: "v1 \<noteq> V_var s"
      proof
        assume v1_eq: "v1 = V_var s"
        have "QHas s (V_var s)"
        proof (unfold QHas_def, rule exI[where x = idx1])
          show "Q_arr s idx1 = V_var s"
            using q1 v1_eq
            unfolding Q_arr_def
            by simp
        qed
        with fresh_not_QHas show False
          by contradiction
      qed
      have act2_ne: "mk_op enq v1 u1 sn1 \<noteq> mk_op enq (V_var s) p (s_var s p)"
        using v1_ne_fresh
        by (simp add: mk_op_def)
      have hb: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
        using hb'
          HB_Act_append_enq_call_other_iff[OF his_eq act2_ne, of "mk_op enq v2 u2 sn2"]
        by simp
      show "idx2 < idx1"
        using hI24_HB_Implies_Idx_Order_s hb q1 q2
        unfolding hI24_HB_Implies_Idx_Order_def
        by blast
    qed

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_enq_call_ret_balanced. *)
    have hI25_Enq_Call_Ret_Balanced_s': "hI25_Enq_Call_Ret_Balanced s'"
      using L0_E1_enq_call_ret_balanced[
        OF hI25_Enq_Call_Ret_Balanced_s his_eq pc_eq_E1 pc_L0
      ] .

   have hI26_DeqRet_D4_Mutex_s': "hI26_DeqRet_D4_Mutex s'"
  proof (unfold hI26_DeqRet_D4_Mutex_def, intro allI impI notI)
    fix q a
    assume a_val: "a \<in> Val"
    assume bad:
      "(\<exists>sn. Model.DeqRetInHis s' q a sn) \<and>
       program_counter s' q = ''D4'' \<and> x_var s' q = a"
    then obtain sn where
      deq': "Model.DeqRetInHis s' q a sn"
      and pc_D4': "program_counter s' q = ''D4''"
      and xq': "x_var s' q = a"
      by blast
    have q_ne_p: "q \<noteq> p"
      using pc_D4' pc_eq_E1[of q]
      by auto
    have deq: "Model.DeqRetInHis s q a sn"
      using deq' his_eq
      unfolding Model.DeqRetInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    have pc_D4: "program_counter s q = ''D4''"
      using q_ne_p pc_D4' pc_eq_E1[of q]
      by simp
    have xq: "x_var s q = a"
      using q_ne_p xq' x_eq_E1[of q]
      by simp
    from hI26_DeqRet_D4_Mutex_s a_val show False
      unfolding hI26_DeqRet_D4_Mutex_def
      using deq pc_D4 xq
      by blast
  qed

    have hI27_Pending_PC_Sync_s': "hI27_Pending_PC_Sync s'"
    proof (unfold hI27_Pending_PC_Sync_def, intro conjI allI impI)
      fix q
      assume pend': "HasPendingDeq s' q"
      have pend: "HasPendingDeq s q"
        using HasPendingDeq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] pend'
        by simp
      have pc_old: "program_counter s q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
        using hI27_Pending_PC_Sync_s pend
        unfolding hI27_Pending_PC_Sync_def
        by blast
      show "program_counter s' q \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      proof (cases "q = p")
        case True
        then have "program_counter s q = ''L0''"
          using pc_L0 by simp
        with pc_old show ?thesis
          using True by auto
      next
        case False
        then show ?thesis
          using pc_old pc_eq_E1[of q] by auto
      qed
    next
      fix q
      assume pend': "HasPendingEnq s' q (v_var s' q)"
      show "program_counter s' q \<in> {''E1'', ''E2'', ''E3''}"
      proof (cases "q = p")
        case True
        then show ?thesis
          using pc_eq_E1[of q]
          by auto
      next
        case False
        have vv_eq: "v_var s' q = v_var s q"
          using v_eq_E1[of q] False
          by simp
        have pend_old': "HasPendingEnq s' q (v_var s q)"
          using pend' vv_eq
          by simp
        have pend_old: "HasPendingEnq s q (v_var s q)"
          using HasPendingEnq_append_enq_call_iff[OF his_eq ssn_eq_E1[of q]] pend_old' False
          by auto
        have pc_old: "program_counter s q \<in> {''E1'', ''E2'', ''E3''}"
          using hI27_Pending_PC_Sync_s pend_old
          unfolding hI27_Pending_PC_Sync_def
          by blast
        show ?thesis
          using pc_old pc_eq_E1[of q] False
          by auto
      qed
    qed

(* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
(* Prove the required intermediate property. Related symbols: L0_E1_fresh_enq_immune. *)
have hI28_Fresh_Enq_Immunity_s': "hI28_Fresh_Enq_Immunity s'"
  using L0_E1_fresh_enq_immune[
    OF INV his_eq v_eq_E1 hI28_Fresh_Enq_Immunity_s pc_eq_E1
       lI3_HB_Ret_Lin_Sync_s lI4_FIFO_Semantics_s fresh_not_SetA fresh_not_SetB
  ] .

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_e2_scanner_immune. *)
    have hI29_E2_Scanner_Immunity_s': "hI29_E2_Scanner_Immunity s'"
      using L0_E1_e2_scanner_immune[
        OF hI29_E2_Scanner_Immunity_s his_eq ssn_eq_E1 pc_eq_E1 InQBack_eq_E1 TypeB_eq_E1
           Idx_eq_E1 j_eq_E1 i_eq_E1 l_eq_E1 v_eq_E1 hI10_Enq_Call_Existence_s
           hI3_L0_E_Phase_Bounds_s pc_L0 pc_D3_eq_E1
      ] .

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_ticket_hb_immune. *)
    have hI30_Ticket_HB_Immunity_s': "hI30_Ticket_HB_Immunity s'"
      using L0_E1_ticket_hb_immune[
        OF hI30_Ticket_HB_Immunity_s pc_eq_E1 InQBack_eq_E1 v_eq_E1 hI1_E_Phase_Pending_Enq_s
           his_eq hI3_L0_E_Phase_Bounds_s Idx_eq_E1 i_eq_E1
      ] .


    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_op_sets_equiv. *)
    have lI1_Op_Sets_Equivalence_s': "lI1_Op_Sets_Equivalence s'"
      using L0_E1_op_sets_equiv[
        OF lI1_Op_Sets_Equivalence_s SetA_eq_E1 his_eq fresh_not_SetA SetB_eq_E1 fresh_not_TypeB
           lin_seq_eq
      ] .

    have lI2_Op_Cardinality_s': "lI2_Op_Cardinality s'"
      using lI2_Op_Cardinality_s lin_seq_eq pc_L0 s'_def
      unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def SetA_def SetB_def TypeA_def TypeB_def
                QHas_def InQBack_def L0_E1_update_state_def
      by (auto simp: Let_def bridge_defs split: if_splits)

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_E1_hb_ret_lin_sync. *)
    have lI3_HB_Ret_Lin_Sync_s': "lI3_HB_Ret_Lin_Sync s'"
      using L0_E1_hb_ret_lin_sync[
        OF lI3_HB_Ret_Lin_Sync_s lin_seq_eq his_eq fresh_not_OPLin
      ] .

    have lI4_FIFO_Semantics_s': "lI4_FIFO_Semantics s'"
      using lI4_FIFO_Semantics_s lin_seq_eq
      unfolding lI4_FIFO_Semantics_def by simp

    have lI5_SA_Prefix_s': "lI5_SA_Prefix s'"
      using lI5_SA_Prefix_s lin_seq_eq
      unfolding lI5_SA_Prefix_def by simp

    have lI6_D4_Deq_Linearized_s': "lI6_D4_Deq_Linearized s'"
    proof (unfold lI6_D4_Deq_Linearized_def, intro allI impI)
      fix q
      assume pc_D4': "program_counter s' q = ''D4''"
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_E1[of q]
        by auto
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_E1[of q]
        by simp
      from lI6_D4_Deq_Linearized_s pc_D4 have old_in:
        "mk_op deq (x_var s q) q (s_var s q) \<in> set (lin_seq s)"
        unfolding lI6_D4_Deq_Linearized_def
        by blast
      show "mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s')"
        using old_in q_ne_p lin_seq_eq x_eq_E1[of q] ssn_eq_E1[of q]
        by simp
    qed

    have lI7_D4_Deq_Deq_HB_s': "lI7_D4_Deq_Deq_HB s'"
    proof (unfold lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def, intro allI impI)
      fix k1 k2 q
      assume pre:
        "k1 < length (lin_seq s') \<and>
         k2 < length (lin_seq s') \<and>
         op_name (lin_seq s' ! k1) = deq \<and>
         lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
         (\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q) \<and>
         program_counter s' q = ''D4'' \<and>
         HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
      then have
        k1_lt': "k1 < length (lin_seq s')"
        and k2_lt': "k2 < length (lin_seq s')"
        and act1_deq': "op_name (lin_seq s' ! k1) = deq"
        and act2_eq': "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
        and tail': "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q"
        and pc_D4': "program_counter s' q = ''D4''"
        and hb': "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
        by auto
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_E1[of q]
        by auto
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_E1[of q]
        by simp
      have k1_lt: "k1 < length (lin_seq s)" and k2_lt: "k2 < length (lin_seq s)"
        using k1_lt' k2_lt' lin_seq_eq by simp_all
      have act2_eq:
        "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
        using act2_eq' lin_seq_eq q_ne_p x_eq_E1[of q] ssn_eq_E1[of q]
        by simp
      have act1_deq: "op_name (lin_seq s ! k1) = deq"
        using act1_deq' lin_seq_eq by simp
      have tail:
        "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
        using tail' lin_seq_eq by simp
      have act2_ne: "lin_seq s ! k2 \<noteq> mk_op enq (V_var s) p (s_var s p)"
        using act2_eq
        by (simp add: mk_op_def)
      have hb_old: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
        using HB_Act_append_enq_call_other_iff[OF his_eq act2_ne]
          hb' lin_seq_eq
        unfolding HB_Act_def
        by simp
      show "k1 < k2"
        using lI7_D4_Deq_Deq_HB_s k1_lt k2_lt act1_deq act2_eq tail pc_D4 hb_old
        unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
        by blast
    qed

   have lI8_D3_Deq_Returned_s': "lI8_D3_Deq_Returned s'"
  proof (unfold lI8_D3_Deq_Returned_def, intro allI impI)
    fix q k
    assume pc_D3': "program_counter s' q = ''D3''"
      and k_lt': "k < length (lin_seq s')"
      and act_match': "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
    have q_ne_p: "q \<noteq> p"
      using pc_D3' pc_eq_E1[of q]
      by auto
    have pc_D3: "program_counter s q = ''D3''"
      using q_ne_p pc_D3' pc_eq_E1[of q]
      by simp
    have k_lt: "k < length (lin_seq s)"
      using k_lt' lin_seq_eq by simp
    have act_match: "op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q"
      using act_match' lin_seq_eq by simp
    have deq_old:
      "Model.DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
      using lI8_D3_Deq_Returned_s pc_D3 k_lt act_match
      unfolding lI8_D3_Deq_Returned_def
      by blast
    show "Model.DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
      using deq_old his_eq lin_seq_eq
      unfolding Model.DeqRetInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  qed

have lI9_D1_D2_Deq_Returned_s': "lI9_D1_D2_Deq_Returned s'"
proof (unfold lI9_D1_D2_Deq_Returned_def, intro allI impI)
  fix q k
  assume pc_D12': "program_counter s' q = ''D1'' \<or> program_counter s' q = ''D2''"
    and k_lt': "k < length (lin_seq s')"
    and act_match': "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
  have q_ne_p: "q \<noteq> p"
    using pc_D12' pc_eq_E1[of q]
    by auto
  have pc_D12: "program_counter s q = ''D1'' \<or> program_counter s q = ''D2''"
    using q_ne_p pc_D12' pc_eq_E1[of q]
    by simp
  have k_lt: "k < length (lin_seq s)"
    using k_lt' lin_seq_eq by simp
  have act_match: "op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q"
    using act_match' lin_seq_eq by simp
  have deq_old:
    "Model.DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
    using lI9_D1_D2_Deq_Returned_s pc_D12 k_lt act_match
    unfolding lI9_D1_D2_Deq_Returned_def
    by blast
  show "Model.DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
    using deq_old his_eq lin_seq_eq
    unfolding Model.DeqRetInHis_def
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
qed

    have lI10_D4_Enq_Deq_HB_s': "lI10_D4_Enq_Deq_HB s'"
    proof (unfold lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def, intro allI impI)
      fix k1 k2 q
      assume pre:
        "k1 < length (lin_seq s') \<and>
         k2 < length (lin_seq s') \<and>
         op_name (lin_seq s' ! k1) = enq \<and>
         lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
         (\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q) \<and>
         program_counter s' q = ''D4'' \<and>
         HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
      then have
        k1_lt': "k1 < length (lin_seq s')"
        and k2_lt': "k2 < length (lin_seq s')"
        and act1_enq': "op_name (lin_seq s' ! k1) = enq"
        and act2_eq': "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
        and tail': "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q"
        and pc_D4': "program_counter s' q = ''D4''"
        and hb': "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
        by auto
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_E1[of q]
        by auto
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_E1[of q]
        by simp
      have k1_lt: "k1 < length (lin_seq s)" and k2_lt: "k2 < length (lin_seq s)"
        using k1_lt' k2_lt' lin_seq_eq by simp_all
      have act2_eq:
        "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
        using act2_eq' lin_seq_eq q_ne_p x_eq_E1[of q] ssn_eq_E1[of q]
        by simp
      have act1_enq: "op_name (lin_seq s ! k1) = enq"
        using act1_enq' lin_seq_eq by simp
      have tail:
        "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
        using tail' lin_seq_eq by simp
      have act2_ne: "lin_seq s ! k2 \<noteq> mk_op enq (V_var s) p (s_var s p)"
        using act2_eq
        by (simp add: mk_op_def)
      have hb_old: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
        using HB_Act_append_enq_call_other_iff[OF his_eq act2_ne]
          hb' lin_seq_eq
        unfolding HB_Act_def
        by simp
      show "k1 < k2"
        using lI10_D4_Enq_Deq_HB_s k1_lt k2_lt act1_enq act2_eq tail pc_D4 hb_old
        unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
        by blast
    qed

   have lI11_D4_Deq_Unique_s': "lI11_D4_Deq_Unique s'"
  proof (unfold lI11_D4_Deq_Unique_def, intro allI impI)
    fix q
    assume pc_D4': "program_counter s' q = ''D4''"
    have q_ne_p: "q \<noteq> p"
      using pc_D4' pc_eq_E1[of q]
      by auto
    have pc_D4: "program_counter s q = ''D4''"
      using q_ne_p pc_D4' pc_eq_E1[of q]
      by simp
    from lI11_D4_Deq_Unique_s[unfolded lI11_D4_Deq_Unique_def, rule_format, OF pc_D4]
    obtain k2 where
      k2_lt: "k2 < length (lin_seq s)"
      and act_eq: "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
      and uniq_old:
        "\<forall>k3<length (lin_seq s).
           op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
           k3 < k2 \<and> Model.DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
      by blast
    have act_eq':
      "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
      using act_eq lin_seq_eq q_ne_p x_eq_E1[of q] ssn_eq_E1[of q]
      by simp
    have uniq_new:
      "\<forall>k3<length (lin_seq s').
         op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
         k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
    proof (intro allI impI)
      fix k3
      assume k3_lt': "k3 < length (lin_seq s')"
      assume match':
        "op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2"
      have k3_lt: "k3 < length (lin_seq s)"
        using k3_lt' lin_seq_eq by simp
      have match:
        "op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = q \<and> k3 \<noteq> k2"
        using match' lin_seq_eq by simp
      from uniq_old k3_lt match have
        "k3 < k2 \<and> Model.DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
        by blast
      then have
        "k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
        using his_eq lin_seq_eq
        unfolding Model.DeqRetInHis_def
        by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      then show
        "k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
        .
    qed
    show "\<exists>k2<length (lin_seq s').
            lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
            (\<forall>k3<length (lin_seq s').
               op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
               k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3)))"
      using k2_lt lin_seq_eq act_eq' uniq_new
      by auto
  qed

    have di_s': "data_independent (lin_seq s')"
      using di_s lin_seq_eq
      unfolding data_independent_def by simp


    (* USpec invariants uI1-uI3. *)
    have uspec_effOps_eq_E1 [simp]: "uspec_effOps s' = uspec_effOps s"
      using s'_def
      unfolding L0_E1_update_state_def uspec_effOps_def
      by (simp add: Let_def)

    have uI1_USpec_EffOps_Lin_s': "uI1_USpec_EffOps_Lin s'"
      using uI1_USpec_EffOps_Lin_s lin_seq_eq uspec_effOps_eq_E1
      unfolding uI1_USpec_EffOps_Lin_def
      by simp

    have upc_eq_E1:
      "\<And>q. u_program_counter (snd s') q =
            (if q = p then ''UE2'' else u_program_counter (snd s) q)"
      using s'_def
      unfolding L0_E1_update_state_def
      by (simp add: Let_def)

    have uI2_USpec_E1UE2_s': "uI2_USpec_E1UE2 s'"
    proof (unfold uI2_USpec_E1UE2_def, intro allI impI)
      fix q
      assume pc_q': "program_counter s' q \<in> {''E1'', ''E2''}"
      assume upc_q': "u_program_counter (snd s') q = ''UE2''"

      let ?fresh_op = "mk_op enq (V_var s) p (s_var s p)"
      let ?fresh_call = "mk_act enq (V_var s) p (s_var s p) call"
      let ?op_q' = "mk_op enq (v_var s' q) q (s_var s' q)"

      show "USpec_GenLin
              (u_his_seq (snd s'))
              (u_eff_ops (snd s'))
              ?op_q'
              (u_lin_seq (snd s') @ [?op_q'])"
      proof (cases "q = p")
        case True

        have op_q_eq:
          "?op_q' = ?fresh_op"
          using True v_eq_E1[of q] ssn_eq_E1[of q]
          by simp

        have H_eq:
          "his_seq s' = his_seq s @ [?fresh_call]"
          using his_eq by simp

        have L_eq:
          "lin_seq s' = lin_seq s"
          using lin_seq_eq .

        have S_eq:
          "uspec_effOps s' = set (lin_seq s)"
          using uI1_USpec_EffOps_Lin_s uspec_effOps_eq_E1
          unfolding uI1_USpec_EffOps_Lin_def
          by simp

        have finite_S:
          "finite (uspec_effOps s')"
          using S_eq by simp

        have subset_S:
          "uspec_effOps s' \<subseteq> set (lin_seq s' @ [?op_q'])"
          using S_eq L_eq op_q_eq
          by auto

        have op_in:
          "?op_q' \<in> set (lin_seq s' @ [?op_q'])"
          by simp

        have old_called:
          "\<forall>a\<in>set (lin_seq s). OpCalledInHis (his_seq s @ [?fresh_call]) a"
        proof
          fix a
          assume a_in: "a \<in> set (lin_seq s)"

          have called_old:
            "OpCalledInHis (his_seq s) a"
            using L0_all_lin_called_from_lI1[OF lI1_Op_Sets_Equivalence_s] a_in
            by blast

          show "OpCalledInHis (his_seq s @ [?fresh_call]) a"
            using called_old L0_OpCalledInHis_append_call_old
            by blast
        qed

        have fresh_called:
          "OpCalledInHis (his_seq s @ [?fresh_call]) ?fresh_op"
          using L0_OpCalledInHis_last_enq_call[of "his_seq s" "V_var s" p "s_var s p"] .

        have all_called:
          "\<forall>a\<in>set (lin_seq s' @ [?op_q']). OpCalledInHis (his_seq s') a"
          using old_called fresh_called L_eq H_eq op_q_eq
          by auto

        have hb_lin_s':
          "HB_consistent (lin_seq s') (his_seq s')"
          using lI3_HB_Ret_Lin_Sync_s'
          unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def HB_consistent_def
          by simp

        have no_ret_fresh:
          "\<forall>k<length (his_seq s'). \<not> match_ret (his_seq s') k ?fresh_op"
        proof (intro allI impI notI)
          fix k
          assume k_lt: "k < length (his_seq s')"
          assume mr: "match_ret (his_seq s') k ?fresh_op"

          have H_app:
            "his_seq s' = his_seq s @ [?fresh_call]"
            using H_eq .

          show False
          proof (cases "k < length (his_seq s)")
            case False
            hence k_last: "k = length (his_seq s)"
              using k_lt H_app by simp

            have last_cr_call:
              "act_cr ((his_seq s @ [?fresh_call]) ! k) = call"
              using k_last
              by (simp add: mk_act_def act_cr_def)

            moreover have "act_cr ((his_seq s @ [?fresh_call]) ! k) = ret"
              using mr H_app
              unfolding match_ret_def Let_def
              by simp
            ultimately show False
              by simp
          next
            case True
            hence mr_old:
              "match_ret (his_seq s) k ?fresh_op"
              using mr H_app
              unfolding match_ret_def Let_def
              by (simp add: nth_append)

            have ret_props:
              "act_name (his_seq s ! k) = enq \<and>
               act_cr (his_seq s ! k) = ret \<and>
               act_val (his_seq s ! k) = V_var s"
              using mr_old
              unfolding match_ret_def Let_def
              by (simp add: mk_op_def op_name_def op_val_def)

            have ret_name_enq:
              "act_name (his_seq s ! k) = enq"
              using ret_props
              by simp

            have ret_cr:
              "act_cr (his_seq s ! k) = ret"
              using ret_props
              by simp

            obtain tm where
              tm_lt: "tm < k"
              and call_pid:
                "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k)"
              and call_name:
                "act_name (his_seq s ! tm) = act_name (his_seq s ! k)"
              and call_cr:
                "act_cr (his_seq s ! tm) = call"
              and call_val:
                "act_val (his_seq s ! tm) = act_val (his_seq s ! k)"
              using hI21_enq_ret_obtain_call[
                OF hI21_Ret_Implies_Call_s True ret_name_enq ret_cr
              ]
              by blast

            have call_props:
              "act_pid (his_seq s ! tm) = act_pid (his_seq s ! k) \<and>
               act_name (his_seq s ! tm) = act_name (his_seq s ! k) \<and>
               act_cr (his_seq s ! tm) = call \<and>
               act_val (his_seq s ! tm) = act_val (his_seq s ! k)"
              using call_pid call_name call_cr call_val
              by simp

            have tm_lt_len:
              "tm < length (his_seq s)"
              using tm_lt True by simp

            have call_tm_name_enq:
              "act_name (his_seq s ! tm) = enq"
              using call_name ret_name_enq
              by simp

            have call_tm_cr_call:
              "act_cr (his_seq s ! tm) = call"
              using call_cr .

            have hI3_call_bound:
              "\<forall>k<length (his_seq s).
                  act_name (his_seq s ! k) = enq \<and>
                  act_cr (his_seq s ! k) = call \<longrightarrow>
                  act_val (his_seq s ! k) < V_var s"
              using hI3_L0_E_Phase_Bounds_s
              unfolding hI3_L0_E_Phase_Bounds_def
              by blast

            have call_lt:
              "act_val (his_seq s ! tm) < V_var s"
              using hI3_call_bound tm_lt_len call_tm_name_enq call_tm_cr_call
              by simp

            moreover have "act_val (his_seq s ! tm) = V_var s"
              using call_props ret_props
              by simp

            ultimately show False
              by simp
          qed
        qed

        have hb_final:
          "HB_consistent (lin_seq s' @ [?op_q']) (his_seq s')"
          using L0_HB_consistent_append_no_ret[
            OF hb_lin_s',
            of ?op_q'
          ] no_ret_fresh op_q_eq
          by simp

        have qs_lin:
          "QueueSpecLin (lin_seq s')"
          using lI4_FIFO_Semantics_s'
          unfolding QueueSpecLin_def lI4_FIFO_Semantics_def
          by simp

        have qs_final:
          "QueueSpecLin (lin_seq s' @ [?op_q'])"
          using E1_QueueSpecLin_append_enq[OF qs_lin, of "V_var s" p "s_var s p"]
                op_q_eq
          by simp

        have fresh_enq_val:
          "\<forall>a\<in>set (lin_seq s). op_name a = enq \<longrightarrow> op_val a \<noteq> V_var s"
        proof (intro ballI impI)
          fix a
          assume a_in: "a \<in> set (lin_seq s)"
          assume a_enq: "op_name a = enq"

          have a_oplin:
            "a \<in> OPLin s"
            using a_in unfolding OPLin_def by simp

          have a_cases:
            "a \<in> OP_A_enq s \<or> a \<in> OP_A_deq s \<or> a \<in> OP_B_enq s"
            using lI1_Op_Sets_Equivalence_s a_oplin
            unfolding lI1_Op_Sets_Equivalence_def
            by blast

          show "op_val a \<noteq> V_var s"
          proof
            assume val_eq: "op_val a = V_var s"

            from a_cases show False
            proof
              assume "a \<in> OP_A_enq s"
              then obtain qq vv sn where
                a_eq: "a = mk_op enq vv qq sn"
                and vv_set: "vv \<in> SetA s"
                unfolding OP_A_enq_def by blast

              have "vv = V_var s"
                using a_eq val_eq
                by (simp add: mk_op_def op_val_def)

              thus False
                using vv_set fresh_not_SetA
                by simp
            next
              assume rest: "a \<in> OP_A_deq s \<or> a \<in> OP_B_enq s"
              thus False
              proof
                assume "a \<in> OP_A_deq s"
                hence "op_name a = deq"
                  unfolding OP_A_deq_def by auto
                with a_enq show False
                  by simp
              next
                assume "a \<in> OP_B_enq s"
                then obtain qq vv sn where
                  a_eq: "a = mk_op enq vv qq sn"
                  and vv_set: "vv \<in> SetB s"
                  unfolding OP_B_enq_def by blast

                have "vv = V_var s"
                  using a_eq val_eq
                  by (simp add: mk_op_def op_val_def)

                thus False
                  using vv_set fresh_not_SetB
                  by simp
              qed
            qed
          qed
        qed

        have fresh_enq_val_idx:
          "\<forall>i<length (lin_seq s).
              op_name (lin_seq s ! i) = enq \<longrightarrow>
              op_val (lin_seq s ! i) \<noteq> V_var s"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < length (lin_seq s)"
          assume name_enq: "op_name (lin_seq s ! i) = enq"

          have mem_i:
            "lin_seq s ! i \<in> set (lin_seq s)"
            using i_lt
            by simp

          show "op_val (lin_seq s ! i) \<noteq> V_var s"
            using fresh_enq_val mem_i name_enq
            by blast
        qed

        have di_old_append:
          "data_independent
             (lin_seq s @ [mk_op enq (V_var s) p (s_var s p)])"
          by (rule data_independent_append_enq_fresh[
                OF di_s fresh_enq_val_idx
              ])

        have di_final:
          "data_independent (lin_seq s' @ [?op_q'])"
          using di_old_append L_eq op_q_eq
          by simp

        have gen:
          "USpec_GenLin (his_seq s') (uspec_effOps s') ?op_q'
             (lin_seq s' @ [?op_q'])"
          unfolding USpec_GenLin_def
          using finite_S subset_S op_in all_called hb_final qs_final di_final
          by blast

        show ?thesis
          using gen
          unfolding his_seq_def lin_seq_def uspec_effOps_def
          by simp
      next
        case False

        have pc_q_old:
          "program_counter s q \<in> {''E1'', ''E2''}"
          using pc_q' pc_eq_E1[of q] False
          by simp

        have upc_q_old:
          "u_program_counter (snd s) q = ''UE2''"
          using upc_q' upc_eq_E1[of q] False
          by simp

        let ?old_op = "mk_op enq (v_var s q) q (s_var s q)"
        let ?old_L = "lin_seq s @ [?old_op]"

        have old_gen:
          "USpec_GenLin (his_seq s) (uspec_effOps s) ?old_op ?old_L"
          using uI2_USpec_E1UE2_s pc_q_old upc_q_old
          unfolding uI2_USpec_E1UE2_def his_seq_def lin_seq_def uspec_effOps_def
          by blast

        have q_ne_p:
          "q \<noteq> p"
          using False
          by simp

        have no_last_match:
          "\<forall>b\<in>set ?old_L.
              \<not> match_call (his_seq s @ [?fresh_call]) (length (his_seq s)) b"
        proof
          fix b
          assume b_in: "b \<in> set ?old_L"

          show "\<not> match_call (his_seq s @ [?fresh_call]) (length (his_seq s)) b"
          proof
            assume mc:
              "match_call (his_seq s @ [?fresh_call]) (length (his_seq s)) b"

            have b_fresh:
              "b = ?fresh_op"
              using mc
              unfolding match_call_def Let_def
              by (cases b)
                 (auto simp add:
                    nth_append
                    mk_act_def mk_op_def
                    act_name_def act_pid_def act_ssn_def act_val_def act_cr_def
                    op_name_def op_pid_def op_ssn_def op_val_def)

            have b_cases:
              "b = ?old_op \<or> b \<in> set (lin_seq s)"
              using b_in
              by simp

            from b_cases show False
            proof
              assume b_old_op:
                "b = ?old_op"

              have pid_q:
                "op_pid b = q"
                using b_old_op
                by (simp add: mk_op_def op_pid_def)

              have pid_p:
                "op_pid b = p"
                using b_fresh
                by (simp add: mk_op_def op_pid_def)

              have q_eq_p:
                "q = p"
                using pid_q pid_p
                by simp

              show False
                using q_eq_p q_ne_p
                by simp
            next
              assume b_old:
                "b \<in> set (lin_seq s)"

              have b_oplin:
                "b \<in> OPLin s"
                using b_old
                unfolding OPLin_def
                by simp

              show False
                using b_fresh b_oplin fresh_not_OPLin
                by simp
            qed
          qed
        qed


        have gen_append:
          "USpec_GenLin
             (his_seq s @ [?fresh_call])
             (uspec_effOps s)
             ?old_op
             ?old_L"
          by (rule L0_USpec_GenLin_append_call_no_new_match[
                OF _ old_gen no_last_match
              ])
             (simp add: mk_act_def act_cr_def)

        have op_eq:
          "?op_q' = ?old_op"
          using False v_eq_E1[of q] ssn_eq_E1[of q]
          by simp

        show ?thesis
          using gen_append op_eq lin_seq_eq his_eq uspec_effOps_eq_E1
          unfolding his_seq_def lin_seq_def uspec_effOps_def
          by simp
      qed
    qed

    have uI3_USpec_D3UD2_s': "uI3_USpec_D3UD2 s'"
    proof (unfold uI3_USpec_D3UD2_def, intro allI impI)
      fix q
      assume pc_q': "program_counter s' q = ''D3''"
      assume qj_q': "Q_arr s' (j_var s' q) \<noteq> BOT"
      assume upc_q': "u_program_counter (snd s') q = ''UD2''"

      let ?x = "Q_arr s' (j_var s' q)"
      let ?op = "mk_op deq ?x q (s_var s' q)"
      let ?base =
        "(if should_modify (lin_seq s') (his_seq s') ?x
          then modify_lin (lin_seq s') (his_seq s') ?x
          else lin_seq s')"
      let ?L = "?base @ [?op]"
      let ?H = "his_seq s'"

      have pending_q:
        "HasPendingDeq s' q"
        using hI12_D_Phase_Pending_Deq_s' pc_q'
        unfolding hI12_D_Phase_Pending_Deq_def
        by auto

      have deq_call_q:
        "DeqCallInHis s' q (s_var s' q)"
        using pending_q
        unfolding HasPendingDeq_def Let_def
        by blast

      have op_called:
        "OpCalledInHis ?H ?op"
        using DeqCallInHis_imp_OpCalledInHis[OF deq_call_q, of ?x]
        by simp

      have no_HB_from_op:
        "\<forall>x. \<not> HB ?H ?op x"
      proof
        fix x
        show "\<not> HB ?H ?op x"
        proof
          assume hb: "HB ?H ?op x"

          then obtain k1 where
            mr: "match_ret ?H k1 ?op"
            unfolding HB_def
            by blast

          have k1_lt:
            "k1 < length ?H"
            using mr
            unfolding match_ret_def Let_def
            by simp

          have pid_eq:
            "act_pid (?H ! k1) = q"
            using mr
            unfolding match_ret_def Let_def
            by (simp add: mk_op_def op_pid_def)

          have ssn_eq:
            "act_ssn (?H ! k1) = s_var s' q"
            using mr
            unfolding match_ret_def Let_def
            by (simp add: mk_op_def op_ssn_def)

          have cr_eq:
            "act_cr (?H ! k1) = ret"
            using mr
            unfolding match_ret_def Let_def
            by simp

          have in_his:
            "?H ! k1 \<in> set ?H"
            using k1_lt
            by simp

          have no_ret:
            "\<forall>e\<in>set ?H.
               \<not> (act_pid e = q \<and>
                    act_ssn e = s_var s' q \<and>
                    act_cr e = ret)"
            using pending_q
            unfolding HasPendingDeq_def Let_def
            by blast

          show False
            using no_ret in_his pid_eq ssn_eq cr_eq
            by blast
        qed
      qed

      have hb_lin:
        "HB_consistent (lin_seq s') ?H"
        using lI3_HB_Ret_Lin_Sync_s'
        unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def HB_consistent_def
        by simp

      have lI4_list_s':
        "lI4_FIFO_Semantics_list (lin_seq s')"
        using lI4_FIFO_Semantics_s'
        unfolding lI4_FIFO_Semantics_def
        by simp

      have lI5_list_s':
        "lI5_SA_Prefix_list (lin_seq s')"
        using lI5_SA_Prefix_s'
        unfolding lI5_SA_Prefix_def
        by simp

      have x_val:
        "?x \<in> Val"
        using TypeOK_s' qj_q'
        unfolding TypeOK_def
        by auto

      have typeBT_x:
        "TypeBT s' ?x"
        using D3_j_nonBOT_TypeBT_from_local[
          OF sI6_D3_Scan_Pointers_s'
             sI8_Q_Qback_Sync_s'
             sI10_Qback_Unique_Vals_s'
             pc_q' qj_q'
        ] .

      have x_SetB:
        "?x \<in> SetB s'"
        using x_val typeBT_x
        unfolding SetB_def TypeBT_def
        by blast

      have pending_x_lin:
        "\<forall>i < length (lin_seq s').
           op_val (lin_seq s' ! i) = ?x \<longrightarrow>
           op_name (lin_seq s' ! i) \<noteq> deq"
        by (rule SetB_implies_no_deq_in_lin_from_LI2[
              OF lI2_Op_Cardinality_s' x_SetB
            ])

      have enq_exists_x_lin:
        "\<exists>k < length (lin_seq s').
           op_name (lin_seq s' ! k) = enq \<and>
           op_val (lin_seq s' ! k) = ?x"
        by (rule SetB_implies_enq_in_lin_from_LI2[
              OF lI2_Op_Cardinality_s' x_SetB
            ])

      have base_def':
        "?base =
          (if should_modify (lin_seq s') (his_seq s') ?x
           then modify_lin (lin_seq s') (his_seq s') ?x
           else lin_seq s')"
        by simp

      have mset_base_eq:
        "mset ?base = mset (lin_seq s')"
        using D3_base_mset_eq_from_local_invs[OF base_def'] .

      have set_base_eq:
        "set ?base = set (lin_seq s')"
        using mset_base_eq
        by (metis set_mset_mset)

      have all_called_lin:
        "\<forall>a\<in>set (lin_seq s'). OpCalledInHis ?H a"
      proof
        fix a
        assume a_in: "a \<in> set (lin_seq s')"

        have a_oplin:
          "a \<in> OPLin s'"
          using a_in
          unfolding OPLin_def
          by simp

        have cases:
          "a \<in> OP_A_enq s' \<or> a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
          using lI1_Op_Sets_Equivalence_s' a_oplin
          unfolding lI1_Op_Sets_Equivalence_def
          by blast

        thus "OpCalledInHis ?H a"
        proof
          assume "a \<in> OP_A_enq s'"
          then obtain qq vv sn where
            a_eq: "a = mk_op enq vv qq sn"
            and call: "EnqCallInHis s' qq vv sn"
            unfolding OP_A_enq_def
            by blast

          show ?thesis
            using EnqCallInHis_imp_OpCalledInHis[OF call]
            unfolding a_eq
            by simp
        next
          assume rest: "a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
          thus ?thesis
          proof
            assume "a \<in> OP_A_deq s'"

            hence name_deq: "op_name a = deq"
              and call: "DeqCallInHis s' (op_pid a) (op_ssn a)"
              unfolding OP_A_deq_def
              by auto

            have a_mk:
              "mk_op deq (op_val a) (op_pid a) (op_ssn a) = a"
              using name_deq
              by (cases a)
                 (simp add: mk_op_def op_name_def op_val_def op_pid_def op_ssn_def)

            have called_mk:
              "OpCalledInHis ?H
                 (mk_op deq (op_val a) (op_pid a) (op_ssn a))"
              using DeqCallInHis_imp_OpCalledInHis[OF call, of "op_val a"] .

            show ?thesis
              using called_mk a_mk
              by simp
          next
            assume "a \<in> OP_B_enq s'"
            then obtain qq vv sn where
              a_eq: "a = mk_op enq vv qq sn"
              and call: "EnqCallInHis s' qq vv sn"
              unfolding OP_B_enq_def
              by blast

            show ?thesis
              using EnqCallInHis_imp_OpCalledInHis[OF call]
              unfolding a_eq
              by simp
          qed
        qed
      qed

      have hb_base:
        "HB_consistent ?base ?H"
      proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
        case False

        have base_eq:
          "?base = lin_seq s'"
          using False
          by (simp only: if_False)

        show ?thesis
          unfolding base_eq
          using hb_lin .
      next
        case True

        have base_eq:
          "?base = modify_lin (lin_seq s') (his_seq s') ?x"
          using True
          by (simp only: if_True)

        have hb_modify:
          "HB_consistent
             (modify_lin (lin_seq s') (his_seq s') ?x)
             (his_seq s')"
        proof (rule modify_preserves_HB_consistent_from_local_invs[
                 where s = s'
                   and L = "lin_seq s'"
                   and H = "his_seq s'"
                   and bt_val = ?x
               ])
          show "his_seq s' = his_seq s'"
            by simp
        next
          show "HB_consistent (lin_seq s') (his_seq s')"
            using hb_lin .
        next
          show "data_independent (lin_seq s')"
            using di_s' .
        next
          show "TypeBT s' ?x"
            using typeBT_x .
        next
          show "mset (lin_seq s') = mset (lin_seq s')"
            by simp
        next
          show "\<forall>v. in_SA v (lin_seq s') = in_SA v (lin_seq s')"
            by simp
        next
          show "lI1_Op_Sets_Equivalence s'"
            using lI1_Op_Sets_Equivalence_s' .
        next
          show "lI2_Op_Cardinality s'"
            using lI2_Op_Cardinality_s' .
        next
          show "lI4_FIFO_Semantics s'"
            using lI4_FIFO_Semantics_s' .
        next
          show "hI5_SSN_Unique s'"
            using hI5_SSN_Unique_s' .
        next
          show "hI7_His_WF s'"
            using hI7_His_WF_s' .
        next
          show "hI16_BO_BT_No_HB s'"
            using hI16_BO_BT_No_HB_s' .
        next
          show "hI17_BT_BT_No_HB s'"
            using hI17_BT_BT_No_HB_s' .
        next
          show "hI20_Enq_Val_Valid s'"
            using hI20_Enq_Val_Valid_s' .
        qed

        show ?thesis
          unfolding base_eq
          using hb_modify .
      qed

      have hb_final:
        "HB_consistent ?L ?H"
      proof (rule HB_consistent_append)
        show "HB_consistent ?base ?H"
          using hb_base .
      next
        show "\<forall>x\<in>set ?base. \<not> HB ?H ?op x"
          using no_HB_from_op
          by blast
      next
        show "\<not> HB ?H ?op ?op"
          using no_HB_from_op
          by blast
      qed

      have qs_base:
        "QueueSpecLin ?base"
      proof (rule D3_qs_base_from_local_invs[
               where L = "lin_seq s'"
                 and H = "his_seq s'"
                 and v = ?x
                 and base_lin = ?base
             ])
        show "lI4_FIFO_Semantics_list (lin_seq s')"
          using lI4_list_s' .
      next
        show "data_independent (lin_seq s')"
          using di_s' .
      next
        show "lI5_SA_Prefix_list (lin_seq s')"
          using lI5_list_s' .
      next
        show "\<forall>k<length (lin_seq s').
                op_val (lin_seq s' ! k) = ?x \<longrightarrow>
                op_name (lin_seq s' ! k) \<noteq> deq"
          using pending_x_lin .
      next
        show "?base =
              (if should_modify (lin_seq s') (his_seq s') ?x
               then modify_lin (lin_seq s') (his_seq s') ?x
               else lin_seq s')"
          using base_def' .
      qed

      have qs_final:
        "QueueSpecLin ?L"
      proof (rule D3_qs_final_from_local_invs[
               where L = "lin_seq s'"
                 and H = "his_seq s'"
                 and v = ?x
                 and base_lin = ?base
                 and deq_act = ?op
             ])
        show "lI4_FIFO_Semantics_list (lin_seq s')"
          using lI4_list_s' .
      next
        show "data_independent (lin_seq s')"
          using di_s' .
      next
        show "lI5_SA_Prefix_list (lin_seq s')"
          using lI5_list_s' .
      next
        show "\<forall>k<length (lin_seq s').
                op_val (lin_seq s' ! k) = ?x \<longrightarrow>
                op_name (lin_seq s' ! k) \<noteq> deq"
          using pending_x_lin .
      next
        show "\<exists>k<length (lin_seq s').
                op_name (lin_seq s' ! k) = enq \<and>
                op_val (lin_seq s' ! k) = ?x"
          using enq_exists_x_lin .
      next
        show "?base =
              (if should_modify (lin_seq s') (his_seq s') ?x
               then modify_lin (lin_seq s') (his_seq s') ?x
               else lin_seq s')"
          using base_def' .
      next
        show "op_name ?op = deq"
          by (simp add: mk_op_def op_name_def)
      next
        show "op_val ?op = ?x"
          by (simp add: mk_op_def op_val_def)
      qed

      have di_final:
        "data_independent ?L"
      proof (rule D3_di_final_from_local_invs[
               where L = "lin_seq s'"
                 and H = "his_seq s'"
                 and v = ?x
                 and base_lin = ?base
                 and p = q
                 and sn = "s_var s' q"
             ])
        show "data_independent (lin_seq s')"
          using di_s' .
      next
        show "\<forall>k<length (lin_seq s').
                op_val (lin_seq s' ! k) = ?x \<longrightarrow>
                op_name (lin_seq s' ! k) \<noteq> deq"
          using pending_x_lin .
      next
        show "?base =
              (if should_modify (lin_seq s') (his_seq s') ?x
               then modify_lin (lin_seq s') (his_seq s') ?x
               else lin_seq s')"
          using base_def' .
      qed

      have eff_subset:
        "uspec_effOps s' \<subseteq> set ?L"
      proof -
        have old_eff:
          "uspec_effOps s' = set (lin_seq s')"
          using uI1_USpec_EffOps_Lin_s'
          unfolding uI1_USpec_EffOps_Lin_def
          by simp

        have "set (lin_seq s') \<subseteq> set ?base"
          using set_base_eq
          by simp

        thus ?thesis
          using old_eff
          by auto
      qed

      have op_in:
        "?op \<in> set ?L"
        by simp

      have all_called:
        "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
        using all_called_lin set_base_eq op_called
        by auto

      have finite_eff:
        "finite (uspec_effOps s')"
        using uI1_USpec_EffOps_Lin_s'
        unfolding uI1_USpec_EffOps_Lin_def
        by simp

      have gen:
        "USpec_GenLin ?H (uspec_effOps s') ?op ?L"
        unfolding USpec_GenLin_def
      proof (intro conjI)
        show "finite (uspec_effOps s')"
          using finite_eff .
      next
        show "uspec_effOps s' \<subseteq> set ?L"
          using eff_subset .
      next
        show "?op \<in> set ?L"
          using op_in .
      next
        show "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
          using all_called .
      next
        show "HB_consistent ?L ?H"
          using hb_final .
      next
        show "QueueSpecLin ?L"
          using qs_final .
      next
        show "data_independent ?L"
          using di_final .
      qed

      show "let cur_lin = lin_seq s';
                cur_his = his_seq s';
                x_val = Q_arr s' (j_var s' q);
                op = mk_op deq x_val q (s_var s' q);
                new_lin =
                  (if should_modify cur_lin cur_his x_val
                   then modify_lin cur_lin cur_his x_val
                   else cur_lin) @ [op]
            in USpec_GenLin cur_his (uspec_effOps s') op new_lin"
        using gen
        by (simp only: Let_def)
    qed


     have sys_inv_s': "system_invariant s'"
       unfolding system_invariant_def
       using Simulate_PC_s' TypeOK_s'
         sI1_Zero_Index_BOT_s' sI2_X_var_Upper_Bound_s' sI3_E2_Slot_Exclusive_s' sI4_E3_Qback_Written_s' sI5_D2_Local_Bound_s' sI6_D3_Scan_Pointers_s' sI7_D4_Deq_Result_s' hI3_L0_E_Phase_Bounds_s' sI8_Q_Qback_Sync_s' sI9_Qback_Discrepancy_E3_s' sI10_Qback_Unique_Vals_s' hI2_SSN_Bounds_s' sI11_x_var_Scope_s' hI1_E_Phase_Pending_Enq_s' sI12_D3_Scanned_Prefix_s' hI4_X_var_Lin_Sync_s'
         hI7_His_WF_s' hI5_SSN_Unique_s' hI6_SSN_Order_s' hI8_Val_Unique_s'
         hI9_Deq_Ret_Unique_s' hI10_Enq_Call_Existence_s' hI11_Enq_Ret_Existence_s' hI12_D_Phase_Pending_Deq_s' hI13_Qback_Deq_Sync_s' hI14_Pending_Enq_Qback_Exclusivity_s' hI15_Deq_Result_Exclusivity_s' hI16_BO_BT_No_HB_s' hI17_BT_BT_No_HB_s' hI18_Idx_Order_No_Rev_HB_s' hI19_Scanner_Catches_Later_Enq_s'
         hI20_Enq_Val_Valid_s' hI21_Ret_Implies_Call_s' hI22_Deq_Local_Pattern_s' hI23_Deq_Call_Ret_Balanced_s' hI24_HB_Implies_Idx_Order_s' hI25_Enq_Call_Ret_Balanced_s' hI26_DeqRet_D4_Mutex_s'
         hI27_Pending_PC_Sync_s' hI28_Fresh_Enq_Immunity_s' hI29_E2_Scanner_Immunity_s' hI30_Ticket_HB_Immunity_s'
         lI1_Op_Sets_Equivalence_s' lI2_Op_Cardinality_s' lI3_HB_Ret_Lin_Sync_s' lI4_FIFO_Semantics_s' lI5_SA_Prefix_s' lI6_D4_Deq_Linearized_s' lI7_D4_Deq_Deq_HB_s' lI8_D3_Deq_Returned_s' lI9_D1_D2_Deq_Returned_s' lI10_D4_Enq_Deq_HB_s' lI11_D4_Deq_Unique_s' uI1_USpec_EffOps_Lin_s' uI2_USpec_E1UE2_s' uI3_USpec_D3UD2_s' di_s'
       by simp
     show ?thesis
       using sys_inv_s'
       by simp
qed

(* Source of the lifted proof block: L0Proof.thy, L0_preserves_invariant, D1. *)
(* Original source location: approximately lines 1, 1. *)
(* Note: the following proof script was moved here from the original file without proof-level changes. *)
lemma L0_D1_preserves_invariant_branch:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "L0 p s s'"
  assumes D1: "program_counter s' p = ''D1''"
  shows "system_invariant s'"
proof -
  note bridge_defs =
    program_counter_def X_var_def V_var_def Q_arr_def Qback_arr_def
    i_var_def j_var_def l_var_def x_var_def v_var_def
    s_var_def lin_seq_def his_seq_def

  (* Prove the required intermediate property. Related symbols: system_invariant. *)
  have Simulate_PC_s: "Simulate_PC s"
    and TypeOK_s: "TypeOK s"
    and sI1_Zero_Index_BOT_s: "sI1_Zero_Index_BOT s"
    and sI2_X_var_Upper_Bound_s: "sI2_X_var_Upper_Bound s" and sI3_E2_Slot_Exclusive_s: "sI3_E2_Slot_Exclusive s" and sI4_E3_Qback_Written_s: "sI4_E3_Qback_Written s"
    and sI5_D2_Local_Bound_s: "sI5_D2_Local_Bound s" and sI6_D3_Scan_Pointers_s: "sI6_D3_Scan_Pointers s" and sI7_D4_Deq_Result_s: "sI7_D4_Deq_Result s" and hI3_L0_E_Phase_Bounds_s: "hI3_L0_E_Phase_Bounds s"
    and sI8_Q_Qback_Sync_s: "sI8_Q_Qback_Sync s" and sI9_Qback_Discrepancy_E3_s: "sI9_Qback_Discrepancy_E3 s" and sI10_Qback_Unique_Vals_s: "sI10_Qback_Unique_Vals s"
    and hI2_SSN_Bounds_s: "hI2_SSN_Bounds s" and sI11_x_var_Scope_s: "sI11_x_var_Scope s" and hI1_E_Phase_Pending_Enq_s: "hI1_E_Phase_Pending_Enq s" and sI12_D3_Scanned_Prefix_s: "sI12_D3_Scanned_Prefix s"
    and hI4_X_var_Lin_Sync_s: "hI4_X_var_Lin_Sync s"
    and hI7_His_WF_s: "hI7_His_WF s"
    and hI5_SSN_Unique_s: "hI5_SSN_Unique s"
    and hI6_SSN_Order_s: "hI6_SSN_Order s"
    and hI8_Val_Unique_s: "hI8_Val_Unique s"
    and hI9_Deq_Ret_Unique_s: "hI9_Deq_Ret_Unique s" and hI10_Enq_Call_Existence_s: "hI10_Enq_Call_Existence s" and hI11_Enq_Ret_Existence_s: "hI11_Enq_Ret_Existence s" and hI12_D_Phase_Pending_Deq_s: "hI12_D_Phase_Pending_Deq s"
    and hI13_Qback_Deq_Sync_s: "hI13_Qback_Deq_Sync s" and hI14_Pending_Enq_Qback_Exclusivity_s: "hI14_Pending_Enq_Qback_Exclusivity s" and hI15_Deq_Result_Exclusivity_s: "hI15_Deq_Result_Exclusivity s" and hI16_BO_BT_No_HB_s: "hI16_BO_BT_No_HB s"
    and hI17_BT_BT_No_HB_s: "hI17_BT_BT_No_HB s" and hI18_Idx_Order_No_Rev_HB_s: "hI18_Idx_Order_No_Rev_HB s" and hI19_Scanner_Catches_Later_Enq_s: "hI19_Scanner_Catches_Later_Enq s"
    and hI20_Enq_Val_Valid_s: "hI20_Enq_Val_Valid s" and hI21_Ret_Implies_Call_s: "hI21_Ret_Implies_Call s" and hI22_Deq_Local_Pattern_s: "hI22_Deq_Local_Pattern s" and hI23_Deq_Call_Ret_Balanced_s: "hI23_Deq_Call_Ret_Balanced s"
    and hI24_HB_Implies_Idx_Order_s: "hI24_HB_Implies_Idx_Order s" and hI25_Enq_Call_Ret_Balanced_s: "hI25_Enq_Call_Ret_Balanced s" and hI26_DeqRet_D4_Mutex_s: "hI26_DeqRet_D4_Mutex s"
    and hI27_Pending_PC_Sync_s: "hI27_Pending_PC_Sync s"
    and hI28_Fresh_Enq_Immunity_s: "hI28_Fresh_Enq_Immunity s"
    and hI29_E2_Scanner_Immunity_s: "hI29_E2_Scanner_Immunity s"
    and hI30_Ticket_HB_Immunity_s: "hI30_Ticket_HB_Immunity s"
    and lI1_Op_Sets_Equivalence_s: "lI1_Op_Sets_Equivalence s" and lI2_Op_Cardinality_s: "lI2_Op_Cardinality s" and lI3_HB_Ret_Lin_Sync_s: "lI3_HB_Ret_Lin_Sync s"
    and lI4_FIFO_Semantics_s: "lI4_FIFO_Semantics s" and lI5_SA_Prefix_s: "lI5_SA_Prefix s"
    and lI6_D4_Deq_Linearized_s: "lI6_D4_Deq_Linearized s" and lI7_D4_Deq_Deq_HB_s: "lI7_D4_Deq_Deq_HB s" and lI8_D3_Deq_Returned_s: "lI8_D3_Deq_Returned s"
    and lI9_D1_D2_Deq_Returned_s: "lI9_D1_D2_Deq_Returned s" and lI10_D4_Enq_Deq_HB_s: "lI10_D4_Enq_Deq_HB s" and lI11_D4_Deq_Unique_s: "lI11_D4_Deq_Unique s"
    and uI1_USpec_EffOps_Lin_s: "uI1_USpec_EffOps_Lin s"
    and uI2_USpec_E1UE2_s: "uI2_USpec_E1UE2 s"
    and uI3_USpec_D3UD2_s: "uI3_USpec_D3UD2 s"
    and di_s: "data_independent (lin_seq s)"
    using INV unfolding system_invariant_def by auto

  have pc_L0: "program_counter s p = ''L0''"
    and Simulate_PC_s': "Simulate_PC s'"
    using L0_step_facts[OF STEP] by auto
    have s'_def: "s' = L0_D1_update_state s p"
      using L0_D1_state[OF STEP D1] .
    have his_eq: "his_seq s' = his_seq s @ [mk_act deq BOT p (s_var s p) call]"
      using L0_D1_history_append[OF STEP D1] .
    have ssn_eq_D1: "s_var s' q = s_var s q" for q
      using s'_def
      unfolding L0_D1_update_state_def s_var_def
      by (auto simp: Let_def)
    have lin_seq_eq: "lin_seq s' = lin_seq s"
      using L0_D1_lin_unchanged[OF STEP D1] .
    have pc_eq_D1: "program_counter s' q = (if q = p then ''D1'' else program_counter s q)" for q
      using s'_def
      unfolding L0_D1_update_state_def program_counter_def
      by (auto simp: Let_def)
    have v_eq_D1: "v_var s' q = v_var s q" for q
      using s'_def
      unfolding L0_D1_update_state_def v_var_def
      by (auto simp: Let_def)
    have i_eq_D1: "i_var s' q = i_var s q" for q
      using s'_def
      unfolding L0_D1_update_state_def i_var_def
      by (auto simp: Let_def)
    have j_eq_D1: "j_var s' q = j_var s q" for q
      using s'_def
      unfolding L0_D1_update_state_def j_var_def
      by (auto simp: Let_def)
    have l_eq_D1: "l_var s' q = l_var s q" for q
      using s'_def
      unfolding L0_D1_update_state_def l_var_def
      by (auto simp: Let_def)
    have x_eq_D1: "x_var s' q = x_var s q" for q
      using s'_def
      unfolding L0_D1_update_state_def x_var_def
      by (auto simp: Let_def)
    have qarr_eq_D1: "Q_arr s' k = Q_arr s k" for k
      using s'_def
      unfolding L0_D1_update_state_def Q_arr_def
      by (auto simp: Let_def)
    have qback_eq_D1: "Qback_arr s' k = Qback_arr s k" for k
      using s'_def
      unfolding L0_D1_update_state_def Qback_arr_def
      by (auto simp: Let_def)
    have QHas_eq_D1: "QHas s' a \<longleftrightarrow> QHas s a" for a
      unfolding QHas_def using qarr_eq_D1 by auto
    have InQBack_eq_D1: "InQBack s' a \<longleftrightarrow> InQBack s a" for a
      unfolding InQBack_def using qback_eq_D1 by auto
    have AtIdx_eq_D1: "AtIdx s' a k \<longleftrightarrow> AtIdx s a k" for a k
      unfolding AtIdx_def using qback_eq_D1 by auto
    have Idx_eq_D1: "Idx s' a = Idx s a" for a
      unfolding Idx_def AtIdx_def using qback_eq_D1 by simp
    have TypeA_eq_D1: "TypeA s' a \<longleftrightarrow> TypeA s a" for a
      unfolding TypeA_def using InQBack_eq_D1[of a] QHas_eq_D1[of a] by simp
    have TypeB_eq_D1: "TypeB s' a \<longleftrightarrow> TypeB s a" for a
      unfolding TypeB_def using QHas_eq_D1[of a] by simp
    have SetA_eq_D1: "SetA s' = SetA s"
      unfolding SetA_def using TypeA_eq_D1 by auto
    have SetB_eq_D1: "SetB s' = SetB s"
      unfolding SetB_def using TypeB_eq_D1 by auto
    have pc_D3_eq_D1: "program_counter s' q = ''D3'' \<longleftrightarrow> program_counter s q = ''D3''" for q
    proof
      assume qD3': "program_counter s' q = ''D3''"
      show "program_counter s q = ''D3''"
      proof (cases "q = p")
        case True
        with qD3' pc_eq_D1[of q] show ?thesis
          by simp
      next
        case False
        with qD3' pc_eq_D1[of q] show ?thesis
          by simp
      qed
    next
      assume qD3: "program_counter s q = ''D3''"
      show "program_counter s' q = ''D3''"
      proof (cases "q = p")
        case True
        with qD3 pc_L0 show ?thesis
          by simp
      next
        case False
        with qD3 pc_eq_D1[of q] show ?thesis
          by simp
      qed
    qed
    have D3Block_eq_D1:
      "(\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT) \<longleftrightarrow>
       (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)" for pa a
    proof
      assume block': "\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
      show "\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT"
      proof (intro allI impI)
        fix k
        assume bounds_k: "j_var s pa \<le> k \<and> k < Idx s a"
        have bounds_k': "j_var s' pa \<le> k \<and> k < Idx s' a"
          using bounds_k Idx_eq_D1[of a] j_eq_D1[of pa] by simp
        have block'_k: "j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
          using block' by (rule spec)
        have "Q_arr s' k = BOT"
          using block'_k bounds_k' by simp
        then show "Q_arr s k = BOT"
          using qarr_eq_D1[of k] by simp
      qed
    next
      assume block: "\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT"
      show "\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
      proof (intro allI impI)
        fix k
        assume bounds_k': "j_var s' pa \<le> k \<and> k < Idx s' a"
        have bounds_k: "j_var s pa \<le> k \<and> k < Idx s a"
          using bounds_k' Idx_eq_D1[of a] j_eq_D1[of pa] by simp
        have block_k: "j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT"
          using block by (rule spec)
        have "Q_arr s k = BOT"
          using block_k bounds_k by simp
        then show "Q_arr s' k = BOT"
          using qarr_eq_D1[of k] by simp
      qed
    qed
    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_d3_witness_eq. *)
    have D3Witness_eq_D1:
      "(\<exists>pa. program_counter s' pa = ''D3'' \<and>
            j_var s' pa \<le> Idx s' a \<and> Idx s' a < l_var s' pa \<and>
            (\<forall>k. j_var s' pa \<le> k \<and> k < Idx s' a \<longrightarrow> Q_arr s' k = BOT)) \<longleftrightarrow>
       (\<exists>pa. program_counter s pa = ''D3'' \<and>
            j_var s pa \<le> Idx s a \<and> Idx s a < l_var s pa \<and>
            (\<forall>k. j_var s pa \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT))" for a
      using L0_D1_d3_witness_eq[
        OF pc_D3_eq_D1 Idx_eq_D1 j_eq_D1 l_eq_D1 D3Block_eq_D1, of a
      ] .
    have PrefixBOT_eq_D1: "(\<forall>k<Idx s' a. Q_arr s' k = BOT) \<longleftrightarrow> (\<forall>k<Idx s a. Q_arr s k = BOT)" for a
    proof
      assume pref': "\<forall>k<Idx s' a. Q_arr s' k = BOT"
      show "\<forall>k<Idx s a. Q_arr s k = BOT"
      proof (intro allI impI)
        fix k
        assume k_lt: "k < Idx s a"
        have k_lt': "k < Idx s' a"
          using k_lt Idx_eq_D1[of a] by simp
        have pref'_k: "k < Idx s' a \<longrightarrow> Q_arr s' k = BOT"
        proof
          assume k_lt'': "k < Idx s' a"
          from pref' and k_lt'' show "Q_arr s' k = BOT"
            by simp
        qed
        have "Q_arr s' k = BOT"
          using pref'_k k_lt' by simp
        then show "Q_arr s k = BOT"
          using qarr_eq_D1[of k] by simp
      qed
    next
      assume pref: "\<forall>k<Idx s a. Q_arr s k = BOT"
      show "\<forall>k<Idx s' a. Q_arr s' k = BOT"
      proof (intro allI impI)
        fix k
        assume k_lt': "k < Idx s' a"
        have k_lt: "k < Idx s a"
          using k_lt' Idx_eq_D1[of a] by simp
        have pref_k: "k < Idx s a \<longrightarrow> Q_arr s k = BOT"
        proof
          assume k_lt'': "k < Idx s a"
          from pref and k_lt'' show "Q_arr s k = BOT"
            by simp
        qed
        have "Q_arr s k = BOT"
          using pref_k k_lt by simp
        then show "Q_arr s' k = BOT"
          using qarr_eq_D1[of k] by simp
      qed
    qed
    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_typebt_eq. *)
    have TypeBT_eq_D1: "TypeBT s' a \<longleftrightarrow> TypeBT s a" for a
      using L0_D1_typebt_eq[
        OF TypeB_eq_D1 InQBack_eq_D1 PrefixBOT_eq_D1 D3Witness_eq_D1, of a
      ] .
    have TypeBO_eq_D1: "TypeBO s' a \<longleftrightarrow> TypeBO s a" for a
      unfolding TypeBO_def
      using TypeB_eq_D1[of a] TypeBT_eq_D1[of a]
      by simp
    have SetBT_eq_D1: "SetBT s' = SetBT s"
      unfolding SetBT_def using TypeBT_eq_D1 by auto
    have SetBO_eq_D1: "SetBO s' = SetBO s"
      unfolding SetBO_def using TypeBO_eq_D1 by auto

    have TypeOK_s': "TypeOK s'"
      using TypeOK_s s'_def
      unfolding TypeOK_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI1_Zero_Index_BOT_s': "sI1_Zero_Index_BOT s'"
      using sI1_Zero_Index_BOT_s s'_def
      unfolding sI1_Zero_Index_BOT_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI2_X_var_Upper_Bound_s': "sI2_X_var_Upper_Bound s'"
      using sI2_X_var_Upper_Bound_s s'_def
      unfolding sI2_X_var_Upper_Bound_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI3_E2_Slot_Exclusive_s': "sI3_E2_Slot_Exclusive s'"
      using sI3_E2_Slot_Exclusive_s pc_L0 s'_def
      unfolding sI3_E2_Slot_Exclusive_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI4_E3_Qback_Written_s': "sI4_E3_Qback_Written s'"
      using sI4_E3_Qback_Written_s pc_L0 s'_def
      unfolding sI4_E3_Qback_Written_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI5_D2_Local_Bound_s': "sI5_D2_Local_Bound s'"
      using sI5_D2_Local_Bound_s pc_L0 s'_def
      unfolding sI5_D2_Local_Bound_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI6_D3_Scan_Pointers_s': "sI6_D3_Scan_Pointers s'"
      using sI6_D3_Scan_Pointers_s pc_L0 s'_def
      unfolding sI6_D3_Scan_Pointers_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI7_D4_Deq_Result_s': "sI7_D4_Deq_Result s'"
      using sI7_D4_Deq_Result_s pc_L0 s'_def
      unfolding sI7_D4_Deq_Result_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have hI3_L0_E_Phase_Bounds_s': "hI3_L0_E_Phase_Bounds s'"
      using hI3_L0_E_Phase_Bounds_L0_to_D1[OF hI3_L0_E_Phase_Bounds_s pc_L0 s'_def] .

    have sI8_Q_Qback_Sync_s': "sI8_Q_Qback_Sync s'"
      using sI8_Q_Qback_Sync_s s'_def
      unfolding sI8_Q_Qback_Sync_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI9_Qback_Discrepancy_E3_s': "sI9_Qback_Discrepancy_E3 s'"
      using sI9_Qback_Discrepancy_E3_s s'_def
      unfolding sI9_Qback_Discrepancy_E3_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have sI10_Qback_Unique_Vals_s': "sI10_Qback_Unique_Vals s'"
      using sI10_Qback_Unique_Vals_s s'_def
      unfolding sI10_Qback_Unique_Vals_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs)

    have hI2_SSN_Bounds_s': "hI2_SSN_Bounds s'"
    proof -
      show ?thesis
      proof (unfold hI2_SSN_Bounds_def, intro allI ballI impI)
        fix q e
        assume e_in': "e \<in> set (his_seq s')"
        assume e_pid_q: "act_pid e = q"
        let ?new = "mk_act deq BOT p (s_var s p) call"
        have e_old_or_new: "e \<in> set (his_seq s) \<or> e = ?new"
          using his_eq e_in' by auto
        show "act_ssn e \<le> s_var s' q \<and> (program_counter s' q = ''L0'' \<longrightarrow> act_ssn e < s_var s' q)"
        proof (cases "e \<in> set (his_seq s)")
          case True
          then have old_bound:
            "act_ssn e \<le> s_var s q \<and>
             (program_counter s q = ''L0'' \<longrightarrow> act_ssn e < s_var s q)"
            using hI2_SSN_Bounds_s e_pid_q unfolding hI2_SSN_Bounds_def by blast
          have le_old: "act_ssn e \<le> s_var s' q"
            using old_bound ssn_eq_D1[of q] by simp
          have strict_old: "program_counter s' q = ''L0'' \<longrightarrow> act_ssn e < s_var s' q"
          proof
            assume qL0': "program_counter s' q = ''L0''"
            have q_ne_p: "q \<noteq> p"
              using qL0' pc_eq_D1[of q] by auto
            have old_pc: "program_counter s q = ''L0''"
              using qL0' q_ne_p pc_eq_D1[of q] by simp
            from old_bound old_pc have "act_ssn e < s_var s q"
              by blast
            with ssn_eq_D1[of q] show "act_ssn e < s_var s' q"
              by simp
          qed
          show ?thesis
            using le_old strict_old
            by simp
        next
          case False
          with e_old_or_new have e_new: "e = ?new"
            by auto
          have q_eq_p: "q = p"
            using e_pid_q e_new
            by (simp add: mk_act_def act_pid_def)
          have le_new: "act_ssn e \<le> s_var s' q"
            using e_new q_eq_p ssn_eq_D1[of q]
            by (simp add: mk_act_def act_ssn_def)
          have not_L0: "program_counter s' q = ''L0'' \<Longrightarrow> False"
            using q_eq_p pc_eq_D1[of p]
            by simp
          show ?thesis
            using le_new not_L0 by blast
        qed
      qed
    qed

    have sI11_x_var_Scope_s': "sI11_x_var_Scope s'"
    proof (unfold sI11_x_var_Scope_def, intro allI impI)
      fix q
      assume q_pc': "program_counter s' q \<noteq> ''D4''"
      show "x_var s' q = BOT"
      proof (cases "q = p")
        case True
        have qL0: "program_counter s q = ''L0''"
          using pc_L0 True by simp
        hence "program_counter s q \<noteq> ''D4''"
          by simp
        hence "x_var s q = BOT"
          using sI11_x_var_Scope_s unfolding sI11_x_var_Scope_def by blast
        then show ?thesis
          using True s'_def
          unfolding L0_D1_update_state_def bridge_defs
          by (auto simp: Let_def)
      next
        case False
        have pc_eq: "program_counter s q = program_counter s' q"
          using False s'_def
          unfolding L0_D1_update_state_def bridge_defs
          by (auto simp: Let_def)
        then have q_pc: "program_counter s q \<noteq> ''D4''"
          using q_pc' by simp
        have "x_var s q = BOT"
          using sI11_x_var_Scope_s q_pc
          unfolding sI11_x_var_Scope_def
          by blast
        then show ?thesis
          using False s'_def
          unfolding L0_D1_update_state_def bridge_defs
          by (auto simp: Let_def)
      qed
    qed

    have hI1_E_Phase_Pending_Enq_s': "hI1_E_Phase_Pending_Enq s'"
      using hI1_E_Phase_Pending_Enq_s s'_def
      unfolding hI1_E_Phase_Pending_Enq_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs HasPendingEnq_append_deq_call_iff)

    have sI12_D3_Scanned_Prefix_s': "sI12_D3_Scanned_Prefix s'"
    proof (unfold sI12_D3_Scanned_Prefix_def, intro allI impI)
      fix pa k
      assume paD3': "program_counter s' pa = ''D3''"
      assume k_lt: "k < j_var s' pa"
      have paD3: "program_counter s pa = ''D3''"
        using paD3' pc_D3_eq_D1[of pa] by simp
      have old_case: "Q_arr s k = BOT \<or> TypeB s (Q_arr s k)"
        using sI12_D3_Scanned_Prefix_s paD3 k_lt
        unfolding sI12_D3_Scanned_Prefix_def
        using j_eq_D1[of pa] by simp
      show "Q_arr s' k = BOT \<or> TypeB s' (Q_arr s' k)"
        using old_case qarr_eq_D1[of k] TypeB_eq_D1[of "Q_arr s k"]
        by simp
    qed

    have hI4_X_var_Lin_Sync_s': "hI4_X_var_Lin_Sync s'"
    proof -
      have x_eq: "X_var s' = X_var s"
        using s'_def
        unfolding L0_D1_update_state_def X_var_def
        by (auto simp: Let_def bridge_defs)
      have cnt_eq: "LinEnqCount s' (length (lin_seq s')) = LinEnqCount s (length (lin_seq s))"
        using lin_seq_eq
        unfolding LinEnqCount_def lin_seq_def
        by (simp add: bridge_defs)
      have pc_E2_eq: "\<And>q. program_counter s' q = ''E2'' \<longleftrightarrow> program_counter s q = ''E2''"
        using pc_eq_D1 pc_L0 by auto
      have slots_eq: "E2SlotCount s' = E2SlotCount s"
        apply (rule E2SlotCount_cong)
        using x_eq apply simp
        using pc_E2_eq apply simp
        using i_eq_D1 apply simp
        done
      show ?thesis
        using hI4_X_var_Lin_Sync_s x_eq cnt_eq slots_eq
        unfolding hI4_X_var_Lin_Sync_def
        by simp
    qed


    have hI7_His_WF_s': "hI7_His_WF s'"
      using hI7_His_WF_append_call[OF hI7_His_WF_s his_eq]
      by (simp add: mk_act_def act_cr_def)

    have hI8_Val_Unique_s': "hI8_Val_Unique s'"
      using hI8_Val_Unique_append_non_enq_call[OF hI8_Val_Unique_s his_eq]
      by (auto simp: mk_act_def act_name_def act_cr_def)

    have ai11_p:
      "\<forall>ev \<in> set (his_seq s).
         act_pid ev = p \<longrightarrow>
         (act_ssn ev \<le> s_var s p \<and>
          (program_counter s p = ''L0'' \<longrightarrow> act_ssn ev < s_var s p))"
      using hI2_SSN_Bounds_s
      unfolding hI2_SSN_Bounds_def
      by blast

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_ssn_unique. *)
    have hI5_SSN_Unique_s': "hI5_SSN_Unique s'"
      using L0_D1_ssn_unique[
        OF hI5_SSN_Unique_s his_eq ai11_p pc_L0
      ] .

    have hI6_SSN_Order_s': "hI6_SSN_Order s'"
    proof (unfold hI6_SSN_Order_def, intro allI impI)
      fix i j
      assume i_lt: "i < length (his_seq s')" and j_lt: "j < length (his_seq s')"
      assume props_raw: "i < j \<and> act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
      let ?L = "length (his_seq s)"
      have len': "length (his_seq s') = Suc ?L"
        using his_eq by simp
      have ij: "i < j"
        and pid_eq: "act_pid (his_seq s' ! i) = act_pid (his_seq s' ! j)"
        using props_raw by auto
      consider (both_old) "j < ?L"
        | (i_old_j_new) "i < ?L" "j = ?L"
        using i_lt j_lt ij len' by linarith
      then show
        "act_ssn (his_seq s' ! i) < act_ssn (his_seq s' ! j) \<or>
         (act_ssn (his_seq s' ! i) = act_ssn (his_seq s' ! j) \<and>
          act_cr (his_seq s' ! i) = call \<and> act_cr (his_seq s' ! j) = ret)"
      proof cases
        case both_old
        have i_old: "i < length (his_seq s)"
          using both_old ij by linarith
        have i_old_eq: "his_seq s' ! i = his_seq s ! i"
          using his_eq i_old
          by (simp add: nth_append)
        have j_old_eq: "his_seq s' ! j = his_seq s ! j"
          using his_eq both_old
          by (simp add: nth_append)
        have pid_old: "act_pid (his_seq s ! i) = act_pid (his_seq s ! j)"
          using pid_eq i_old_eq j_old_eq
          by simp
        have old_order:
          "act_ssn (his_seq s ! i) < act_ssn (his_seq s ! j) \<or>
           (act_ssn (his_seq s ! i) = act_ssn (his_seq s ! j) \<and>
            act_cr (his_seq s ! i) = call \<and> act_cr (his_seq s ! j) = ret)"
          using hI6_SSN_Order_s[unfolded hI6_SSN_Order_def, rule_format, OF i_old both_old]
            ij pid_old
          by blast
        then show ?thesis
          using old_order i_old_eq j_old_eq
          by simp
      next
        case i_old_j_new
        have j_new: "his_seq s' ! j = mk_act deq BOT p (s_var s p) call"
          using his_eq i_old_j_new by (simp add: nth_append)
        then have pid_j: "act_pid (his_seq s' ! j) = p"
          and ssn_j: "act_ssn (his_seq s' ! j) = s_var s p"
          by (simp_all add: mk_act_def act_pid_def act_ssn_def)
        have i_old: "his_seq s' ! i = his_seq s ! i"
          using his_eq i_old_j_new by (simp add: nth_append)
        have i_in: "his_seq s ! i \<in> set (his_seq s)"
          using i_old_j_new by simp
        have pid_i: "act_pid (his_seq s ! i) = p"
          using pid_eq pid_j i_old by simp
        have "act_ssn (his_seq s ! i) < s_var s p"
          using ai11_p i_in pid_i pc_L0
          by blast
        then show ?thesis
          using i_old ssn_j by simp
      qed
    qed

   have hI9_Deq_Ret_Unique_s': "hI9_Deq_Ret_Unique s'"
  using hI9_Deq_Ret_Unique_append_call_event_simple[OF hI9_Deq_Ret_Unique_s his_eq]
  by (simp add: mk_act_def act_cr_def)

have hI10_Enq_Call_Existence_s': "hI10_Enq_Call_Existence s'"
proof (unfold hI10_Enq_Call_Existence_def, intro conjI)
  show "\<forall>pa a. (program_counter s' pa \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' pa = a) \<longrightarrow>
               Model.EnqCallInHis s' pa a (s_var s' pa)"
  proof (intro allI impI)
    fix pa a
    assume pcv': "program_counter s' pa \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s' pa = a"
    have pend': "HasPendingEnq s' pa a"
      using hI1_E_Phase_Pending_Enq_s' pcv'
      unfolding hI1_E_Phase_Pending_Enq_def
      by blast
    then show "Model.EnqCallInHis s' pa a (s_var s' pa)"
      unfolding HasPendingEnq_def Let_def
      by blast
  qed
  show "\<forall>a. a \<in> Val \<and> (\<exists>k. Qback_arr s' k = a) \<longrightarrow>
            (\<exists>q sn. Model.EnqCallInHis s' q a sn)"
  proof (intro allI impI)
    fix a
    assume PRE: "a \<in> Val \<and> (\<exists>k. Qback_arr s' k = a)"
    then have A_VAL: "a \<in> Val" and qb': "\<exists>k. Qback_arr s' k = a"
      by blast+
    have qb_old: "\<exists>k. Qback_arr s k = a"
      using qb' qback_eq_D1
      by auto
    then obtain q sn where old_enq: "Model.EnqCallInHis s q a sn"
      using hI10_Enq_Call_Existence_s A_VAL
      unfolding hI10_Enq_Call_Existence_def
      by blast
    have new_enq: "Model.EnqCallInHis s' q a sn"
      using old_enq his_eq
      unfolding Model.EnqCallInHis_def
      by auto
    show "\<exists>q sn. Model.EnqCallInHis s' q a sn"
      using new_enq by blast
  qed
qed

have hI11_Enq_Ret_Existence_s': "hI11_Enq_Ret_Existence s'"
proof (unfold hI11_Enq_Ret_Existence_def, intro allI impI)
  fix pa a sn
  assume cond':
    "(program_counter s' pa \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s' pa \<noteq> a \<or> s_var s' pa \<noteq> sn) \<and>
     (\<exists>k. Qback_arr s' k = a) \<and>
     Model.EnqCallInHis s' pa a sn"
  have qback_old: "\<exists>k. Qback_arr s k = a"
    using cond' qback_eq_D1 by auto
  have old_pcv:
    "program_counter s pa \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s pa \<noteq> a \<or> s_var s pa \<noteq> sn"
  proof (cases "pa = p")
    case True
    then show ?thesis
      using pc_L0 by simp
  next
    case False
    from cond' show ?thesis
      using False pc_eq_D1[of pa] v_eq_D1[of pa] ssn_eq_D1[of pa] by auto
  qed
  have enq_old: "Model.EnqCallInHis s pa a sn"
  proof -
    have enq': "Model.EnqCallInHis s' pa a sn"
      using cond'
      by simp
    show ?thesis
      using enq' his_eq
      unfolding Model.EnqCallInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  qed
  have ret_old: "Model.EnqRetInHis s pa a sn"
    using hI11_Enq_Ret_Existence_s old_pcv qback_old enq_old
    unfolding hI11_Enq_Ret_Existence_def by blast
  have ret_iff: "Model.EnqRetInHis s' pa a sn \<longleftrightarrow> Model.EnqRetInHis s pa a sn"
    using his_eq
    unfolding Model.EnqRetInHis_def
    by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
  show "Model.EnqRetInHis s' pa a sn"
    using ret_iff ret_old
    by blast
qed

have hI12_D_Phase_Pending_Deq_s': "hI12_D_Phase_Pending_Deq s'"
proof (unfold hI12_D_Phase_Pending_Deq_def, intro allI impI)
  fix pa
  assume paD': "program_counter s' pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
  show "HasPendingDeq s' pa"
  proof (cases "pa = p")
    case True
    have call_in_new: "Model.DeqCallInHis s' p (s_var s' p)"
      using his_eq ssn_eq_D1[of p]
      unfolding Model.DeqCallInHis_def
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    have no_ret_cur_p_old:
      "\<forall>e \<in> set (his_seq s). \<not> (act_pid e = p \<and> act_ssn e = s_var s p \<and> act_cr e = ret)"
      using L0_no_ret_at_current_ssn[OF hI2_SSN_Bounds_s pc_L0] .
    have no_ret_cur_p_new:
      "\<forall>e \<in> set (his_seq s'). \<not> (act_pid e = p \<and> act_ssn e = s_var s' p \<and> act_cr e = ret)"
      using no_ret_cur_p_old his_eq ssn_eq_D1[of p]
      by (auto simp: mk_act_def act_pid_def act_ssn_def act_cr_def)
    show ?thesis
      using True call_in_new no_ret_cur_p_new
      unfolding HasPendingDeq_def Let_def by simp
  next
    case False
    have paD: "program_counter s pa \<in> {''D1'', ''D2'', ''D3'', ''D4''}"
      using paD' False pc_eq_D1[of pa] by auto
    have pending_old: "HasPendingDeq s pa"
      using hI12_D_Phase_Pending_Deq_s paD unfolding hI12_D_Phase_Pending_Deq_def by blast
    have pending_eq: "HasPendingDeq s' pa \<longleftrightarrow> HasPendingDeq s pa"
      using HasPendingDeq_append_deq_call_other_iff[OF his_eq False ssn_eq_D1[of pa]] .
    show ?thesis
      using pending_old pending_eq by blast
  qed
qed

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_qback_deq_sync. *)
    have hI13_Qback_Deq_Sync_s': "hI13_Qback_Deq_Sync s'"
      using L0_D1_qback_deq_sync[
        OF hI13_Qback_Deq_Sync_s qarr_eq_D1 qback_eq_D1 pc_L0 pc_eq_D1 x_eq_D1 his_eq
      ] .

    have hI14_Pending_Enq_Qback_Exclusivity_s': "hI14_Pending_Enq_Qback_Exclusivity s'"
    proof (unfold hI14_Pending_Enq_Qback_Exclusivity_def, intro conjI allI impI)
      fix q a
      assume hq': "HasPendingEnq s' q a \<and> program_counter s' q \<in> {''E2'', ''E3''}"
      then have pend': "HasPendingEnq s' q a"
        and pc_oldish: "program_counter s' q \<in> {''E2'', ''E3''}"
        by auto
      have q_ne_p: "q \<noteq> p"
        using pc_oldish pc_eq_D1[of q] by auto
      have pend: "HasPendingEnq s q a"
        using HasPendingEnq_append_deq_call_iff[OF his_eq ssn_eq_D1[of q]] pend'
        by simp
      have pc_old: "program_counter s q \<in> {''E2'', ''E3''}"
        using pc_oldish q_ne_p pc_eq_D1[of q] by auto
      have old_no_qback: "\<not> (\<exists>k. Qback_arr s k = a \<and> k \<noteq> i_var s q)"
        using hI14_Pending_Enq_Qback_Exclusivity_s pend pc_old
        unfolding hI14_Pending_Enq_Qback_Exclusivity_def by auto
      show "\<not> (\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q)"
      proof
        assume "\<exists>k. Qback_arr s' k = a \<and> k \<noteq> i_var s' q"
        then obtain k where
          qback_k': "Qback_arr s' k = a"
          and ki_ne': "k \<noteq> i_var s' q"
          by blast
        have "Qback_arr s k = a \<and> k \<noteq> i_var s q"
          using qback_k' ki_ne' qback_eq_D1[of k] i_eq_D1[of q] by simp
        then show False
          using old_no_qback by blast
      qed
    next
      fix q a
      assume hq': "HasPendingEnq s' q a \<and> program_counter s' q = ''E1''"
      then have pend': "HasPendingEnq s' q a"
        and pcE1': "program_counter s' q = ''E1''"
        by auto
      have q_ne_p: "q \<noteq> p"
        using pcE1' pc_eq_D1[of q] by auto
      have pend: "HasPendingEnq s q a"
        using HasPendingEnq_append_deq_call_iff[OF his_eq ssn_eq_D1[of q]] pend'
        by simp
      have pc_old: "program_counter s q = ''E1''"
        using q_ne_p pcE1' pc_eq_D1[of q] by auto
      have old_no_qback: "\<not> (\<exists>k. Qback_arr s k = a)"
        using hI14_Pending_Enq_Qback_Exclusivity_s pend pc_old
        unfolding hI14_Pending_Enq_Qback_Exclusivity_def by auto
      show "\<not> (\<exists>k. Qback_arr s' k = a)"
        using old_no_qback qback_eq_D1 by auto
    qed

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_deq_result_exclusive. *)
    have hI15_Deq_Result_Exclusivity_s': "hI15_Deq_Result_Exclusivity s'"
      using L0_D1_deq_result_exclusive[
        OF hI15_Deq_Result_Exclusivity_s his_eq pc_eq_D1 x_eq_D1 qarr_eq_D1 ssn_eq_D1 pc_L0 sI11_x_var_Scope_s
      ] .

    have hI16_BO_BT_No_HB_s': "hI16_BO_BT_No_HB s'"
    proof (unfold hI16_BO_BT_No_HB_def, intro allI impI)
      fix a b
      assume ab': "a \<in> SetBO s' \<and> b \<in> SetBT s'"
      have a_old: "a \<in> SetBO s"
        and b_old: "b \<in> SetBT s"
        using SetBO_eq_D1 SetBT_eq_D1 ab' by auto
      have old_no: "\<not> HB_EnqRetCall s a b"
        using hI16_BO_BT_No_HB_s a_old b_old unfolding hI16_BO_BT_No_HB_def by blast
      show "\<not> HB_EnqRetCall s' a b"
        using old_no HB_EnqRetCall_append_deq_call_iff[OF his_eq, of a b]
        by blast
    qed

    have hI17_BT_BT_No_HB_s': "hI17_BT_BT_No_HB s'"
    proof (unfold hI17_BT_BT_No_HB_def, intro allI impI)
      fix a b
      assume ab': "a \<in> SetBT s' \<and> b \<in> SetBT s'"
      have a_old: "a \<in> SetBT s"
        and b_old: "b \<in> SetBT s"
        using SetBT_eq_D1 ab' by auto
      have old_no: "\<not> HB_EnqRetCall s a b"
        using hI17_BT_BT_No_HB_s a_old b_old unfolding hI17_BT_BT_No_HB_def by blast
      show "\<not> HB_EnqRetCall s' a b"
        using old_no HB_EnqRetCall_append_deq_call_iff[OF his_eq, of a b]
        by blast
    qed

    have hI18_Idx_Order_No_Rev_HB_s': "hI18_Idx_Order_No_Rev_HB s'"
    proof (unfold hI18_Idx_Order_No_Rev_HB_def, intro allI impI)
      fix a b
      assume prem': "InQBack s' a \<and> InQBack s' b \<and> Idx s' a < Idx s' b"
      have inq_a: "InQBack s a" and inq_b: "InQBack s b"
        using prem' InQBack_eq_D1 by auto
      have idx_old: "Idx s a < Idx s b"
        using prem' Idx_eq_D1[of a] Idx_eq_D1[of b] by simp
      have old_no: "\<not> HB_EnqRetCall s b a"
        using hI18_Idx_Order_No_Rev_HB_s inq_a inq_b idx_old unfolding hI18_Idx_Order_No_Rev_HB_def by blast
      show "\<not> HB_EnqRetCall s' b a"
        using old_no HB_EnqRetCall_append_deq_call_iff[OF his_eq, of b a]
        by blast
    qed

have hI19_Scanner_Catches_Later_Enq_s': "hI19_Scanner_Catches_Later_Enq s'"
proof (unfold hI19_Scanner_Catches_Later_Enq_def, intro allI impI)
  fix a b
  assume prem':
    "InQBack s' a \<and> InQBack s' b \<and> TypeB s' a \<and> TypeB s' b \<and> Idx s' a < Idx s' b \<and>
     (\<exists>q. HasPendingDeq s' q \<and> program_counter s' q = ''D3'' \<and>
          Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q)"
  have inq_a': "InQBack s' a" and inq_b': "InQBack s' b"
    using prem' by auto
  have type_a': "TypeB s' a" and type_b': "TypeB s' b"
    using prem' by auto
  have type_a: "TypeB s a" and type_b: "TypeB s b"
    using type_a' type_b' TypeB_eq_D1 by auto
  have inq_a: "InQBack s a" and inq_b: "InQBack s b"
    using inq_a' inq_b' qback_eq_D1
    unfolding InQBack_def
    by auto
  have idx_old: "Idx s a < Idx s b"
    using prem' Idx_eq_D1[of a] Idx_eq_D1[of b] by simp
  have d3_block_old:
    "\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and>
         Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
  proof -
    from prem' obtain q where
      pend': "HasPendingDeq s' q"
      and qD3': "program_counter s' q = ''D3''"
      and bounds':
        "Idx s' a < j_var s' q \<and> j_var s' q \<le> Idx s' b \<and> Idx s' b < l_var s' q"
      by blast
    have q_ne_p: "q \<noteq> p"
    proof
      assume q_eq: "q = p"
      with qD3' pc_eq_D1[of q] show False
        by simp
    qed
    have pend_eq: "HasPendingDeq s' q \<longleftrightarrow> HasPendingDeq s q"
      using HasPendingDeq_append_deq_call_other_iff[OF his_eq q_ne_p ssn_eq_D1[of q]] .
    have "HasPendingDeq s q"
      using pend' pend_eq by blast
    moreover have "program_counter s q = ''D3''"
      using qD3' pc_D3_eq_D1[of q] by simp
    moreover have "Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q"
      using bounds' Idx_eq_D1[of a] Idx_eq_D1[of b] j_eq_D1[of q] l_eq_D1[of q]
      by simp
    ultimately show ?thesis
      by blast
  qed
  have old_no: "\<not> HB_EnqRetCall s a b"
    using hI19_Scanner_Catches_Later_Enq_s inq_a inq_b type_a type_b idx_old d3_block_old
    unfolding hI19_Scanner_Catches_Later_Enq_def
    by blast
  show "\<not> HB_EnqRetCall s' a b"
    using old_no HB_EnqRetCall_append_deq_call_iff[OF his_eq, of a b]
    by blast
qed

   have hI20_Enq_Val_Valid_s': "hI20_Enq_Val_Valid s'"
  using hI20_Enq_Val_Valid_append_non_enq[OF hI20_Enq_Val_Valid_s his_eq]
  by (auto simp: mk_act_def act_name_def)

have hI21_Ret_Implies_Call_s': "hI21_Ret_Implies_Call s'"
  using hI21_Ret_Implies_Call_append_call[OF hI21_Ret_Implies_Call_s his_eq]
  by (simp add: mk_act_def act_cr_def)

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_deq_local_pattern. *)
    have hI22_Deq_Local_Pattern_s': "hI22_Deq_Local_Pattern s'"
      using L0_D1_deq_local_pattern[
        OF hI22_Deq_Local_Pattern_s his_eq qarr_eq_D1 qback_eq_D1 x_eq_D1
      ] .

    have deq_balanced_p:
      "length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
       length (filter (\<lambda>e. act_pid e = p \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))"
      using hI3_L0_E_Phase_Bounds_L0_deq_balanced[OF hI3_L0_E_Phase_Bounds_s pc_L0] .
    have hI23_Deq_Call_Ret_Balanced_s': "hI23_Deq_Call_Ret_Balanced s'"
      using hI23_Deq_Call_Ret_Balanced_append_deq_call_if_balanced_deq[OF hI23_Deq_Call_Ret_Balanced_s deq_balanced_p his_eq] .

    have hI24_HB_Implies_Idx_Order_s': "hI24_HB_Implies_Idx_Order s'"
    proof (unfold hI24_HB_Implies_Idx_Order_def, intro allI impI)
      fix u1 u2 v1 v2 idx1 idx2 sn1 sn2
      assume pre:
        "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1) \<and>
         CState.Q_arr (fst s') idx1 = v1 \<and>
         CState.Q_arr (fst s') idx2 = v2"
      have hb': "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
        using pre by simp
      have q1': "CState.Q_arr (fst s') idx1 = v1"
        using pre by simp
      have q2': "CState.Q_arr (fst s') idx2 = v2"
        using pre by simp
      have act2_safe:
        "op_name (mk_op enq v1 u1 sn1) \<noteq> deq \<or>
         op_pid (mk_op enq v1 u1 sn1) \<noteq> p \<or>
         op_ssn (mk_op enq v1 u1 sn1) \<noteq> s_var s p"
        by (simp add: mk_op_def op_name_def op_pid_def op_ssn_def)
      have "HB_Act s' (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1) \<longleftrightarrow>
            HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
        using HB_Act_append_deq_call_other_iff[OF his_eq act2_safe] .
      then have hb: "HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1)"
        using hb' by blast
      have q1: "CState.Q_arr (fst s) idx1 = v1"
        using q1' qarr_eq_D1[of idx1]
        unfolding Q_arr_def by simp
      have q2: "CState.Q_arr (fst s) idx2 = v2"
        using q2' qarr_eq_D1[of idx2]
        unfolding Q_arr_def by simp
      show "idx2 < idx1"
        using hI24_HB_Implies_Idx_Order_s hb q1 q2
        unfolding hI24_HB_Implies_Idx_Order_def
        by blast
    qed

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_enq_call_ret_balanced. *)
    have hI25_Enq_Call_Ret_Balanced_s': "hI25_Enq_Call_Ret_Balanced s'"
      using L0_D1_enq_call_ret_balanced[
        OF hI25_Enq_Call_Ret_Balanced_s his_eq pc_eq_D1 pc_L0
      ] .

   have hI26_DeqRet_D4_Mutex_s': "hI26_DeqRet_D4_Mutex s'"
    proof (unfold hI26_DeqRet_D4_Mutex_def, intro allI impI notI)
      fix q a
      assume a_val: "a \<in> Val"
      assume bad:
        "(\<exists>sn. Model.DeqRetInHis s' q a sn) \<and>
         program_counter s' q = ''D4'' \<and> x_var s' q = a"
      then obtain sn where
        deq': "Model.DeqRetInHis s' q a sn"
        and pc_D4': "program_counter s' q = ''D4''"
        and xq': "x_var s' q = a"
        by blast
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_D1[of q]
        by auto
      have deq: "Model.DeqRetInHis s q a sn"
        using deq' his_eq
        unfolding Model.DeqRetInHis_def
        by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_D1[of q]
        by simp
      have xq: "x_var s q = a"
        using q_ne_p xq' x_eq_D1[of q]
        by simp
      from hI26_DeqRet_D4_Mutex_s a_val show False
        unfolding hI26_DeqRet_D4_Mutex_def
        using deq pc_D4 xq
        by blast
    qed

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_pending_pc_sync. *)
    have hI27_Pending_PC_Sync_s': "hI27_Pending_PC_Sync s'"
      using L0_D1_pending_pc_sync[
        OF hI27_Pending_PC_Sync_s pc_eq_D1 his_eq ssn_eq_D1 hI3_L0_E_Phase_Bounds_s pc_L0 v_eq_D1
      ] .

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_fresh_enq_immune. *)
    have hI28_Fresh_Enq_Immunity_s': "hI28_Fresh_Enq_Immunity s'"
      using L0_D1_fresh_enq_immune[
        OF hI28_Fresh_Enq_Immunity_s pc_eq_D1 v_eq_D1 his_eq
      ] .

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_e2_scanner_immune. *)
    have hI29_E2_Scanner_Immunity_s': "hI29_E2_Scanner_Immunity s'"
      using L0_D1_e2_scanner_immune[
        OF hI29_E2_Scanner_Immunity_s his_eq ssn_eq_D1 pc_eq_D1 InQBack_eq_D1 TypeB_eq_D1
           Idx_eq_D1 j_eq_D1 i_eq_D1 l_eq_D1 v_eq_D1 pc_L0 pc_D3_eq_D1
      ] .

    have hI30_Ticket_HB_Immunity_s': "hI30_Ticket_HB_Immunity s'"
    proof (unfold hI30_Ticket_HB_Immunity_def, intro allI impI)
      fix b u
      assume prem':
        "program_counter s' u \<in> {''E2'', ''E3''} \<and>
         InQBack s' b \<and> b \<noteq> BOT \<and>
         b \<noteq> v_var s' u \<and> HB_EnqRetCall s' b (v_var s' u)"
      have u_ne_p: "u \<noteq> p"
        using prem' pc_eq_D1[of u]
        by auto

      have pc_old: "program_counter s u \<in> {''E2'', ''E3''}"
        using prem' u_ne_p pc_eq_D1[of u]
        by auto

      have inq_old: "InQBack s b"
        using prem' InQBack_eq_D1[of b]
        by auto

      have b_not_bot_old: "b \<noteq> BOT"
        using prem'
        by auto

      have neq_old: "b \<noteq> v_var s u"
        using prem' u_ne_p v_eq_D1[of u]
        by auto

      have hb_old: "HB_EnqRetCall s b (v_var s u)"
        using prem' u_ne_p HB_EnqRetCall_append_deq_call_iff[OF his_eq]
        by (simp add: v_eq_D1[of u])

      have old_prem:
        "program_counter s u \<in> {''E2'', ''E3''} \<and>
         InQBack s b \<and> b \<noteq> BOT \<and>
         b \<noteq> v_var s u \<and> HB_EnqRetCall s b (v_var s u)"
        using pc_old inq_old b_not_bot_old neq_old hb_old
        by blast

      have old_idx: "Idx s b < i_var s u"
        using hI30_Ticket_HB_Immunity_s old_prem
        unfolding hI30_Ticket_HB_Immunity_def
        by blast

      show "Idx s' b < i_var s' u"
        using old_idx u_ne_p Idx_eq_D1[of b] i_eq_D1[of u]
        by simp
    qed


    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_op_sets_equiv. *)
    have lI1_Op_Sets_Equivalence_s': "lI1_Op_Sets_Equivalence s'"
      using L0_D1_op_sets_equiv[
        OF lI1_Op_Sets_Equivalence_s SetA_eq_D1 SetB_eq_D1 his_eq lin_seq_eq
      ] .

    have lI2_Op_Cardinality_s': "lI2_Op_Cardinality s'"
      using lI2_Op_Cardinality_s lin_seq_eq pc_L0 s'_def
      unfolding lI2_Op_Cardinality_def EnqIdxs_def DeqIdxs_def SetA_def SetB_def TypeA_def TypeB_def
                QHas_def InQBack_def L0_D1_update_state_def
      by (auto simp: Let_def bridge_defs split: if_splits)

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_hb_ret_lin_sync. *)
    have lI3_HB_Ret_Lin_Sync_s': "lI3_HB_Ret_Lin_Sync s'"
      using L0_D1_hb_ret_lin_sync[
        OF lI3_HB_Ret_Lin_Sync_s lin_seq_eq his_eq lI1_Op_Sets_Equivalence_s hI2_SSN_Bounds_s pc_L0
      ] .
    have lI4_FIFO_Semantics_s': "lI4_FIFO_Semantics s'"
      using lI4_FIFO_Semantics_s lin_seq_eq
      unfolding lI4_FIFO_Semantics_def by simp

    have lI5_SA_Prefix_s': "lI5_SA_Prefix s'"
      using lI5_SA_Prefix_s lin_seq_eq
      unfolding lI5_SA_Prefix_def by simp

    have lI6_D4_Deq_Linearized_s': "lI6_D4_Deq_Linearized s'"
    proof (unfold lI6_D4_Deq_Linearized_def, intro allI impI)
      fix q
      assume pc_D4': "program_counter s' q = ''D4''"
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_D1[of q]
        by auto
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_D1[of q]
        by simp
      from lI6_D4_Deq_Linearized_s pc_D4 have old_in:
        "mk_op deq (x_var s q) q (s_var s q) \<in> set (lin_seq s)"
        unfolding lI6_D4_Deq_Linearized_def
        by blast
      show "mk_op deq (x_var s' q) q (s_var s' q) \<in> set (lin_seq s')"
        using old_in q_ne_p lin_seq_eq x_eq_D1[of q] ssn_eq_D1[of q]
        by simp
    qed

    have lI7_D4_Deq_Deq_HB_s': "lI7_D4_Deq_Deq_HB s'"
    proof (unfold lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def, intro allI impI)
      fix k1 k2 q
      assume pre:
        "k1 < length (lin_seq s') \<and>
         k2 < length (lin_seq s') \<and>
         op_name (lin_seq s' ! k1) = deq \<and>
         lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
         (\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q) \<and>
         program_counter s' q = ''D4'' \<and>
         HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
      then have
        k1_lt': "k1 < length (lin_seq s')"
        and k2_lt': "k2 < length (lin_seq s')"
        and act1_deq': "op_name (lin_seq s' ! k1) = deq"
        and act2_eq': "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
        and tail': "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q"
        and pc_D4': "program_counter s' q = ''D4''"
        and hb': "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
        by auto
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_D1[of q]
        by auto
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_D1[of q]
        by simp
      have k1_lt: "k1 < length (lin_seq s)" and k2_lt: "k2 < length (lin_seq s)"
        using k1_lt' k2_lt' lin_seq_eq by simp_all
      have act2_eq:
        "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
        using act2_eq' lin_seq_eq q_ne_p x_eq_D1[of q] ssn_eq_D1[of q]
        by simp
      have act1_deq: "op_name (lin_seq s ! k1) = deq"
        using act1_deq' lin_seq_eq by simp
      have tail:
        "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
        using tail' lin_seq_eq by simp
      have act2_safe:
        "op_name (lin_seq s ! k2) \<noteq> deq \<or>
         op_pid (lin_seq s ! k2) \<noteq> p \<or>
         op_ssn (lin_seq s ! k2) \<noteq> s_var s p"
      proof -
        have pid_not_p: "op_pid (lin_seq s ! k2) \<noteq> p"
          using act2_eq q_ne_p
          by (simp add: mk_op_def op_pid_def)
        show ?thesis
          using pid_not_p by blast
      qed
      have hb_old: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
        using HB_Act_append_deq_call_other_iff[OF his_eq act2_safe]
          hb' lin_seq_eq
        unfolding HB_Act_def
        by simp
      show "k1 < k2"
        using lI7_D4_Deq_Deq_HB_s k1_lt k2_lt act1_deq act2_eq tail pc_D4 hb_old
        unfolding lI7_D4_Deq_Deq_HB_def lI7_D4_Deq_Deq_HB_list_def
        by blast
    qed

       have lI8_D3_Deq_Returned_s': "lI8_D3_Deq_Returned s'"
    proof (unfold lI8_D3_Deq_Returned_def, intro allI impI)
      fix q k
      assume pc_D3': "program_counter s' q = ''D3''"
        and k_lt': "k < length (lin_seq s')"
        and act_match': "op_name (lin_seq s' ! k) = deq \<and> op_pid (lin_seq s' ! k) = q"
      have q_ne_p: "q \<noteq> p"
        using pc_D3' pc_eq_D1[of q]
        by auto
      have pc_D3: "program_counter s q = ''D3''"
        using q_ne_p pc_D3' pc_eq_D1[of q]
        by simp
      have k_lt: "k < length (lin_seq s)"
        using k_lt' lin_seq_eq by simp
      have act_match: "op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = q"
        using act_match' lin_seq_eq by simp
      have deq_old:
        "Model.DeqRetInHis s q (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k))"
        using lI8_D3_Deq_Returned_s pc_D3 k_lt act_match
        unfolding lI8_D3_Deq_Returned_def
        by blast
      show "Model.DeqRetInHis s' q (op_val (lin_seq s' ! k)) (op_ssn (lin_seq s' ! k))"
        using deq_old his_eq lin_seq_eq
        unfolding Model.DeqRetInHis_def
        by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
    qed

    (* Prove the required intermediate property. Related symbols: L0Proof.thy, L0Lemmas.thy. *)
    (* Prove the required intermediate property. Related symbols: L0_D1_d12_deq_returned. *)
    have lI9_D1_D2_Deq_Returned_s': "lI9_D1_D2_Deq_Returned s'"
      using L0_D1_d12_deq_returned[
        OF lI9_D1_D2_Deq_Returned_s pc_eq_D1 lin_seq_eq his_eq lI1_Op_Sets_Equivalence_s
           lI2_Op_Cardinality_s sI8_Q_Qback_Sync_s hI13_Qback_Deq_Sync_s
           lI6_D4_Deq_Linearized_s lI3_HB_Ret_Lin_Sync_s pc_L0
      ] .

    have lI10_D4_Enq_Deq_HB_s': "lI10_D4_Enq_Deq_HB s'"
    proof (unfold lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def, intro allI impI)
      fix k1 k2 q
      assume pre:
        "k1 < length (lin_seq s') \<and>
         k2 < length (lin_seq s') \<and>
         op_name (lin_seq s' ! k1) = enq \<and>
         lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
         (\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q) \<and>
         program_counter s' q = ''D4'' \<and>
         HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
      then have
        k1_lt': "k1 < length (lin_seq s')"
        and k2_lt': "k2 < length (lin_seq s')"
        and act1_enq': "op_name (lin_seq s' ! k1) = enq"
        and act2_eq': "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
        and tail': "\<forall>k3>k2. k3 < length (lin_seq s') \<longrightarrow> op_name (lin_seq s' ! k3) \<noteq> deq \<or> op_pid (lin_seq s' ! k3) \<noteq> q"
        and pc_D4': "program_counter s' q = ''D4''"
        and hb': "HB (his_seq s') (lin_seq s' ! k1) (lin_seq s' ! k2)"
        by auto
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_D1[of q]
        by auto
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_D1[of q]
        by simp
      have k1_lt: "k1 < length (lin_seq s)" and k2_lt: "k2 < length (lin_seq s)"
        using k1_lt' k2_lt' lin_seq_eq by simp_all
      have act2_eq:
        "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
        using act2_eq' lin_seq_eq q_ne_p x_eq_D1[of q] ssn_eq_D1[of q]
        by simp
      have act1_enq: "op_name (lin_seq s ! k1) = enq"
        using act1_enq' lin_seq_eq by simp
      have tail:
        "\<forall>k3>k2. k3 < length (lin_seq s) \<longrightarrow> op_name (lin_seq s ! k3) \<noteq> deq \<or> op_pid (lin_seq s ! k3) \<noteq> q"
        using tail' lin_seq_eq by simp
      have act2_safe:
        "op_name (lin_seq s ! k2) \<noteq> deq \<or>
         op_pid (lin_seq s ! k2) \<noteq> p \<or>
         op_ssn (lin_seq s ! k2) \<noteq> s_var s p"
      proof -
        have pid_not_p: "op_pid (lin_seq s ! k2) \<noteq> p"
          using act2_eq q_ne_p
          by (simp add: mk_op_def op_pid_def)
        show ?thesis
          using pid_not_p by blast
      qed
      have hb_old: "HB (his_seq s) (lin_seq s ! k1) (lin_seq s ! k2)"
        using HB_Act_append_deq_call_other_iff[OF his_eq act2_safe]
          hb' lin_seq_eq
        unfolding HB_Act_def
        by simp
      show "k1 < k2"
        using lI10_D4_Enq_Deq_HB_s k1_lt k2_lt act1_enq act2_eq tail pc_D4 hb_old
        unfolding lI10_D4_Enq_Deq_HB_def lI10_D4_Enq_Deq_HB_list_def
        by blast
    qed

    have lI11_D4_Deq_Unique_s': "lI11_D4_Deq_Unique s'"
    proof (unfold lI11_D4_Deq_Unique_def, intro allI impI)
      fix q
      assume pc_D4': "program_counter s' q = ''D4''"
      have q_ne_p: "q \<noteq> p"
        using pc_D4' pc_eq_D1[of q]
        by auto
      have pc_D4: "program_counter s q = ''D4''"
        using q_ne_p pc_D4' pc_eq_D1[of q]
        by simp
      from lI11_D4_Deq_Unique_s[unfolded lI11_D4_Deq_Unique_def, rule_format, OF pc_D4]
      obtain k2 where
        k2_lt: "k2 < length (lin_seq s)"
        and act_eq: "lin_seq s ! k2 = mk_op deq (x_var s q) q (s_var s q)"
        and uniq_old:
          "\<forall>k3<length (lin_seq s).
             op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
             k3 < k2 \<and> Model.DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
        by blast
      have act_eq':
        "lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q)"
        using act_eq lin_seq_eq q_ne_p x_eq_D1[of q] ssn_eq_D1[of q]
        by simp
      have uniq_new:
        "\<forall>k3<length (lin_seq s').
           op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
           k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
      proof (intro allI impI)
        fix k3
        assume k3_lt': "k3 < length (lin_seq s')"
        assume match':
          "op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2"
        have k3_lt: "k3 < length (lin_seq s)"
          using k3_lt' lin_seq_eq by simp
        have match:
          "op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = q \<and> k3 \<noteq> k2"
          using match' lin_seq_eq by simp
        from uniq_old k3_lt match have
          "k3 < k2 \<and> Model.DeqRetInHis s q (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))"
          by blast
        then have
          "k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
          using his_eq lin_seq_eq
          unfolding Model.DeqRetInHis_def
          by (auto simp: mk_act_def act_pid_def act_ssn_def act_name_def act_cr_def act_val_def)
        then show
          "k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3))"
          .
      qed
      show "\<exists>k2<length (lin_seq s').
              lin_seq s' ! k2 = mk_op deq (x_var s' q) q (s_var s' q) \<and>
              (\<forall>k3<length (lin_seq s').
                 op_name (lin_seq s' ! k3) = deq \<and> op_pid (lin_seq s' ! k3) = q \<and> k3 \<noteq> k2 \<longrightarrow>
                 k3 < k2 \<and> Model.DeqRetInHis s' q (op_val (lin_seq s' ! k3)) (op_ssn (lin_seq s' ! k3)))"
        using k2_lt lin_seq_eq act_eq' uniq_new
        by auto
    qed

    have di_s': "data_independent (lin_seq s')"
      using di_s lin_seq_eq
      unfolding data_independent_def by simp


    (* USpec invariants uI1-uI3. *)
    have uspec_effOps_eq_D1 [simp]: "uspec_effOps s' = uspec_effOps s"
      using s'_def
      unfolding L0_D1_update_state_def uspec_effOps_def
      by (simp add: Let_def)

    have uI1_USpec_EffOps_Lin_s': "uI1_USpec_EffOps_Lin s'"
      using uI1_USpec_EffOps_Lin_s lin_seq_eq uspec_effOps_eq_D1
      unfolding uI1_USpec_EffOps_Lin_def
      by simp

    have upc_eq_D1:
      "\<And>q. u_program_counter (snd s') q =
            (if q = p then ''UD2'' else u_program_counter (snd s) q)"
      using s'_def
      unfolding L0_D1_update_state_def
      by (simp add: Let_def)

    have uI2_USpec_E1UE2_s': "uI2_USpec_E1UE2 s'"
    proof (unfold uI2_USpec_E1UE2_def, intro allI impI)
      fix q
      assume pc_q': "program_counter s' q \<in> {''E1'', ''E2''}"
      assume upc_q': "u_program_counter (snd s') q = ''UE2''"

      let ?fresh_call = "mk_act deq BOT p (s_var s p) call"
      let ?op_q' = "mk_op enq (v_var s' q) q (s_var s' q)"

      have q_ne_p:
        "q \<noteq> p"
        using pc_q' pc_eq_D1[of q]
        by auto

      have pc_q_old:
        "program_counter s q \<in> {''E1'', ''E2''}"
        using pc_q' pc_eq_D1[of q] q_ne_p
        by simp

      have upc_q_old:
        "u_program_counter (snd s) q = ''UE2''"
        using upc_q' upc_eq_D1[of q] q_ne_p
        by simp

      let ?old_op = "mk_op enq (v_var s q) q (s_var s q)"
      let ?old_L = "lin_seq s @ [?old_op]"

      have old_gen:
        "USpec_GenLin (his_seq s) (uspec_effOps s) ?old_op ?old_L"
        using uI2_USpec_E1UE2_s pc_q_old upc_q_old
        unfolding uI2_USpec_E1UE2_def his_seq_def lin_seq_def uspec_effOps_def
        by blast

      have no_last_match:
        "\<forall>b\<in>set ?old_L.
            \<not> match_call (his_seq s @ [?fresh_call]) (length (his_seq s)) b"
      proof
        fix b
        assume b_in: "b \<in> set ?old_L"

        show "\<not> match_call (his_seq s @ [?fresh_call]) (length (his_seq s)) b"
        proof
          assume mc:
            "match_call (his_seq s @ [?fresh_call]) (length (his_seq s)) b"

          have b_cases:
            "b = ?old_op \<or> b \<in> set (lin_seq s)"
            using b_in
            by simp

          from b_cases show False
          proof
            assume b_old_op:
              "b = ?old_op"

            show False
              using mc b_old_op
              unfolding match_call_def Let_def
              by (simp add:
                    nth_append
                    mk_act_def mk_op_def
                    act_name_def act_pid_def act_ssn_def act_val_def act_cr_def
                    op_name_def op_pid_def op_ssn_def op_val_def)
          next
            assume b_old_lin:
              "b \<in> set (lin_seq s)"

            have b_oplin:
              "b \<in> OPLin s"
              using b_old_lin
              unfolding OPLin_def
              by simp

            have b_deq:
              "op_name b = deq"
              using mc
              unfolding match_call_def Let_def
              by (cases b)
                 (auto simp add:
                    nth_append
                    mk_act_def mk_op_def
                    act_name_def act_pid_def act_ssn_def act_val_def act_cr_def
                    op_name_def op_pid_def op_ssn_def op_val_def)

            have b_pid:
              "op_pid b = p"
              using mc
              unfolding match_call_def Let_def
              by (cases b)
                 (auto simp add:
                    nth_append
                    mk_act_def mk_op_def
                    act_name_def act_pid_def act_ssn_def act_val_def act_cr_def
                    op_name_def op_pid_def op_ssn_def op_val_def)

            have b_ssn:
              "op_ssn b = s_var s p"
              using mc
              unfolding match_call_def Let_def
              by (cases b)
                 (auto simp add:
                    nth_append
                    mk_act_def mk_op_def
                    act_name_def act_pid_def act_ssn_def act_val_def act_cr_def
                    op_name_def op_pid_def op_ssn_def op_val_def)

            have ssn_ne:
              "op_ssn b \<noteq> s_var s p"
              using OPLin_deq_not_current_ssn_at_L0[
                OF lI1_Op_Sets_Equivalence_s hI2_SSN_Bounds_s pc_L0
                   b_oplin b_deq b_pid
              ] .

            show False
              using ssn_ne b_ssn
              by simp
          qed
        qed
      qed

      have gen_append:
        "USpec_GenLin
           (his_seq s @ [?fresh_call])
           (uspec_effOps s)
           ?old_op
           ?old_L"
      proof (rule L0_USpec_GenLin_append_call_no_new_match)
        show "act_cr ?fresh_call = call"
          by (simp add: mk_act_def act_cr_def)
      next
        show "USpec_GenLin (his_seq s) (uspec_effOps s) ?old_op ?old_L"
          using old_gen .
      next
        show "\<forall>b\<in>set ?old_L.
                \<not> match_call (his_seq s @ [?fresh_call]) (length (his_seq s)) b"
          using no_last_match .
      qed

      have op_eq:
        "?op_q' = ?old_op"
        using q_ne_p v_eq_D1[of q] ssn_eq_D1[of q]
        by simp

      show "USpec_GenLin
              (u_his_seq (snd s'))
              (u_eff_ops (snd s'))
              ?op_q'
              (u_lin_seq (snd s') @ [?op_q'])"
        using gen_append op_eq lin_seq_eq his_eq uspec_effOps_eq_D1
        unfolding his_seq_def lin_seq_def uspec_effOps_def
        by simp
    qed

    have uI3_USpec_D3UD2_s': "uI3_USpec_D3UD2 s'"
    proof (unfold uI3_USpec_D3UD2_def, intro allI impI)
      fix q
      assume pc_q': "program_counter s' q = ''D3''"
      assume qj_q': "Q_arr s' (j_var s' q) \<noteq> BOT"
      assume upc_q': "u_program_counter (snd s') q = ''UD2''"

      let ?x = "Q_arr s' (j_var s' q)"
      let ?op = "mk_op deq ?x q (s_var s' q)"
      let ?base =
        "(if should_modify (lin_seq s') (his_seq s') ?x
          then modify_lin (lin_seq s') (his_seq s') ?x
          else lin_seq s')"
      let ?L = "?base @ [?op]"
      let ?H = "his_seq s'"

      have pending_q:
        "HasPendingDeq s' q"
        using hI12_D_Phase_Pending_Deq_s' pc_q'
        unfolding hI12_D_Phase_Pending_Deq_def
        by auto

      have deq_call_q:
        "DeqCallInHis s' q (s_var s' q)"
        using pending_q
        unfolding HasPendingDeq_def Let_def
        by blast

      have op_called:
        "OpCalledInHis ?H ?op"
        using DeqCallInHis_imp_OpCalledInHis[OF deq_call_q, of ?x]
        by simp

      have no_HB_from_op:
        "\<forall>x. \<not> HB ?H ?op x"
      proof
        fix x
        show "\<not> HB ?H ?op x"
        proof
          assume hb: "HB ?H ?op x"

          then obtain k1 where
            mr: "match_ret ?H k1 ?op"
            unfolding HB_def
            by blast

          have k1_lt:
            "k1 < length ?H"
            using mr
            unfolding match_ret_def Let_def
            by simp

          have pid_eq:
            "act_pid (?H ! k1) = q"
            using mr
            unfolding match_ret_def Let_def
            by (simp add: mk_op_def op_pid_def)

          have ssn_eq:
            "act_ssn (?H ! k1) = s_var s' q"
            using mr
            unfolding match_ret_def Let_def
            by (simp add: mk_op_def op_ssn_def)

          have cr_eq:
            "act_cr (?H ! k1) = ret"
            using mr
            unfolding match_ret_def Let_def
            by simp

          have in_his:
            "?H ! k1 \<in> set ?H"
            using k1_lt
            by simp

          have no_ret:
            "\<forall>e\<in>set ?H.
               \<not> (act_pid e = q \<and>
                    act_ssn e = s_var s' q \<and>
                    act_cr e = ret)"
            using pending_q
            unfolding HasPendingDeq_def Let_def
            by blast

          show False
            using no_ret in_his pid_eq ssn_eq cr_eq
            by blast
        qed
      qed

      have hb_lin:
        "HB_consistent (lin_seq s') ?H"
        using lI3_HB_Ret_Lin_Sync_s'
        unfolding lI3_HB_Ret_Lin_Sync_def HB_Act_def HB_consistent_def
        by simp

      have lI4_list_s':
        "lI4_FIFO_Semantics_list (lin_seq s')"
        using lI4_FIFO_Semantics_s'
        unfolding lI4_FIFO_Semantics_def
        by simp

      have lI5_list_s':
        "lI5_SA_Prefix_list (lin_seq s')"
        using lI5_SA_Prefix_s'
        unfolding lI5_SA_Prefix_def
        by simp

      have x_val:
        "?x \<in> Val"
        using TypeOK_s' qj_q'
        unfolding TypeOK_def
        by auto

      have typeBT_x:
        "TypeBT s' ?x"
        using D3_j_nonBOT_TypeBT_from_local[
          OF sI6_D3_Scan_Pointers_s'
             sI8_Q_Qback_Sync_s'
             sI10_Qback_Unique_Vals_s'
             pc_q' qj_q'
        ] .

      have x_SetB:
        "?x \<in> SetB s'"
        using x_val typeBT_x
        unfolding SetB_def TypeBT_def
        by blast

      have pending_x_lin:
        "\<forall>i < length (lin_seq s').
           op_val (lin_seq s' ! i) = ?x \<longrightarrow>
           op_name (lin_seq s' ! i) \<noteq> deq"
        by (rule SetB_implies_no_deq_in_lin_from_LI2[
              OF lI2_Op_Cardinality_s' x_SetB
            ])

      have enq_exists_x_lin:
        "\<exists>k < length (lin_seq s').
           op_name (lin_seq s' ! k) = enq \<and>
           op_val (lin_seq s' ! k) = ?x"
        by (rule SetB_implies_enq_in_lin_from_LI2[
              OF lI2_Op_Cardinality_s' x_SetB
            ])

      have base_def':
        "?base =
          (if should_modify (lin_seq s') (his_seq s') ?x
           then modify_lin (lin_seq s') (his_seq s') ?x
           else lin_seq s')"
        by simp

      have mset_base_eq:
        "mset ?base = mset (lin_seq s')"
        using D3_base_mset_eq_from_local_invs[OF base_def'] .

      have set_base_eq:
        "set ?base = set (lin_seq s')"
        using mset_base_eq
        by (metis set_mset_mset)

      have all_called_lin:
        "\<forall>a\<in>set (lin_seq s'). OpCalledInHis ?H a"
      proof
        fix a
        assume a_in: "a \<in> set (lin_seq s')"

        have a_oplin:
          "a \<in> OPLin s'"
          using a_in
          unfolding OPLin_def
          by simp

        have cases:
          "a \<in> OP_A_enq s' \<or> a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
          using lI1_Op_Sets_Equivalence_s' a_oplin
          unfolding lI1_Op_Sets_Equivalence_def
          by blast

        thus "OpCalledInHis ?H a"
        proof
          assume "a \<in> OP_A_enq s'"
          then obtain qq vv sn where
            a_eq: "a = mk_op enq vv qq sn"
            and call: "EnqCallInHis s' qq vv sn"
            unfolding OP_A_enq_def
            by blast

          show ?thesis
            using EnqCallInHis_imp_OpCalledInHis[OF call]
            unfolding a_eq
            by simp
        next
          assume rest: "a \<in> OP_A_deq s' \<or> a \<in> OP_B_enq s'"
          thus ?thesis
          proof
            assume "a \<in> OP_A_deq s'"

            hence name_deq: "op_name a = deq"
              and call: "DeqCallInHis s' (op_pid a) (op_ssn a)"
              unfolding OP_A_deq_def
              by auto

            have a_mk:
              "mk_op deq (op_val a) (op_pid a) (op_ssn a) = a"
              using name_deq
              by (cases a)
                 (simp add: mk_op_def op_name_def op_val_def op_pid_def op_ssn_def)

            have called_mk:
              "OpCalledInHis ?H
                 (mk_op deq (op_val a) (op_pid a) (op_ssn a))"
              using DeqCallInHis_imp_OpCalledInHis[OF call, of "op_val a"] .

            show ?thesis
              using called_mk a_mk
              by simp
          next
            assume "a \<in> OP_B_enq s'"
            then obtain qq vv sn where
              a_eq: "a = mk_op enq vv qq sn"
              and call: "EnqCallInHis s' qq vv sn"
              unfolding OP_B_enq_def
              by blast

            show ?thesis
              using EnqCallInHis_imp_OpCalledInHis[OF call]
              unfolding a_eq
              by simp
          qed
        qed
      qed

      have hb_base:
        "HB_consistent ?base ?H"
      proof (cases "should_modify (lin_seq s') (his_seq s') ?x")
        case False

        have base_eq:
          "?base = lin_seq s'"
          using False
          by (simp only: if_False)

        show ?thesis
          unfolding base_eq
          using hb_lin .
      next
        case True

        have base_eq:
          "?base = modify_lin (lin_seq s') (his_seq s') ?x"
          using True
          by (simp only: if_True)

        have hb_modify:
          "HB_consistent
             (modify_lin (lin_seq s') (his_seq s') ?x)
             (his_seq s')"
        proof (rule modify_preserves_HB_consistent_from_local_invs[
                 where s = s'
                   and L = "lin_seq s'"
                   and H = "his_seq s'"
                   and bt_val = ?x
               ])
          show "his_seq s' = his_seq s'"
            by simp
        next
          show "HB_consistent (lin_seq s') (his_seq s')"
            using hb_lin .
        next
          show "data_independent (lin_seq s')"
            using di_s' .
        next
          show "TypeBT s' ?x"
            using typeBT_x .
        next
          show "mset (lin_seq s') = mset (lin_seq s')"
            by simp
        next
          show "\<forall>v. in_SA v (lin_seq s') = in_SA v (lin_seq s')"
            by simp
        next
          show "lI1_Op_Sets_Equivalence s'"
            using lI1_Op_Sets_Equivalence_s' .
        next
          show "lI2_Op_Cardinality s'"
            using lI2_Op_Cardinality_s' .
        next
          show "lI4_FIFO_Semantics s'"
            using lI4_FIFO_Semantics_s' .
        next
          show "hI5_SSN_Unique s'"
            using hI5_SSN_Unique_s' .
        next
          show "hI7_His_WF s'"
            using hI7_His_WF_s' .
        next
          show "hI16_BO_BT_No_HB s'"
            using hI16_BO_BT_No_HB_s' .
        next
          show "hI17_BT_BT_No_HB s'"
            using hI17_BT_BT_No_HB_s' .
        next
          show "hI20_Enq_Val_Valid s'"
            using hI20_Enq_Val_Valid_s' .
        qed

        show ?thesis
          unfolding base_eq
          using hb_modify .
      qed

      have hb_final:
        "HB_consistent ?L ?H"
      proof (rule HB_consistent_append)
        show "HB_consistent ?base ?H"
          using hb_base .
      next
        show "\<forall>x\<in>set ?base. \<not> HB ?H ?op x"
          using no_HB_from_op
          by blast
      next
        show "\<not> HB ?H ?op ?op"
          using no_HB_from_op
          by blast
      qed

      have qs_base:
        "QueueSpecLin ?base"
      proof (rule D3_qs_base_from_local_invs[
               where L = "lin_seq s'"
                 and H = "his_seq s'"
                 and v = ?x
                 and base_lin = ?base
             ])
        show "lI4_FIFO_Semantics_list (lin_seq s')"
          using lI4_list_s' .
      next
        show "data_independent (lin_seq s')"
          using di_s' .
      next
        show "lI5_SA_Prefix_list (lin_seq s')"
          using lI5_list_s' .
      next
        show "\<forall>k<length (lin_seq s').
                op_val (lin_seq s' ! k) = ?x \<longrightarrow>
                op_name (lin_seq s' ! k) \<noteq> deq"
          using pending_x_lin .
      next
        show "?base =
              (if should_modify (lin_seq s') (his_seq s') ?x
               then modify_lin (lin_seq s') (his_seq s') ?x
               else lin_seq s')"
          using base_def' .
      qed

      have qs_final:
        "QueueSpecLin ?L"
      proof (rule D3_qs_final_from_local_invs[
               where L = "lin_seq s'"
                 and H = "his_seq s'"
                 and v = ?x
                 and base_lin = ?base
                 and deq_act = ?op
             ])
        show "lI4_FIFO_Semantics_list (lin_seq s')"
          using lI4_list_s' .
      next
        show "data_independent (lin_seq s')"
          using di_s' .
      next
        show "lI5_SA_Prefix_list (lin_seq s')"
          using lI5_list_s' .
      next
        show "\<forall>k<length (lin_seq s').
                op_val (lin_seq s' ! k) = ?x \<longrightarrow>
                op_name (lin_seq s' ! k) \<noteq> deq"
          using pending_x_lin .
      next
        show "\<exists>k<length (lin_seq s').
                op_name (lin_seq s' ! k) = enq \<and>
                op_val (lin_seq s' ! k) = ?x"
          using enq_exists_x_lin .
      next
        show "?base =
              (if should_modify (lin_seq s') (his_seq s') ?x
               then modify_lin (lin_seq s') (his_seq s') ?x
               else lin_seq s')"
          using base_def' .
      next
        show "op_name ?op = deq"
          by (simp add: mk_op_def op_name_def)
      next
        show "op_val ?op = ?x"
          by (simp add: mk_op_def op_val_def)
      qed

      have di_final:
        "data_independent ?L"
      proof (rule D3_di_final_from_local_invs[
               where L = "lin_seq s'"
                 and H = "his_seq s'"
                 and v = ?x
                 and base_lin = ?base
                 and p = q
                 and sn = "s_var s' q"
             ])
        show "data_independent (lin_seq s')"
          using di_s' .
      next
        show "\<forall>k<length (lin_seq s').
                op_val (lin_seq s' ! k) = ?x \<longrightarrow>
                op_name (lin_seq s' ! k) \<noteq> deq"
          using pending_x_lin .
      next
        show "?base =
              (if should_modify (lin_seq s') (his_seq s') ?x
               then modify_lin (lin_seq s') (his_seq s') ?x
               else lin_seq s')"
          using base_def' .
      qed

      have eff_subset:
        "uspec_effOps s' \<subseteq> set ?L"
      proof -
        have old_eff:
          "uspec_effOps s' = set (lin_seq s')"
          using uI1_USpec_EffOps_Lin_s'
          unfolding uI1_USpec_EffOps_Lin_def
          by simp

        have "set (lin_seq s') \<subseteq> set ?base"
          using set_base_eq
          by simp

        thus ?thesis
          using old_eff
          by auto
      qed

      have op_in:
        "?op \<in> set ?L"
        by simp

      have all_called:
        "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
        using all_called_lin set_base_eq op_called
        by auto

      have finite_eff:
        "finite (uspec_effOps s')"
        using uI1_USpec_EffOps_Lin_s'
        unfolding uI1_USpec_EffOps_Lin_def
        by simp

      have gen:
        "USpec_GenLin ?H (uspec_effOps s') ?op ?L"
        unfolding USpec_GenLin_def
      proof (intro conjI)
        show "finite (uspec_effOps s')"
          using finite_eff .
      next
        show "uspec_effOps s' \<subseteq> set ?L"
          using eff_subset .
      next
        show "?op \<in> set ?L"
          using op_in .
      next
        show "\<forall>a\<in>set ?L. OpCalledInHis ?H a"
          using all_called .
      next
        show "HB_consistent ?L ?H"
          using hb_final .
      next
        show "QueueSpecLin ?L"
          using qs_final .
      next
        show "data_independent ?L"
          using di_final .
      qed

      show "let cur_lin = lin_seq s';
                cur_his = his_seq s';
                x_val = Q_arr s' (j_var s' q);
                op = mk_op deq x_val q (s_var s' q);
                new_lin =
                  (if should_modify cur_lin cur_his x_val
                   then modify_lin cur_lin cur_his x_val
                   else cur_lin) @ [op]
            in USpec_GenLin cur_his (uspec_effOps s') op new_lin"
        using gen
        by (simp only: Let_def)
    qed


    show ?thesis
      unfolding system_invariant_def
      using Simulate_PC_s' TypeOK_s'
        sI1_Zero_Index_BOT_s' sI2_X_var_Upper_Bound_s' sI3_E2_Slot_Exclusive_s' sI4_E3_Qback_Written_s' sI5_D2_Local_Bound_s' sI6_D3_Scan_Pointers_s' sI7_D4_Deq_Result_s' hI3_L0_E_Phase_Bounds_s' sI8_Q_Qback_Sync_s' sI9_Qback_Discrepancy_E3_s' sI10_Qback_Unique_Vals_s' hI2_SSN_Bounds_s' sI11_x_var_Scope_s' hI1_E_Phase_Pending_Enq_s' sI12_D3_Scanned_Prefix_s' hI4_X_var_Lin_Sync_s'
        hI7_His_WF_s' hI5_SSN_Unique_s' hI6_SSN_Order_s' hI8_Val_Unique_s'
        hI9_Deq_Ret_Unique_s' hI10_Enq_Call_Existence_s' hI11_Enq_Ret_Existence_s' hI12_D_Phase_Pending_Deq_s' hI13_Qback_Deq_Sync_s' hI14_Pending_Enq_Qback_Exclusivity_s' hI15_Deq_Result_Exclusivity_s' hI16_BO_BT_No_HB_s' hI17_BT_BT_No_HB_s' hI18_Idx_Order_No_Rev_HB_s' hI19_Scanner_Catches_Later_Enq_s'
        hI20_Enq_Val_Valid_s' hI21_Ret_Implies_Call_s' hI22_Deq_Local_Pattern_s' hI23_Deq_Call_Ret_Balanced_s' hI24_HB_Implies_Idx_Order_s' hI25_Enq_Call_Ret_Balanced_s' hI26_DeqRet_D4_Mutex_s'
        hI27_Pending_PC_Sync_s' hI28_Fresh_Enq_Immunity_s' hI29_E2_Scanner_Immunity_s' hI30_Ticket_HB_Immunity_s'
        lI1_Op_Sets_Equivalence_s' lI2_Op_Cardinality_s' lI3_HB_Ret_Lin_Sync_s' lI4_FIFO_Semantics_s' lI5_SA_Prefix_s' lI6_D4_Deq_Linearized_s' lI7_D4_Deq_Deq_HB_s' lI8_D3_Deq_Returned_s' lI9_D1_D2_Deq_Returned_s' lI10_D4_Enq_Deq_HB_s' lI11_D4_Deq_Unique_s' uI1_USpec_EffOps_Lin_s' uI2_USpec_E1UE2_s' uI3_USpec_D3UD2_s' di_s'
      by blast
qed



(* ================================================================== *)
(* Use the relevant invariant, lemma, or hypothesis. Related symbols: L0, L0Proof. *)
(* Prove the required intermediate property. *)
(* ================================================================== *)

lemma L0_E1_preserves_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "L0 p s s'"
  assumes E1: "program_counter s' p = ''E1''"
  shows
    "hI3_L0_E_Phase_Bounds s' \<and>
     hI2_SSN_Bounds s' \<and>
     sI11_x_var_Scope s' \<and>
     hI1_E_Phase_Pending_Enq s' \<and>
     sI12_D3_Scanned_Prefix s' \<and>
     hI4_X_var_Lin_Sync s' \<and>
     hI7_His_WF s' \<and>
     hI8_Val_Unique s' \<and>
     hI5_SSN_Unique s' \<and>
     hI6_SSN_Order s' \<and>
     hI9_Deq_Ret_Unique s' \<and>
     hI10_Enq_Call_Existence s' \<and>
     hI11_Enq_Ret_Existence s' \<and>
     hI12_D_Phase_Pending_Deq s' \<and>
     hI13_Qback_Deq_Sync s' \<and>
     hI14_Pending_Enq_Qback_Exclusivity s' \<and>
     hI15_Deq_Result_Exclusivity s' \<and>
     hI16_BO_BT_No_HB s' \<and>
     hI17_BT_BT_No_HB s' \<and>
     hI18_Idx_Order_No_Rev_HB s' \<and>
     hI19_Scanner_Catches_Later_Enq s' \<and>
     hI20_Enq_Val_Valid s' \<and>
     hI21_Ret_Implies_Call s' \<and>
     hI22_Deq_Local_Pattern s' \<and>
     hI23_Deq_Call_Ret_Balanced s' \<and>
     hI24_HB_Implies_Idx_Order s' \<and>
     hI25_Enq_Call_Ret_Balanced s' \<and>
     hI26_DeqRet_D4_Mutex s' \<and>
     hI27_Pending_PC_Sync s' \<and>
     hI28_Fresh_Enq_Immunity s' \<and>
     hI29_E2_Scanner_Immunity s' \<and>
     hI30_Ticket_HB_Immunity s' \<and>
     lI1_Op_Sets_Equivalence s' \<and>
     lI2_Op_Cardinality s' \<and>
     lI3_HB_Ret_Lin_Sync s' \<and>
     lI4_FIFO_Semantics s' \<and>
     lI5_SA_Prefix s' \<and>
     lI6_D4_Deq_Linearized s' \<and>
     lI7_D4_Deq_Deq_HB s' \<and>
     lI8_D3_Deq_Returned s' \<and>
     lI9_D1_D2_Deq_Returned s' \<and>
     lI10_D4_Enq_Deq_HB s' \<and>
     lI11_D4_Deq_Unique s' \<and>
     data_independent (lin_seq s')"
  using L0_E1_preserves_invariant_branch[OF INV STEP E1]
  unfolding system_invariant_def
  by auto

lemma L0_D1_preserves_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "L0 p s s'"
  assumes D1: "program_counter s' p = ''D1''"
  shows
    "hI3_L0_E_Phase_Bounds s' \<and>
     hI2_SSN_Bounds s' \<and>
     sI11_x_var_Scope s' \<and>
     hI1_E_Phase_Pending_Enq s' \<and>
     sI12_D3_Scanned_Prefix s' \<and>
     hI4_X_var_Lin_Sync s' \<and>
     hI7_His_WF s' \<and>
     hI8_Val_Unique s' \<and>
     hI5_SSN_Unique s' \<and>
     hI6_SSN_Order s' \<and>
     hI9_Deq_Ret_Unique s' \<and>
     hI10_Enq_Call_Existence s' \<and>
     hI11_Enq_Ret_Existence s' \<and>
     hI12_D_Phase_Pending_Deq s' \<and>
     hI13_Qback_Deq_Sync s' \<and>
     hI14_Pending_Enq_Qback_Exclusivity s' \<and>
     hI15_Deq_Result_Exclusivity s' \<and>
     hI16_BO_BT_No_HB s' \<and>
     hI17_BT_BT_No_HB s' \<and>
     hI18_Idx_Order_No_Rev_HB s' \<and>
     hI19_Scanner_Catches_Later_Enq s' \<and>
     hI20_Enq_Val_Valid s' \<and>
     hI21_Ret_Implies_Call s' \<and>
     hI22_Deq_Local_Pattern s' \<and>
     hI23_Deq_Call_Ret_Balanced s' \<and>
     hI24_HB_Implies_Idx_Order s' \<and>
     hI25_Enq_Call_Ret_Balanced s' \<and>
     hI26_DeqRet_D4_Mutex s' \<and>
     hI27_Pending_PC_Sync s' \<and>
     hI28_Fresh_Enq_Immunity s' \<and>
     hI29_E2_Scanner_Immunity s' \<and>
     hI30_Ticket_HB_Immunity s' \<and>
     lI1_Op_Sets_Equivalence s' \<and>
     lI2_Op_Cardinality s' \<and>
     lI3_HB_Ret_Lin_Sync s' \<and>
     lI4_FIFO_Semantics s' \<and>
     lI5_SA_Prefix s' \<and>
     lI6_D4_Deq_Linearized s' \<and>
     lI7_D4_Deq_Deq_HB s' \<and>
     lI8_D3_Deq_Returned s' \<and>
     lI9_D1_D2_Deq_Returned s' \<and>
     lI10_D4_Enq_Deq_HB s' \<and>
     lI11_D4_Deq_Unique s' \<and>
     data_independent (lin_seq s')"
  using L0_D1_preserves_invariant_branch[OF INV STEP D1]
  unfolding system_invariant_def
  by auto


lemma L0_E1_preserves_uspec_invs_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "L0 p s s'"
  assumes E1: "program_counter s' p = ''E1''"
  shows "uI1_USpec_EffOps_Lin s' \<and> uI2_USpec_E1UE2 s' \<and> uI3_USpec_D3UD2 s'"
  using L0_E1_preserves_invariant_branch[OF INV STEP E1]
  unfolding system_invariant_def
  by auto

lemma L0_D1_preserves_uspec_invs_rest:
  fixes s s' :: SysState and p :: nat
  assumes INV: "system_invariant s"
  assumes STEP: "L0 p s s'"
  assumes D1: "program_counter s' p = ''D1''"
  shows "uI1_USpec_EffOps_Lin s' \<and> uI2_USpec_E1UE2 s' \<and> uI3_USpec_D3UD2 s'"
  using L0_D1_preserves_invariant_branch[OF INV STEP D1]
  unfolding system_invariant_def
  by auto

end
