theory Model
  imports 
    Main 
    "HOL-Library.Multiset"
begin

(* Type definitions *)
datatype mname = enq | deq
datatype cr_type = call | ret

(* ========================================================== *)
(* Action and operation records with SSN (Session Sequence Number) *)
(* ========================================================== *)
type_synonym ActRec = "mname \<times> nat \<times> nat \<times> nat \<times> cr_type"
type_synonym OpRec = "mname \<times> nat \<times> nat \<times> nat"

(* Accessors for tuple fields *)
definition act_name :: "ActRec \<Rightarrow> mname" where "act_name e = fst e"
definition act_val :: "ActRec \<Rightarrow> nat" where "act_val e = fst (snd e)"
definition act_pid :: "ActRec \<Rightarrow> nat" where "act_pid e = fst (snd (snd e))"
definition act_ssn :: "ActRec \<Rightarrow> nat" where "act_ssn e = fst (snd (snd (snd e)))"
definition act_cr :: "ActRec \<Rightarrow> cr_type" where "act_cr e = snd (snd (snd (snd e)))"

definition op_name :: "OpRec \<Rightarrow> mname" where "op_name a = fst a"
definition op_val :: "OpRec \<Rightarrow> nat" where "op_val a = fst (snd a)"
definition op_pid :: "OpRec \<Rightarrow> nat" where "op_pid a = fst (snd (snd a))"
definition op_ssn :: "OpRec \<Rightarrow> nat" where "op_ssn a = snd (snd (snd a))"

(* Constructors *)
definition mk_act :: "mname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cr_type \<Rightarrow> ActRec" where
  "mk_act m v p sn cr = (m, v, p, sn, cr)"

definition mk_op :: "mname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> OpRec" where
  "mk_op m v p sn = (m, v, p, sn)"

(* Constants *)
definition BOT :: nat where "BOT = 0"

(* definition ProcSet :: "nat set" where "ProcSet = UNIV" *)

axiomatization N_Procs :: nat where 
  N_Procs_gt_0: "N_Procs > 0"

(* The process set is the bounded natural interval [0, N_Procs). *)
definition ProcSet :: "nat set" where 
  "ProcSet = {0..<N_Procs}"

lemma finite_ProcSet [simp]: "finite ProcSet"
  unfolding ProcSet_def by simp

lemma ProcSet_iff [simp]: "p \<in> ProcSet \<longleftrightarrow> p < N_Procs"
  unfolding ProcSet_def by simp

lemma ProcSet_nonempty: "ProcSet \<noteq> {}"
  using N_Procs_gt_0 unfolding ProcSet_def by auto

lemma zero_in_ProcSet [simp]: "0 \<in> ProcSet"
  using N_Procs_gt_0 unfolding ProcSet_def by auto

definition Val :: "nat set" where "Val = {n. n > 0}"


(* ========================================================== *)
(* 1. State decomposition: concrete vs. abstract components   *)
(* ========================================================== *)

record CState =
  c_program_counter :: "nat \<Rightarrow> string"
  X_var :: nat
  Q_arr :: "nat \<Rightarrow> nat"
  i_var :: "nat \<Rightarrow> nat"
  j_var :: "nat \<Rightarrow> nat"
  l_var :: "nat \<Rightarrow> nat"
  x_var :: "nat \<Rightarrow> nat"
  v_var :: "nat \<Rightarrow> nat"
  (* Auxiliary variables maintained in the concrete state *)
  Qback_arr :: "nat \<Rightarrow> nat"
  V_var :: nat

record UState =
  u_program_counter :: "nat \<Rightarrow> string"
  u_lin_seq :: "OpRec list"
  u_his_seq :: "ActRec list"
  (* Abstract-state variables *)
  S_var :: "nat \<Rightarrow> nat"


type_synonym SysState = "CState \<times> UState"

(* ========================================================== *)
(* 2. Accessor bridge from SysState to its components         *)
(* ========================================================== *)

definition program_counter :: "SysState \<Rightarrow> nat \<Rightarrow> string" where "program_counter s p = c_program_counter (fst s) p"
definition X_var :: "SysState \<Rightarrow> nat" where "X_var s = CState.X_var (fst s)"
definition V_var :: "SysState \<Rightarrow> nat" where "V_var s = CState.V_var (fst s)"
definition Q_arr :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "Q_arr s = CState.Q_arr (fst s)"
definition Qback_arr :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "Qback_arr s = CState.Qback_arr (fst s)"
definition i_var :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "i_var s = CState.i_var (fst s)"
definition j_var :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "j_var s = CState.j_var (fst s)"
definition l_var :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "l_var s = CState.l_var (fst s)"
definition x_var :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "x_var s = CState.x_var (fst s)"
definition v_var :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "v_var s = CState.v_var (fst s)"
definition s_var :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where "s_var s = UState.S_var (snd s)"

definition lin_seq :: "SysState \<Rightarrow> OpRec list" where "lin_seq s = u_lin_seq (snd s)"
definition his_seq :: "SysState \<Rightarrow> ActRec list" where "his_seq s = u_his_seq (snd s)"


definition Simulate_PC :: "SysState \<Rightarrow> bool" where
  "Simulate_PC s \<equiv> (\<forall>p.
    (c_program_counter (fst s) p = ''L0'' \<longleftrightarrow> u_program_counter (snd s) p = ''UL0'') \<and>    
    (c_program_counter (fst s) p = ''E1'' \<longleftrightarrow> u_program_counter (snd s) p = ''UE2'') \<and>
    (c_program_counter (fst s) p \<in> {''E2'', ''E3''} \<longleftrightarrow> u_program_counter (snd s) p = ''UE3'') \<and>    
    (c_program_counter (fst s) p \<in> {''D1'', ''D2'', ''D3''} \<longleftrightarrow> u_program_counter (snd s) p = ''UD2'') \<and>
    (c_program_counter (fst s) p = ''D4'' \<longleftrightarrow> u_program_counter (snd s) p = ''UD3'')
  )"

definition data_independent :: "OpRec list \<Rightarrow> bool" where
  "data_independent L \<equiv> 
   (\<forall>v. card {i. i < length L \<and> op_name (L ! i) = enq \<and> op_val (L ! i) = v} \<le> 1) \<and>
   (\<forall>v. card {i. i < length L \<and> op_name (L ! i) = deq \<and> op_val (L ! i) = v} \<le> 1)"


(* ========================================================== *)
(* Core happens-before definitions based on SSN matching      *)
(* ========================================================== *)

definition match_call :: "ActRec list \<Rightarrow> nat \<Rightarrow> OpRec \<Rightarrow> bool" where
  "match_call H k act \<equiv> 
    k < length H \<and>
    (let e = H ! k in
     act_name e = op_name act \<and> act_pid e = op_pid act \<and> 
     act_ssn e = op_ssn act \<and> act_val e = (if op_name act = deq then BOT else op_val act) \<and> 
     act_cr e = call)"

definition match_ret :: "ActRec list \<Rightarrow> nat \<Rightarrow> OpRec \<Rightarrow> bool" where
  "match_ret H k act \<equiv> 
    k < length H \<and>
    (let e = H ! k in
     act_name e = op_name act \<and> act_pid e = op_pid act \<and> 
     act_ssn e = op_ssn act \<and> act_val e = op_val act \<and> act_cr e = ret)"

definition HB :: "ActRec list \<Rightarrow> OpRec \<Rightarrow> OpRec \<Rightarrow> bool" where
  "HB H act1 act2 \<equiv> (
    \<exists>k1 k2. k1 < k2 \<and> match_ret H k1 act1 \<and> match_call H k2 act2
  )"

abbreviation happens_before :: "OpRec \<Rightarrow> OpRec \<Rightarrow> ActRec list \<Rightarrow> bool" where
  "happens_before a b H \<equiv> HB H a b"

definition HB_Act :: "SysState \<Rightarrow> OpRec \<Rightarrow> OpRec \<Rightarrow> bool" where
  "HB_Act s a b \<equiv> HB (his_seq s) a b"

definition HB_consistent :: "OpRec list \<Rightarrow> ActRec list \<Rightarrow> bool" where 
  "HB_consistent L H \<equiv> (\<forall>k1 k2. k1 < length L \<and> k2 < length L \<and> 
    HB H (L!k1) (L!k2) \<longrightarrow> k1 < k2)"


(* ========== Distance measure and modify_lin ========== *)

definition find_indices :: "(OpRec \<Rightarrow> bool) \<Rightarrow> OpRec list \<Rightarrow> nat list" where
  "find_indices P L = [i \<leftarrow> [0..<length L]. P (L ! i)]"

definition find_unique_index :: "(OpRec \<Rightarrow> bool) \<Rightarrow> OpRec list \<Rightarrow> nat option" where
  "find_unique_index P L = (
    let indices = find_indices P L in
    if indices = [] then None else Some (hd indices)
  )"

definition in_SA :: "nat \<Rightarrow> OpRec list \<Rightarrow> bool" where
  "in_SA v L =
    (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = v) L of
       None \<Rightarrow> False
     | Some enq_idx \<Rightarrow>
       (case find_unique_index (\<lambda>a. op_name a = deq \<and> op_val a = v) L of
            None \<Rightarrow> False
          | Some deq_idx \<Rightarrow> True))"

definition distance_func :: "nat \<Rightarrow> nat \<Rightarrow> OpRec list \<Rightarrow> nat" where
  "distance_func x_val bt_val L =
     (if in_SA x_val L then 0
      else
        (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = x_val) L of
           None \<Rightarrow> 0
         | Some pos_x \<Rightarrow>
             (case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) L of
                None \<Rightarrow> 0
              | Some pos_bt \<Rightarrow>
                 if pos_x < pos_bt then pos_bt - pos_x
                 else 0)))"

definition Distance :: "OpRec list \<Rightarrow> nat \<Rightarrow> nat" where
  "Distance L bt_val = (
    let all_enqueues = filter (\<lambda>a. op_name a = enq) L in
    let enqueued_values = set (map op_val all_enqueues) in
    sum_list (map (\<lambda>v. distance_func v bt_val L) (sorted_list_of_set enqueued_values))
  )"

definition find_last_SA :: "OpRec list \<Rightarrow> int" where
  "find_last_SA L = (
    let sa_indices = find_indices (\<lambda>a. op_name a = enq \<and> in_SA (op_val a) L) L in
    if sa_indices = [] then -1 else int (last sa_indices)
  )"

definition find_last_enq :: "OpRec list \<Rightarrow> (OpRec list \<times> OpRec \<times> OpRec list) option" where
  "find_last_enq L = (
    let enq_indices = find_indices (\<lambda>a. op_name a = enq) L in
    if enq_indices = [] then None
    else (
      let last_idx = last enq_indices in
      let before = take last_idx L in
      let enq_act = L ! last_idx in
      let after = drop (last_idx + 1) L in
      Some (before, enq_act, after)
    )
  )"

definition should_modify :: "OpRec list \<Rightarrow> ActRec list \<Rightarrow> nat \<Rightarrow> bool" where
  "should_modify L H bt_val = (
    data_independent L \<and>
    (let dist = Distance L bt_val in dist \<noteq> 0) \<and>
    (let last_sa_pos = find_last_SA L in
     let remaining = drop (nat (last_sa_pos + 1)) L in
     case find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining of
       None \<Rightarrow> False 
     | Some bt_idx \<Rightarrow>
         let l2 = take bt_idx remaining in
         l2 \<noteq> [] \<and> 
         (let l2_last = last l2 in
          op_name l2_last = enq \<or> 
          (case find_last_enq l2 of
             None \<Rightarrow> False
           | Some (l21, b_act, l22) \<Rightarrow> l22 \<noteq> [] 
          )
         )
    )
  )"

function modify_lin :: "OpRec list \<Rightarrow> ActRec list \<Rightarrow> nat \<Rightarrow> OpRec list" where
  "modify_lin L H bt_val = (
    if \<not> should_modify L H bt_val then L
    else
      let dist = Distance L bt_val in
      let last_sa_pos = find_last_SA L in
      let l1 = take (nat (last_sa_pos + 1)) L in
      let remaining = drop (nat (last_sa_pos + 1)) L in
      let bt_idx = the (find_unique_index (\<lambda>a. op_name a = enq \<and> op_val a = bt_val) remaining) in
      let bt_act = remaining ! bt_idx in
      let l2 = take bt_idx remaining in
      let l3 = drop (bt_idx + 1) remaining in
      let l2_last = last l2 in
      
      if op_name l2_last = enq then
        let ll2 = butlast l2 in
        let new_L = l1 @ ll2 @ [bt_act] @ [l2_last] @ l3 in
        modify_lin new_L H bt_val
      else
        let (l21, b_act, l22) = the (find_last_enq l2) in
        let o1 = hd l22 in
        let ou = last l22 in
        
        if happens_before o1 bt_act H then
          let new_l22 = tl l22 in
          let new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3 in
          modify_lin new_L H bt_val
        else if happens_before b_act o1 H then
          let new_L = l1 @ l21 @ [bt_act] @ [b_act] @ l22 @ l3 in
          modify_lin new_L H bt_val
        else 
          let new_l22 = tl l22 in
          let new_L = l1 @ l21 @ [o1] @ [b_act] @ new_l22 @ [bt_act] @ l3 in
          modify_lin new_L H bt_val
  )"
by pat_completeness auto


(* ========================================================================= *)
(* Auxiliary definitions based on SSN and set-based characterizations        *)
(* ========================================================================= *)

definition QHas :: "SysState \<Rightarrow> nat \<Rightarrow> bool" where 
  "QHas s a = (\<exists>k. Q_arr s k = a)"

definition InQBack :: "SysState \<Rightarrow> nat \<Rightarrow> bool" where 
  "InQBack s a = (\<exists>k. Qback_arr s k = a)"

definition TypeA :: "SysState \<Rightarrow> nat \<Rightarrow> bool" where 
  "TypeA s a = (InQBack s a \<and> \<not> QHas s a)"

definition TypeB :: "SysState \<Rightarrow> nat \<Rightarrow> bool" where 
  "TypeB s a = (QHas s a \<or> (\<exists>p. program_counter s p = ''E2'' \<and> v_var s p = a))"

definition AtIdx :: "SysState \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where 
  "AtIdx s a k = (Qback_arr s k = a)"

definition Idx :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where 
  "Idx s a = (SOME k. AtIdx s a k)"  

definition TypeBT :: "SysState \<Rightarrow> nat \<Rightarrow> bool" where
  "TypeBT s a = (
    TypeB s a \<and> 
    InQBack s a \<and>
    ( (\<forall>k. k < Idx s a \<longrightarrow> Q_arr s k = BOT) \<or>
      (\<exists>p. program_counter s p = ''D3'' \<and>
           j_var s p \<le> Idx s a \<and> 
           Idx s a < l_var s p \<and>
           (\<forall>k. j_var s p \<le> k \<and> k < Idx s a \<longrightarrow> Q_arr s k = BOT)) )
  )"

definition TypeBO :: "SysState \<Rightarrow> nat \<Rightarrow> bool" where 
  "TypeBO s a = (TypeB s a \<and> \<not> TypeBT s a)"

definition SetA :: "SysState \<Rightarrow> nat set" where 
  "SetA s = {a \<in> Val. TypeA s a}"

definition SetB :: "SysState \<Rightarrow> nat set" where 
  "SetB s = {a \<in> Val. TypeB s a}"

definition SetBT :: "SysState \<Rightarrow> nat set" where 
  "SetBT s = {a \<in> Val. TypeBT s a}"

definition SetBO :: "SysState \<Rightarrow> nat set" where 
  "SetBO s = {a \<in> Val. TypeBO s a}"

(* --- History-existence predicates --- *)

(* Number of enqueue operations among the first n linearized actions *)
definition LinEnqCount :: "SysState \<Rightarrow> nat \<Rightarrow> nat" where
  "LinEnqCount s n = (
    let sub_lin = take n (lin_seq s) in
    length (filter (\<lambda>act. op_name act = enq) sub_lin)
  )"

definition EnqCallInHis :: "SysState \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "EnqCallInHis s p a sn = (
    \<exists>e \<in> set (his_seq s). 
      act_pid e = p \<and> act_ssn e = sn \<and> act_name e = enq \<and> act_cr e = call \<and> act_val e = a
  )"

definition EnqRetInHis :: "SysState \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "EnqRetInHis s p a sn = (
    \<exists>e \<in> set (his_seq s). 
      act_pid e = p \<and> act_ssn e = sn \<and> act_name e = enq \<and> act_cr e = ret \<and> act_val e = a
  )"

definition DeqCallInHis :: "SysState \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "DeqCallInHis s p sn = (
    \<exists>e \<in> set (his_seq s). 
      act_pid e = p \<and> act_ssn e = sn \<and> act_name e = deq \<and> act_cr e = call \<and> act_val e = BOT
  )"

definition DeqRetInHis :: "SysState \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "DeqRetInHis s p a sn = (
    \<exists>e \<in> set (his_seq s). 
      act_pid e = p \<and> act_ssn e = sn \<and> act_name e = deq \<and> act_cr e = ret \<and> act_val e = a
  )"

(* --- Pending-operation predicates --- *)

definition HasPendingEnq :: "SysState \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "HasPendingEnq s p a = (
    let cur_sn = s_var s p in
    EnqCallInHis s p a cur_sn \<and> 
    (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = p \<and> act_ssn e = cur_sn \<and> act_cr e = ret))
  )"

definition HasPendingDeq :: "SysState \<Rightarrow> nat \<Rightarrow> bool" where
  "HasPendingDeq s p = (
    let cur_sn = s_var s p in
    DeqCallInHis s p cur_sn \<and> 
    (\<forall>e \<in> set (his_seq s). \<not> (act_pid e = p \<and> act_ssn e = cur_sn \<and> act_cr e = ret))
  )"

(* --- Auxiliary happens-before checks for SSN-identified operations --- *)
definition HB_EnqRetCall :: "SysState \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where 
  "HB_EnqRetCall s v1 v2 \<equiv> 
    \<exists>p1 p2 sn1 sn2. HB_Act s (mk_op enq v1 p1 sn1) (mk_op enq v2 p2 sn2)"

(* ========== Linearization sets and operation classes ========== *)

definition EnqIdxs :: "SysState \<Rightarrow> nat \<Rightarrow> nat set" where
  "EnqIdxs s a = {k. k < length (lin_seq s) \<and> op_name (lin_seq s ! k) = enq \<and> op_val (lin_seq s ! k) = a}"

definition DeqIdxs :: "SysState \<Rightarrow> nat \<Rightarrow> nat set" where
  "DeqIdxs s a = {k. k < length (lin_seq s) \<and> op_name (lin_seq s ! k) = deq \<and> op_val (lin_seq s ! k) = a}"

definition OPLin :: "SysState \<Rightarrow> OpRec set" where 
  "OPLin s = set (lin_seq s)"

(* Alternative characterization of operation sets using SSN-based identifiers *)
(*
definition OP_A_enq :: "SysState \<Rightarrow> OpRec set" where
  "OP_A_enq s = {mk_op enq a p sn | p a sn. 
    a \<in> SetA s \<and> EnqCallInHis s p a sn \<and> EnqRetInHis s p a sn
  }"
*)
definition OP_A_enq :: "SysState \<Rightarrow> OpRec set" where
  "OP_A_enq s = {mk_op enq a p sn | p a sn. a \<in> SetA s \<and> EnqCallInHis s p a sn}"

definition OP_A_deq :: "SysState \<Rightarrow> OpRec set" where
  "OP_A_deq s = {act \<in> OPLin s. 
    op_name act = deq \<and> op_val act \<in> SetA s \<and> 
    DeqCallInHis s (op_pid act) (op_ssn act)
  }"

definition OP_B_enq :: "SysState \<Rightarrow> OpRec set" where
  "OP_B_enq s = {mk_op enq b p sn | p b sn. 
    b \<in> SetB s \<and> EnqCallInHis s p b sn
  }"

definition active_enqs :: "SysState \<Rightarrow> OpRec set" where 
  "active_enqs s = OP_B_enq s"



(* ========================================================== *)
(* Invariants for the HWQ-to-U^s_Queue simulation             *)
(* They are organized into three classes:                     *)
(*   1. state invariants,                                     *)
(*   2. history invariants, and                               *)
(*   3. linearization-sequence invariants.                    *)
(* ========================================================== *)

(* ========================================================================= *)
(* State invariants                                                          *)
(* This class includes type/range constraints and structural invariants      *)
(* over the HWQ state used in the simulation relation.                       *)
(* ========================================================================= *)

definition TypeOK :: "SysState \<Rightarrow> bool" where
  "TypeOK s = (
    (\<forall>p. program_counter s p \<in> {''L0'', ''E1'', ''E2'', ''E3'', ''D1'', ''D2'', ''D3'', ''D4''}) \<and>
    X_var s \<in> Val \<and> 
    V_var s \<in> Val \<and>
    (\<forall>idx. Q_arr s idx \<in> Val \<union> {BOT}) \<and>
    (\<forall>idx. Qback_arr s idx \<in> Val \<union> {BOT}) \<and>
    (\<forall>p. i_var s p \<in> Val \<union> {BOT}) \<and>
    (\<forall>p. j_var s p \<in> Val \<union> {BOT}) \<and>
    (\<forall>p. l_var s p \<in> Val \<union> {BOT}) \<and>
    (\<forall>p. x_var s p \<in> Val \<union> {BOT}) \<and>
    (\<forall>p. v_var s p \<in> Val \<union> {BOT}) \<and>
    (\<forall>p. s_var s p \<in> Val) 
  )"



definition sI1_Zero_Index_BOT :: "SysState \<Rightarrow> bool" where 
  "sI1_Zero_Index_BOT s = (Q_arr s 0 = BOT \<and> Qback_arr s 0 = BOT)"

definition sI2_X_var_Upper_Bound :: "SysState \<Rightarrow> bool" where 
  "sI2_X_var_Upper_Bound s = (
    X_var s \<in> Val \<and> 
    (\<forall>k. k \<ge> X_var s \<longrightarrow> Q_arr s k = BOT \<and> Qback_arr s k = BOT)
  )"

definition sI3_E2_Slot_Exclusive :: "SysState \<Rightarrow> bool" where
  "sI3_E2_Slot_Exclusive s \<equiv> (
    \<forall>p. program_counter s p = ''E2'' \<longrightarrow>
      (i_var s p \<in> Val \<and> 
       i_var s p < X_var s \<and> 
       Q_arr s (i_var s p) = BOT \<and> 
       Qback_arr s (i_var s p) = BOT \<and>
       (\<forall>q. q \<noteq> p \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p \<noteq> i_var s q))
  )"

definition sI4_E3_Qback_Written :: "SysState \<Rightarrow> bool" where
  "sI4_E3_Qback_Written s \<equiv> (
    \<forall>p. program_counter s p = ''E3'' \<longrightarrow>
      (i_var s p \<in> Val \<and> 
       i_var s p < X_var s \<and> 
       (Q_arr s (i_var s p) = v_var s p \<or> Q_arr s (i_var s p) = BOT) \<and> 
       Qback_arr s (i_var s p) = v_var s p \<and> 
       (\<forall>q. q \<noteq> p \<and> program_counter s q \<in> {''E2'', ''E3''} \<longrightarrow> i_var s p \<noteq> i_var s q))
  )"

definition sI5_D2_Local_Bound :: "SysState \<Rightarrow> bool" where 
  "sI5_D2_Local_Bound s = (
    \<forall>p. program_counter s p = ''D2'' \<longrightarrow> 
      l_var s p \<in> Val \<and> 
      1 \<le> l_var s p \<and> 
      l_var s p \<le> X_var s
  )"

definition sI6_D3_Scan_Pointers :: "SysState \<Rightarrow> bool" where 
  "sI6_D3_Scan_Pointers s = (
    \<forall>p. program_counter s p = ''D3'' \<longrightarrow> 
      j_var s p \<in> Val \<and> 
      l_var s p \<in> Val \<and> 
      1 \<le> j_var s p \<and> 
      j_var s p < l_var s p \<and> 
      l_var s p \<le> X_var s
  )"

definition sI7_D4_Deq_Result :: "SysState \<Rightarrow> bool" where 
  "sI7_D4_Deq_Result s = (
    \<forall>p. program_counter s p = ''D4'' \<longrightarrow> 
      j_var s p \<in> Val \<and> 
      Q_arr s (j_var s p) = BOT \<and> 
      Qback_arr s (j_var s p) = x_var s p \<and> 
      x_var s p \<noteq> BOT
  )"


definition sI8_Q_Qback_Sync :: "SysState \<Rightarrow> bool" where 
  "sI8_Q_Qback_Sync s = (\<forall>k. (Q_arr s k = Qback_arr s k) \<or> (Q_arr s k = BOT))"

definition sI9_Qback_Discrepancy_E3 :: "SysState \<Rightarrow> bool" where 
  "sI9_Qback_Discrepancy_E3 s = (
    \<forall>k. (Q_arr s k = BOT \<and> Qback_arr s k \<noteq> BOT) \<longrightarrow> 
        (\<forall>p. (program_counter s p \<in> {''E3''} \<and> i_var s p = k) \<longrightarrow> v_var s p = Qback_arr s k)
  )"

definition sI10_Qback_Unique_Vals :: "SysState \<Rightarrow> bool" where 
  "sI10_Qback_Unique_Vals s = (
    \<forall>k1 k2. k1 \<noteq> k2 \<and> Qback_arr s k1 \<noteq> BOT \<and> Qback_arr s k2 \<noteq> BOT 
            \<longrightarrow> Qback_arr s k1 \<noteq> Qback_arr s k2
  )"

definition sI11_x_var_Scope :: "SysState \<Rightarrow> bool" where 
  "sI11_x_var_Scope s = (\<forall>p. program_counter s p \<noteq> ''D4'' \<longrightarrow> x_var s p = BOT)"


definition sI12_D3_Scanned_Prefix :: "SysState \<Rightarrow> bool" where 
  "sI12_D3_Scanned_Prefix s = (
    \<forall>p. program_counter s p = ''D3'' \<longrightarrow> 
      (\<forall>k < j_var s p. Q_arr s k = BOT \<or> TypeB s (Q_arr s k))
  )"

(* ========================================================================= *)
(* History invariants                                                        *)
(* This class constrains the history sequence and its relation to the        *)
(* current HWQ/U state.                                                      *)
(* ========================================================================= *)

definition hI1_E_Phase_Pending_Enq :: "SysState \<Rightarrow> bool" where 
  "hI1_E_Phase_Pending_Enq s = (
    \<forall>p. program_counter s p \<in> {''E1'', ''E2'', ''E3''} \<longrightarrow> HasPendingEnq s p (v_var s p)
  )"

definition hI2_SSN_Bounds :: "SysState \<Rightarrow> bool" where
  "hI2_SSN_Bounds s = (
    \<forall>p. \<forall>e \<in> set (his_seq s). act_pid e = p \<longrightarrow> 
      (act_ssn e \<le> s_var s p \<and> 
      (program_counter s p = ''L0'' \<longrightarrow> act_ssn e < s_var s p))
  )"

(* ========================================================================= *)
(* hI3_L0_E_Phase_Bounds: idle-state cleanliness and enqueue-value freshness  *)
(* Idle processes have no pending operations, while active enqueue values     *)
(* and recorded enqueue calls remain below the current V_var bound.           *)
(* ========================================================================= *)
definition hI3_L0_E_Phase_Bounds :: "SysState \<Rightarrow> bool" where
  "hI3_L0_E_Phase_Bounds s \<equiv>
     (\<forall>q. program_counter s q = ''L0'' \<longrightarrow> (\<forall>a. \<not> HasPendingEnq s q a) \<and> \<not> HasPendingDeq s q) \<and>
     (\<forall>q. program_counter s q = ''L0'' \<longrightarrow>
          length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = call) (his_seq s)) =
          length (filter (\<lambda>e. act_pid e = q \<and> act_name e = deq \<and> act_cr e = ret) (his_seq s))) \<and>
     (\<forall>q. program_counter s q \<in> {''E1'', ''E2'', ''E3''} \<longrightarrow> v_var s q < V_var s) \<and>
     (\<forall>k<length (his_seq s).
          act_name (his_seq s ! k) = enq \<and> act_cr (his_seq s ! k) = call \<longrightarrow>
          act_val (his_seq s ! k) < V_var s) \<and>
     (\<forall>k. Qback_arr s k = BOT \<or> Qback_arr s k < V_var s)"

(* ========================================================================= *)
(* hI4_X_var_Lin_Sync: X_var matches the number of linearized enqueues        *)
(* The next concrete enqueue index equals the number of linearized enqueue    *)
(* operations plus one.                                                       *)
(* ========================================================================= *)

definition hI4_X_var_Lin_Sync :: "SysState \<Rightarrow> bool" where 
  "hI4_X_var_Lin_Sync s = (X_var s = LinEnqCount s (length (lin_seq s)) + 1)"


(* ========================================================================= *)
(* Additional history invariants derived from SSN ordering                    *)
(* ========================================================================= *)

definition hI5_SSN_Unique :: "SysState \<Rightarrow> bool" where
  "hI5_SSN_Unique s = (
    \<forall>i < length (his_seq s). \<forall>j < length (his_seq s).
      act_pid (his_seq s ! i) = act_pid (his_seq s ! j) \<and>
      act_ssn (his_seq s ! i) = act_ssn (his_seq s ! j) \<and>
      act_cr (his_seq s ! i) = act_cr (his_seq s ! j) 
      \<longrightarrow> i = j
  )"

definition hI6_SSN_Order :: "SysState \<Rightarrow> bool" where
  "hI6_SSN_Order s = (
    \<forall>i < length (his_seq s). \<forall>j < length (his_seq s).
      i < j \<and> act_pid (his_seq s ! i) = act_pid (his_seq s ! j) 
      \<longrightarrow> 
      (act_ssn (his_seq s ! i) < act_ssn (his_seq s ! j) \<or> 
      (act_ssn (his_seq s ! i) = act_ssn (his_seq s ! j) \<and> 
       act_cr (his_seq s ! i) = call \<and> act_cr (his_seq s ! j) = ret))
  )"

definition hI7_His_WF :: "SysState \<Rightarrow> bool" where
  "hI7_His_WF s = (
    \<forall>k < length (his_seq s).
      let e_ret = his_seq s ! k in
      act_cr e_ret = ret \<longrightarrow>
      (\<exists>j < k.
         let e_call = his_seq s ! j in
         act_pid e_call = act_pid e_ret \<and>
         act_ssn e_call = act_ssn e_ret \<and>
         act_name e_call = act_name e_ret \<and>
         act_cr e_call = call \<and>
         (if act_name e_ret = enq 
          then act_val e_call = act_val e_ret 
          else act_val e_call = BOT))
  )"

definition hI8_Val_Unique :: "SysState \<Rightarrow> bool" where
  "hI8_Val_Unique s = (\<forall>i < length (his_seq s). \<forall>j < length (his_seq s).
     act_name (his_seq s ! i) = enq \<and> act_name (his_seq s ! j) = enq \<and>
     act_cr (his_seq s ! i) = call \<and> act_cr (his_seq s ! j) = call \<and>
     act_val (his_seq s ! i) = act_val (his_seq s ! j)
     \<longrightarrow> i = j
  )"

definition hI9_Deq_Ret_Unique :: "SysState \<Rightarrow> bool" where 
  "hI9_Deq_Ret_Unique s = (
    \<forall>i < length (his_seq s). \<forall>j < length (his_seq s). 
      act_name (his_seq s ! i) = deq \<and> 
      act_name (his_seq s ! j) = deq \<and> 
      act_cr (his_seq s ! i) = ret \<and> 
      act_cr (his_seq s ! j) = ret \<and> 
      act_val (his_seq s ! i) \<noteq> BOT \<and> 
      act_val (his_seq s ! i) = act_val (his_seq s ! j) 
      \<longrightarrow> i = j
  )"

definition hI10_Enq_Call_Existence :: "SysState \<Rightarrow> bool" where 
  "hI10_Enq_Call_Existence s = (
    (\<forall>p a. (program_counter s p \<in> {''E1'', ''E2'', ''E3''} \<and> v_var s p = a) \<longrightarrow> EnqCallInHis s p a (s_var s p)) \<and> 
    (\<forall>a. (\<exists>k. Qback_arr s k = a) \<longrightarrow> (\<exists>q sn. EnqCallInHis s q a sn))
  )"

definition hI11_Enq_Ret_Existence :: "SysState \<Rightarrow> bool" where 
  "hI11_Enq_Ret_Existence s = (
    \<forall>p a sn. 
      (program_counter s p \<notin> {''E1'', ''E2'', ''E3''} \<or> v_var s p \<noteq> a \<or> s_var s p \<noteq> sn) \<and> 
      (\<exists>k. Qback_arr s k = a) \<and> 
      EnqCallInHis s p a sn 
      \<longrightarrow> EnqRetInHis s p a sn
  )"

definition hI12_D_Phase_Pending_Deq :: "SysState \<Rightarrow> bool" where 
  "hI12_D_Phase_Pending_Deq s = (
    \<forall>p. program_counter s p \<in> {''D1'', ''D2'', ''D3'', ''D4''} \<longrightarrow> HasPendingDeq s p
  )"

definition hI13_Qback_Deq_Sync :: "SysState \<Rightarrow> bool" where 
  "hI13_Qback_Deq_Sync s \<equiv> (
    \<forall>a. a \<noteq> BOT \<longrightarrow> 
        (\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a) \<longrightarrow> 
        (\<exists>p. (program_counter s p = ''D4'' \<and> x_var s p = a) \<or> (\<exists>sn. DeqRetInHis s p a sn))
  )"

definition hI14_Pending_Enq_Qback_Exclusivity :: "SysState \<Rightarrow> bool" where 
  "hI14_Pending_Enq_Qback_Exclusivity s = (
    (\<forall>p a. (HasPendingEnq s p a \<and> program_counter s p \<in> {''E2'', ''E3''}) \<longrightarrow> 
           \<not> (\<exists>k. Qback_arr s k = a \<and> k \<noteq> i_var s p)) \<and> 
    (\<forall>p a. (HasPendingEnq s p a \<and> program_counter s p = ''E1'') \<longrightarrow> 
           \<not> (\<exists>k. Qback_arr s k = a))
  )"

definition hI15_Deq_Result_Exclusivity :: "SysState \<Rightarrow> bool" where 
  "hI15_Deq_Result_Exclusivity s = (
    (\<forall>a p1 p2. a \<in> Val \<longrightarrow> p1 \<noteq> p2 \<longrightarrow> 
       \<not> (((\<exists>sn1. DeqRetInHis s p1 a sn1) \<or> (program_counter s p1 = ''D4'' \<and> x_var s p1 = a)) \<and> 
          ((\<exists>sn2. DeqRetInHis s p2 a sn2) \<or> (program_counter s p2 = ''D4'' \<and> x_var s p2 = a)))) \<and> 
    (\<forall>p a k. a \<in> Val \<longrightarrow> HasPendingDeq s p \<longrightarrow> \<not> (x_var s p = a \<and> Q_arr s k = a)) \<and> 
    (\<forall>p a. a \<in> Val \<longrightarrow> (\<exists>sn. DeqRetInHis s p a sn) \<longrightarrow> (\<forall>k. Q_arr s k \<noteq> a))
  )"

definition hI16_BO_BT_No_HB :: "SysState \<Rightarrow> bool" where 
  "hI16_BO_BT_No_HB s = (
    \<forall>a b. a \<in> SetBO s \<and> b \<in> SetBT s \<longrightarrow> \<not> HB_EnqRetCall s a b
  )"

definition hI17_BT_BT_No_HB :: "SysState \<Rightarrow> bool" where 
  "hI17_BT_BT_No_HB s = (
    \<forall>a b. a \<in> SetBT s \<and> b \<in> SetBT s \<longrightarrow> \<not> HB_EnqRetCall s a b
  )"

definition hI18_Idx_Order_No_Rev_HB :: "SysState \<Rightarrow> bool" where 
  "hI18_Idx_Order_No_Rev_HB s = (
    \<forall>a b. InQBack s a \<and> InQBack s b \<and> Idx s a < Idx s b \<longrightarrow> \<not> HB_EnqRetCall s b a
  )"

definition hI19_Scanner_Catches_Later_Enq :: "SysState \<Rightarrow> bool" where
"hI19_Scanner_Catches_Later_Enq s \<equiv> \<forall>a b. InQBack s a \<and> InQBack s b \<and> TypeB s a \<and> TypeB s b \<and> Idx s a < Idx s b \<and> 
               (\<exists>q. HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and> 
                    Idx s a < j_var s q \<and> j_var s q \<le> Idx s b \<and> Idx s b < l_var s q) 
               \<longrightarrow> \<not> HB_EnqRetCall s a b"

definition hI20_Enq_Val_Valid :: "SysState \<Rightarrow> bool" where 
  "hI20_Enq_Val_Valid s = (
    \<forall>k < length (his_seq s). 
      act_name (his_seq s ! k) = enq \<longrightarrow> act_val (his_seq s ! k) \<in> Val
  )"

definition hI21_Ret_Implies_Call :: "SysState \<Rightarrow> bool" where 
  "hI21_Ret_Implies_Call s \<equiv> 
    \<forall>k < length (his_seq s). act_cr (his_seq s ! k) = ret \<longrightarrow>
      (\<exists>tm<k. act_pid (his_seq s ! tm) = act_pid (his_seq s ! k) \<and>
              act_name (his_seq s ! tm) = act_name (his_seq s ! k) \<and>
              act_cr (his_seq s ! tm) = call \<and>
              (if act_name (his_seq s ! k) = enq 
               then act_val (his_seq s ! tm) = act_val (his_seq s ! k) 
               else act_val (his_seq s ! tm) = BOT))"

(* ========================================================================= *)
(* hI22_Deq_Local_Pattern: local history shape of dequeue operations          *)
(* A successful dequeue is represented by a matching call(BOT) and ret(a)     *)
(* pair with the same SSN.                                                     *)
(* ========================================================================= *)
definition hI22_Deq_Local_Pattern :: "SysState \<Rightarrow> bool" where
  "hI22_Deq_Local_Pattern s = (
    \<forall>p a sn.
      ((\<exists>k. Q_arr s k = BOT \<and> Qback_arr s k = a \<and> (\<forall>q. x_var s q \<noteq> a)) \<and>
      DeqRetInHis s p a sn) \<longrightarrow>
      (let p_his = filter (\<lambda>e. act_pid e = p) (his_seq s) in
      \<exists>i < length p_his. 
          p_his ! i = mk_act deq a p sn ret \<and>        
         (i > 0 \<and> p_his ! (i - 1) = mk_act deq BOT p sn call)) 
  )"

definition hI23_Deq_Call_Ret_Balanced :: "SysState \<Rightarrow> bool" where
  "hI23_Deq_Call_Ret_Balanced s = (\<forall>q. \<forall>k \<le> length (his_seq s). 
    let q_his = filter (\<lambda>e. act_pid e = q) (take k (his_seq s)) in
    length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 
    length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) \<and>    
    length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) - 
    length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his) \<le> 1 \<and>    
    (q_his \<noteq> [] \<and> act_cr (last q_his) = call \<and> act_name (last q_his) \<noteq> deq \<longrightarrow> 
     length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = call) q_his) = 
     length (filter (\<lambda>e. act_name e = deq \<and> act_cr e = ret) q_his))
  )"

definition hI24_HB_Implies_Idx_Order :: "SysState \<Rightarrow> bool" where 
  "hI24_HB_Implies_Idx_Order s = (
    \<forall>u1 u2 v1 v2 idx1 idx2 sn1 sn2. 
      HB_Act s (mk_op enq v2 u2 sn2) (mk_op enq v1 u1 sn1) \<and> 
      CState.Q_arr (fst s) idx1 = v1 \<and> 
      CState.Q_arr (fst s) idx2 = v2 
      \<longrightarrow> idx2 < idx1
  )"

definition hI25_Enq_Call_Ret_Balanced :: "SysState \<Rightarrow> bool" where
  "hI25_Enq_Call_Ret_Balanced s = (\<forall>p. \<forall>k \<le> length (his_seq s).
    let p_his = filter (\<lambda>e. act_pid e = p \<and> act_name e = enq) (take k (his_seq s)) in
    let n_call = length (filter (\<lambda>e. act_cr e = call) p_his) in
    let n_ret  = length (filter (\<lambda>e. act_cr e = ret) p_his) in
    n_call \<ge> n_ret \<and> n_call - n_ret \<le> 1 \<and>
    (k = length (his_seq s) \<longrightarrow> (program_counter s p \<in> {''E1'', ''E2'', ''E3''} \<longleftrightarrow> n_call - n_ret = 1))
  )"

definition hI26_DeqRet_D4_Mutex :: "SysState \<Rightarrow> bool" where 
  "hI26_DeqRet_D4_Mutex s = (
    \<forall>p a. a \<in> Val \<longrightarrow> \<not> ((\<exists>sn. DeqRetInHis s p a sn) \<and> program_counter s p = ''D4'' \<and> x_var s p = a)
  )"

definition hI27_Pending_PC_Sync :: "SysState \<Rightarrow> bool" where 
  "hI27_Pending_PC_Sync s = (
    (\<forall>p. HasPendingDeq s p \<longrightarrow> program_counter s p \<in> {''D1'', ''D2'', ''D3'', ''D4''}) \<and>
    (\<forall>p. HasPendingEnq s p (v_var s p) \<longrightarrow> program_counter s p \<in> {''E1'', ''E2'', ''E3''})
  )"

definition hI28_Fresh_Enq_Immunity :: "SysState \<Rightarrow> bool" where 
  "hI28_Fresh_Enq_Immunity s = (
    \<forall>p q a sn. 
      program_counter s p \<in> {''E1'', ''E2''} \<and> v_var s p = a \<and> a \<noteq> BOT 
      \<longrightarrow> \<not> DeqRetInHis s q a sn
  )"

definition hI29_E2_Scanner_Immunity :: "SysState \<Rightarrow> bool" where 
  "hI29_E2_Scanner_Immunity s = (
    \<forall>p a q. program_counter s p = ''E2'' \<and> 
            InQBack s a \<and> TypeB s a \<and> 
            HasPendingDeq s q \<and> program_counter s q = ''D3'' \<and> 
            Idx s a < j_var s q \<and> j_var s q \<le> i_var s p \<and> i_var s p < l_var s q 
            \<longrightarrow> \<not> HB_EnqRetCall s a (v_var s p)
  )"

(* ========================================================================= *)
(* hI30_Ticket_HB_Immunity: ticket-order compatibility with happens-before    *)
(* This invariant avoids over-constraining TypeB and only relates             *)
(* happens-before information to the index order in Qback.                     *)
(* ========================================================================= *)
definition hI30_Ticket_HB_Immunity :: "SysState \<Rightarrow> bool" where
  "hI30_Ticket_HB_Immunity s \<equiv> 
    \<forall>b p. program_counter s p \<in> {''E2'', ''E3''} \<and> 
          InQBack s b \<and> b \<noteq> BOT \<and>  
          b \<noteq> v_var s p \<and> HB_EnqRetCall s b (v_var s p) 
    \<longrightarrow> Idx s b < i_var s p"

(* ========================================================================= *)
(* Linearization-sequence invariants                                         *)
(* This class constrains the linearization sequence maintained in U^s_Queue. *)
(* ========================================================================= *)

definition lI1_Op_Sets_Equivalence :: "SysState \<Rightarrow> bool" where 
  "lI1_Op_Sets_Equivalence s = (OPLin s = OP_A_enq s \<union> OP_A_deq s \<union> OP_B_enq s)"

definition lI2_Op_Cardinality :: "SysState \<Rightarrow> bool" where
  "lI2_Op_Cardinality s = (
    (\<forall>a. a \<in> SetA s \<longrightarrow> card (EnqIdxs s a) = 1 \<and> card (DeqIdxs s a) = 1) \<and>
    (\<forall>b. b \<in> SetB s \<longrightarrow> card (EnqIdxs s b) = 1 \<and> card (DeqIdxs s b) = 0)
  )"

definition lI3_HB_Ret_Lin_Sync :: "SysState \<Rightarrow> bool" where
  "lI3_HB_Ret_Lin_Sync s = (
    (\<forall>k1 k2. k1 < length (lin_seq s) \<and> k2 < length (lin_seq s) \<and>
             HB_Act s (lin_seq s ! k1) (lin_seq s ! k2) \<longrightarrow> k1 < k2) \<and>
    (\<forall>p a sn. EnqRetInHis s p a sn \<longrightarrow>
       (\<exists>k < length (lin_seq s). lin_seq s ! k = mk_op enq a p sn)) \<and>
    (\<forall>p a sn. DeqRetInHis s p a sn \<longrightarrow>
       (\<exists>k < length (lin_seq s). lin_seq s ! k = mk_op deq a p sn))
  )"

definition lI4_FIFO_Semantics_list :: "OpRec list \<Rightarrow> bool" where
  "lI4_FIFO_Semantics_list L \<equiv> (
    \<forall>k1 < length L. 
      let act1 = L ! k1 in 
      op_name act1 = deq \<longrightarrow>
      (let a = op_val act1 in
       \<exists>k2 < k1. 
         let act2 = L ! k2 in
         op_name act2 = enq \<and> op_val act2 = a \<and>
         (\<forall>k3 < k2. 
            let act3 = L ! k3 in
            op_name act3 = enq \<longrightarrow>
            (\<exists>k4. k3 < k4 \<and> k4 < k1 \<and>
                  (let act4 = L ! k4 in
                   op_name act4 = deq \<and> op_val act4 = op_val act3))))
  )"

definition lI4_FIFO_Semantics :: "SysState \<Rightarrow> bool" where 
  "lI4_FIFO_Semantics s = lI4_FIFO_Semantics_list (lin_seq s)"

definition lI5_SA_Prefix_list :: "OpRec list \<Rightarrow> bool" where
  "lI5_SA_Prefix_list L \<equiv> (
    \<forall>k < length L. 
      op_name (L ! k) = enq \<longrightarrow> 
      (in_SA (op_val (L ! k)) L \<longleftrightarrow> int k \<le> find_last_SA L)
  )"

definition lI5_SA_Prefix :: "SysState \<Rightarrow> bool" where 
  "lI5_SA_Prefix s \<equiv> lI5_SA_Prefix_list (lin_seq s)"

definition lI6_D4_Deq_Linearized :: "SysState \<Rightarrow> bool" where
  "lI6_D4_Deq_Linearized s = (
    \<forall>p. program_counter s p = ''D4'' \<longrightarrow> 
      mk_op deq (x_var s p) p (s_var s p) \<in> set (lin_seq s)
  )"

(* Use SSN-exact matching when expressing dequeue-to-dequeue happens-before constraints. *)
definition lI7_D4_Deq_Deq_HB_list :: "OpRec list \<Rightarrow> ActRec list \<Rightarrow> (nat \<Rightarrow> string) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "lI7_D4_Deq_Deq_HB_list L H pc xv sv = (
    \<forall>k1 k2 p.
      k1 < length L \<and> k2 < length L \<and>
      op_name (L ! k1) = deq \<and> 
      L ! k2 = mk_op deq (xv p) p (sv p) \<and>
      (\<forall>k3>k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p) \<and> 
      pc p = ''D4'' \<and>
      HB H (L ! k1) (L ! k2)
      \<longrightarrow> k1 < k2
  )"

definition lI7_D4_Deq_Deq_HB :: "SysState \<Rightarrow> bool" where 
  "lI7_D4_Deq_Deq_HB s = lI7_D4_Deq_Deq_HB_list (lin_seq s) (his_seq s) (\<lambda>p. program_counter s p) (\<lambda>p. x_var s p) (\<lambda>p. s_var s p)"

definition lI8_D3_Deq_Returned :: "SysState \<Rightarrow> bool" where
  "lI8_D3_Deq_Returned s \<equiv> (
    \<forall>p. program_counter s p = ''D3'' \<longrightarrow> 
      (\<forall>k < length (lin_seq s). 
        (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = p) \<longrightarrow> 
        DeqRetInHis s p (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))
  )"

definition lI9_D1_D2_Deq_Returned :: "SysState \<Rightarrow> bool" where
  "lI9_D1_D2_Deq_Returned s \<equiv> (
    \<forall>p. (program_counter s p = ''D1'' \<or> program_counter s p = ''D2'') \<longrightarrow>
      (\<forall>k < length (lin_seq s). 
        (op_name (lin_seq s ! k) = deq \<and> op_pid (lin_seq s ! k) = p) \<longrightarrow>
        DeqRetInHis s p (op_val (lin_seq s ! k)) (op_ssn (lin_seq s ! k)))
  )"

(* Analogous to lI7, but for enqueue-to-dequeue happens-before constraints. *)
definition lI10_D4_Enq_Deq_HB_list :: "OpRec list \<Rightarrow> ActRec list \<Rightarrow> (nat \<Rightarrow> string) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "lI10_D4_Enq_Deq_HB_list L H pc xv sv = (
    \<forall>k1 k2 p.
      k1 < length L \<and> k2 < length L \<and>
      op_name (L ! k1) = enq \<and> 
      L ! k2 = mk_op deq (xv p) p (sv p) \<and>
      (\<forall>k3>k2. k3 < length L \<longrightarrow> op_name (L ! k3) \<noteq> deq \<or> op_pid (L ! k3) \<noteq> p) \<and> 
      pc p = ''D4'' \<and>
      HB H (L ! k1) (L ! k2)
      \<longrightarrow> k1 < k2
  )"

definition lI10_D4_Enq_Deq_HB :: "SysState \<Rightarrow> bool" where 
  "lI10_D4_Enq_Deq_HB s = lI10_D4_Enq_Deq_HB_list (lin_seq s) (his_seq s) (\<lambda>p. program_counter s p) (\<lambda>p. x_var s p) (\<lambda>p. s_var s p)"

definition lI11_D4_Deq_Unique :: "SysState \<Rightarrow> bool" where
  "lI11_D4_Deq_Unique s = (
    \<forall>p. program_counter s p = ''D4'' \<longrightarrow>
      (\<exists>k2 < length (lin_seq s).
         lin_seq s ! k2 = mk_op deq (x_var s p) p (s_var s p) \<and>
         (\<forall>k3 < length (lin_seq s). 
            op_name (lin_seq s ! k3) = deq \<and> op_pid (lin_seq s ! k3) = p \<and> k3 \<noteq> k2 \<longrightarrow>
            k3 < k2 \<and> DeqRetInHis s p (op_val (lin_seq s ! k3)) (op_ssn (lin_seq s ! k3))))
  )"

(* ========================================================================= *)
(* Global system invariant                                                   *)
(* It is defined as the conjunction of the state invariants, history         *)
(* invariants, and linearization-sequence invariants above.                  *)
(* ========================================================================= *)

definition system_invariant :: "SysState \<Rightarrow> bool" where
  "system_invariant s \<equiv> (
    Simulate_PC s \<and>
    TypeOK s \<and>
    sI1_Zero_Index_BOT s \<and> sI2_X_var_Upper_Bound s \<and> sI3_E2_Slot_Exclusive s \<and> sI4_E3_Qback_Written s \<and> sI5_D2_Local_Bound s \<and> sI6_D3_Scan_Pointers s \<and> sI7_D4_Deq_Result s \<and>  hI3_L0_E_Phase_Bounds s \<and> 
    sI8_Q_Qback_Sync s \<and> sI9_Qback_Discrepancy_E3 s \<and> sI10_Qback_Unique_Vals s \<and> hI2_SSN_Bounds s \<and> sI11_x_var_Scope s \<and> hI1_E_Phase_Pending_Enq s \<and> sI12_D3_Scanned_Prefix s \<and> hI4_X_var_Lin_Sync s \<and>
    hI7_His_WF s \<and> hI5_SSN_Unique s \<and> hI6_SSN_Order s \<and> hI8_Val_Unique s \<and>
    hI9_Deq_Ret_Unique s \<and> hI10_Enq_Call_Existence s \<and> hI11_Enq_Ret_Existence s \<and> hI12_D_Phase_Pending_Deq s \<and> hI13_Qback_Deq_Sync s \<and> hI14_Pending_Enq_Qback_Exclusivity s \<and> hI15_Deq_Result_Exclusivity s \<and> 
    hI16_BO_BT_No_HB s \<and> hI17_BT_BT_No_HB s \<and> hI18_Idx_Order_No_Rev_HB s \<and> hI19_Scanner_Catches_Later_Enq s \<and> hI20_Enq_Val_Valid s \<and> hI21_Ret_Implies_Call s \<and> hI22_Deq_Local_Pattern s \<and>
    hI23_Deq_Call_Ret_Balanced s \<and> hI24_HB_Implies_Idx_Order s \<and> hI25_Enq_Call_Ret_Balanced s \<and> hI26_DeqRet_D4_Mutex s \<and>
    hI27_Pending_PC_Sync s \<and> hI28_Fresh_Enq_Immunity s \<and> hI29_E2_Scanner_Immunity s \<and>
    hI30_Ticket_HB_Immunity s \<and>
    lI1_Op_Sets_Equivalence s \<and> lI2_Op_Cardinality s \<and> lI3_HB_Ret_Lin_Sync s \<and> lI4_FIFO_Semantics s \<and> lI5_SA_Prefix s \<and> lI6_D4_Deq_Linearized s \<and> 
    lI7_D4_Deq_Deq_HB s \<and> lI8_D3_Deq_Returned s \<and> lI9_D1_D2_Deq_Returned s \<and> lI10_D4_Enq_Deq_HB s \<and> lI11_D4_Deq_Unique s \<and>
    data_independent (lin_seq s) 
  )"

(* ========================================================== *)
(* System transition rules with SSN synchronization           *)
(* ========================================================== *)

(* --- Concrete transitions --- *)

definition C_L0 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_L0 p cs cs' = (
    CState.c_program_counter cs p = ''L0'' \<and>
    (\<exists>new_line \<in> {''E1'', ''D1''}.
      (let new_pc = (\<lambda>x. if x = p then new_line else CState.c_program_counter cs x) in
       if new_line = ''E1'' then
         cs' = cs\<lparr> c_program_counter := new_pc, 
                   V_var := CState.V_var cs + 1, 
                   v_var := (\<lambda>x. if x = p then CState.V_var cs else CState.v_var cs x) \<rparr>
       else
         cs' = cs\<lparr> c_program_counter := new_pc \<rparr>))
  )"

definition C_E1 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_E1 p cs cs' = (
    CState.c_program_counter cs p = ''E1'' \<and>
    cs' = cs\<lparr> i_var := (\<lambda>x. if x = p then CState.X_var cs else CState.i_var cs x),
              X_var := CState.X_var cs + 1,
              c_program_counter := (\<lambda>x. if x = p then ''E2'' else CState.c_program_counter cs x) \<rparr>
  )"

definition C_E2 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_E2 p cs cs' = (
    CState.c_program_counter cs p = ''E2'' \<and>
    (let i_val = CState.i_var cs p in
     cs' = cs\<lparr> Q_arr := (\<lambda>x. if x = i_val then CState.v_var cs p else CState.Q_arr cs x),
               Qback_arr := (\<lambda>x. if x = i_val then CState.v_var cs p else CState.Qback_arr cs x),
               c_program_counter := (\<lambda>x. if x = p then ''E3'' else CState.c_program_counter cs x) \<rparr>)
  )"

definition C_E3 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_E3 p cs cs' = (
    CState.c_program_counter cs p = ''E3'' \<and>
    cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''L0'' else CState.c_program_counter cs x),
              i_var := (\<lambda>x. if x = p then BOT else CState.i_var cs x),
              v_var := (\<lambda>x. if x = p then BOT else CState.v_var cs x) \<rparr>
  )"

definition C_D1 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_D1 p cs cs' = (
    CState.c_program_counter cs p = ''D1'' \<and>
    cs' = cs\<lparr> l_var := (\<lambda>x. if x = p then CState.X_var cs else CState.l_var cs x),
              c_program_counter := (\<lambda>x. if x = p then ''D2'' else CState.c_program_counter cs x) \<rparr>
  )"

definition C_D2 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_D2 p cs cs' = (
    CState.c_program_counter cs p = ''D2'' \<and>
    (let lp = CState.l_var cs p in
     if lp = 1 then
        cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D1'' else CState.c_program_counter cs x) \<rparr>
     else
        cs' = cs\<lparr> j_var := (\<lambda>x. if x = p then 1 else CState.j_var cs x),
                  c_program_counter := (\<lambda>x. if x = p then ''D3'' else CState.c_program_counter cs x) \<rparr>)
  )"

definition C_D3 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_D3 p cs cs' = (
    CState.c_program_counter cs p = ''D3'' \<and>
    (let jp = CState.j_var cs p; lp = CState.l_var cs p; q_val = CState.Q_arr cs jp in
     cs' = cs\<lparr>
       c_program_counter := (\<lambda>x. if x = p then (if q_val = BOT then (if jp = lp - 1 then ''D1'' else ''D3'') else ''D4'') else CState.c_program_counter cs x),
       Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr cs x),
       j_var := (\<lambda>x. if x = p then (if q_val = BOT \<and> jp \<noteq> lp - 1 then jp + 1 else jp) else CState.j_var cs x),
       x_var := (\<lambda>x. if x = p then q_val else CState.x_var cs x) \<rparr>)
  )"

definition C_D4 :: "nat \<Rightarrow> CState \<Rightarrow> CState \<Rightarrow> bool" where
  "C_D4 p cs cs' = (
    CState.c_program_counter cs p = ''D4'' \<and>
    cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''L0'' else CState.c_program_counter cs x),
              j_var := (\<lambda>x. if x = p then BOT else CState.j_var cs x),
              l_var := (\<lambda>x. if x = p then BOT else CState.l_var cs x),
              x_var := (\<lambda>x. if x = p then BOT else CState.x_var cs x) \<rparr>
  )"


(* --- Abstract transitions with internal SSN synchronization --- *)

definition U_L0_E :: "nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_L0_E p us us' = (u_program_counter us p = ''UL0'' \<and> us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UE1'' else u_program_counter us x) \<rparr>)"

definition U_E1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_E1 p v_val sn us us' = (u_program_counter us p = ''UE1'' \<and> 
    us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UE2'' else u_program_counter us x),
              u_his_seq := u_his_seq us @ [mk_act enq v_val p sn call] \<rparr>)"

definition U_E2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_E2 p v_val sn us us' = (u_program_counter us p = ''UE2'' \<and> 
    us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UE3'' else u_program_counter us x),
              u_lin_seq := u_lin_seq us @ [mk_op enq v_val p sn] \<rparr>)"

definition U_E3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_E3 p v_val sn us us' = (u_program_counter us p = ''UE3'' \<and> 
    us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UE4'' else u_program_counter us x),
              u_his_seq := u_his_seq us @ [mk_act enq v_val p sn ret] \<rparr>)"

definition U_E4 :: "nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_E4 p us us' = (
    u_program_counter us p = ''UE4'' \<and>
    us' = us\<lparr>
      u_program_counter := (\<lambda>x. if x = p then ''UL0'' else u_program_counter us x),
      S_var := (\<lambda>x. if x = p then S_var us p + 1 else S_var us x)
    \<rparr>
  )"

definition U_L0_D :: "nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_L0_D p us us' = (u_program_counter us p = ''UL0'' \<and> us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD1'' else u_program_counter us x) \<rparr>)"

definition U_D1 :: "nat \<Rightarrow> nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_D1 p sn us us' = (u_program_counter us p = ''UD1'' \<and> 
    us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD2'' else u_program_counter us x),
              u_his_seq := u_his_seq us @ [mk_act deq BOT p sn call] \<rparr>)"

definition U_D2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_D2 p x_val sn us us' = (u_program_counter us p = ''UD2'' \<and> 
    (let cur_lin = u_lin_seq us; cur_his = u_his_seq us;
         new_lin = (if should_modify cur_lin cur_his x_val then modify_lin cur_lin cur_his x_val else cur_lin) @ [mk_op deq x_val p sn]
     in us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD3'' else u_program_counter us x),
                  u_lin_seq := new_lin \<rparr>))"

definition U_D3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_D3 p x_val sn us us' = (u_program_counter us p = ''UD3'' \<and> 
    us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD4'' else u_program_counter us x),
              u_his_seq := u_his_seq us @ [mk_act deq x_val p sn ret] \<rparr>)"

definition U_D4 :: "nat \<Rightarrow> UState \<Rightarrow> UState \<Rightarrow> bool" where
  "U_D4 p us us' = (
    u_program_counter us p = ''UD4'' \<and>
    us' = us\<lparr>
      u_program_counter := (\<lambda>x. if x = p then ''UL0'' else u_program_counter us x),
      S_var := (\<lambda>x. if x = p then S_var us p + 1 else S_var us x)
    \<rparr>
  )"

(* --- Combined system transitions (Sys_ rules) --- *)

definition Sys_L0 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_L0 p s s' = (
    system_invariant s \<and> C_L0 p (fst s) (fst s') \<and>
    (if CState.c_program_counter (fst s') p = ''E1'' then
       (\<exists>us_mid. U_L0_E p (snd s) us_mid \<and> U_E1 p (CState.V_var (fst s)) (s_var s p) us_mid (snd s'))
     else
       (\<exists>us_mid. U_L0_D p (snd s) us_mid \<and> U_D1 p (s_var s p) us_mid (snd s'))) \<and>
    Simulate_PC s'
  )"

definition Sys_E1 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_E1 p s s' = (
    system_invariant s \<and> C_E1 p (fst s) (fst s') \<and>
    U_E2 p (CState.v_var (fst s) p) (s_var s p) (snd s) (snd s') \<and>
    Simulate_PC s'
  )"

definition Sys_E2 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_E2 p s s' = (
    system_invariant s \<and> C_E2 p (fst s) (fst s') \<and>
    snd s' = snd s \<and>
    Simulate_PC s'
  )"

definition Sys_E3 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_E3 p s s' = (
    system_invariant s \<and> C_E3 p (fst s) (fst s') \<and>
    (\<exists>us_mid. U_E3 p (CState.v_var (fst s) p) (s_var s p) (snd s) us_mid \<and> U_E4 p us_mid (snd s')) \<and>
    Simulate_PC s'
  )"

definition Sys_D1 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_D1 p s s' = (system_invariant s \<and> C_D1 p (fst s) (fst s') \<and> snd s' = snd s \<and> Simulate_PC s')"

definition Sys_D2 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_D2 p s s' = (system_invariant s \<and> C_D2 p (fst s) (fst s') \<and> snd s' = snd s \<and> Simulate_PC s')"

definition Sys_D3 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_D3 p s s' = (
    system_invariant s \<and> C_D3 p (fst s) (fst s') \<and>
    (let q_val = CState.Q_arr (fst s) (CState.j_var (fst s) p) in
     if q_val = BOT then snd s' = snd s 
     else U_D2 p q_val (s_var s p) (snd s) (snd s')) \<and>
    Simulate_PC s'
  )"

definition Sys_D3_success_update :: "SysState \<Rightarrow> nat \<Rightarrow> SysState" where
  "Sys_D3_success_update s p \<equiv> 
    (let cs = fst s; us = snd s; jp = CState.j_var cs p; val = CState.Q_arr cs jp;
         sn = UState.S_var us p; 
         cur_lin = u_lin_seq us; cur_his = u_his_seq us;         
         base_lin = (if should_modify cur_lin cur_his val then modify_lin cur_lin cur_his val else cur_lin);
         new_lin = base_lin @ [mk_op deq val p sn];         
         cs' = cs\<lparr> c_program_counter := (\<lambda>x. if x = p then ''D4'' else CState.c_program_counter cs x),
                   Q_arr := (\<lambda>x. if x = jp then BOT else CState.Q_arr cs x),
                   x_var := (\<lambda>x. if x = p then val else CState.x_var cs x) \<rparr>;
         us' = us\<lparr> u_program_counter := (\<lambda>x. if x = p then ''UD3'' else u_program_counter us x),
                   u_lin_seq := new_lin \<rparr>
     in (cs', us'))"

definition Sys_D4 :: "nat \<Rightarrow> SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Sys_D4 p s s' = (
    system_invariant s \<and> C_D4 p (fst s) (fst s') \<and>
    (\<exists>us_mid. U_D3 p (CState.x_var (fst s) p) (s_var s p) (snd s) us_mid \<and> U_D4 p us_mid (snd s')) \<and>
    Simulate_PC s'
  )"


(* ========================================================== *)
(* 7. System execution and initial states                     *)
(* ========================================================== *)

definition Next :: "SysState \<Rightarrow> SysState \<Rightarrow> bool" where
  "Next s s' = (\<exists>p\<in>ProcSet.
    Sys_L0 p s s' \<or> Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_E3 p s s' \<or>
    Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s' \<or> Sys_D4 p s s')"

definition Init :: "SysState \<Rightarrow> bool" where
  "Init s = (
    (\<forall>p. c_program_counter (fst s) p = ''L0'') \<and>
    (\<forall>p. u_program_counter (snd s) p = ''UL0'') \<and>
    X_var s = 1 \<and> V_var s = 1 \<and> 
    (\<forall>idx. Q_arr s idx = BOT) \<and> (\<forall>idx. Qback_arr s idx = BOT) \<and>
    (\<forall>p. i_var s p > 0) \<and> (\<forall>p. j_var s p > 0) \<and> (\<forall>p. l_var s p > 0) \<and> (\<forall>p. x_var s p \<ge> 0) \<and> (\<forall>p. v_var s p > 0) \<and>
    (\<forall>p. UState.S_var (snd s) p = 1) \<and> 
    u_lin_seq (snd s) = [] \<and>
    u_his_seq (snd s) = [] \<and>
    Simulate_PC s \<and>
    system_invariant s
  )"

lemma system_invariant_Init:
  assumes "Init s"
  shows "system_invariant s"
  using assms unfolding Init_def by blast

(* Reachability of the concrete-to-abstract system *)
inductive Reachable_Sys :: "SysState \<Rightarrow> bool" where
  init: "Init s \<Longrightarrow> Reachable_Sys s"
| step: "Reachable_Sys s \<Longrightarrow> Next s s' \<Longrightarrow> Reachable_Sys s'"

end