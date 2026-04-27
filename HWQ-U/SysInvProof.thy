theory SysInvProof
  imports Main 
    Model
    D3Proof
    D4Proof
    D1Proof
    D2Proof
    E3Proof
    E2Proof
    E1Proof
    L0Proof

begin

(* ========================================================== *)
(* Preservation of the global system invariant              *)
(* ========================================================== *)
lemma Sys_Inv_Step:
  assumes "system_invariant s"
      and "Next s s'"
  shows "system_invariant s'"
proof -
  (* Step 1: unfold Next and extract the process p that performs the step. *)
  from assms(2) obtain p where step_cases:
    "Sys_L0 p s s' \<or> 
     Sys_E1 p s s' \<or> Sys_E2 p s s' \<or> Sys_E3 p s s' \<or> 
     Sys_D1 p s s' \<or> Sys_D2 p s s' \<or> Sys_D3 p s s' \<or> Sys_D4 p s s'"
    unfolding Next_def by blast

  (* Step 2: discharge the goal by case analysis over the eight transition rules. *)
  from step_cases show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    thus ?case using L0_preserves_invariant[OF assms(1)]
      by (simp add: L0_def) 
  next
    case 2
    thus ?case using E1_preserves_invariant[OF assms(1)] by simp
  next
    case 3
    thus ?case using E2_preserves_invariant[OF assms(1)] by simp
  next
    case 4
    thus ?case using E3_preserves_invariant[OF assms(1)] by simp
  next
    case 5
    thus ?case using D1_preserves_invariant[OF assms(1)] by simp
  next
    case 6
    thus ?case using D2_preserves_invariant[OF assms(1)] by simp
  next
    case 7
    thus ?case using D3_preserves_invariant[OF assms(1)] by simp
  next
    case 8
    thus ?case using D4_preserves_invariant[OF assms(1)] by simp
  qed
qed

end