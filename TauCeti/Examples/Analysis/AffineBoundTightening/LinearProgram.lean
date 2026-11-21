/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Analysis.AffineBoundTightening.LinearProgram
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Examples of the affine bound tightening linear program

The examples check negative and zero coefficients, no rows and no variables. A four-row
system shows that even a feasible assignment with ordered endpoints need not enclose an
affine graph point.
-/

open Set

namespace TauCeti.AffineBoundTightening.Examples

-- The feasible singleton for x = 1 in the row -2x = -2 has both products equal to -2,
-- and the sign-swapped inverse endpoints are both 1.
example :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![-2]
    let g := graph A ![1]
    let q : Raw 1 1 := (g, g)
    let p := canonical A q
    lpFeasible A q p ∧ p.zL 0 0 = -2 ∧ p.zU 0 0 = -2 ∧
      inverseLo A q 0 0 = 1 ∧ inverseHi A q 0 0 = 1 := by
  intro A g q p
  have ha : A 0 0 < 0 := by norm_num [A]
  have hg : g (.inr 0) = -2 := by simp [g, A, Matrix.mulVec, dotProduct]
  have hl : restLo A q 0 0 = 0 := restLo_eq_zero_of_subsingleton A q 0 0
  have hu : restHi A q 0 0 = 0 := restHi_eq_zero_of_subsingleton A q 0 0
  refine ⟨lpFeasible_canonical_graph ⟨le_rfl, le_rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp [p, q, g, A]
  · simp [p, q, g, A]
  · rw [inverseLo_of_neg ha, hl]
    norm_num [q, hg, A]
  · rw [inverseHi_of_neg ha, hu]
    norm_num [q, hg, A]

-- Zero products are constrained even if the two variable endpoints differ.
example :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let q : Raw 1 1 := (0, Sum.elim (fun _ => 1) 0)
    (feasibleSet A q).Nonempty ∧ ∀ p ∈ feasibleSet A q, p.zL 0 0 = 0 ∧ p.zU 0 0 = 0 := by
  intro A q
  constructor
  · refine ⟨canonical A q, mem_feasibleSet.mpr ((lp_iff_fixed A q _).mpr ?_)⟩
    simp only [canonical_endpoints, true_and]
    refine ⟨fun c => ?_, isFixedPt_step_iff.mpr ⟨Within.rfl, ?_, ?_⟩⟩
    · cases c <;> norm_num [q]
    · intro i
      simp [A, q]
    · intro i j
      have hz : A i j = 0 := rfl
      simp [inverseLo_of_zero hz, inverseHi_of_zero hz]
  · intro p hp
    have h := mem_feasibleSet.mp hp
    rw [h.productLo 0 0, h.productHi 0 0]
    simp [A]

-- The row [1,1] conflicts with a zero coefficient. No width assumption on the variable
-- interval is needed, since a feasible assignment would already order the endpoints.
example (q : Raw 1 1) (h : 0 < q.1 (.inr 0)) :
    feasibleSet (0 : Matrix (Fin 1) (Fin 1) ℝ) q = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  obtain ⟨_, ho, hf⟩ := (lp_iff_fixed _ q p).mp (mem_feasibleSet.mp hp)
  obtain ⟨hw, hr, _⟩ := isFixedPt_step_iff.mp hf
  have hle := (hr 0).2
  rw [imageHi_zero] at hle
  exact h.not_ge ((hw.fst_le (.inr 0)).trans ((ho (.inr 0)).trans hle))

-- With no variables, the row sum is empty, so [1,1] is infeasible even as an LP.
example (A : Matrix (Fin 1) (Fin 0) ℝ) :
    let q : Raw 0 1 := (fun _ => 1, fun _ => 1)
    feasibleSet A q = ∅ ∧ graph A ⁻¹' Icc q.1 q.2 = ∅ := by
  intro q
  have he : feasibleSet A q = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun _ hp => ?_
    have hp' := mem_feasibleSet.mp hp
    have h := (hp'.within.fst_le (.inr 0)).trans
      ((hp'.ordered (.inr 0)).trans (hp'.row 0).2)
    norm_num [q] at h
  exact ⟨he, preimage_Icc_eq_empty_of_feasibleSet_eq_empty he⟩

-- With no rows the LP imposes only orderedness and initial containment.
example (A : Matrix (Fin 0) (Fin 1) ℝ) :
    let q₀ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    let q₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let q₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    let q₃ : Raw 1 0 := (fun _ => 0, fun _ => 3)
    lpFeasible A q₀ (canonical A q₁) ∧ lpFeasible A q₀ (canonical A q₂) ∧
      lpFeasible A q₀ (canonical A q₀) ∧ ¬ lpFeasible A q₀ (canonical A q₃) ∧
      objective (canonical A q₁) = 1 ∧ objective (canonical A q₂) = 1 ∧
      objective (canonical A q₀) = 2 ∧ ¬ Within q₁ q₂ ∧ ¬ Within q₂ q₁ := by
  intro q₀ q₁ q₂ q₃
  have h₁₂ : ¬ Within q₁ q₂ := fun h => by have := h.fst_le (.inl 0); norm_num [q₁, q₂] at this
  have h₂₁ : ¬ Within q₂ q₁ := fun h => by have := h.le_snd (.inl 0); norm_num [q₁, q₂] at this
  have h₃ : ¬ Within q₃ q₀ := fun h => by have := h.le_snd (.inl 0); norm_num [q₀, q₃] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h₁₂, h₂₁⟩
  · norm_num [lp_iff_fixed, isFixedPt_step_zero_rows_iff, within_iff, Pi.le_def, q₀, q₁]
  · norm_num [lp_iff_fixed, isFixedPt_step_zero_rows_iff, within_iff, Pi.le_def, q₀, q₂]
  · norm_num [lp_iff_fixed, isFixedPt_step_zero_rows_iff, within_iff, Pi.le_def, q₀]
  · simp [lp_iff_fixed, isFixedPt_step_zero_rows_iff, h₃]
  all_goals rw [objective_eq_sum_add_sum]; norm_num [q₀, q₁, q₂]

private def inconsistentMatrix : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1, 1, 1; 1, 1, -1; 1, -1, 1; -1, 1, 1]

private def inconsistentBox : Raw 3 4 :=
  (Sum.elim (fun _ => -1) ![0, 0, 0, 1], Sum.elim (fun _ => 1) ![0, 0, 0, 1])

private theorem inconsistentBox_fixed :
    Function.IsFixedPt (step inconsistentMatrix inconsistentBox) inconsistentBox := by
  have hzL (i : Fin 4) (j : Fin 3) : zLo inconsistentMatrix inconsistentBox i j = -1 := by
    fin_cases i <;> fin_cases j <;>
      norm_num [inconsistentMatrix, inconsistentBox, zLo_of_nonneg, zLo_of_nonpos]
  have hzU (i : Fin 4) (j : Fin 3) : zHi inconsistentMatrix inconsistentBox i j = 1 := by
    fin_cases i <;> fin_cases j <;>
      norm_num [inconsistentMatrix, inconsistentBox, zHi_of_nonneg, zHi_of_nonpos]
  have himL (i : Fin 4) : imageLo inconsistentMatrix inconsistentBox i = -3 := by
    norm_num [imageLo_def, hzL]
  have himU (i : Fin 4) : imageHi inconsistentMatrix inconsistentBox i = 3 := by
    norm_num [imageHi_def, hzU]
  have hrsL (i : Fin 4) (j : Fin 3) : restLo inconsistentMatrix inconsistentBox i j = -2 := by
    linarith [imageLo_eq_zLo_add_restLo inconsistentMatrix inconsistentBox i j, himL i, hzL i j]
  have hrsU (i : Fin 4) (j : Fin 3) : restHi inconsistentMatrix inconsistentBox i j = 2 := by
    linarith [imageHi_eq_zHi_add_restHi inconsistentMatrix inconsistentBox i j, himU i, hzU i j]
  refine isFixedPt_step_iff.mpr ⟨Within.rfl, ?_, ?_⟩
  · intro i
    rw [himL, himU]
    fin_cases i <;> norm_num [inconsistentBox]
  · intro i j
    have ha : inconsistentMatrix i j = 1 ∨ inconsistentMatrix i j = -1 := by
      fin_cases i <;> fin_cases j <;> norm_num [inconsistentMatrix]
    rcases ha with ha | ha
    · have hs : 0 < inconsistentMatrix i j := by rw [ha]; norm_num
      rw [inverseLo_of_pos hs, inverseHi_of_pos hs, hrsU, hrsL, ha]
      fin_cases i <;> norm_num [inconsistentBox]
    · have hs : inconsistentMatrix i j < 0 := by rw [ha]; norm_num
      rw [inverseLo_of_neg hs, inverseHi_of_neg hs, hrsL, hrsU, ha]
      fin_cases i <;> norm_num [inconsistentBox]

private theorem inconsistentGraph : graph inconsistentMatrix ⁻¹'
    Icc inconsistentBox.1 inconsistentBox.2 = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hrow := (mem_Icc_graph_iff.mp (mem_preimage.mp hx)).2
  have hr (i : Fin 4) : (inconsistentMatrix.mulVec x) i = ![0, 0, 0, 1] i :=
    (hrow i).2.antisymm (hrow i).1
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  norm_num [inconsistentMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2 h3
  -- The first three equations force all variables to be zero, contradicting the fourth.
  linarith

/-- The tightening LP can be feasible even when the initial box encloses no graph point.
The witness uses three variables in `[-1,1]` and four equality rows. -/
public theorem exists_lpFeasible_without_graph :
    ∃ (A : Matrix (Fin 4) (Fin 3) ℝ) (q : Raw 3 4),
      canonical A q ∈ feasibleSet A q ∧ graph A ⁻¹' Icc q.1 q.2 = ∅ := by
  refine ⟨inconsistentMatrix, inconsistentBox, mem_feasibleSet.mpr ((lp_iff_fixed _ _ _).mpr ?_),
    inconsistentGraph⟩
  simp only [canonical_endpoints, true_and]
  refine ⟨fun c => ?_, inconsistentBox_fixed⟩
  cases c <;> norm_num [inconsistentBox]

end TauCeti.AffineBoundTightening.Examples
