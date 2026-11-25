/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Esymm

/-!
# Checks: hyperbolic polynomials and the cones `Γ_k`

* `x² + y²` is positive at `(1, 0)` but not hyperbolic in that direction: on the line through
  `(0, 1)` it is `t² + 1`, with no real root (`not_isHyperbolic_sq_add_sq`).
* In `ℝ³`, `λ = (3, 3, −1)` has `σ₁ = 5`, `σ₂ = 3`, `σ₃ = −9`, so it lies in
  `Γ₂ = Γ(σ₂, e)` but not in `Γ₃ = Γ(σ₃, e)` (`mem_gardingCone_esymm_two`,
  `notMem_gardingCone_esymm_three`).
* `σ₂(−e) = 3 > 0` in `ℝ³`, but `−e ∉ Γ₂` since `σ₁(−e) = −3`; as `σ₂(0) = 0`, the set
  `{σ₂ > 0}` contains `e` and `−e` but not their midpoint, so `Γ₂` needs the condition on `σ₁`
  (`eval_neg_one_esymm_two`, `neg_one_notMem_gardingCone_esymm_two`).
* For `n = 2`, `(1, −1/2)` lies in the half-plane `Γ₁` but not in the quadrant `Γ₂`
  (`mem_gardingCone_esymm_one_two`, `notMem_gardingCone_esymm_two_two`).
-/

public section

open MvPolynomial

namespace TauCeti.HyperbolicChecks

/-- `x² + y²` is not hyperbolic in the direction `(1, 0)`, although it is positive there. -/
theorem not_isHyperbolic_sq_add_sq :
    ¬ IsHyperbolic (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) 2 ![1, 0] := by
  intro h
  have hcard := h.card_roots ![0, 1]
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard]; norm_num)
  have h0 := Polynomial.isRoot_of_mem_roots hr
  rw [Polynomial.IsRoot.def, eval_aeval_C_add_C_mul_X] at h0
  simp only [map_add, map_pow, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
  norm_num at h0
  nlinarith [sq_nonneg r]

/-- `σ₂` in three variables, written out. -/
theorem eval_esymm_two_fin_three (x : Fin 3 → ℝ) :
    eval x (esymm (Fin 3) ℝ 2) = x 0 * x 1 + x 0 * x 2 + x 1 * x 2 := by
  have h : Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)) = {{0, 1}, {0, 2}, {1, 2}} := by
    decide
  simp (config := { decide := true }) only [esymm, h, Finset.sum_insert, Finset.prod_insert,
    Finset.sum_singleton, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton]
  simp [add_assoc]

/-- `σ₂(3, 3, −1) = 3`. -/
theorem eval_esymm_two : eval ![(3 : ℝ), 3, -1] (esymm (Fin 3) ℝ 2) = 3 := by
  rw [eval_esymm_two_fin_three]
  norm_num

/-- `σ₃(3, 3, −1) = −9`. -/
theorem eval_esymm_three : eval ![(3 : ℝ), 3, -1] (esymm (Fin 3) ℝ 3) = -9 := by
  have h : esymm (Fin 3) ℝ 3 = ∏ i, X i := by simpa using esymm_card (Fin 3) ℝ
  norm_num [h, Fin.prod_univ_three]

/-- `σ₁(3, 3, −1) = 5`. -/
theorem eval_esymm_one : eval ![(3 : ℝ), 3, -1] (esymm (Fin 3) ℝ 1) = 5 := by
  norm_num [Fin.sum_univ_three]

/-- `(3, 3, −1) ∈ Γ₂`. -/
theorem mem_gardingCone_esymm_two : ![(3 : ℝ), 3, -1] ∈ gardingCone (esymm (Fin 3) ℝ 2) 1 := by
  rw [gardingCone_esymm _]
  intro j hj1 hj2
  interval_cases j
  · rw [eval_esymm_one]
    norm_num
  · rw [eval_esymm_two]
    norm_num

/-- `(3, 3, −1) ∉ Γ₃`, since `σ₃(3, 3, −1) = −9 < 0`. -/
theorem notMem_gardingCone_esymm_three :
    ![(3 : ℝ), 3, -1] ∉ gardingCone (esymm (Fin 3) ℝ 3) 1 := by
  rw [gardingCone_esymm _]
  intro h
  have := h 3 (by norm_num) le_rfl
  rw [eval_esymm_three] at this
  norm_num at this

/-- `σ₂(−e) = 3` in `ℝ³`. -/
theorem eval_neg_one_esymm_two : eval (-1 : Fin 3 → ℝ) (esymm (Fin 3) ℝ 2) = 3 := by
  rw [eval_esymm_two_fin_three]
  norm_num

/-- `−e ∉ Γ₂` in `ℝ³`, since `σ₁(−e) = −3`. -/
theorem neg_one_notMem_gardingCone_esymm_two :
    (-1 : Fin 3 → ℝ) ∉ gardingCone (esymm (Fin 3) ℝ 2) 1 := by
  rw [gardingCone_esymm _]
  intro h
  have := h 1 le_rfl (by norm_num)
  norm_num [Fin.sum_univ_three] at this

/-- `(1, −1/2) ∈ Γ₁` for `n = 2`. -/
theorem mem_gardingCone_esymm_one_two :
    ![(1 : ℝ), -1 / 2] ∈ gardingCone (esymm (Fin 2) ℝ 1) 1 := by
  rw [gardingCone_esymm _]
  intro j hj1 hj2
  obtain rfl : j = 1 := by omega
  norm_num [Fin.sum_univ_two]

/-- `(1, −1/2) ∉ Γ₂` for `n = 2`, since `σ₂(1, −1/2) = −1/2`. -/
theorem notMem_gardingCone_esymm_two_two :
    ![(1 : ℝ), -1 / 2] ∉ gardingCone (esymm (Fin 2) ℝ 2) 1 := by
  rw [gardingCone_esymm _]
  intro h
  have := h 2 (by norm_num) le_rfl
  have h2 : esymm (Fin 2) ℝ 2 = ∏ i, X i := by simpa using esymm_card (Fin 2) ℝ
  norm_num [h2, Fin.prod_univ_two] at this

end TauCeti.HyperbolicChecks
