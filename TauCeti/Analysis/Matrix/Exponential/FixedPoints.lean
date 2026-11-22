/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Fixed vectors of the exponential of a small matrix

For a square matrix `a` over `ℝ` or `ℂ` whose operator norm `‖a‖` is less than `log 2`, the
vectors fixed by `exp a` are the kernel of `a`. This is the matrix form of
`ContinuousLinearMap.exp_apply_eq_self_iff`, read through `Matrix.toEuclideanCLM`. Applied to
`exp a * exp a = exp (a + a)` it shows that, when `2 ‖a‖ < log 2`, the matrix `exp a` does not
have the eigenvalue `-1`.

The norm is the operator norm `Matrix.Norms.L2Operator` for the Euclidean norm.

## Main results

* `Matrix.exp_mulVec_eq_self_iff`: if `‖a‖ < log 2`, then `exp a *ᵥ v = v ↔ a *ᵥ v = 0`.
* `Matrix.mulVec_eq_zero_of_exp_mulVec_exp_mulVec_eq`: if `2 ‖a‖ < log 2`, a vector fixed by
  `exp a ^ 2` lies in the kernel of `a`.
* `Matrix.isUnit_det_exp_add_one`: if `2 ‖a‖ < log 2`, then `exp a + 1` is invertible.
-/

public section

open NormedSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

open scoped Matrix.Norms.L2Operator in
/-- **The fixed vectors of a small matrix exponential are the kernel.** For `‖a‖ < log 2`, the
vectors fixed by `exp a` are the kernel of `a`. This is `ContinuousLinearMap.exp_apply_eq_self_iff`
read through `Matrix.toEuclideanCLM`. -/
theorem exp_mulVec_eq_self_iff {a : Matrix m m 𝕜} (ha : ‖a‖ < Real.log 2) {v : m → 𝕜} :
    exp a *ᵥ v = v ↔ a *ᵥ v = 0 := by
  have h := ContinuousLinearMap.exp_apply_eq_self_iff (𝕜 := 𝕜)
    (B := toEuclideanCLM (n := m) (𝕜 := 𝕜) a) (x := WithLp.toLp 2 v)
    (by rwa [← cstar_norm_def])
  let +nondep : NormedAlgebra ℚ (Matrix m m 𝕜) := .restrictScalars ℚ 𝕜 _
  rw [← NormedSpace.map_exp _ continuous_toEuclideanCLM, toEuclideanCLM_toLp, toEuclideanCLM_toLp,
    ← WithLp.toLp_zero 2, (WithLp.toLp_injective 2).eq_iff, (WithLp.toLp_injective 2).eq_iff] at h
  exact h

open scoped Matrix.Norms.L2Operator in
/-- If `2 ‖a‖ < log 2`, a vector fixed by `exp a ^ 2` lies in the kernel of `a`. -/
theorem mulVec_eq_zero_of_exp_mulVec_exp_mulVec_eq {a : Matrix m m 𝕜}
    (ha : 2 * ‖a‖ < Real.log 2) {v : m → 𝕜} (hv : exp a *ᵥ (exp a *ᵥ v) = v) : a *ᵥ v = 0 := by
  have hnorm : ‖a + a‖ < Real.log 2 := (norm_add_le a a).trans_lt (by rwa [← two_mul])
  have h := (exp_mulVec_eq_self_iff hnorm (v := v)).1 (by
    rw [Matrix.exp_add_of_commute _ _ (Commute.refl a), ← mulVec_mulVec, hv])
  rwa [add_mulVec, ← two_smul 𝕜 (a *ᵥ v), smul_eq_zero, or_iff_right two_ne_zero] at h

open scoped Matrix.Norms.L2Operator in
/-- **A small matrix exponential does not have the eigenvalue `-1`.** If `2 ‖a‖ < log 2`, then
`exp a + 1` is invertible. -/
theorem isUnit_det_exp_add_one {a : Matrix m m 𝕜} (ha : 2 * ‖a‖ < Real.log 2) :
    IsUnit (exp a + 1).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  have hneg : exp a *ᵥ v = -v := by
    rwa [add_mulVec, one_mulVec, add_eq_zero_iff_eq_neg] at hv
  have hker := mulVec_eq_zero_of_exp_mulVec_exp_mulVec_eq ha
    (by rw [hneg, mulVec_neg, hneg, neg_neg])
  have hfix := (exp_mulVec_eq_self_iff
    ((le_mul_of_one_le_left (norm_nonneg a) one_le_two).trans_lt ha) (v := v)).2 hker
  rw [hneg, neg_eq_iff_add_eq_zero, ← two_smul 𝕜 v, smul_eq_zero] at hfix
  exact hv0 (hfix.resolve_left two_ne_zero)

end Matrix
