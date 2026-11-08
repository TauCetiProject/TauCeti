/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Basic lemmas on normed scalar actions and modules

This file collects elementary norm facts for scalar actions on seminormed additive groups:

* `RingHomIsometric.intCastRingHom`: in a seminormed ring in which `ℤ` acts isometrically and
  `‖1‖ = 1`, such as `ℝ` or `ℂ`, `Int.castRingHom R` preserves norms, making lemmas stated for a
  `RingHomIsometric` ring homomorphism (such as `Polynomial.supNorm_map`) apply to integer
  polynomials.
* `TauCeti.norm_sum_smul_le_sum_div_mul`: when scalar coefficients satisfy `‖a i‖ * r i ≤ b`
  against positive weights `r i`, the combination `∑ i ∈ s, a i • u i` has norm at most
  `(∑ i ∈ s, ‖u i‖ / r i) * b`; in particular, strict-generator representations yield uniformly
  norm-bounded preimages along linear maps.
* `TauCeti.mul_norm_le_two_mul_norm_of_norm_sub_smul_le`: a vector within `K * a ^ 2` of the real
  multiple `a • v`, with `|a| * (2 * K) ≤ ‖v‖`, still has norm at least half of `|a| * ‖v‖`.
-/

public section

/-- The cast from `ℤ` is norm-preserving in a normed ring in which `ℤ` acts isometrically and
`‖1‖ = 1`, such as `ℝ` or `ℂ`. -/
instance RingHomIsometric.intCastRingHom {R : Type*} [SeminormedRing R]
    [NormSMulClass ℤ R] [NormOneClass R] : RingHomIsometric (Int.castRingHom R) where
  norm_map {n} := by simp [norm_intCast_eq_abs_mul_norm_one, Int.norm_eq_abs]

namespace TauCeti

/-- If scalar coefficients `a i` satisfy `‖a i‖ * r i ≤ b` against positive weights `r i`, then
`‖∑ i ∈ s, a i • u i‖ ≤ (∑ i ∈ s, ‖u i‖ / r i) * b`. -/
theorem norm_sum_smul_le_sum_div_mul {ι A E : Type*} [SeminormedAddGroup A]
    [SeminormedAddCommGroup E] [SMulZeroClass A E] [IsBoundedSMul A E] {s : Finset ι}
    {r : ι → ℝ} (hr : ∀ i ∈ s, 0 < r i) {u : ι → E} {a : ι → A} {b : ℝ}
    (ha : ∀ i ∈ s, ‖a i‖ * r i ≤ b) :
    ‖∑ i ∈ s, a i • u i‖ ≤ (∑ i ∈ s, ‖u i‖ / r i) * b := by
  calc ‖∑ i ∈ s, a i • u i‖
      ≤ ∑ i ∈ s, ‖a i • u i‖ := norm_sum_le s _
    _ ≤ ∑ i ∈ s, ‖a i‖ * ‖u i‖ := Finset.sum_le_sum fun _ _ ↦ norm_smul_le _ _
    _ ≤ ∑ i ∈ s, ‖u i‖ / r i * b := Finset.sum_le_sum fun i hi ↦ by
        calc ‖a i‖ * ‖u i‖
            ≤ b / r i * ‖u i‖ :=
              mul_le_mul_of_nonneg_right ((le_div_iff₀ (hr i hi)).mpr (ha i hi)) (norm_nonneg _)
          _ = ‖u i‖ / r i * b := by ring
    _ = (∑ i ∈ s, ‖u i‖ / r i) * b := (Finset.sum_mul s _ b).symm

/-- **A quadratic error cannot swallow the linear term.** If `z` lies within `K * a ^ 2` of the
real multiple `a • v`, and `a` is small enough that `|a| * (2 * K) ≤ ‖v‖`, then `z` still inherits
half of the length `|a| * ‖v‖` of that multiple. -/
theorem mul_norm_le_two_mul_norm_of_norm_sub_smul_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {z v : E} {a K : ℝ} (hR : ‖z - a • v‖ ≤ K * a ^ 2)
    (ha : |a| * (2 * K) ≤ ‖v‖) :
    |a| * ‖v‖ ≤ 2 * ‖z‖ := by
  have h1 : ‖a • v‖ - ‖z - a • v‖ ≤ ‖z‖ := by
    simpa [norm_sub_rev z (a • v)] using norm_sub_norm_le (a • v) (a • v - z)
  rw [norm_smul, Real.norm_eq_abs] at h1
  rw [← sq_abs a] at hR
  nlinarith [mul_le_mul_of_nonneg_left ha (abs_nonneg a),
    mul_nonneg (abs_nonneg a) (norm_nonneg v)]

end TauCeti

end
