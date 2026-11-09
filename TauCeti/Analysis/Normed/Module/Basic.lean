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
* `TauCeti.norm_smul_sq_div_add_norm_smul_sq`: the ratio `‖u‖² / (‖u‖² + ‖v‖²)` is unchanged when
  `u` and `v` are scaled by the same nonzero scalar.
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

/-- The ratio `‖u‖² / (‖u‖² + ‖v‖²)` is unchanged when `u` and `v` are scaled by the same nonzero
scalar. -/
theorem norm_smul_sq_div_add_norm_smul_sq {𝕜 E F : Type*} [NormedDivisionRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SeminormedAddCommGroup F]
    [Module 𝕜 F] [NormSMulClass 𝕜 F] (u : E) (v : F) {t : 𝕜} (ht : t ≠ 0) :
    ‖t • u‖ ^ 2 / (‖t • u‖ ^ 2 + ‖t • v‖ ^ 2) = ‖u‖ ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  simp only [norm_smul, mul_pow, ← mul_add]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 ht))

end TauCeti

end
