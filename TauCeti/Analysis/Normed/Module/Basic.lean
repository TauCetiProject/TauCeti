/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Basic lemmas on normed scalar actions and modules

This file collects elementary facts about scalar actions on seminormed additive groups and real
normed spaces:

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
* `TauCeti.mul_norm_le_two_mul_norm_of_norm_sub_smul_le`: a vector within `K * a ^ 2` of the real
  multiple `a • v`, with `|a| * (2 * K) ≤ ‖v‖`, still has norm at least half of `|a| * ‖v‖`.
* `TauCeti.norm_smul_le_mul_norm_of_support_subset`: a multiplier bounded by `K` on a set
  containing the support of `f` gives `‖g • f‖ ≤ K ‖f‖` everywhere.
* `IsOpen.diam_pos`: a nonempty bounded open set in a nontrivial real normed space has positive
  diameter.
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

/-- A multiplier bounded by `K` on a set containing the support of `f` gives `‖g • f‖ ≤ K ‖f‖`
everywhere. -/
theorem norm_smul_le_mul_norm_of_support_subset {α A E : Type*} [SeminormedAddGroup A]
    [SeminormedAddCommGroup E] [SMulZeroClass A E] [IsBoundedSMul A E] {f : α → E} {g : α → A}
    {s : Set α} {K : ℝ} (hsupp : Function.support f ⊆ s) (hK : ∀ x ∈ s, ‖g x‖ ≤ K) (x : α) :
    ‖g x • f x‖ ≤ K * ‖f x‖ := by
  by_cases hx : f x = 0
  · simp [hx]
  · exact (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hK x (hsupp hx)) (norm_nonneg _))

end TauCeti

/-- A nonempty bounded open set in a nontrivial real normed space has positive diameter. -/
theorem IsOpen.diam_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {s : Set E} (hs : IsOpen s) (hb : Bornology.IsBounded s) {x : E} (hx : x ∈ s) :
    0 < Metric.diam s := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hs x hx
  calc 0 < 2 * r := by positivity
    _ = Metric.diam (Metric.ball x r) := (Metric.diam_ball_eq x hr.le).symm
    _ ≤ Metric.diam s := Metric.diam_mono hball hb

end
