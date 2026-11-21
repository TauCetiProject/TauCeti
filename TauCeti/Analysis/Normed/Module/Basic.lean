/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module

/-!
# Basic lemmas on normed scalar actions and modules

This file collects elementary facts about scalar actions on seminormed additive groups and real
normed spaces:

* `TauCeti.isOpen_exists_mem_norm_sum_lt`: existence of a small finite linear combination
  with coefficients in a fixed set is an open condition on a family of vectors.
* `RingHomIsometric.intCastRingHom`: in a seminormed ring in which `ℤ` acts isometrically and
  `‖1‖ = 1`, such as `ℝ` or `ℂ`, `Int.castRingHom R` preserves norms, making lemmas stated for a
  `RingHomIsometric` ring homomorphism (such as `Polynomial.supNorm_map`) apply to integer
  polynomials.
* `TauCeti.norm_sum_smul_le_sum_div_mul`: when scalar coefficients satisfy `‖a i‖ * r i ≤ b`
  against positive weights `r i`, the combination `∑ i ∈ s, a i • u i` has norm at most
  `(∑ i ∈ s, ‖u i‖ / r i) * b`; in particular, strict-generator representations yield uniformly
  norm-bounded preimages along linear maps.
* `TauCeti.norm_sum_smul_le_sum_norm_mul` and `TauCeti.norm_sum_smul_sub_smul_le`: when vectors
  satisfy `‖u i‖ ≤ C` (or perturbations satisfy `‖u i - v i‖ ≤ δ`) on `s`, the scalar-weighted sum
  `∑ i ∈ s, a i • u i` (or difference `∑ i ∈ s, a i • u i - ∑ i ∈ s, a i • v i`) has norm at most
  `(∑ i ∈ s, ‖a i‖) * C` (respectively `(∑ i ∈ s, ‖a i‖) * δ`).
* `TauCeti.norm_neg_one_pow_smul`: the sign `(-1) ^ n` does not change norms.
* `TauCeti.norm_smul_sq_div_add_norm_smul_sq`: the ratio `‖u‖² / (‖u‖² + ‖v‖²)` is unchanged when
  `u` and `v` are scaled by the same nonzero scalar.
* `TauCeti.mul_norm_le_two_mul_norm_of_norm_sub_smul_le`: a vector within `K * a ^ 2` of the real
  multiple `a • v`, with `|a| * (2 * K) ≤ ‖v‖`, still has norm at least half of `|a| * ‖v‖`.
* `TauCeti.norm_smul_le_mul_norm_of_support_subset`: a multiplier bounded by `K` on a set
  containing the support of `f` gives `‖g • f‖ ≤ K ‖f‖` everywhere.
* `TauCeti.norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq_le` and
  `TauCeti.le_two_mul_norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq`: for the conformal
  linear map `(1, 0) ↦ (a, b)`, `(0, 1) ↦ (-b, a)` of the plane, the sum `‖X‖² + ‖Y‖²` of the
  squared norms of the values of a linear map on the coordinate vectors and the same sum
  `‖a • X + b • Y‖² + ‖(-b) • X + a • Y‖²` after composing with the conformal map agree up to the
  conformal factor `a² + b²` and a factor `2`. These compare `W^{1,2}` densities under a
  holomorphic change of coordinates.
* `IsOpen.diam_pos`: a nonempty bounded open set in a nontrivial real normed space has positive
  diameter.
* `LipschitzWith.smul_const`: if a scalar function `f` is `K`-Lipschitz, then `y ↦ f y • c` is
  `K ‖c‖`-Lipschitz.
-/

public section

/-- The cast from `ℤ` is norm-preserving in a normed ring in which `ℤ` acts isometrically and
`‖1‖ = 1`, such as `ℝ` or `ℂ`. -/
instance RingHomIsometric.intCastRingHom {R : Type*} [SeminormedRing R]
    [NormSMulClass ℤ R] [NormOneClass R] : RingHomIsometric (Int.castRingHom R) where
  norm_map {n} := by simp [norm_intCast_eq_abs_mul_norm_one, Int.norm_eq_abs]

namespace TauCeti

/-- Having a small linear combination with coefficients in any fixed set is an open condition
on a family of vectors, with a fixed finite set of indices. -/
theorem isOpen_exists_mem_norm_sum_lt {𝕜 E ι : Type*} [SeminormedAddCommGroup E]
    [SMul 𝕜 E] [ContinuousConstSMul 𝕜 E] (s : Finset ι) (S : Set (ι → 𝕜)) (t : ℝ) :
    IsOpen {v : ι → E | ∃ c ∈ S, ‖∑ i ∈ s, c i • v i‖ < t} := by
  simp only [← exists_prop, Set.ofPred_exists]
  exact isOpen_biUnion fun c _ ↦ isOpen_lt (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).const_smul (c i)).norm continuous_const

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

/-- If each vector `u i` on `s` has norm at most `C`, then
`‖∑ i ∈ s, a i • u i‖ ≤ (∑ i ∈ s, ‖a i‖) * C`. -/
theorem norm_sum_smul_le_sum_norm_mul {ι A E : Type*} [SeminormedAddGroup A]
    [SeminormedAddCommGroup E] [SMulZeroClass A E] [IsBoundedSMul A E] {s : Finset ι}
    {a : ι → A} {u : ι → E} {C : ℝ} (hu : ∀ i ∈ s, ‖u i‖ ≤ C) :
    ‖∑ i ∈ s, a i • u i‖ ≤ (∑ i ∈ s, ‖a i‖) * C := by
  rw [Finset.sum_mul]
  exact norm_sum_le_of_le s fun i hi ↦
    (norm_smul_le (a i) (u i)).trans (mul_le_mul_of_nonneg_left (hu i hi) (norm_nonneg (a i)))

/-- Perturbing each vector in `∑ i ∈ s, a i • u i` by at most `δ` in norm changes the sum by at
most `(∑ i ∈ s, ‖a i‖) * δ`. -/
theorem norm_sum_smul_sub_smul_le {ι A E : Type*} [SeminormedAddGroup A]
    [SeminormedAddCommGroup E] [DistribSMul A E] [IsBoundedSMul A E] {s : Finset ι}
    {a : ι → A} {u v : ι → E} {δ : ℝ} (huv : ∀ i ∈ s, ‖u i - v i‖ ≤ δ) :
    ‖∑ i ∈ s, a i • u i - ∑ i ∈ s, a i • v i‖ ≤ (∑ i ∈ s, ‖a i‖) * δ := by
  simpa only [smul_sub, Finset.sum_sub_distrib] using
    norm_sum_smul_le_sum_norm_mul (a := a) huv

/-- The sign `(-1) ^ n` does not change norms. -/
@[simp]
theorem norm_neg_one_pow_smul {R G : Type*} [SeminormedRing R] [NormOneClass R] [Norm G]
    [SMul R G] [NormSMulClass R G] (n : ℕ) (y : G) : ‖(-1 : R) ^ n • y‖ = ‖y‖ := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h, norm_smul]

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

/-- The elementary inequality behind the comparison of `W^{1,2}` densities under conformal
changes of coordinates. -/
private theorem add_sq_add_add_sq_le (a b x y : ℝ) :
    (|a| * x + |b| * y) ^ 2 + (|b| * x + |a| * y) ^ 2 ≤
      2 * ((a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2)) := by
  nlinarith [mul_nonneg (sq_nonneg (|a| - |b|)) (add_nonneg (sq_nonneg x) (sq_nonneg y)),
    mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg b)) (sq_nonneg (x - y)), sq_abs a, sq_abs b]

/-- Under the conformal linear map `(1, 0) ↦ (a, b)`, `(0, 1) ↦ (-b, a)` of the plane, the sum of
the squared norms of the two partial derivatives `X`, `Y` of a map grows at most by twice the
conformal factor `a² + b²`. -/
theorem norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq_le {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ) (X Y : E) :
    ‖a • X + b • Y‖ ^ 2 + ‖(-b) • X + a • Y‖ ^ 2 ≤
      2 * ((a ^ 2 + b ^ 2) * (‖X‖ ^ 2 + ‖Y‖ ^ 2)) := by
  have h₁ : ‖a • X + b • Y‖ ≤ |a| * ‖X‖ + |b| * ‖Y‖ :=
    (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])
  have h₂ : ‖(-b) • X + a • Y‖ ≤ |b| * ‖X‖ + |a| * ‖Y‖ :=
    (norm_add_le _ _).trans_eq (by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg])
  have h₁' := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have h₂' := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  linarith [add_sq_add_add_sq_le a b ‖X‖ ‖Y‖]

/-- Conversely, under the conformal linear map `(1, 0) ↦ (a, b)`, `(0, 1) ↦ (-b, a)`, the sum of
the squared norms of the two partial derivatives of a map, times the conformal factor `a² + b²`, is
at most twice the sum after the change of coordinates. -/
theorem le_two_mul_norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ) (X Y : E) :
    (a ^ 2 + b ^ 2) * (‖X‖ ^ 2 + ‖Y‖ ^ 2) ≤
      2 * (‖a • X + b • Y‖ ^ 2 + ‖(-b) • X + a • Y‖ ^ 2) := by
  set P := a • X + b • Y
  set Q := (-b) • X + a • Y
  set d := a ^ 2 + b ^ 2
  have hd : 0 ≤ d := by positivity
  -- Inverting the conformal map: `d X = a P - b Q` and `d Y = b P + a Q`.
  have hX : d * ‖X‖ ≤ |a| * ‖P‖ + |b| * ‖Q‖ := by
    have h : d • X = a • P - b • Q := by simp only [P, Q, d]; module
    rw [← Real.norm_of_nonneg hd, ← norm_smul, h]
    exact (norm_sub_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs])
  have hY : d * ‖Y‖ ≤ |b| * ‖P‖ + |a| * ‖Q‖ := by
    have h : d • Y = b • P + a • Q := by simp only [P, Q, d]; module
    rw [← Real.norm_of_nonneg hd, ← norm_smul, h]
    exact (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs])
  have hX' := pow_le_pow_left₀ (by positivity) hX 2
  have hY' := pow_le_pow_left₀ (by positivity) hY 2
  have key := add_sq_add_add_sq_le a b ‖P‖ ‖Q‖
  rcases hd.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    positivity
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith

end TauCeti

/-- A nonempty bounded open set in a nontrivial real normed space has positive diameter. -/
theorem IsOpen.diam_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {s : Set E} (hs : IsOpen s) (hb : Bornology.IsBounded s) {x : E} (hx : x ∈ s) :
    0 < Metric.diam s := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hs x hx
  calc 0 < 2 * r := by positivity
    _ = Metric.diam (Metric.ball x r) := (Metric.diam_ball_eq x hr.le).symm
    _ ≤ Metric.diam s := Metric.diam_mono hball hb

/-- If a scalar function `f` is `K`-Lipschitz, then `y ↦ f y • c` is `K ‖c‖`-Lipschitz. -/
theorem LipschitzWith.smul_const {α 𝕜 E : Type*} [PseudoEMetricSpace α] [SeminormedRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {K : NNReal} {f : α → 𝕜}
    (hf : LipschitzWith K f) (c : E) : LipschitzWith (K * ‖c‖₊) fun y ↦ f y • c := by
  have hc : LipschitzWith ‖c‖₊ fun r : 𝕜 ↦ r • c := .of_dist_le_mul fun r s ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← sub_smul, coe_nnNorm, mul_comm]
    exact norm_smul_le _ _
  rw [mul_comm]
  exact hc.comp hf

end
