/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Data.Nat.Choose.Sum
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
* `TauCeti.norm_sqrt_smul_sq`: scaling a vector by `√a`, `a ≥ 0`, multiplies its squared norm by
  `a`.
* `TauCeti.norm_inv_sqrt_smul_sq`: scaling a vector by `(√a)⁻¹`, `a ≥ 0`, divides its squared
  norm by `a`.
* `TauCeti.norm_sum_choose_smul_le`: a binomially weighted sum `∑ j ≤ r, (r choose j) • w j` of
  vectors of norm at most `c` has norm at most `2 ^ r * c`.
* `TauCeti.norm_neg_one_pow_smul`: the sign `(-1) ^ n` does not change norms.
* `TauCeti.norm_smul_sq_div_add_norm_smul_sq`: the ratio `‖u‖² / (‖u‖² + ‖v‖²)` is unchanged when
  `u` and `v` are scaled by the same nonzero scalar.
* `TauCeti.norm_smul_add_smul_sq_le`: the Cauchy–Schwarz bound
  `‖a • v + b • w‖² ≤ (a² + b²) (‖v‖² + ‖w‖²)` for real scalars.
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
* `TauCeti.edist_map_smul`: evaluating two linear maps at `r • a` scales their extended
  distance by `‖r‖ₑ`.
* `TauCeti.norm_div_norm_smul_le`: for a bounded real scalar action, rescaling a vector `y` by
  `τ / ‖y‖` gives a vector of norm at most `‖τ‖`, for any real `τ` (exactly `‖τ‖` when `‖y‖ ≠ 0`
  and the action preserves norms; `0` when `‖y‖ = 0`).
* `Continuous.div_norm_smul`: for a continuous real scalar action and continuous `τ` and `y`, the
  radial rescaling `p ↦ (τ p / ‖y p‖) • y p` is continuous as long as `τ` vanishes on the frontier
  of the locus where `‖y‖` vanishes.
* `IsOpen.diam_pos`: a nonempty bounded open set in a nontrivial real normed space has positive
  diameter.
* `Units.norm_coe_zpow_smul`, `Units.exists_zpow_smul_mem_annulus`: on the nonzero vectors of a
  normed space, the dilation by `cᵏ` for a unit `c` of the scalar field multiplies norms by
  `‖c‖ ^ k`, so for `1 < ‖c‖` every orbit meets the annulus `1 ≤ ‖v‖ < ‖c‖`.
* `Units.coe_zpow_smul_of_eq_algebraMap`: a unit that is the image of a real `r` acts on nonzero
  vectors by powers of `r`.
* `LipschitzWith.smul_const`: if a scalar function `f` is `K`-Lipschitz, then `y ↦ f y • c` is
  `K ‖c‖`-Lipschitz.
* `LinearMap.norm_apply_le_sum_norm_mul`: for a semilinear map `L : (ι → R) →ₛₗ[σ] F` on a
  finite product over a semiring, into a seminormed group with a bounded scalar action of a
  seminormed ring `S`, the values at the coordinate vectors bound every value:
  `‖L v‖ ≤ ∑ j, ‖σ (v j)‖ * ‖L (Pi.single j 1)‖`. For the sup norm, `‖σ r‖ ≤ ‖r‖` and a bound `M`
  on the values at the coordinate vectors this gives `‖L v‖ ≤ #ι * ‖v‖ * M`.
* `LinearMap.norm_inv_smul_sub_apply`: for a semilinear map `L : E →ₛₗ[σ] F` from any module `E`
  over a semiring, neither of which needs a norm, into a seminormed group with a bounded scalar
  action of a normed division ring, and `σ t ≠ 0`, rescaling by `(σ t)⁻¹` turns the error at
  `t • v` into the error at `v`: `‖(σ t)⁻¹ • w - L v‖ = ‖σ t‖⁻¹ * ‖w - L (t • v)‖`. No continuity
  of `L` is needed.

The coordinate bound is adapted from [KLS](https://github.com/human-ai-mathematics/kls-lean),
commit `65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/Disk.lean`.
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

/-- The squared norm of a vector scaled by the square root of `a ≥ 0` is multiplied by `a`. -/
theorem norm_sqrt_smul_sq {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}
    (ha : 0 ≤ a) (x : E) : ‖√a • x‖ ^ 2 = a * ‖x‖ ^ 2 := by
  simp [norm_smul, mul_pow, Real.sq_sqrt ha]

/-- The squared norm of a vector scaled by the inverse square root of `a ≥ 0` is divided by `a`. -/
theorem norm_inv_sqrt_smul_sq {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}
    (ha : 0 ≤ a) (x : E) : ‖(√a)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / a := by
  simp [norm_smul, mul_pow, Real.sq_sqrt ha, div_eq_inv_mul]

/-- A binomially weighted sum `∑ j ≤ r, (r choose j) • w j` of vectors of norm at most `c` has norm
at most `2 ^ r * c`. -/
theorem norm_sum_choose_smul_le {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {r : ℕ} {w : ℕ → V} {c : ℝ} (hw : ∀ j ∈ Finset.range (r + 1), ‖w j‖ ≤ c) :
    ‖∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) • w j‖ ≤ 2 ^ r * c := by
  refine (norm_sum_smul_le_sum_norm_mul hw).trans_eq ?_
  simp only [Real.norm_natCast]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

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

/-- **Cauchy–Schwarz for a combination of two vectors.** For real scalars `a`, `b`,
`‖a • v + b • w‖² ≤ (a² + b²) (‖v‖² + ‖w‖²)`. -/
theorem norm_smul_add_smul_sq_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (v w : E) :
    ‖a • v + b • w‖ ^ 2 ≤ (a ^ 2 + b ^ 2) * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have h : ‖a • v + b • w‖ ≤ |a| * ‖v‖ + |b| * ‖w‖ :=
    (norm_add_le _ _).trans (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])
  have hab : (|a| * ‖v‖ + |b| * ‖w‖) ^ 2 ≤ (a ^ 2 + b ^ 2) * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    nlinarith [sq_nonneg (|a| * ‖w‖ - |b| * ‖v‖), sq_abs a, sq_abs b]
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans hab

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

/-- Evaluating two linear maps at `r • a` scales their extended distance by `‖r‖ₑ`. -/
theorem edist_map_smul {𝕜 E G H : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] [Module 𝕜 G] [NormSMulClass 𝕜 G] [FunLike H E G]
    [LinearMapClass H 𝕜 E G] (φ ψ : H) (r : 𝕜) (a : E) :
    edist (φ (r • a)) (ψ (r • a)) = ‖r‖ₑ * edist (φ a) (ψ a) := by
  rw [map_smul, map_smul, edist_smul₀, ENNReal.smul_def, smul_eq_mul, eNorm_eq_nnNorm]

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
  linarith [norm_smul_add_smul_sq_le a b X Y, norm_smul_add_smul_sq_le (-b) a X Y, neg_sq b]

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

/-- For a bounded real scalar action, rescaling a vector `y` by `τ / ‖y‖` gives a vector of norm
at most `‖τ‖`, for any real `τ`. -/
theorem norm_div_norm_smul_le {F : Type*} [SeminormedAddGroup F] [SMulZeroClass ℝ F]
    [IsBoundedSMul ℝ F] (y : F) (τ : ℝ) : ‖(τ / ‖y‖) • y‖ ≤ ‖τ‖ :=
  (norm_smul_le _ _).trans <| by
    rw [norm_div, Real.norm_of_nonneg (norm_nonneg y), div_eq_mul_inv, mul_assoc]
    exact mul_le_of_le_one_right (norm_nonneg τ) inv_mul_le_one

end TauCeti

/-- A nonempty bounded open set in a nontrivial real normed space has positive diameter. -/
theorem IsOpen.diam_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {s : Set E} (hs : IsOpen s) (hb : Bornology.IsBounded s) {x : E} (hx : x ∈ s) :
    0 < Metric.diam s := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hs x hx
  calc 0 < 2 * r := by positivity
    _ = Metric.diam (Metric.ball x r) := (Metric.diam_ball_eq x hr.le).symm
    _ ≤ Metric.diam s := Metric.diam_mono hball hb

namespace Units

section Norm

/-! ### Norms of dilated nonzero vectors -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The dilation by `cᵏ` multiplies the norm of a nonzero vector by `‖c‖ ^ k`. -/
theorem norm_coe_zpow_smul (c : 𝕜ˣ) (k : ℤ) (v : {v : E // v ≠ 0}) :
    ‖((c ^ k • v : {v : E // v ≠ 0}) : E)‖ = ‖(c : 𝕜)‖ ^ k * ‖(v : E)‖ := by
  rw [Units.smul_coe, Units.smul_def, norm_smul, Units.val_zpow_eq_zpow_val, norm_zpow]

/-- For `1 < ‖c‖` every nonzero vector has a multiple by a power of `c` in the annulus
`1 ≤ ‖v‖ < ‖c‖`. -/
theorem exists_zpow_smul_mem_annulus {c : 𝕜ˣ} (hc : 1 < ‖(c : 𝕜)‖) (v : {v : E // v ≠ 0}) :
    ∃ k : ℤ, 1 ≤ ‖((c ^ k • v : {v : E // v ≠ 0}) : E)‖ ∧
      ‖((c ^ k • v : {v : E // v ≠ 0}) : E)‖ < ‖(c : 𝕜)‖ := by
  obtain ⟨k, -, hk₂, hk₁, -⟩ := rescale_to_shell_zpow hc (one_pos.trans hc) v.property
  rw [div_self (one_pos.trans hc).ne'] at hk₁
  refine ⟨k, ?_, ?_⟩ <;>
    rwa [Units.smul_coe, Units.smul_def, Units.val_zpow_eq_zpow_val]

/-- A power of a unit of a normed `ℝ`-algebra `𝕜` that is the image of a real `r` acts on
nonzero vectors as the real scalar `r ^ k`. -/
theorem coe_zpow_smul_of_eq_algebraMap [NormedAlgebra ℝ 𝕜] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] {c : 𝕜ˣ} {r : ℝ} (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r) (k : ℤ)
    (v : {v : E // v ≠ 0}) : ((c ^ k • v : {v : E // v ≠ 0}) : E) = (r ^ k) • (v : E) := by
  rw [Units.smul_coe, Units.smul_def, Units.val_zpow_eq_zpow_val, hc, ← map_zpow₀,
    algebraMap_smul]

end Norm

end Units
/-- If a scalar function `f` is `K`-Lipschitz, then `y ↦ f y • c` is `K ‖c‖`-Lipschitz. -/
theorem LipschitzWith.smul_const {α 𝕜 E : Type*} [PseudoEMetricSpace α] [SeminormedRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {K : NNReal} {f : α → 𝕜}
    (hf : LipschitzWith K f) (c : E) : LipschitzWith (K * ‖c‖₊) fun y ↦ f y • c := by
  have hc : LipschitzWith ‖c‖₊ fun r : 𝕜 ↦ r • c := .of_dist_le_mul fun r s ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← sub_smul, coe_nnNorm, mul_comm]
    exact norm_smul_le _ _
  rw [mul_comm]
  exact hc.comp hf

namespace LinearMap

/-- The value of a semilinear map `L : (ι → R) →ₛₗ[σ] F` on a finite product at a vector `v` is
bounded by `∑ j, ‖σ (v j)‖ * ‖L (Pi.single j 1)‖`, its values at the coordinate vectors weighted
by the coordinates of `v`, when `S` acts on `F` with bounded scalar action. -/
theorem norm_apply_le_sum_norm_mul {ι R S F : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    [SeminormedRing S] [SeminormedAddCommGroup F] [Module S F] [IsBoundedSMul S F] {σ : R →+* S}
    (L : (ι → R) →ₛₗ[σ] F) (v : ι → R) :
    ‖L v‖ ≤ ∑ j, ‖σ (v j)‖ * ‖L (Pi.single j 1)‖ := by
  -- Expand `v` in the coordinate vectors.
  have hv : L v = ∑ j, σ (v j) • L (Pi.single j 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    simp only [map_sum, ← map_smulₛₗ, ← Pi.single_smul', smul_eq_mul, mul_one]
  exact hv ▸ norm_sum_le_of_le _ fun j _ ↦ norm_smul_le _ _

section Rescale

variable {𝕜 𝕜₂ E F : Type*} [Semiring 𝕜] [NormedDivisionRing 𝕜₂] {σ : 𝕜 →+* 𝕜₂}
  [AddCommMonoid E] [Module 𝕜 E] [SeminormedAddCommGroup F] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F]

/-- A first-order error at `t • v` rescales to one at `v`: for a semilinear map `L` into a
seminormed group with a bounded scalar action of a normed division ring `𝕜₂`, and `σ t ≠ 0`, the
distance from `(σ t)⁻¹ • w` to `L v` is `‖σ t‖⁻¹` times the distance from `w` to `L (t • v)`.
Neither `E` nor `𝕜` needs a norm. -/
theorem norm_inv_smul_sub_apply (L : E →ₛₗ[σ] F) {t : 𝕜} (ht : σ t ≠ 0) (w : F) (v : E) :
    ‖(σ t)⁻¹ • w - L v‖ = ‖σ t‖⁻¹ * ‖w - L (t • v)‖ := by
  have := NormedDivisionRing.toNormSMulClass (α := 𝕜₂) (β := F)
  rw [← norm_inv, ← norm_smul, smul_sub, map_smulₛₗ, inv_smul_smul₀ ht]

end Rescale

end LinearMap

open Filter Topology in
/-- **Continuity of a radial rescaling.** If `τ` and `y` are continuous and `τ` vanishes on the
frontier of the locus `{p | ‖y p‖ = 0}`, then `p ↦ (τ p / ‖y p‖) • y p` is continuous. The map
vanishes on that locus, and it tends to `0` at a point of its frontier. Only continuity of the
scalar action is assumed, not a bound on it. -/
theorem Continuous.div_norm_smul {X F : Type*} [TopologicalSpace X] [SeminormedAddCommGroup F]
    [Module ℝ F] [ContinuousSMul ℝ F] {τ : X → ℝ} {y : X → F} (hτ : Continuous τ)
    (hy : Continuous y) (hτ0 : ∀ p ∈ frontier {q | ‖y q‖ = 0}, τ p = 0) :
    Continuous fun p ↦ (τ p / ‖y p‖) • y p := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rcases eq_or_ne ‖y p‖ 0 with hp | hp
  swap
  · exact (hτ.continuousAt.div hy.norm.continuousAt hp).smul hy.continuousAt
  suffices Tendsto (fun q ↦ (τ q / ‖y q‖) • y q) (𝓝 p) (𝓝 0) by
    simpa [ContinuousAt, hp] using this
  by_cases hpf : p ∈ frontier {q | ‖y q‖ = 0}
  swap
  · -- at an interior point of the locus, the map vanishes nearby
    have hint : p ∈ interior {q | ‖y q‖ = 0} := by
      rw [← self_sdiff_frontier]
      exact ⟨hp, hpf⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [mem_interior_iff_mem_nhds.1 hint] with q hq
    simp [show ‖y q‖ = 0 from hq]
  -- At a frontier point, split `c = τ q / ‖y q‖` as `⌊c⌋ + fract c`. The integer part moves
  -- `y q` by at most `(|c| + 1) * ‖y q‖ ≤ |τ q| + ‖y q‖`, and by compactness of `[0, 1]`,
  -- `r • y q` tends to `0` uniformly in `r ∈ [0, 1]`, which covers the fractional part.
  have hle (q : X) : ‖(τ q / ‖y q‖) • y q‖ ≤
      ‖τ q‖ + ‖y q‖ + ‖Int.fract (τ q / ‖y q‖) • y q‖ := by
    set c := τ q / ‖y q‖
    have hc : |c| * ‖y q‖ ≤ ‖τ q‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_norm] using
        TauCeti.norm_div_norm_smul_le ‖y q‖ (τ q)
    have hfl : |(⌊c⌋ : ℝ)| ≤ |c| + 1 := abs_le.2
      ⟨by linarith [Int.sub_one_lt_floor c, neg_abs_le c],
        by linarith [Int.floor_le c, le_abs_self c]⟩
    calc ‖c • y q‖ = ‖⌊c⌋ • y q + Int.fract c • y q‖ := by
          rw [← Int.cast_smul_eq_zsmul ℝ, ← add_smul, Int.floor_add_fract]
      _ ≤ |(⌊c⌋ : ℝ)| * ‖y q‖ + ‖Int.fract c • y q‖ := by
          grw [norm_add_le, norm_zsmul_le, Int.norm_eq_abs]
      _ ≤ ‖τ q‖ + ‖y q‖ + ‖Int.fract c • y q‖ := by nlinarith [norm_nonneg (y q)]
  have hfract : Tendsto (fun q ↦ Int.fract (τ q / ‖y q‖) • y q) (𝓝 p) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    have hK : ∀ᶠ v in 𝓝 (y p), ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖r • v‖ < ε :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun r _ ↦ by
        have h0 : ‖r • y p‖ = 0 := by
          have h := (inseparable_zero_iff_norm.2 hp).map (continuous_const_smul r)
          rw [smul_zero] at h
          exact inseparable_zero_iff_norm.1 h
        exact ((continuous_snd.smul continuous_fst).norm.tendsto (y p, r)).eventually
          (gt_mem_nhds (h0.symm ▸ hε))
    filter_upwards [hy.tendsto p hK] with q hq
    simpa using hq _ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  refine squeeze_zero_norm hle ?_
  simpa [hτ0 p hpf, hp] using
    ((hτ.norm.tendsto p).add (hy.norm.tendsto p)).add hfract.norm

end
