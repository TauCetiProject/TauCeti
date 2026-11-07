/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking, Claude Opus 5, OpenAI GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Coercive bounded operators

A uniformly coercive real part of the quadratic form makes a bounded operator
on a real or complex Hilbert space invertible. Self-adjointness is not needed.
The inverse follows from Mathlib’s operator invertibility criterion for a
uniform lower bound on the norm of the quadratic form.
For complex operators the same argument applied to a scalar shift bounds the
real part of every spectral value below by the coercivity constant.

These facts supply the invertibility and spectral half-plane steps in
Lyapunov arguments comparing positive spectral subspaces.

For an operator on a real inner product space, the quadratic form `⟪T v, v⟫` is bounded by
`‖T‖ ‖v‖²` (`ContinuousLinearMap.abs_inner_apply_le`), and the form `⟪S (A v), v⟫` of `S`
against `A` by `‖S‖ ‖A‖ ‖v‖²` (`ContinuousLinearMap.abs_inner_apply_apply_le`). Two consequences
bound the change of this form under a perturbation of `A`
(`ContinuousLinearMap.inner_apply_apply_sub_le`) and bound below the form
`⟪S (A v), v⟫ - ½ ⟪D v, v⟫` that appears when integrating against a family of quadratic forms
(`ContinuousLinearMap.neg_mul_norm_sq_le_inner_sub`).

In a real inner product space we also record the quadratic perturbation estimates for a coercive
symmetric operator `A`: the increment of `F - ⟪·, y + A z⟫` is that of a quadratic centred at
`x + z` up to the second-order error of `F`
(`abs_increment_le_of_abs_expansion_le`), and a coercive quadratic of this form dominates its
perturbation on a sphere (`lt_of_forall_abs_increment_le`).

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/CoerciveUnit.lean`
(Jon Crall and Claude Fable 5) and
`DavisKahan/InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`
(Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5), in the
[Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
Apache-2.0, copyright 2026 Kitware, Inc. The invertibility proof here applies
Mathlib's `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` directly.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A quadratic-form lower bound yields the corresponding norm lower bound. -/
theorem mul_norm_le_norm_apply_of_coercive (N : E →L[𝕜] E) {c : ℝ}
    (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) (z : E) :
    c * ‖z‖ ≤ ‖N z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have h := (hcoer z).trans ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _))
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp (by nlinarith [h])

/-- A bounded operator with a uniformly coercive real quadratic form is a unit. -/
theorem isUnit_of_coercive [CompleteSpace E] (N : E →L[𝕜] E) {c : ℝ}
    (hc : 0 < c) (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) : IsUnit N := by
  apply isUnit_of_forall_le_norm_inner_map N (c := ⟨c, hc.le⟩) hc
  intro x
  exact (mul_comm _ _).le.trans ((hcoer x).trans (RCLike.re_le_norm _))

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The quadratic form of a bounded operator `T` is bounded by `‖T‖ ‖v‖²`. -/
theorem abs_inner_apply_le (T : F →L[ℝ] F) (v : F) : |⟪T v, v⟫_ℝ| ≤ ‖T‖ * ‖v‖ ^ 2 :=
  calc |⟪T v, v⟫_ℝ| ≤ ‖T v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖T‖ * ‖v‖ * ‖v‖ := by gcongr; exact T.le_opNorm v
    _ = ‖T‖ * ‖v‖ ^ 2 := by ring

/-- The quadratic form of `S` against `A` is bounded by `‖S‖ ‖A‖ ‖v‖²`. -/
theorem abs_inner_apply_apply_le (S A : F →L[ℝ] F) (v : F) :
    |⟪S (A v), v⟫_ℝ| ≤ ‖S‖ * ‖A‖ * ‖v‖ ^ 2 :=
  ((S.comp A).abs_inner_apply_le v).trans
    (mul_le_mul_of_nonneg_right (S.opNorm_comp_le A) (sq_nonneg _))

/-- The quadratic form of `S` against `B` differs from that against `A` by at most
`‖S‖ ‖B - A‖ ‖v‖²`. -/
theorem inner_apply_apply_sub_le (S A B : F →L[ℝ] F) (v : F) :
    ⟪S (A v), v⟫_ℝ - ⟪S (B v), v⟫_ℝ ≤ ‖S‖ * ‖B - A‖ * ‖v‖ ^ 2 := by
  have h : ⟪S (A v), v⟫_ℝ - ⟪S (B v), v⟫_ℝ = -⟪S ((B - A) v), v⟫_ℝ := by
    simp only [sub_apply, map_sub, inner_sub_left]
    ring
  rw [h, neg_le]
  exact neg_le_of_abs_le (S.abs_inner_apply_apply_le (B - A) v)

/-- The quadratic form `⟪S (A v), v⟫ - ½ ⟪D v, v⟫` is at least `-(‖S‖ ‖A‖ + ‖D‖ / 2) ‖v‖²`. -/
theorem neg_mul_norm_sq_le_inner_sub (S A D : F →L[ℝ] F) (v : F) :
    -((‖S‖ * ‖A‖ + ‖D‖ / 2) * ‖v‖ ^ 2) ≤ ⟪S (A v), v⟫_ℝ - ⟪D v, v⟫_ℝ / 2 := by
  have h₁ := neg_le_of_abs_le (S.abs_inner_apply_apply_le A v)
  have h₂ := le_of_abs_le (D.abs_inner_apply_le v)
  linarith

end Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A uniform lower bound for the real quadratic form bounds real parts of spectral values below. -/
theorem le_re_of_mem_spectrum_of_coercive (N : E →L[ℂ] E) {c : ℝ}
    (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ (⟪N x, x⟫_ℂ).re)
    {z : ℂ} (hz : z ∈ spectrum ℂ N) : c ≤ z.re := by
  by_contra hnot
  have hgap : 0 < c - z.re := sub_pos.mpr (lt_of_not_ge hnot)
  have hunit : IsUnit (N - z • 1) := isUnit_of_coercive _ hgap fun x ↦ by
    have hx := hcoer x
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, map_sub]
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.re_mul_ofReal,
      RCLike.conj_re]
    -- Normalize the RCLike real projection to the complex field projection for arithmetic.
    change (c - z.re) * ‖x‖ ^ 2 ≤ (⟪N x, x⟫_ℂ).re - z.re * ‖x‖ ^ 2
    nlinarith
  rw [spectrum.mem_iff] at hz
  exact hz (by simpa [Algebra.algebraMap_eq_smul_one] using hunit.neg)

end ContinuousLinearMap

section Real

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The increment of `g = F - ⟪·, p⟫` for `p = y + A z` from `x` to `x'` is
`⟪A (x' - x - z), x' - x - z⟫ / 2 - ⟪A z, z⟫ / 2`, up to the error of the second-order expansion
of `F` at `x` with gradient `y` and Hessian `A`. -/
theorem abs_increment_le_of_abs_expansion_le {A : E →L[ℝ] E} (hA : (A : E →ₗ[ℝ] E).IsSymmetric)
    {x x' y z : E} {a b δ : ℝ}
    (hb : |a - b - ⟪y, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2| ≤ δ * ‖x' - x‖ ^ 2) :
    |(a - ⟪x', y + A z⟫_ℝ) - (b - ⟪x, y + A z⟫_ℝ) -
      (⟪A (x' - x - z), x' - x - z⟫_ℝ / 2 - ⟪A z, z⟫_ℝ / 2)| ≤ δ * ‖x' - x‖ ^ 2 := by
  have hsym : ⟪A z, x' - x⟫_ℝ = ⟪A (x' - x), z⟫_ℝ := by
    exact (hA z (x' - x)).trans (real_inner_comm _ _)
  have hexp : ⟪A (x' - x - z), x' - x - z⟫_ℝ =
      ⟪A (x' - x), x' - x⟫_ℝ - 2 * ⟪A (x' - x), z⟫_ℝ + ⟪A z, z⟫_ℝ := by
    generalize x' - x = h at hsym ⊢
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym]
    ring
  have hpx : ⟪x', y + A z⟫_ℝ - ⟪x, y + A z⟫_ℝ = ⟪y, x' - x⟫_ℝ + ⟪A (x' - x), z⟫_ℝ := by
    rw [← inner_sub_left, inner_add_right, ← hsym, real_inner_comm y, real_inner_comm (A z)]
  convert hb using 2
  linarith

/-- If `g` has, on `closedBall x r`, the increment from `x` of a quadratic centred at `x + z`, up
to `δ ‖x' - x‖ ^ 2` with `δ` small relative to the coercivity constant `c` of `A` and `‖z‖ ≤ s * r`
for `s < 1`, then `g` on the sphere exceeds `g (x + z)`. -/
theorem lt_of_forall_abs_increment_le {A : E →L[ℝ] E} {g : E → ℝ} {x z : E}
    {r s c δ : ℝ} (hc : 0 < c) (hcA : ∀ w, c * ‖w‖ ^ 2 ≤ ⟪A w, w⟫_ℝ) (hs : s < 1) (hr : 0 < r)
    (hδ : δ = c * (1 - s) ^ 2 / 8) (hz : ‖z‖ ≤ s * r)
    (hincr : ∀ x' ∈ closedBall x r, |g x' - g x - (⟪A (x' - x - z), x' - x - z⟫_ℝ / 2 -
      ⟪A z, z⟫_ℝ / 2)| ≤ δ * ‖x' - x‖ ^ 2) :
    ∀ x' ∈ closedBall x r \ ball x r, g (x + z) < g x' := by
  have hη : 0 < 1 - s := sub_pos.2 hs
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hsr : s * r ≤ r := by nlinarith [norm_nonneg z]
  rintro x' ⟨hx', hx'b⟩
  have hnorm : ‖x' - x‖ = r := by
    rw [← dist_eq_norm]
    exact le_antisymm (mem_closedBall.1 hx') (not_lt.1 hx'b)
  have hzr : x + z ∈ closedBall x r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hz.trans hsr
  have h₁ := hincr _ hzr
  have h₂ := hincr x' hx'
  rw [add_sub_cancel_left, sub_self, map_zero, inner_zero_left, zero_div, zero_sub] at h₁
  have hηr : (1 - s) * r ≤ ‖x' - x - z‖ := by
    have := norm_sub_norm_le (x' - x) z
    rw [hnorm] at this
    linarith
  have hq := hcA (x' - x - z)
  have hq' : c * ((1 - s) * r) ^ 2 ≤ c * ‖x' - x - z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hη hr).le hηr 2) hc.le
  have hzr' : ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hz.trans hsr) 2
  have hδz : δ * ‖z‖ ^ 2 ≤ δ * r ^ 2 := mul_le_mul_of_nonneg_left hzr' hδ0.le
  have hδr : δ * r ^ 2 = c * ((1 - s) * r) ^ 2 / 8 := by rw [hδ]; ring
  have hpos : 0 < c * ((1 - s) * r) ^ 2 := by positivity
  rw [abs_le] at h₁ h₂
  rw [hnorm] at h₂
  linarith [h₁.2, h₂.1]

end Real
