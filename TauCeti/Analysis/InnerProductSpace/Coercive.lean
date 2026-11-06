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

A real coercive quadratic form also stays nonnegative under a small perturbation of the operator
and a small scalar shift (`inner_add_smul_id_nonneg_of_norm_sub_le`), which gives the convexity
of perturbed barrier functions, for instance in the Monge–Ampère viscosity argument.

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

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The quadratic form stays nonnegative under small perturbations.** If `κ ‖v‖² ≤ ⟪A v, v⟫`
and `‖D - A‖ ≤ κ + t`, then `0 ≤ ⟪(D + t • id) v, v⟫`. -/
theorem inner_add_smul_id_nonneg_of_norm_sub_le {A D : F →L[ℝ] F} {κ t : ℝ}
    (hA : ∀ v, κ * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (hD : ‖D - A‖ ≤ κ + t) (v : F) :
    0 ≤ inner ℝ ((D + t • ContinuousLinearMap.id ℝ F) v) v := by
  set B := D - A
  have h₁ : -(‖B‖ * ‖v‖ ^ 2) ≤ inner ℝ (B v) v := by
    nlinarith [abs_le.1 (abs_real_inner_le_norm (B v) v), B.le_opNorm v, norm_nonneg v]
  have h₂ : inner ℝ ((D + t • ContinuousLinearMap.id ℝ F) v) v =
      inner ℝ (A v) v + inner ℝ (B v) v + t * ‖v‖ ^ 2 := by
    simp only [B, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [h₂]
  nlinarith [hA v, mul_nonneg (sub_nonneg.2 hD) (sq_nonneg ‖v‖)]

end Real

end ContinuousLinearMap
