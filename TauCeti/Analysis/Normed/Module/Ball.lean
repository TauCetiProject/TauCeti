/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Metric balls and spheres in normed spaces

This file records how the affine map `y ↦ c • y +ᵥ x` pulls metric balls, closed balls, and
spheres back to their corresponding sets centered at zero.

The preimage formulas need only `[Norm 𝕜] [SMul 𝕜 E] [NormSMulClass 𝕜 E]` on the
scalars and their action. Balls and closed balls require `0 < ‖c‖`; spheres only require
`‖c‖ ≠ 0`. Over a normed division ring these conditions are equivalent to `c ≠ 0`, via
`norm_pos_iff` and `norm_ne_zero_iff` respectively.

The range formula identifies a positive real scaling of the unit sphere with the sphere
of that radius in a seminormed real vector space. Two points on a sphere of nonzero radius
centered at zero lie on the same line exactly when they are equal or antipodal.

The normalization lemmas compute the norm of `R⁻¹ • z` when `R ≥ 0` and characterize the unit
norm conditions for `R⁻¹ • z` when `R > 0`.
They need only a norm homogeneous under real scalar multiplication; no additive structure
or metric on the vector type is required.

In a nontrivial real normed space, one ball lies in another exactly when its radius plus the
distance between the centres is at most the radius of the other. The sufficiency holds in every
pseudometric space (`Metric.closedBall_subset_closedBall'`, `Metric.ball_subset_ball'`); the
necessity uses a point of the smaller ball on the far side of its centre.
-/

public section

namespace TauCeti

section Preimage

variable {𝕜 E P : Type*} [Norm 𝕜] [SeminormedAddCommGroup E]
  [SMul 𝕜 E] [NormSMulClass 𝕜 E] [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- The affine normalization map `y ↦ c • y +ᵥ x` pulls the ball `Metric.ball x (‖c‖ * r)` back
to `Metric.ball 0 r`, for a scale `c` of positive norm. -/
@[simp]
theorem preimage_smul_vadd_ball_norm (x : P) {c : 𝕜} (hc : 0 < ‖c‖) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.ball x (‖c‖ * r)) = Metric.ball 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_lt_mul_iff_right₀ hc

/-- The affine map `y ↦ c • y +ᵥ x` pulls the closed ball of radius `‖c‖ * r` about `x`
back to the closed ball of radius `r` about `0`. -/
@[simp]
theorem preimage_smul_vadd_closedBall (x : P) {c : 𝕜} (hc : 0 < ‖c‖) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.closedBall x (‖c‖ * r)) =
      Metric.closedBall 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_le_mul_iff_right₀ hc

/-- The affine map `y ↦ c • y +ᵥ x` pulls the sphere of radius `‖c‖ * r` about `x`
back to the sphere of radius `r` about `0`, provided `‖c‖ ≠ 0`. -/
@[simp]
theorem preimage_smul_vadd_sphere (x : P) {c : 𝕜} (hc : ‖c‖ ≠ 0) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.sphere x (‖c‖ * r)) = Metric.sphere 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_sphere, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_right_inj' hc

end Preimage

section Sphere

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of the unit sphere under scaling by a positive real `c` is the sphere of radius
`c`. -/
@[simp]
theorem range_smul_coe_sphere {c : ℝ} (hc : 0 < c) :
    Set.range (fun u : Metric.sphere (0 : E) 1 ↦ c • (u : E)) = Metric.sphere 0 c := by
  rw [Set.range_comp' (c • ·) Subtype.val, Subtype.range_coe, Set.image_smul,
    smul_sphere' hc.ne', smul_zero, Real.norm_of_nonneg hc.le, mul_one]

/-- Two points of a sphere of nonzero radius centered at zero in a real seminormed space
lie on the same line exactly when they are equal or antipodal. -/
@[simp]
theorem coe_mem_span_singleton_iff {r : ℝ} (hr : r ≠ 0) {x p : Metric.sphere (0 : E) r} :
    (x : E) ∈ ℝ ∙ (p : E) ↔ x = p ∨ x = -p := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
    have habs : |a| = 1 := by
      apply (mul_eq_right₀ hr).1
      simpa [← ha, norm_smul] using norm_eq_of_mem_sphere x
    rcases (abs_eq zero_le_one).1 habs with rfl | rfl
    · exact Or.inl (Subtype.ext (by rw [← ha, one_smul]))
    · exact Or.inr (Subtype.ext (by rw [← ha, coe_neg_sphere, neg_one_smul]))
  · rintro (rfl | rfl)
    · exact Submodule.mem_span_singleton_self _
    · rw [coe_neg_sphere]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)

/-- The unit sphere minus `p` and `-p` is the set of its points off the line through `p`. -/
theorem compl_singleton_inter_compl_singleton_neg_eq (p : Metric.sphere (0 : E) 1) :
    ({p}ᶜ ∩ {-p}ᶜ : Set (Metric.sphere (0 : E) 1)) =
      ({x | (x : E) ∉ ℝ ∙ (p : E)} : Set (Metric.sphere (0 : E) 1)) := by
  ext x
  simp [not_or]

end Sphere

section Normalization

variable {E : Type*} [Norm E] [SMul ℝ E] [NormSMulClass ℝ E]

/-- Scaling a vector by the inverse of a positive radius puts it inside the unit norm bound
exactly when its original norm is less than that radius. -/
@[simp]
theorem norm_inv_smul_lt_one_iff {z : E} {R : ℝ} (hR : 0 < R) :
    ‖R⁻¹ • z‖ < 1 ↔ ‖z‖ < R := by
  simp [norm_smul, Real.norm_of_nonneg hR.le, inv_mul_lt_iff₀ hR]

/-- Scaling a vector by the inverse of a positive radius gives unit norm exactly when its
original norm equals that radius. -/
@[simp]
theorem norm_inv_smul_eq_one_iff {z : E} {R : ℝ} (hR : 0 < R) :
    ‖R⁻¹ • z‖ = 1 ↔ ‖z‖ = R := by
  simp [norm_smul, Real.norm_of_nonneg hR.le, inv_mul_eq_iff_eq_mul₀ hR.ne']

/-- Scaling a vector by the inverse of a nonnegative real divides its norm by that real. -/
theorem norm_inv_smul_of_nonneg {z : E} {R : ℝ} (hR : 0 ≤ R) : ‖R⁻¹ • z‖ = ‖z‖ / R := by
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hR, inv_mul_eq_div]

end Normalization

section Subset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {x y : E} {r s : ℝ}

/-- In a nontrivial real normed space, the closed ball of nonnegative radius `r` about `x` lies in
the closed ball of radius `s` about `y` exactly when `r + dist x y ≤ s`. -/
theorem closedBall_subset_closedBall_iff (hr : 0 ≤ r) :
    Metric.closedBall x r ⊆ Metric.closedBall y s ↔ r + dist x y ≤ s := by
  refine ⟨fun h => ?_, Metric.closedBall_subset_closedBall'⟩
  -- A vector `v` of norm `r` pointing away from `y`, so that `x + v` is as far from `y` as
  -- the closed ball about `x` allows.
  obtain ⟨v, hv, hxyv⟩ : ∃ v : E, ‖v‖ = r ∧ ‖x - y + v‖ = ‖x - y‖ + r := by
    rcases eq_or_ne x y with rfl | hxy
    · obtain ⟨v, hv⟩ := exists_norm_eq E hr
      exact ⟨v, hv, by simp [hv]⟩
    · have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
      refine ⟨(r / ‖x - y‖) • (x - y), ?_, ?_⟩
      · rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hpos.ne']
      · nth_rw 1 [← one_smul ℝ (x - y)]
        rw [← add_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
        field_simp
  have hmem := h (Metric.mem_closedBall.2 (by rw [dist_eq_norm, add_sub_cancel_left, hv]))
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_right_comm, hxyv] at hmem
  rwa [dist_eq_norm, add_comm]

/-- In a nontrivial real normed space, the ball of positive radius `r` about `x` lies in the ball
of radius `s` about `y` exactly when `r + dist x y ≤ s`. -/
theorem ball_subset_ball_iff (hr : 0 < r) :
    Metric.ball x r ⊆ Metric.ball y s ↔ r + dist x y ≤ s := by
  refine ⟨fun h => ?_, Metric.ball_subset_ball'⟩
  -- Every closed ball of radius `t < r` about `x` lies in the closed ball of radius `s`.
  suffices ∀ t < r, t ≤ s - dist x y by linarith [le_of_forall_lt_imp_le_of_dense this]
  intro t ht
  have hsub : Metric.closedBall x (max t 0) ⊆ Metric.closedBall y s :=
    (Metric.closedBall_subset_ball (max_lt ht hr)).trans (h.trans Metric.ball_subset_closedBall)
  linarith [le_max_left t 0, (closedBall_subset_closedBall_iff (le_max_right t 0)).1 hsub]

end Subset

end TauCeti
