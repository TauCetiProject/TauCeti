/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Inner-product half-spaces

A translation orthogonal to the normal vector preserves a strict half-space, and the open and
closed half-spaces are convex (`TauCeti.convex_of_halfSpace`, `TauCeti.convex_setOf_le_inner`).
The ball of radius `r` about a unit vector `x` lies in the half-space `{z | 1 - r ≤ ⟪x, z⟫}`, and
more generally a closed ball `closedBall w r` lies in `{y | ⟪y, ν⟫ < c}` whenever
`⟪w, ν⟫ + r * ‖ν‖ < c` (`TauCeti.closedBall_subset_setOf_inner_lt`) and in `{y | c < ⟪y, ν⟫}`
whenever `c + r * ‖ν‖ < ⟪w, ν⟫` (`TauCeti.closedBall_subset_setOf_lt_inner`); for `ν ≠ 0`, an
open ball `ball w r` lies in `{y | c < ⟪y, ν⟫}` already when `c + r * ‖ν‖ ≤ ⟪w, ν⟫`
(`TauCeti.ball_subset_setOf_lt_inner`). For `ν ≠ 0` and `x` in the closed half-space
`{z | c ≤ ⟪z, ν⟫}`, the open ball of radius `ρ` about `x + (ρ / ‖ν‖) ν` lies in the open
half-space `{z | c < ⟪z, ν⟫}` (`TauCeti.ball_add_smul_subset_setOf_lt_inner`). For `ν ≠ 0`, the
foot `x - ((⟪x, ν⟫ - c) / ‖ν‖²) ν` of the perpendicular from `x` lies on the hyperplane
`{y | ⟪y, ν⟫ = c}`, at distance `|⟪x, ν⟫ - c| / ‖ν‖` from `x`, and every point of that
hyperplane lies at distance at least `(⟪x, ν⟫ - c) / ‖ν‖` from `x`. In rigid coordinates
`e : F ≃ᵃⁱ ℝ × E`, the normal coordinate `(e x).fst` is `⟪x, ν⟫` plus a constant, so the region
where it is positive is a half-space.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

/-- Every translation parallel to the boundary of the half-space `{x | c < ⟪x, ν⟫}` maps it into
itself. -/
theorem mapsTo_add_smul_of_halfSpace {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : Set E} {ν τ : E} {c : ℝ}
    (hΩ : ∀ x, x ∈ s ↔ c < ⟪x, ν⟫_ℝ) (hτ : ⟪τ, ν⟫_ℝ = 0) (t : ℝ) :
    Set.MapsTo (· + t • τ) s s := fun x hx =>
  (hΩ _).2 (by simpa [inner_add_left, real_inner_smul_left, hτ] using (hΩ x).1 hx)

/-- The half-space `{x | c < ⟪x, ν⟫}` is convex. -/
theorem convex_of_halfSpace {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set E} {ν : E} {c : ℝ} (hΩ : ∀ x, x ∈ s ↔ c < ⟪x, ν⟫_ℝ) : Convex ℝ s := by
  obtain rfl : s = {x | c < ⟪x, ν⟫_ℝ} := Set.ext hΩ
  simpa only [LinearMap.flip_apply, innerₗ_apply_apply] using
    convex_halfSpace_gt ((innerₗ E).flip ν).isLinear c

/-- The closed half-space `{x | c ≤ ⟪x, ν⟫}` is convex. -/
theorem convex_setOf_le_inner {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : E) (c : ℝ) : Convex ℝ {x : E | c ≤ ⟪x, ν⟫_ℝ} :=
  convex_halfSpace_ge ⟨fun x y => inner_add_left x y ν, fun a x => real_inner_smul_left x ν a⟩ c

/-- The inner product of a unit vector `x` with `z` is at least `1 - ‖z - x‖`. -/
theorem one_sub_norm_sub_le_inner {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : ‖x‖ = 1) (z : E) : 1 - ‖z - x‖ ≤ ⟪x, z⟫_ℝ := by
  have h := real_inner_le_norm x (x - z)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hx, norm_sub_rev] at h
  linarith

/-- A closed ball `Metric.closedBall w r` lies in the open half-space `{y | ⟪y, ν⟫ < c}` whenever
`⟪w, ν⟫ + r * ‖ν‖ < c`. -/
theorem closedBall_subset_setOf_inner_lt {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {w ν : E} {r c : ℝ} (h : ⟪w, ν⟫_ℝ + r * ‖ν‖ < c) :
    Metric.closedBall w r ⊆ {y | ⟪y, ν⟫_ℝ < c} := fun y hy => by
  have hyw := (real_inner_le_norm (y - w) ν).trans
    (mul_le_mul_of_nonneg_right (mem_closedBall_iff_norm.1 hy) (norm_nonneg ν))
  rw [inner_sub_left] at hyw
  exact Set.mem_ofPred.2 (by linarith)

/-- A closed ball `Metric.closedBall w r` lies in the open half-space `{y | c < ⟪y, ν⟫}` whenever
`c + r * ‖ν‖ < ⟪w, ν⟫`. -/
theorem closedBall_subset_setOf_lt_inner {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {w ν : E} {r c : ℝ} (h : c + r * ‖ν‖ < ⟪w, ν⟫_ℝ) :
    Metric.closedBall w r ⊆ {y | c < ⟪y, ν⟫_ℝ} := fun y hy => by
  have h' : ⟪w, -ν⟫_ℝ + r * ‖-ν‖ < -c := by
    rw [inner_neg_right, norm_neg]
    linarith
  simpa [inner_neg_right] using closedBall_subset_setOf_inner_lt h' hy

/-- An open ball `Metric.ball w r` lies in the open half-space `{y | c < ⟪y, ν⟫}` whenever
`ν ≠ 0` and `c + r * ‖ν‖ ≤ ⟪w, ν⟫`. -/
theorem ball_subset_setOf_lt_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w ν : E} {r c : ℝ} (hν : ν ≠ 0) (h : c + r * ‖ν‖ ≤ ⟪w, ν⟫_ℝ) :
    Metric.ball w r ⊆ {y | c < ⟪y, ν⟫_ℝ} := by
  intro y hy
  have hyw : ‖w - y‖ < r := by rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hy
  have hcs : ⟪w - y, ν⟫_ℝ < r * ‖ν‖ :=
    (real_inner_le_norm (w - y) ν).trans_lt
      (mul_lt_mul_of_pos_right hyw (norm_pos_iff.2 hν))
  rw [inner_sub_left] at hcs
  exact Set.mem_ofPred.2 (by linarith)

/-- For a point `x` of the closed half-space `{z | c ≤ ⟪z, ν⟫}`, `ν ≠ 0`, the open ball of radius
`ρ` about `x + (ρ / ‖ν‖) ν` lies in the open half-space `{z | c < ⟪z, ν⟫}`. -/
theorem ball_add_smul_subset_setOf_lt_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ν x : E} {c ρ : ℝ} (hν : ν ≠ 0) (hx : c ≤ ⟪x, ν⟫_ℝ) :
    Metric.ball (x + (ρ / ‖ν‖) • ν) ρ ⊆ {z | c < ⟪z, ν⟫_ℝ} :=
  ball_subset_setOf_lt_inner hν (by
    have h : ρ / ‖ν‖ * ‖ν‖ ^ 2 = ρ * ‖ν‖ := by
      rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hν)]
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, h]
    linarith)

/-- The vector `(t / ‖ν‖²) ν` has norm `|t| / ‖ν‖`. -/
theorem norm_div_norm_sq_smul_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) (ν : E) : ‖(t / ‖ν‖ ^ 2) • ν‖ = |t| / ‖ν‖ := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < ‖ν‖ ^ 2)]
  field_simp

/-- The foot `x - ((⟪x, ν⟫ - c) / ‖ν‖²) ν` of the perpendicular from `x` to the hyperplane
`{y | ⟪y, ν⟫ = c}` lies on that hyperplane. -/
theorem real_inner_sub_div_norm_sq_smul_self_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ν : E} (hν : ν ≠ 0) (x : E) (c : ℝ) :
    ⟪x - ((⟪x, ν⟫_ℝ - c) / ‖ν‖ ^ 2) • ν, ν⟫_ℝ = c := by
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_pos (norm_pos_iff.2 hν) 2).ne', sub_sub_cancel]

/-- Every point `w` of the hyperplane `{y | ⟪y, ν⟫ = c}` lies at distance at least
`(⟪x, ν⟫ - c) / ‖ν‖` from `x`. -/
theorem div_norm_le_dist_of_inner_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x w ν : E} {c : ℝ} (hw : ⟪w, ν⟫_ℝ = c) : (⟪x, ν⟫_ℝ - c) / ‖ν‖ ≤ dist x w := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  rw [div_le_iff₀ (norm_pos_iff.2 hν), dist_eq_norm, ← hw, ← inner_sub_left]
  exact real_inner_le_norm _ _

end TauCeti

namespace AffineIsometryEquiv

open scoped InnerProductSpace

/-- **The normal coordinate of rigid coordinates is affine.** For an affine isometry equivalence
`e : F ≃ᵃⁱ ℝ × E`, the first coordinate `(e x).fst` is `⟪x, ν⟫ + (e 0).fst`, where `ν` is the
preimage of the unit normal `(1, 0)` under the linear part of `e`. -/
theorem fst_apply_eq_inner_add {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (x : F) :
    (e x).fst = ⟪x, e.linearIsometryEquiv.symm (WithLp.toLp 2 (1, 0))⟫_ℝ + (e 0).fst := by
  have hx : e.linearIsometryEquiv x = e x - e 0 := by
    simpa only [vsub_eq_sub, sub_zero] using e.map_vsub x 0
  rw [← e.linearIsometryEquiv.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    WithLp.prod_inner_apply, hx]
  simp

end AffineIsometryEquiv
