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

A translation orthogonal to the normal vector preserves a strict half-space. The ball of radius
`r` about a unit vector `x` lies in the half-space `{z | 1 - r ≤ ⟪x, z⟫}`, and more generally a
closed ball `closedBall w r` lies in `{y | ⟪y, ν⟫ < c}` whenever `⟪w, ν⟫ + r * ‖ν‖ < c`
(`TauCeti.closedBall_subset_setOf_inner_lt`) and in `{y | c < ⟪y, ν⟫}` whenever
`c + r * ‖ν‖ < ⟪w, ν⟫` (`TauCeti.closedBall_subset_setOf_lt_inner`). For `x` in the closed
half-space `{z | c ≤ ⟪z, ν⟫}`, the open ball of radius `ρ` about `x + (ρ / ‖ν‖) ν` lies in the
open half-space `{z | c < ⟪z, ν⟫}` (`TauCeti.ball_add_smul_subset_setOf_lt_inner`). In rigid
coordinates `e : F ≃ᵃⁱ ℝ × E`, the normal coordinate `(e x).fst` is `⟪x, ν⟫` plus a constant, so
the region where it is positive is a half-space.
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

/-- For a point `x` of the closed half-space `{z | c ≤ ⟪z, ν⟫}`, `ν ≠ 0`, the open ball of radius
`ρ` about `x + (ρ / ‖ν‖) ν` lies in the open half-space `{z | c < ⟪z, ν⟫}`. -/
theorem ball_add_smul_subset_setOf_lt_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ν x : E} {c ρ : ℝ} (hν : ν ≠ 0) (hx : c ≤ ⟪x, ν⟫_ℝ) :
    Metric.ball (x + (ρ / ‖ν‖) • ν) ρ ⊆ {z | c < ⟪z, ν⟫_ℝ} := by
  intro z hz
  have hν0 : 0 < ‖ν‖ := norm_pos_iff.2 hν
  set w := z - (x + (ρ / ‖ν‖) • ν)
  have hw : ‖w‖ * ‖ν‖ < ρ * ‖ν‖ :=
    mul_lt_mul_of_pos_right (by rw [← dist_eq_norm]; exact hz) hν0
  have hc : ⟪(ρ / ‖ν‖) • ν, ν⟫_ℝ = ρ * ‖ν‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hz' : ⟪z, ν⟫_ℝ = ⟪x, ν⟫_ℝ + ⟪(ρ / ‖ν‖) • ν, ν⟫_ℝ + ⟪w, ν⟫_ℝ := by
    simp only [w, inner_sub_left, inner_add_left]
    ring
  exact Set.mem_ofPred.2 (by linarith [neg_le_of_abs_le (abs_real_inner_le_norm w ν)])

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
