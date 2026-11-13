/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.StrictConvexBetween

/-!
# Isometries of a ball into a strictly convex space

Let `A : V → W` be a map between real normed spaces, with `W` strictly convex. If `A` fixes the
origin and preserves the distance between any two points of the ball of radius `ρ > 0` about the
origin, then `A` agrees on that ball with a linear isometry `V →ₗᵢ[ℝ] W`
(`TauCeti.exists_linearIsometry_eqOn_ball`). No surjectivity is assumed.

This is the local form of the fact that an isometry into a strictly convex space is affine
(`Isometry.affineIsometryOfStrictConvexSpace`). Strict convexity forces `A (t • v) = t • A v` for
`t ∈ [0, 1]`, since `A (t • v)` lies metrically between `A 0 = 0` and `A v`. The map
`v ↦ s⁻¹ • A (s • v)` therefore does not depend on the scale `s > 0` once `s • v` lies in the ball,
and it is an isometry of all of `V`, to which the global theorem applies.

It applies to a map defined only near the origin, such as a map between tangent spaces obtained
from a distance-preserving map of Riemannian manifolds through normal coordinates. Such a map is
first shown to preserve distances on a ball: one which scales along rays there and changes
distances near the origin by factors arbitrarily close to one preserves them on the whole ball
(`TauCeti.dist_eq_of_forall_norm_sub_bounds`, which needs no strict convexity).

## Main results

* `TauCeti.dist_eq_of_forall_norm_sub_bounds`: a map scaling along rays with distortion
  arbitrarily close to one near the origin preserves distances on the ball.
* `TauCeti.apply_smul_of_forall_dist_eq`: a map fixing the origin and preserving distances on a
  ball scales along rays, when the target is strictly convex.
* `TauCeti.exists_linearIsometry_eqOn_ball`: such a map agrees on the ball with a linear isometry.
-/

public section

open Filter Metric Set
open scoped Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {A : V → W} {ρ : ℝ}

/-- A map between normed spaces which scales along rays on a ball, and which near the origin
changes distances by at most any factor `c > 1` in either direction, preserves distances on that
ball. -/
theorem dist_eq_of_forall_norm_sub_bounds
    (hsmul : ∀ v ∈ ball (0 : V) ρ, ∀ t ∈ Icc (0 : ℝ) 1, A (t • v) = t • A v)
    (hbound : ∀ c : ℝ, 1 < c → ∃ s > 0, ∀ v ∈ ball (0 : V) s, ∀ w ∈ ball (0 : V) s,
      ‖A v - A w‖ ≤ c * ‖v - w‖ ∧ ‖v - w‖ ≤ c * ‖A v - A w‖)
    {v w : V} (hv : v ∈ ball (0 : V) ρ) (hw : w ∈ ball (0 : V) ρ) :
    dist (A v) (A w) = dist v w := by
  -- Rescaling `v` and `w` into the small ball transfers the bounds to them.
  have key (c : ℝ) (hc : 1 < c) :
      ‖A v - A w‖ ≤ c * ‖v - w‖ ∧ ‖v - w‖ ≤ c * ‖A v - A w‖ := by
    obtain ⟨s, hs, hb⟩ := hbound c hc
    have hsmall (u : V) : ∀ᶠ t in 𝓝[>] (0 : ℝ), t • u ∈ ball (0 : V) s := by
      have h : Tendsto (fun t : ℝ ↦ t • u) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const u
      exact (h.mono_left nhdsWithin_le_nhds).eventually (isOpen_ball.mem_nhds (mem_ball_self hs))
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
    obtain ⟨t, ⟨ht0, ht1⟩, htv, htw⟩ := (hI.and ((hsmall v).and (hsmall w))).exists
    have h := hb _ htv _ htw
    rw [hsmul v hv t ⟨ht0.le, ht1⟩, hsmul w hw t ⟨ht0.le, ht1⟩, ← smul_sub, ← smul_sub,
      norm_smul, norm_smul, Real.norm_of_nonneg ht0.le] at h
    exact ⟨le_of_mul_le_mul_left (by linarith [h.1]) ht0,
      le_of_mul_le_mul_left (by linarith [h.2]) ht0⟩
  -- Letting `c` tend to `1` gives both inequalities without a factor.
  have hlim {a b : ℝ} (h : ∀ c : ℝ, 1 < c → a ≤ c * b) : a ≤ b := by
    have hb : Tendsto (fun c : ℝ ↦ c * b) (𝓝[>] 1) (𝓝 b) := by
      simpa using ((tendsto_id (x := 𝓝 (1 : ℝ))).mul_const b).mono_left
        (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    exact ge_of_tendsto hb (eventually_nhdsWithin_of_forall fun c hc ↦ h c hc)
  rw [dist_eq_norm, dist_eq_norm]
  exact le_antisymm (hlim fun c hc ↦ (key c hc).1) (hlim fun c hc ↦ (key c hc).2)

variable [StrictConvexSpace ℝ W]

/-- A map fixing the origin and preserving distances on a ball about it scales along rays: in a
strictly convex space, `A (t • v)` is the point between `0` and `A v` at the right distances. -/
theorem apply_smul_of_forall_dist_eq (h0 : A 0 = 0)
    (hA : ∀ x ∈ ball (0 : V) ρ, ∀ y ∈ ball (0 : V) ρ,
      dist (A x) (A y) = dist x y) {v : V} (hv : v ∈ ball (0 : V) ρ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : A (t • v) = t • A v := by
  have h0b : (0 : V) ∈ ball (0 : V) ρ := mem_ball_self (pos_of_mem_ball hv)
  have htv : t • v ∈ ball (0 : V) ρ := (convex_ball (0 : V) ρ).smul_mem_of_zero_mem h0b hv ht
  have hd0 : dist (A 0) (A v) = ‖v‖ := by rw [hA 0 h0b v hv, dist_zero_left]
  have hsub : t • v - v = -((1 - t) • v) := by rw [sub_smul, one_smul, neg_sub]
  have h := eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (x := A 0) (y := A (t • v)) (z := A v)
    (r := t) (by rw [hA 0 h0b _ htv, dist_zero_left, hd0, norm_smul, Real.norm_of_nonneg ht.1])
    (by rw [hA _ htv v hv, dist_eq_norm, hd0, hsub, norm_neg, norm_smul,
      Real.norm_of_nonneg (sub_nonneg.2 ht.2)])
  rw [h, h0, AffineMap.lineMap_apply_module, smul_zero, zero_add]

/-- Under the hypotheses of `apply_smul_of_forall_dist_eq`, the rescaled value
`s⁻¹ • A (s • v)` does not depend on the admissible scale `s`. -/
private theorem inv_smul_apply_smul_eq (h0 : A 0 = 0)
    (hA : ∀ x ∈ ball (0 : V) ρ, ∀ y ∈ ball (0 : V) ρ,
      dist (A x) (A y) = dist x y) {v : V} {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') (hsv : s • v ∈ ball (0 : V) ρ) (hs'v : s' • v ∈ ball (0 : V) ρ) :
    s⁻¹ • A (s • v) = s'⁻¹ • A (s' • v) := by
  wlog h : s ≤ s' generalizing s s'
  · exact (this hs' hs hs'v hsv (le_of_not_ge h)).symm
  have hss : s • v = (s / s') • s' • v := by rw [smul_smul, div_mul_cancel₀ _ hs'.ne']
  rw [hss, apply_smul_of_forall_dist_eq h0 hA hs'v
    ⟨div_nonneg hs.le hs'.le, div_le_one_of_le₀ h hs'.le⟩, smul_smul, inv_mul_eq_div,
    div_div_cancel_left' hs.ne']

/-- **A map preserving distances on a ball about the origin is linear there.** If `A : V → W`
fixes the origin and preserves distances between points of the ball of radius `ρ > 0` about the
origin, and `W` is strictly convex, then `A` agrees on that ball with a linear isometry. -/
theorem exists_linearIsometry_eqOn_ball (hρ : 0 < ρ) (h0 : A 0 = 0)
    (hA : ∀ x ∈ ball (0 : V) ρ, ∀ y ∈ ball (0 : V) ρ,
      dist (A x) (A y) = dist x y) :
    ∃ L : V →ₗᵢ[ℝ] W, EqOn A L (ball 0 ρ) := by
  -- Extend `A` to all of `V` by rescaling each vector into the ball.
  let δ : V → ℝ := fun v ↦ ρ / (‖v‖ + 1)
  have hδ (v : V) : 0 < δ v := by positivity
  have hδmem (v : V) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ δ v) : s • v ∈ ball (0 : V) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖v‖ ≤ δ v * ‖v‖ := by gcongr
      _ < ρ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
  let B : V → W := fun v ↦ (δ v)⁻¹ • A (δ v • v)
  have hB (v : V) {s : ℝ} (hs : 0 < s) (hsv : s • v ∈ ball (0 : V) ρ) :
      B v = s⁻¹ • A (s • v) :=
    inv_smul_apply_smul_eq h0 hA (hδ v) hs (hδmem v (hδ v) le_rfl) hsv
  have hBiso : Isometry B := by
    refine Isometry.of_dist_eq fun v w ↦ ?_
    have hs : 0 < min (δ v) (δ w) := lt_min (hδ v) (hδ w)
    have hv := hδmem v hs (min_le_left _ _)
    have hw := hδmem w hs (min_le_right _ _)
    rw [hB v hs hv, hB w hs hw, dist_smul₀, hA _ hv _ hw,
      dist_smul₀, ← mul_assoc, Real.norm_of_nonneg (inv_nonneg.2 hs.le),
      Real.norm_of_nonneg hs.le, inv_mul_cancel₀ hs.ne', one_mul]
  have hB0 : B 0 = 0 := by simp [B, h0]
  refine ⟨hBiso.affineIsometryOfStrictConvexSpace.linearIsometry, fun v hv ↦ ?_⟩
  have hL := hBiso.affineIsometryOfStrictConvexSpace.map_vsub v 0
  simp only [vsub_eq_sub, sub_zero, Isometry.affineIsometryOfStrictConvexSpace_apply, hB0] at hL
  rw [hL, hB v one_pos (by rwa [one_smul]), inv_one, one_smul, one_smul]

end TauCeti
