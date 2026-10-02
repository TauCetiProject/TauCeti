/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle

/-!
# Frontiers of local half-planes and sectors

When a domain agrees locally with an open half-plane, its frontier lies on the bounding line.
When it agrees locally with an open sector, its frontier away from the vertex lies on the
bounding rays, and the vertex itself lies on the frontier. When it agrees far out with an open
sector of opening less than `2π`, its closure is not the whole plane. These facts supply the
boundary conditions for polygonal conformal maps.
-/

public section

open Complex Metric Set Topology

namespace TauCeti

variable {U : Set ℂ}

/-! ### The frontier near a side and near a vertex -/

/-- Near a boundary point where `U` coincides with an open half-plane, the frontier of `U` lies on
the bounding line. -/
theorem im_div_eq_zero_of_mem_frontier {w q b z : ℂ} {ρ : ℝ}
    (hU : ∀ y ∈ ball w ρ, (y ∈ U ↔ 0 < ((y - q) / b).im)) (hz : z ∈ ball w ρ)
    (hzU : z ∈ frontier U) : ((z - q) / b).im = 0 := by
  have hUO : U ∩ ball w ρ = {y : ℂ | 0 < ((y - q) / b).im} ∩ ball w ρ :=
    Set.ext fun y => and_congr_left (hU y)
  have h : z ∈ frontier {y : ℂ | 0 < ((y - q) / b).im} ∩ ball w ρ := by
    rw [← frontier_inter_open_inter isOpen_ball, ← hUO, frontier_inter_open_inter isOpen_ball]
    exact ⟨hzU, hz⟩
  exact (frontier_lt_subset_eq continuous_const (by fun_prop) h.1).symm

/-- On an open set `V` where `U` coincides, away from the vertex `v`, with the open sector
`{|arg ((z - v) / b)| < α}`, the frontier of `U` away from the vertex lies on the two bounding rays
`|arg ((z - v) / b)| = α`.  Typically `V` is a ball about the vertex, or the exterior of a ball when
`U` is a sector near infinity. -/
theorem abs_arg_div_eq_of_mem_frontier {V : Set ℂ} {v b z : ℂ} {α : ℝ} (hb : b ≠ 0)
    (hV : IsOpen V) (hU : ∀ y ∈ V, y ≠ v → (y ∈ U ↔ |((y - v) / b).arg| < α)) (hz : z ∈ V)
    (hzv : z ≠ v) (hzU : z ∈ frontier U) : |((z - v) / b).arg| = α := by
  set O := V \ {v}
  have hO : IsOpen O := hV.sdiff isClosed_singleton
  -- `|arg|` is the unoriented angle with `1`, which is continuous away from `0`
  have hφ : ContinuousOn (fun y : ℂ => |((y - v) / b).arg|) O := fun y hy => by
    have hy0 : (y - v) / b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hy.2) hb
    have hangle : ContinuousAt (fun y : ℂ => InnerProductGeometry.angle ((y - v) / b) 1) y :=
      (InnerProductGeometry.continuousAt_angle (x := ((y - v) / b, (1 : ℂ))) hy0
        one_ne_zero).comp (f := fun y : ℂ => ((y - v) / b, (1 : ℂ))) (by fun_prop)
    refine (hangle.congr ?_).continuousWithinAt
    filter_upwards [isOpen_ne.mem_nhds hy.2] with y hy
    exact angle_one_right (div_ne_zero (sub_ne_zero.mpr hy) hb)
  -- on `V` minus the vertex, `U` is the strict sublevel set of `|arg|`
  have hfr : (⟨z, hz, hzv⟩ : O) ∈ frontier {y : O | |((y - v : ℂ) / b).arg| < α} := by
    have hpreimage : ((↑) : O → ℂ) ⁻¹' U =
        {y : O | |((y - v : ℂ) / b).arg| < α} :=
      Set.ext fun y => hU y y.2.1 y.2.2
    rw [← hpreimage,
      ← hO.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val]
    exact hzU
  exact frontier_lt_subset_eq hφ.domRestrict continuous_const hfr

/-- If a set `U` coincides near `v`, away from `v` itself, with the open sector
`{|arg ((z - v) / b)| < α}` of half-opening `α ∈ (0, π]`, then the vertex `v` lies on the frontier
of `U`. -/
theorem mem_frontier_of_forall_mem_iff_abs_arg_lt {v b : ℂ} {ρ α : ℝ}
    (hρ : 0 < ρ) (hb : b ≠ 0) (hα₀ : 0 < α) (hα : α ≤ Real.pi)
    (hU : ∀ z ∈ ball v ρ, z ≠ v → (z ∈ U ↔ |((z - v) / b).arg| < α)) : v ∈ frontier U := by
  -- the ray `t ↦ v + (s * t) * b` leaves `v` in the direction `s * b`
  have hlim (s : ℝ) : Filter.Tendsto (fun t : ℝ => v + ((s * t : ℝ) : ℂ) * b) (𝓝[>] 0) (𝓝 v) := by
    have hc : Continuous fun t : ℝ => v + ((s * t : ℝ) : ℂ) * b := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hmem (s : ℝ) (hs : s ≠ 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ (v + ((s * t : ℝ) : ℂ) * b ∈ U ↔ |(((s * t : ℝ) : ℂ)).arg| < α) := by
    filter_upwards [(hlim s).eventually (ball_mem_nhds v hρ), self_mem_nhdsWithin]
      with t ht (htpos : 0 < t)
    refine ⟨htpos, ?_⟩
    rw [hU _ ht (by simp [hs, htpos.ne', hb]), add_sub_cancel_left, mul_div_cancel_right₀ _ hb]
  rw [frontier_eq_closure_inter_closure]
  refine ⟨mem_closure_of_tendsto (hlim 1) ?_, mem_closure_of_tendsto (hlim (-1)) ?_⟩
  · filter_upwards [hmem 1 one_ne_zero] with t ⟨ht, h⟩
    rw [h, arg_ofReal_of_nonneg (by positivity), abs_zero]
    exact hα₀
  · filter_upwards [hmem (-1) (by norm_num)] with t ⟨ht, h⟩ htU
    have harg := h.mp htU
    rw [arg_ofReal_of_neg (by linarith), abs_of_pos Real.pi_pos] at harg
    exact harg.not_ge hα

/-! ### A sector near infinity -/

/-- If a set `U` coincides far from `c` with the open sector `{|arg ((z - c) / b)| < α}` of
half-opening `α ∈ [0, π)`, then `U` misses the far part of the opposite sector, an open set, so the
closure of `U` is not the whole plane. -/
theorem closure_ne_univ_of_forall_mem_iff_abs_arg_lt {c b : ℂ} {ρ α : ℝ} (hb : b ≠ 0)
    (hα₀ : 0 ≤ α) (hα : α < Real.pi)
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ → (z ∈ U ↔ |((z - c) / b).arg| < α)) :
    closure U ≠ univ := by
  -- points far out in the opposite direction, where `arg` is close to `π`
  set W : Set ℂ := {z | ρ < ‖z - c‖ ∧ ((z - c) / b).re < Real.cos α * ‖(z - c) / b‖}
  have hWo : IsOpen W :=
    (isOpen_lt (g := fun z : ℂ => ‖z - c‖) continuous_const (by fun_prop)).inter
      (isOpen_lt (f := fun z : ℂ => ((z - c) / b).re) (by fun_prop) (by fun_prop))
  have hWU : Disjoint W U := by
    refine disjoint_left.2 fun z ⟨hz, hzW⟩ hzU => ?_
    have hx : (z - c) / b ≠ 0 := fun h => by simp [h] at hzW
    -- in the sector, `cos (arg x) > cos α`
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hα.le ((hU z hz).1 hzU)
    rw [Real.cos_abs, cos_arg hx, lt_div_iff₀ (norm_pos_iff.2 hx)] at hcos
    exact hcos.not_gt hzW
  set t : ℝ := (|ρ| + 1) / ‖b‖
  have ht : 0 < t := by have := norm_pos_iff.2 hb; positivity
  have hpW : c - b * t ∈ W := by
    have hdiv : (c - b * t - c) / b = ((-t : ℝ) : ℂ) := by field_simp; push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le,
        mul_div_cancel₀ _ (norm_ne_zero_iff.2 hb)]
      linarith [le_abs_self ρ]
    · rw [hdiv, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hα₀ le_rfl hα
      rw [Real.cos_pi] at this
      nlinarith
  exact fun h => (hWU.closure_right hWo).notMem_of_mem_left hpW (h ▸ mem_univ _)

end TauCeti

end
