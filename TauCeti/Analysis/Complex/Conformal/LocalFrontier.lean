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
bounding rays, and the vertex itself lies on the frontier. These facts supply the boundary
conditions for polygonal conformal maps.
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

/-- Near a vertex where `U` coincides with the open sector `{|arg ((z - v) / b)| < α}`, the
frontier of `U` away from the vertex lies on the two bounding rays `|arg ((z - v) / b)| = α`. -/
theorem abs_arg_div_eq_of_mem_frontier {v b z : ℂ} {ρ α : ℝ} (hb : b ≠ 0)
    (hU : ∀ y ∈ ball v ρ, y ≠ v → (y ∈ U ↔ |((y - v) / b).arg| < α)) (hz : z ∈ ball v ρ)
    (hzv : z ≠ v) (hzU : z ∈ frontier U) : |((z - v) / b).arg| = α := by
  set O := ball v ρ \ {v}
  have hO : IsOpen O := isOpen_ball.sdiff isClosed_singleton
  -- `|arg|` is the unoriented angle with `1`, which is continuous away from `0`
  have hφ : ContinuousOn (fun y : ℂ => |((y - v) / b).arg|) O := fun y hy => by
    have hy0 : (y - v) / b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hy.2) hb
    have hangle : ContinuousAt (fun y : ℂ => InnerProductGeometry.angle ((y - v) / b) 1) y :=
      (InnerProductGeometry.continuousAt_angle (x := ((y - v) / b, (1 : ℂ))) hy0
        one_ne_zero).comp (f := fun y : ℂ => ((y - v) / b, (1 : ℂ))) (by fun_prop)
    refine (hangle.congr ?_).continuousWithinAt
    filter_upwards [isOpen_ne.mem_nhds hy.2] with y hy
    exact angle_one_right (div_ne_zero (sub_ne_zero.mpr hy) hb)
  -- on the punctured ball `U` is the strict sublevel set of `|arg|`
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

end TauCeti

end
