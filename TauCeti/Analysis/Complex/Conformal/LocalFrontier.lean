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
sector of opening less than `2π`, some point lies outside its closure. When it agrees far out with
an open half-strip, its frontier far out lies on the two bounding rays, and again some point lies
outside its closure. These facts supply the boundary conditions for polygonal conformal maps.
-/

public section

open Complex Metric Set Topology

namespace TauCeti

variable {U : Set ℂ}

/-- The absolute value of the argument, the unoriented angle with `1`, is continuous away from
`0`, across the negative real axis too, where the argument itself jumps. -/
theorem continuousAt_abs_arg {w : ℂ} (hw : w ≠ 0) : ContinuousAt (fun z : ℂ => |z.arg|) w := by
  have hangle : ContinuousAt (fun z : ℂ => InnerProductGeometry.angle z 1) w :=
    (InnerProductGeometry.continuousAt_angle (x := (w, (1 : ℂ))) hw one_ne_zero).comp
      (f := fun z : ℂ => (z, (1 : ℂ))) (by fun_prop)
  refine hangle.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with z hz
  exact angle_one_right hz

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
  have hφ : ContinuousOn (fun y : ℂ => |((y - v) / b).arg|) O := fun y hy =>
    ((continuousAt_abs_arg (div_ne_zero (sub_ne_zero.mpr hy.2) hb)).comp
      (f := fun y : ℂ => (y - v) / b) (by fun_prop)).continuousWithinAt
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

/-! ### A sector at infinity -/

/-- If a set `U` coincides far from `c` with the open sector `{|arg ((z - c) / b)| < α}` of
half-opening `α < π`, then some point lies outside the closure of `U`, far out on the ray opposite
to the sector. -/
theorem exists_notMem_closure_of_forall_mem_iff_abs_arg_lt {c b : ℂ} {ρ α : ℝ} (hb : b ≠ 0)
    (hα : α < Real.pi) (hU : ∀ z : ℂ, ρ < ‖z - c‖ → (z ∈ U ↔ |((z - c) / b).arg| < α)) :
    ∃ q, q ∉ closure U := by
  -- the point `q = c - t * b`, at distance `|ρ| + 1` from `c`, sees the sector at the angle `π`
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set t : ℝ := (|ρ| + 1) / ‖b‖ with ht_def
  have ht : 0 < t := by positivity
  have hdiv : (c - (t : ℂ) * b - c) / b = ((-t : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  have hρ : ρ < ‖c - (t : ℂ) * b - c‖ := by
    rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le,
      ht_def, div_mul_cancel₀ _ hb'.ne']
    linarith [le_abs_self ρ]
  have harg : α < |((c - (t : ℂ) * b - c) / b).arg| := by
    rwa [hdiv, arg_ofReal_of_neg (by linarith), abs_of_pos Real.pi_pos]
  refine ⟨c - (t : ℂ) * b, ?_⟩
  rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds]
  have hφ : ContinuousAt (fun z : ℂ => |((z - c) / b).arg|) (c - (t : ℂ) * b) :=
    (continuousAt_abs_arg (by rw [hdiv]; exact_mod_cast (neg_neg_of_pos ht).ne)).comp
      (f := fun z : ℂ => (z - c) / b) (by fun_prop)
  filter_upwards [(continuous_norm.comp (continuous_sub_right c)).continuousAt.eventually
    (lt_mem_nhds hρ), hφ.eventually (lt_mem_nhds harg)] with z hzρ hzα hzU
  exact lt_asymm ((hU z hzρ).mp hzU) hzα

/-! ### A half-strip at infinity -/

/-- If a set `U` coincides far from `c` with the open half-strip
`{0 < re ((z - c) / b), 0 < im ((z - c) / b) < π}`, then far from `c` the frontier of `U` lies on
the two bounding rays `im ((z - c) / b) ∈ {0, π}`, with `0 ≤ re ((z - c) / b)`.  Here "far" also
excludes the short side `re ((z - c) / b) = 0` of the half-strip, which lies within distance
`π * ‖b‖` of `c`. -/
theorem re_div_nonneg_and_im_div_eq_zero_or_eq_pi_of_mem_frontier {c b z : ℂ} {ρ : ℝ}
    (hU : ∀ y : ℂ, ρ < ‖y - c‖ →
      (y ∈ U ↔ 0 < ((y - c) / b).re ∧ ((y - c) / b).im ∈ Ioo 0 Real.pi))
    (hzρ : ρ < ‖z - c‖) (hzb : Real.pi * ‖b‖ < ‖z - c‖) (hzU : z ∈ frontier U) :
    0 ≤ ((z - c) / b).re ∧ (((z - c) / b).im = 0 ∨ ((z - c) / b).im = Real.pi) := by
  set V := {y : ℂ | ρ < ‖y - c‖}
  have hV : IsOpen V := isOpen_lt continuous_const (by fun_prop)
  set S := {y : ℂ | 0 < ((y - c) / b).re ∧ ((y - c) / b).im ∈ Ioo 0 Real.pi}
  have hζ : Continuous fun y : ℂ => (y - c) / b := by fun_prop
  have hS : IsOpen S := (isOpen_lt continuous_const (continuous_re.comp hζ)).inter
    (isOpen_Ioo.preimage (continuous_im.comp hζ))
  have hUV : U ∩ V = S ∩ V := Set.ext fun y => and_congr_left (hU y)
  have hzS : z ∈ frontier S ∩ V := by
    rw [← frontier_inter_open_inter hV, ← hUV, frontier_inter_open_inter hV]
    exact ⟨hzU, hzρ⟩
  rw [hS.frontier_eq] at hzS
  obtain ⟨⟨hcl, hzS⟩, -⟩ := hzS
  -- the closure of the half-strip lies in the closed half-strip
  have hT : IsClosed {y : ℂ | 0 ≤ ((y - c) / b).re ∧ ((y - c) / b).im ∈ Icc 0 Real.pi} :=
    (isClosed_le continuous_const (continuous_re.comp hζ)).inter
      (isClosed_Icc.preimage (continuous_im.comp hζ))
  obtain ⟨hre, him₀, himπ⟩ := closure_minimal
    (fun y (hy : y ∈ S) => (⟨hy.1.le, Ioo_subset_Icc_self hy.2⟩ :
      0 ≤ ((y - c) / b).re ∧ ((y - c) / b).im ∈ Icc 0 Real.pi)) hT hcl
  -- for `b = 0` the half-strip is empty
  rcases eq_or_ne b 0 with rfl | hb
  · simp [S] at hcl
  -- the short side `re = 0` is within distance `π * ‖b‖` of `c`
  have hre' : 0 < ((z - c) / b).re := by
    refine hre.lt_of_ne fun h => ?_
    have hnorm : ‖(z - c) / b‖ ≤ Real.pi := by
      calc ‖(z - c) / b‖ ≤ |((z - c) / b).re| + |((z - c) / b).im| := norm_le_abs_re_add_abs_im _
        _ ≤ Real.pi := by rw [← h, abs_zero, zero_add, abs_of_nonneg him₀]; exact himπ
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hb)] at hnorm
    exact hnorm.not_gt hzb
  refine ⟨hre, ?_⟩
  by_contra h
  rw [not_or] at h
  exact hzS ⟨hre', him₀.lt_of_ne (Ne.symm h.1), himπ.lt_of_ne h.2⟩

/-- If, far from `c`, every point `z` of a set `U` has `0 < re ((z - c) / b)` (as for a set that
coincides far out with a half-strip or a half-plane), then some point lies outside the closure of
`U`, far out in the direction `-b`. -/
theorem exists_notMem_closure_of_forall_mem_re_div_pos {c b : ℂ} {ρ : ℝ} (hb : b ≠ 0)
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ → z ∈ U → 0 < ((z - c) / b).re) : ∃ q, q ∉ closure U := by
  -- the point `q = c - t * b`, at distance `|ρ| + 1` from `c`, has `re ((q - c) / b) = -t < 0`
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set t : ℝ := (|ρ| + 1) / ‖b‖ with ht_def
  have ht : 0 < t := by positivity
  have hρ : ρ < ‖c - (t : ℂ) * b - c‖ := by
    rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le,
      ht_def, div_mul_cancel₀ _ hb'.ne']
    linarith [le_abs_self ρ]
  have hre : ((c - (t : ℂ) * b - c) / b).re < 0 := by
    rw [sub_sub_cancel_left, neg_div, mul_div_cancel_right₀ _ hb]
    simpa using ht
  refine ⟨c - (t : ℂ) * b, ?_⟩
  rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds]
  filter_upwards [(continuous_norm.comp (continuous_sub_right c)).continuousAt.eventually
    (lt_mem_nhds hρ), ((continuous_re.comp ((continuous_sub_right c).div_const b)).continuousAt
      (x := c - (t : ℂ) * b)).eventually (gt_mem_nhds hre)] with z hzρ hzre hzU
  exact lt_asymm (hU z hzρ hzU) hzre

end TauCeti

end
