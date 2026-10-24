/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle
public import TauCeti.Topology.ClusterSet

import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Frontiers of local half-planes and sectors

When a domain agrees locally with an open half-plane, its frontier lies on the bounding line.
When it agrees locally with an open sector, its frontier away from the vertex lies on the
bounding rays, and the vertex itself lies on the frontier. When it agrees far out with an open
sector of opening less than `2π`, some point lies outside its closure. When it agrees far out with
an open half-strip, its frontier far out lies on the two bounding rays, and again some point lies
outside its closure; the same holds when far out it misses an open half-strip. The exponential
coordinate `exp (π * I - ζ)` is injective on the closed strip `0 ≤ im ζ ≤ π`, real on its bounding
lines and in the upper half-plane inside it, and on the closed half-strip it tends to `0` at
infinity. These facts supply the boundary conditions for polygonal conformal maps.
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

/-! ### Preconnected approach regions at a side or a vertex -/

/-- If a set `U` coincides near `w` with the open half-plane `{0 < im ((z - q) / b)}`, then `U` has
preconnected approach regions at `w`: its traces on small balls about `w` are convex. -/
theorem isPreconnectedApproachAt_of_forall_mem_iff_im_div_pos {w q b : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im)) : IsPreconnectedApproachAt U w := by
  have hconv : Convex ℝ {z : ℂ | (q / b).im < (z / b).im} :=
    convex_halfSpace_gt (.mk (fun x y => by simp [add_div])
      (fun c x => by simp [Complex.real_smul, mul_div_assoc])) _
  refine isPreconnectedApproachAt_of_isPreconnected_inter_ball hρ fun δ _ hδ => ?_
  have heq : U ∩ ball w δ = {z : ℂ | (q / b).im < (z / b).im} ∩ ball w δ := by
    ext z
    refine and_congr_left fun hz => ?_
    rw [hU z (ball_subset_ball hδ hz), sub_div, sub_im, sub_pos, mem_ofPred_eq]
  rw [heq]
  exact (hconv.inter (convex_ball w δ)).isPreconnected

/-- If a set `U` coincides near `v`, away from `v` itself, with the open sector
`{|arg ((z - v) / b)| < α}` of half-opening `α ≤ π`, then `U` has preconnected approach regions at
`v`: in polar coordinates about `v` its traces on small punctured balls are rectangles. -/
theorem isPreconnectedApproachAt_of_forall_mem_iff_abs_arg_lt {v b : ℂ} {ρ α : ℝ} (hρ : 0 < ρ)
    (hb : b ≠ 0) (hα : α ≤ Real.pi)
    (hU : ∀ z ∈ ball v ρ, z ≠ v → (z ∈ U ↔ |((z - v) / b).arg| < α)) :
    IsPreconnectedApproachAt U v := by
  refine isPreconnectedApproachAt_of_isPreconnected_inter_ball hρ fun δ hδ hδρ => ?_
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set P : ℝ × ℝ → ℂ := fun p =>
    v + b * ((p.1 : ℂ) * (Complex.cos (p.2 : ℂ) + Complex.sin (p.2 : ℂ) * I))
  set A : Set (ℝ × ℝ) := Ioo 0 (δ / ‖b‖) ×ˢ Ioo (-α) α
  have hPc : Continuous P := by fun_prop
  -- away from the vertex, `U ∩ ball v δ` is the image of the polar rectangle `A`
  have hS : (U ∩ ball v δ) \ {v} = P '' A := by
    rw [image_polar_rectangle_eq hb hα]
    ext z
    exact ⟨fun ⟨⟨hzU, hzb⟩, hzv⟩ => ⟨hzb, hzv, (hU z (ball_subset_ball hδρ hzb) hzv).mp hzU⟩,
      fun ⟨hzb, hzv, harg⟩ => ⟨⟨(hU z (ball_subset_ball hδρ hzb) hzv).mpr harg, hzb⟩, hzv⟩⟩
  have hsub : U ∩ ball v δ ⊆ insert v (P '' A) := fun z hz => by
    by_cases hzv : z = v
    · exact Or.inl hzv
    · exact Or.inr (hS ▸ ⟨hz, hzv⟩)
  rcases le_or_gt α 0 with hα₀ | hα₀
  · -- an empty sector: only the vertex can remain
    have hA : A = ∅ := prod_eq_empty_iff.mpr (Or.inr (Ioo_eq_empty (by linarith)))
    rw [hA, image_empty, insert_empty_eq] at hsub
    exact (subsingleton_singleton.anti hsub).isPreconnected
  · -- the vertex is the image of the corner `(0, 0)` of the closed polar rectangle
    have hv : v ∈ closure (P '' A) := by
      have h0 : ((0 : ℝ), (0 : ℝ)) ∈ closure A := by
        rw [closure_prod_eq, closure_Ioo (div_pos hδ hb').ne, closure_Ioo (by linarith)]
        exact ⟨⟨le_rfl, (div_pos hδ hb').le⟩, ⟨by linarith, hα₀.le⟩⟩
      simpa [P] using mem_closure_image hPc.continuousAt h0
    exact ((isPreconnected_Ioo.prod isPreconnected_Ioo).image P hPc.continuousOn).subset_closure
      (hS ▸ sdiff_subset) (hsub.trans (insert_subset hv subset_closure))

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

/-- A point `ζ` of the closed strip `0 ≤ im ζ ≤ π` has `‖ζ‖ ≤ |re ζ| + π`. -/
theorem norm_le_abs_re_add_pi_of_im_mem_Icc {ζ : ℂ} (him : ζ.im ∈ Icc 0 Real.pi) :
    ‖ζ‖ ≤ |ζ.re| + Real.pi := by
  have h := norm_le_abs_re_add_abs_im ζ
  rw [abs_of_nonneg him.1] at h
  linarith [him.2]

/-- The imaginary part of the exponential coordinate `exp (π * I - ζ)` of the half-strip, which
is positive on the open strip `0 < im ζ < π` and vanishes on its bounding lines. -/
theorem im_exp_pi_mul_I_sub (ζ : ℂ) :
    (exp (Real.pi * I - ζ)).im = Real.exp (-ζ.re) * Real.sin ζ.im := by
  rw [exp_im]
  simp [Real.sin_pi_sub]

/-- The exponential coordinate `exp (π * I - ζ)` is injective on the closed strip
`0 ≤ im ζ ≤ π`. -/
theorem injOn_exp_pi_mul_I_sub :
    InjOn (fun ζ : ℂ => exp (Real.pi * I - ζ)) {ζ : ℂ | ζ.im ∈ Icc 0 Real.pi} := by
  have hlog {ζ : ℂ} (hζ : ζ.im ∈ Icc 0 Real.pi) :
      log (exp (Real.pi * I - ζ)) = Real.pi * I - ζ := by
    have him : (Real.pi * I - ζ).im = Real.pi - ζ.im := by simp
    exact log_exp (by rw [him]; linarith [hζ.2, Real.pi_pos]) (by rw [him]; linarith [hζ.1])
  intro ζ hζ ξ hξ h
  simpa using (hlog hζ).symm.trans ((congrArg log h).trans (hlog hξ))

/-- The exponential coordinate `exp (π * I - (w - c) / b)` of the half-strip
`{0 < re ((w - c) / b), 0 < im ((w - c) / b) < π}` is an exponential `exp ((w - c') / b')`. -/
theorem exp_pi_mul_I_sub_div {w c b : ℂ} (hb : b ≠ 0) :
    exp (Real.pi * I - (w - c) / b) = exp ((w - (c + Real.pi * I * b)) / -b) := by
  congr 1
  field_simp
  ring

/-- In the closed half-strip `{0 ≤ re ζ, 0 ≤ im ζ ≤ π}`, the exponential coordinate
`exp (π * I - ζ)`, which maps the half-strip into the closed upper half-disc, tends to `0` as `ζ`
tends to infinity. -/
theorem tendsto_exp_pi_mul_I_sub_of_tendsto_cobounded {α : Type*} {l : Filter α} {ζ : α → ℂ}
    (hζ : Filter.Tendsto ζ l (Bornology.cobounded ℂ))
    (hmem : ∀ᶠ a in l, 0 ≤ (ζ a).re ∧ (ζ a).im ∈ Icc 0 Real.pi) :
    Filter.Tendsto (fun a => exp (Real.pi * I - ζ a)) l (𝓝 0) := by
  -- on the half-strip `re ζ ≥ ‖ζ‖ - π`, which tends to infinity
  have hre : Filter.Tendsto (fun a => (ζ a).re) l Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ (Filter.tendsto_atTop_add_const_right _ (-Real.pi)
      (tendsto_norm_cobounded_atTop.comp hζ))
    filter_upwards [hmem] with a ⟨hre, him⟩
    have h := norm_le_abs_re_add_pi_of_im_mem_Icc him
    rw [abs_of_nonneg hre] at h
    simp only [Function.comp_apply]
    linarith
  refine tendsto_exp_comap_re_atBot.comp (Filter.tendsto_comap_iff.mpr ?_)
  simpa [Function.comp_def] using Filter.tendsto_neg_atTop_atBot.comp hre

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

/-! ### The exterior of a half-strip at infinity -/

/-- If, far from `c`, no point `z` of a set `U` lies in the open half-strip
`{0 < re ((z - c) / b), 0 < im ((z - c) / b) < π}` (as for a set that coincides far out with the
exterior of the closed half-strip), then some point lies outside the closure of `U`. -/
theorem exists_notMem_closure_of_forall_mem_notMem_halfStrip {c b : ℂ} {ρ : ℝ} (hb : b ≠ 0)
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ → z ∈ U →
      ¬(0 < ((z - c) / b).re ∧ ((z - c) / b).im ∈ Ioo 0 Real.pi)) :
    ∃ q, q ∉ closure U := by
  -- the point `q = c + (t + π / 2 * I) * b` has `(q - c) / b = t + π / 2 * I`
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set t : ℝ := (|ρ| + 1) / ‖b‖ with ht_def
  have ht : 0 < t := by positivity
  set ζ : ℂ := t + (Real.pi / 2 : ℝ) * I
  have hdiv : (c + ζ * b - c) / b = ζ := by
    rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hb]
  have hρ : ρ < ‖c + ζ * b - c‖ := by
    rw [add_sub_cancel_left, norm_mul]
    calc ρ < t * ‖b‖ := by rw [ht_def, div_mul_cancel₀ _ hb'.ne']; linarith [le_abs_self ρ]
      _ ≤ ‖ζ‖ * ‖b‖ := by
        gcongr
        simpa [ζ, abs_of_pos ht] using abs_re_le_norm ζ
  have hre : 0 < ((c + ζ * b - c) / b).re := by rw [hdiv]; simpa [ζ] using ht
  have him : ((c + ζ * b - c) / b).im ∈ Ioo 0 Real.pi := by
    rw [hdiv]
    simp [ζ, Real.pi_pos]
  refine ⟨c + ζ * b, ?_⟩
  rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds]
  have hζc : Continuous fun z : ℂ => (z - c) / b := by fun_prop
  filter_upwards [(continuous_norm.comp (continuous_sub_right c)).continuousAt.eventually
    (lt_mem_nhds hρ), (continuous_re.comp hζc).continuousAt.eventually (lt_mem_nhds hre),
    (continuous_im.comp hζc).continuousAt.eventually (isOpen_Ioo.mem_nhds him)]
    with z hzρ hzre hzim hzU
  exact hU z hzρ hzU ⟨hzre, hzim⟩

end TauCeti

end
