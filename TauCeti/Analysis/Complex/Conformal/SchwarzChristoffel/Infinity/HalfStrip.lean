/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Parallel
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.SimpleBoundary
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# The half-strip end of a logarithmic Schwarz--Christoffel image

When the total turning exponent is `-1`, the two outer boundary rays are horizontal,
point to the right, and have heights `im c` and `im c + π`, where `c` is the logarithmic
constant at infinity. The boundary agrees with these two lines sufficiently far to the
right, without any simplicity assumption.

If the boundary is simple, the image of the upper half-plane agrees there with the open
strip between those lines. Thus the direct mapping theorem gives a polygonal domain with
an actual half-strip end, rather than only a complementary-component description.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Filter Metric Set Topology
open UpperHalfPlane hiding I

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- With total exponent `-1`, sufficiently far to the right the real boundary range is
exactly the pair of horizontal lines at heights `im c` and `im c + π`. Repeated prevertices
and nonsimple boundary chains are allowed. -/
theorem exists_mem_range_schwarzChristoffelBoundary_iff_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = -1) :
    ∃ R : ℝ, ∀ w : ℂ, R < w.re →
      (w ∈ range (schwarzChristoffelBoundary a e z₀) ↔
        w.im = (schwarzChristoffelLogConstantAtInfinity a e z₀).im ∨
        w.im = (schwarzChristoffelLogConstantAtInfinity a e z₀).im + Real.pi) := by
  obtain ⟨A, _, ha⟩ := (finite_range a).isBounded.exists_pos_norm_le
  have ha' (i : ι) : -A ≤ a i ∧ a i ≤ A :=
    abs_le.mp (by simpa using ha (a i) (mem_range_self i))
  obtain ⟨R, hR⟩ := exists_mem_range_schwarzChristoffelBoundary_iff_of_sum_eq_neg_one_or_eq_one
    a e z₀ hfinite (fun i _ => (ha' i).1) (fun i _ => (ha' i).2) (Or.inl hsum)
  rw [im_schwarzChristoffelBoundary_of_forall_le_of_sum_eq_neg_one a e z₀
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite A) (fun i _ => (ha' i).2) hsum,
    im_schwarzChristoffelBoundary_of_forall_ge_of_sum_eq_neg_one a e z₀
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite (-A)) (fun i _ => (ha' i).1)
      hsum] at hR
  exact ⟨R, hR⟩

/-- The logarithmic asymptotic confines image points far to the right to a slightly wider
strip. The finite part is bounded using the continuous extension at the prevertices. -/
private theorem exists_im_bounds_of_re_gt_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = -1) :
    ∃ R : ℝ, ∀ z ∈ upperHalfPlaneSet, R < (schwarzChristoffelPrimitive a e z₀ z).re →
      (schwarzChristoffelLogConstantAtInfinity a e z₀).im - 1 <
          (schwarzChristoffelPrimitive a e z₀ z).im ∧
        (schwarzChristoffelPrimitive a e z₀ z).im <
          (schwarzChristoffelLogConstantAtInfinity a e z₀).im + Real.pi + 1 := by
  let F := schwarzChristoffelPrimitive a e z₀
  let c := schwarzChristoffelLogConstantAtInfinity a e z₀
  have htail : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet, ‖F z - log z - c‖ < 1 := by
    have h : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet, F z - log z ∈ ball c 1 :=
      (tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e z₀ hsum).eventually
        (ball_mem_nhds c zero_lt_one)
    exact h.mono fun z hz => (mem_ball_iff_norm.mp hz)
  rw [eventually_inf_principal, hasBasis_cobounded_norm.eventually_iff] at htail
  obtain ⟨A, _, htail⟩ := htail
  let K := closedBall (0 : ℂ) A ∩ closure upperHalfPlaneSet
  obtain ⟨M, _, hM⟩ := ((isCompact_closedBall (0 : ℂ) A).inter_right isClosed_closure
    |>.image_of_continuousOn
      ((continuousOn_extendFrom_schwarzChristoffelPrimitive a e z₀ hfinite).mono
        inter_subset_right)).isBounded.exists_pos_norm_le
  refine ⟨M, fun z hz hMz => ?_⟩
  have hzA : A ≤ ‖z‖ := by
    by_contra h
    have hzK : z ∈ K := ⟨by simpa using (not_le.mp h).le, subset_closure hz⟩
    have hb := hM _ (mem_image_of_mem _ hzK)
    rw [extendFrom_extends
      (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hz] at hb
    exact not_lt_of_ge ((re_le_norm _).trans hb) hMz
  have herr := (abs_le.mp (abs_im_le_norm (F z - log z - c)))
  have hnorm := htail hzA hz
  have harg := arg_nonneg_iff.mpr (le_of_lt hz)
  have harg' := arg_le_pi z
  simp only [sub_im, log_im] at herr
  constructor <;> linarith

/-- The logarithmic image has points arbitrarily far to the right between its two outer
boundary heights. -/
private theorem exists_mem_image_in_strip_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) (R : ℝ) :
    ∃ w ∈ schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet, R < w.re ∧
      (schwarzChristoffelLogConstantAtInfinity a e z₀).im < w.im ∧
        w.im < (schwarzChristoffelLogConstantAtInfinity a e z₀).im + Real.pi := by
  let F := schwarzChristoffelPrimitive a e z₀
  let c := schwarzChristoffelLogConstantAtInfinity a e z₀
  have hpath : Tendsto (fun y : ℝ => (y : ℂ) * I) atTop
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · apply tendsto_norm_atTop_iff_cobounded.mp
      simpa using (tendsto_abs_atTop_atTop : Tendsto (fun y : ℝ => |y|) atTop atTop)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      simpa using hy
  have him : Tendsto (fun y : ℝ => (F ((y : ℂ) * I)).im) atTop
      (𝓝 (c.im + Real.pi / 2)) := by
    have h := ((continuous_im.tendsto c).comp
      ((tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e z₀ hsum).comp hpath)).add_const
      (Real.pi / 2)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    simp [F, arg_real_mul I hy, arg_I, log_im]
  have hre := (tendsto_re_schwarzChristoffelPrimitive_atTop_of_sum_eq_neg_one
    a e z₀ hsum).comp hpath
  have hstrip := him.eventually (Ioo_mem_nhds
    (by linarith [Real.pi_pos] : c.im < c.im + Real.pi / 2)
    (by linarith [Real.pi_pos] : c.im + Real.pi / 2 < c.im + Real.pi))
  obtain ⟨y, hy, hyr, hyim⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and ((hre.eventually (eventually_gt_atTop R)).and hstrip)).exists
  exact ⟨F ((y : ℂ) * I), ⟨(y : ℂ) * I, by simpa using hy, rfl⟩, hyr, hyim⟩

/-- **The half-strip end of a simple logarithmic Schwarz--Christoffel map.** For integrable
finite prevertices, total exponent `-1`, and an injective real boundary parametrization,
the image sufficiently far to the right is exactly the open strip of width `π` between
the heights `im c` and `im c + π`. No ordering or sign assumption on the finite data is needed. -/
theorem exists_mem_image_schwarzChristoffelPrimitive_iff_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : ∑ i, e i = -1)
    (hinj : Function.Injective (schwarzChristoffelBoundary a e z₀)) :
    ∃ R : ℝ, ∀ w : ℂ, R < w.re →
      (w ∈ schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ↔
        (schwarzChristoffelLogConstantAtInfinity a e z₀).im < w.im ∧
          w.im < (schwarzChristoffelLogConstantAtInfinity a e z₀).im + Real.pi) := by
  let U := schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet
  let c := schwarzChristoffelLogConstantAtInfinity a e z₀
  obtain ⟨R₁, hboundary⟩ :=
    exists_mem_range_schwarzChristoffelBoundary_iff_of_sum_eq_neg_one a e z₀ hfinite hsum
  obtain ⟨R₂, hbounds⟩ := exists_im_bounds_of_re_gt_of_sum_eq_neg_one a e z₀ hfinite hsum
  let R := max R₁ R₂
  have hUo : IsOpen U :=
    isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl
  have hfrontier : frontier U = range (schwarzChristoffelBoundary a e z₀) :=
    frontier_image_schwarzChristoffelPrimitive_eq_range_of_neg_one_le_sum
      a e z₀ hfinite hsum.ge (Or.inl (by rw [hsum]; norm_num)) hinj
  -- Each of the three regions to the right of `R` avoids the frontier, so connectedness
  -- makes membership in the open image constant on that region.
  have dichotomy (s : Set ℂ) (hs : IsPreconnected s)
      (havoid : ∀ w ∈ s, R < w.re ∧ w.im ≠ c.im ∧ w.im ≠ c.im + Real.pi) :
      s ⊆ U ∨ s ⊆ (closure U)ᶜ := by
    apply hs.subset_or_subset hUo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.mpr subset_closure))
    intro w hw
    by_cases hwU : w ∈ U
    · exact Or.inl hwU
    · right
      intro hwcl
      have hwfr : w ∈ frontier U := by rw [hUo.frontier_eq]; exact ⟨hwcl, hwU⟩
      rw [hfrontier] at hwfr
      have hav := havoid w hw
      exact ((hboundary w ((le_max_left _ _).trans_lt hav.1)).mp hwfr).elim hav.2.1 hav.2.2
  -- The vertical path to infinity supplies the interior witness for the middle region.
  let S : Set ℂ := {w | R < w.re ∧ c.im < w.im ∧ w.im < c.im + Real.pi}
  have hS : S ⊆ U := by
    have hs : IsPreconnected S := ((convex_halfSpace_re_gt R).inter
      ((convex_halfSpace_im_gt c.im).inter
        (convex_halfSpace_im_lt (c.im + Real.pi)))).isPreconnected
    obtain ⟨w, hwU, hwR, hwlo, hwhi⟩ :=
      exists_mem_image_in_strip_of_sum_eq_neg_one a e z₀ hsum R
    exact (dichotomy S hs (fun w hw => ⟨hw.1, ne_of_gt hw.2.1, ne_of_lt hw.2.2⟩)).resolve_right
      (fun h => h ⟨hwR, hwlo, hwhi⟩ (subset_closure hwU))
  -- The wider asymptotic strip gives exterior witnesses above and below the two rays.
  have hout (b : ℝ) (s : Set ℂ) (hs : IsPreconnected s)
      (havoid : ∀ w ∈ s, R < w.re ∧ w.im ≠ c.im ∧ w.im ≠ c.im + Real.pi)
      (hb : b < c.im - 1 ∨ c.im + Real.pi + 1 < b)
      (hmem : (R + 1 : ℂ) + (b : ℂ) * I ∈ s) : s ⊆ (closure U)ᶜ := by
    refine (dichotomy s hs havoid).resolve_left fun h => ?_
    obtain ⟨z, hz, heq⟩ := h hmem
    have hwR : R₂ < ((R + 1 : ℂ) + (b : ℂ) * I).re := by
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, one_re]
      exact (le_max_right R₁ R₂).trans_lt (lt_add_one R)
    have h := hbounds z hz (heq ▸ hwR)
    rw [heq] at h
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, one_im] at h
    dsimp only [c] at hb
    rcases hb with hb | hb <;> linarith
  have hlow : {w : ℂ | R < w.re ∧ w.im < c.im} ⊆ (closure U)ᶜ := by
    apply hout (c.im - 2) _ ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_lt c.im)).isPreconnected
    · intro w hw
      exact ⟨hw.1, ne_of_lt hw.2,
        ne_of_lt (hw.2.trans (lt_add_of_pos_right _ Real.pi_pos))⟩
    · left; linarith
    · simp
  have hhigh : {w : ℂ | R < w.re ∧ c.im + Real.pi < w.im} ⊆ (closure U)ᶜ := by
    apply hout (c.im + Real.pi + 2) _ ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_gt (c.im + Real.pi))).isPreconnected
    · intro w hw
      exact ⟨hw.1, ne_of_gt ((lt_add_of_pos_right _ Real.pi_pos).trans hw.2), ne_of_gt hw.2⟩
    · right; linarith
    · simp
  -- The boundary lines themselves are excluded because the image is open.
  refine ⟨R, fun w hwR => ⟨fun hwU => ?_, fun hw => hS ⟨hwR, hw⟩⟩⟩
  have hwcl := subset_closure hwU
  have hne : w.im ≠ c.im ∧ w.im ≠ c.im + Real.pi := by
    constructor <;> intro h
    all_goals
      have hwfr : w ∈ frontier U := by
        rw [hfrontier]
        exact (hboundary w ((le_max_left _ _).trans_lt hwR)).mpr (by simp only [c] at h; tauto)
      rw [hUo.frontier_eq] at hwfr
      exact hwfr.2 hwU
  constructor
  · exact lt_of_le_of_ne (le_of_not_gt (fun h => hlow ⟨hwR, h⟩ hwcl)) hne.1.symm
  · exact lt_of_le_of_ne (le_of_not_gt (fun h => hhigh ⟨hwR, h⟩ hwcl)) hne.2

end TauCeti
