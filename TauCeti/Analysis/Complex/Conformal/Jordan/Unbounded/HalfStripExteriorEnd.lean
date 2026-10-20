/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.BoundaryPrevertex
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.InvertedCoordinate
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.ModelEnd
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Complex.Conformal.LocalFrontier
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Half-strip-exterior ends of an inverted coordinate

Let `f` be a conformal map of the upper half-plane onto an unbounded domain with several accesses
to infinity, and let `g = (f - q)⁻¹` be its inverted coordinate, continuous on the closed upper
half-plane and injective away from its zeros.  The real zeros of `g` are the boundary parameters at
which `f` tends to infinity.

This file treats a zero `x` of `g` at which the domain ends in the exterior of a half-strip: `f`
maps the points of the upper half-plane near `x` into the far part
`E = {ρ < ‖w - c‖, re ((w - c) / b) < 0 ∨ im ((w - c) / b) ∉ [0, π]}` of the exterior of the closed
half-strip `{0 ≤ re ((w - c) / b), 0 ≤ im ((w - c) / b) ≤ π}`, and `E` lies in the image of `f`.
This is an end of opening `2 * π`, between two parallel sides pointing the same way.  Then the
recovered map `q + g⁻¹` is continuous and injective on a closed upper half-disc about `x` with `x`
removed, tends to infinity at `x`, and far out maps the open upper half-disc exactly onto the
exterior of the half-strip.  These are the local conditions at a vertex at infinity of opening
`2 * π`, with turning exponent `-3`, in the Schwarz--Christoffel formula
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary`, so they apply to
polygonal domains with several ends, one of which is of this kind.

With several accesses to infinity, `g` is only injective away from its zeros, so it is not clear a
priori that `x` is the only zero nearby.  Unlike the sector and parallel-sided ends, the exterior
of a half-strip has no elementary straightening coordinate in which reflection would isolate the
zero.  Instead the argument is topological.  Near `x` the nonzero real boundary values of
`q + g⁻¹` lie on the two bounding rays of the half-strip.  Between two zeros of `g` there would be
a zero-free real interval, on which `q + g⁻¹` would run injectively along one ray and tend to
infinity at both ends, which is impossible.  The description of the far image then follows
because the exterior of a half-strip is preconnected at infinity
(`TauCeti.isPreconnectedAtInfinityIn_halfStripExterior`), while the bounded image of a semicircle
about `x` separates the image of the half-disc from the image of the rest of the upper
half-plane.

## Main results

* `TauCeti.exists_ball_halfStripExterior_end_of_inverted_coordinate`: at a zero of the inverted
  coordinate whose end is the exterior of a half-strip, the recovered map satisfies the local
  conditions at a vertex at infinity of opening `2 * π`.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- A continuous injective map of an open interval into the two rays
`{0 ≤ re ζ, im ζ ∈ {0, π}}` cannot tend to infinity at both ends.  Indeed, by connectedness it
stays on one ray, along which its real part is injective, hence strictly monotone, while it tends
to `+∞` at both ends. -/
private theorem false_of_injOn_rays_of_tendsto {φ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn φ (Ioo a b)) (hi : InjOn φ (Ioo a b))
    (hφ : ∀ u ∈ Ioo a b, 0 ≤ (φ u).re ∧ ((φ u).im = 0 ∨ (φ u).im = Real.pi))
    (ha : Tendsto (fun u => ‖φ u‖) (𝓝[>] a) atTop)
    (hb : Tendsto (fun u => ‖φ u‖) (𝓝[<] b) atTop) : False := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  set m := (a + b) / 2
  -- the imaginary part is constant
  have him (u : ℝ) (hu : u ∈ Ioo a b) : (φ u).im = (φ m).im := by
    by_contra hne
    have hpre : IsPreconnected ((fun u => (φ u).im) '' Ioo a b) :=
      isPreconnected_Ioo.image _ (continuous_im.comp_continuousOn hc)
    have h0π : (0 : ℝ) ∈ (fun u => (φ u).im) '' Ioo a b ∧
        Real.pi ∈ (fun u => (φ u).im) '' Ioo a b := by
      rcases (hφ u hu).2 with h | h <;> rcases (hφ m hm).2 with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · exact ⟨⟨u, hu, h⟩, ⟨m, hm, h'⟩⟩
      · exact ⟨⟨m, hm, h'⟩, ⟨u, hu, h⟩⟩
      · exact absurd (h.trans h'.symm) hne
    obtain ⟨v, hv, hvπ⟩ := hpre.Icc_subset h0π.1 h0π.2
      (show Real.pi / 2 ∈ Icc 0 Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩)
    rcases (hφ v hv).2 with h | h <;> simp only at hvπ <;> linarith [Real.pi_pos]
  -- so the real part is continuous and injective, and tends to `+∞` at both ends
  have hinj : InjOn (fun u => (φ u).re) (Ioo a b) := fun u hu v hv h =>
    hi hu hv (Complex.ext h ((him u hu).trans (him v hv).symm))
  have hre (u : ℝ) (hu : u ∈ Ioo a b) : ‖φ u‖ ≤ (φ u).re + Real.pi := by
    have := norm_le_abs_re_add_pi_of_im_mem_Icc (ζ := φ u)
      (by rcases (hφ u hu).2 with h | h <;> simp [h, Real.pi_pos.le])
    rwa [abs_of_nonneg (hφ u hu).1] at this
  rcases (continuous_re.comp_continuousOn hc).strictMonoOn_of_injOn_Ioo hab hinj with h | h
  · obtain ⟨u, hu, hnorm⟩ :=
      ((eventually_mem_set.mpr (Ioo_mem_nhdsGT hm.1)).and
        (ha.eventually_gt_atTop ((φ m).re + Real.pi))).exists
    have : (φ u).re < (φ m).re := h ⟨hu.1, hu.2.trans hm.2⟩ hm hu.2
    linarith [hre u ⟨hu.1, hu.2.trans hm.2⟩]
  · obtain ⟨u, hu, hnorm⟩ :=
      ((eventually_mem_set.mpr (Ioo_mem_nhdsLT hm.2)).and
        (hb.eventually_gt_atTop ((φ m).re + Real.pi))).exists
    have : (φ u).re < (φ m).re := h hm ⟨hm.1.trans hu.1, hu.2⟩ hu.1
    linarith [hre u ⟨hm.1.trans hu.1, hu.2⟩]

variable {f g : ℂ → ℂ} {q : ℂ}

/-- Near a zero of the inverted coordinate whose end is the far part
`E = {ρ < ‖w - c‖, re ((w - c) / b) < 0 ∨ im ((w - c) / b) ∉ [0, π]}` of the exterior of a
half-strip, a nonzero real boundary value `w = q + g⁻¹` far from `c` lies on one of the two
bounding rays: `ζ = (w - c) / b` has `0 ≤ re ζ` and `im ζ ∈ {0, π}`.  Indeed `w` is a limit of
values of `f` in `E` but not itself a value of `f`, so `ζ` lies on the frontier of the closed
half-strip, and far out that frontier consists of the two rays. -/
private theorem re_nonneg_and_im_eq_zero_or_eq_pi_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x r ρ : ℝ} {c b : ℂ} (hb : b ≠ 0)
    (hS : {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆
      f '' upperHalfPlaneSet)
    (hfS : ∀ z ∈ ball (x : ℂ) r ∩ upperHalfPlaneSet, f z ∈
      {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)})
    {z : ℂ} (hz : z ∈ ball (x : ℂ) r) (hz0 : z.im = 0) (hgz : g z ≠ 0)
    (hρ : ρ < ‖q + (g z)⁻¹ - c‖) (hπ : Real.pi * ‖b‖ < ‖q + (g z)⁻¹ - c‖) :
    0 ≤ ((q + (g z)⁻¹ - c) / b).re ∧
      (((q + (g z)⁻¹ - c) / b).im = 0 ∨ ((q + (g z)⁻¹ - c) / b).im = Real.pi) := by
  set E := {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)}
  set w := q + (g z)⁻¹
  -- `w` is the limit of values of `f` in `E`
  have hwcl : w ∈ closure E := by
    have hzcl : z ∈ closure (ball (x : ℂ) r ∩ upperHalfPlaneSet) :=
      isOpen_ball.inter_closure ⟨hz, by simp [upperHalfPlaneSet, ← hz0]⟩
    have hFc : ContinuousWithinAt (fun y => q + (g y)⁻¹)
        (ball (x : ℂ) r ∩ upperHalfPlaneSet) z :=
      (continuousWithinAt_const.add ((hgc z hz0.ge).inv₀ hgz)).mono
        fun y (hy : y ∈ ball (x : ℂ) r ∩ upperHalfPlaneSet) => mem_ofPred.mpr (le_of_lt hy.2)
    refine closure_mono ?_ (hFc.mem_closure_image hzcl)
    rintro _ ⟨y, hy, rfl⟩
    simpa only [eq_add_inv_of_inverted_coordinate hgf hy.2] using hfS y hy
  -- but not a value of `f` at an interior point, since `g` is injective off its zeros
  have hwE : w ∉ E := fun hw =>
    add_inv_notMem_image_of_inverted_coordinate hgf hgi hz0 hgz (hS hw)
  have hζ : Continuous fun y : ℂ => (y - c) / b := by fun_prop
  have hC : IsClosed {y : ℂ | ((y - c) / b).re ≤ 0 ∨ ((y - c) / b).im ≤ 0 ∨
      Real.pi ≤ ((y - c) / b).im} :=
    (isClosed_le (continuous_re.comp hζ) continuous_const).union
      ((isClosed_le (continuous_im.comp hζ) continuous_const).union
        (isClosed_le continuous_const (continuous_im.comp hζ)))
  have hcl := closure_minimal (fun y (hy : y ∈ E) => by
    rcases hy.2 with h | h
    · exact Or.inl h.le
    · rw [mem_Icc, not_and_or, not_le, not_le] at h
      exact Or.inr (h.imp le_of_lt le_of_lt)) hC hwcl
  have hnot : 0 ≤ ((w - c) / b).re ∧ ((w - c) / b).im ∈ Icc 0 Real.pi := by
    by_contra h
    rw [not_and_or, not_le] at h
    exact hwE ⟨hρ, h⟩
  rcases hcl with h | h | h
  · -- the short side `re ζ = 0` is within distance `π * ‖b‖` of `c`
    have hnorm := norm_le_abs_re_add_pi_of_im_mem_Icc hnot.2
    rw [le_antisymm h hnot.1, abs_zero, zero_add, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr hb)] at hnorm
    exact absurd hπ hnorm.not_gt
  · exact ⟨hnot.1, Or.inl (le_antisymm h hnot.2.1)⟩
  · exact ⟨hnot.1, Or.inr (le_antisymm hnot.2.2 h)⟩

/-- Two real zeros of the inverted coordinate cannot both lie in a disc on whose diameter the
nonzero boundary values lie on the two bounding rays of a half-strip: between the two zeros there
is a maximal zero-free interval, which would be mapped injectively into the rays with both ends
going to infinity. -/
private theorem false_of_inverted_coordinate_eq_zero_of_rays
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    {x r : ℝ} {c b : ℂ} (hb : b ≠ 0)
    (hray : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → g z ≠ 0 → 0 ≤ ((q + (g z)⁻¹ - c) / b).re ∧
      (((q + (g z)⁻¹ - c) / b).im = 0 ∨ ((q + (g z)⁻¹ - c) / b).im = Real.pi))
    {u v : ℝ} (huv : u < v) (hu : (u : ℂ) ∈ ball (x : ℂ) r) (hv : (v : ℂ) ∈ ball (x : ℂ) r)
    (hgu : g u = 0) (hgv : g v = 0) : False := by
  have hgR : Continuous fun s : ℝ => g s :=
    hgc.comp_continuous continuous_ofReal fun s => by simp
  have hZ : IsClosed {s : ℝ | g s = 0} := isClosed_eq hgR continuous_const
  obtain ⟨t, ht, hgt⟩ : ∃ t ∈ Ioo u v, g t ≠ 0 := by
    have h := exists_mem_Ioo_ne_zero_of_ne_zero (f := g) (x := (u + v) / 2) (r := (v - u) / 2)
      (by linarith) (hgc.mono inter_subset_right) (hgd.mono inter_subset_right)
      fun z _ hzH => hgne z hzH
    rwa [show (u + v) / 2 - (v - u) / 2 = u by ring, show (u + v) / 2 + (v - u) / 2 = v by ring]
      at h
  -- the zeros of `g` nearest to `t` on either side
  set A := Icc u t ∩ {s : ℝ | g s = 0}
  set B := Icc t v ∩ {s : ℝ | g s = 0}
  have hAt : BddAbove A := ⟨t, fun s (hs : s ∈ A) => hs.1.2⟩
  have hBt : BddBelow B := ⟨t, fun s (hs : s ∈ B) => hs.1.1⟩
  have hA : sSup A ∈ A := (isClosed_Icc.inter hZ).csSup_mem ⟨u, ⟨le_rfl, ht.1.le⟩, hgu⟩ hAt
  have hB : sInf B ∈ B := (isClosed_Icc.inter hZ).csInf_mem ⟨v, ⟨ht.2.le, le_rfl⟩, hgv⟩ hBt
  set a := sSup A
  set a' := sInf B
  have hat : a < t := hA.1.2.lt_of_ne fun h => hgt (h ▸ hA.2)
  have hta : t < a' := hB.1.1.lt_of_ne fun h => hgt (h.symm ▸ hB.2)
  have hgap (s : ℝ) (hs : s ∈ Ioo a a') : g s ≠ 0 := fun h => by
    rcases le_total s t with hst | hst
    · exact (le_csSup hAt ⟨⟨hA.1.1.trans hs.1.le, hst⟩, h⟩).not_gt hs.1
    · exact (csInf_le hBt ⟨⟨hst, hs.2.le.trans hB.1.2⟩, h⟩).not_gt hs.2
  have hball (s : ℝ) (hs : s ∈ Ioo a a') : (s : ℂ) ∈ ball (x : ℂ) r := by
    rw [mem_ball, isometry_ofReal.dist_eq, Real.dist_eq, abs_lt] at hu hv ⊢
    constructor <;> linarith [hA.1.1, hB.1.2, hs.1, hs.2]
  -- the normalized coordinate on the zero-free interval runs along the rays to infinity at both
  -- ends, which is impossible
  have hlim (l : Filter ℝ) (hl : Tendsto (fun s : ℝ => g s) l (𝓝[≠] 0)) :
      Tendsto (fun s : ℝ => ‖(q + (g s)⁻¹ - c) / b‖) l atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_div_of_tendsto_nhdsNE_zero hb hl)
  refine false_of_injOn_rays_of_tendsto (φ := fun s : ℝ => (q + (g s)⁻¹ - c) / b)
    (hat.trans hta) ?_ ?_ (fun s hs => hray s (hball s hs) (by simp) (hgap s hs)) (hlim _ ?_)
    (hlim _ ?_)
  · exact ((continuousOn_const.add (hgR.continuousOn.inv₀ hgap)).sub continuousOn_const).div_const b
  · intro s hs s' hs' h
    simp only [div_left_inj' hb, sub_left_inj, add_right_inj, inv_inj] at h
    exact ofReal_injective (hgi ⟨by simp, hgap s hs⟩ ⟨by simp, hgap s' hs'⟩ h)
  · refine tendsto_nhdsWithin_iff.mpr ⟨hA.2 ▸ hgR.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (hat.trans hta)] with s hs using hgap s hs
  · refine tendsto_nhdsWithin_iff.mpr ⟨hB.2 ▸ hgR.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (hat.trans hta)] with s hs using hgap s hs

/-- Near a zero `x` of the inverted coordinate whose end is the far part `E` of the exterior of a
half-strip, `f` maps an upper half-disc about `x` into `E`, and `x` is the only zero of `g` on that
half-disc. -/
private theorem exists_ball_eq_of_inverted_coordinate_eq_zero
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x : ℝ} (hx : g x = 0)
    {ρ : ℝ} {c b : ℂ} (hb : b ≠ 0)
    (hS : {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆
      f '' upperHalfPlaneSet)
    (hfS : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ), f z ∈
      {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)}) :
    ∃ r > 0, (∀ z ∈ ball (x : ℂ) r ∩ upperHalfPlaneSet, f z ∈
      {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)}) ∧
      ∀ z ∈ ball (x : ℂ) r, 0 ≤ z.im → g z = 0 → z = x := by
  obtain ⟨r₁, hr₁, hS₁⟩ := Metric.mem_nhdsWithin_iff.mp hfS
  obtain ⟨r₂, hr₂, hfar⟩ :=
    exists_ball_lt_norm_of_inverted_coordinate (q := q) hgc hx c (max ρ (Real.pi * ‖b‖))
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have h₁ : ball (x : ℂ) (min r₁ r₂) ⊆ ball (x : ℂ) r₁ := ball_subset_ball (min_le_left _ _)
  have hfS' (z : ℂ) (hz : z ∈ ball (x : ℂ) (min r₁ r₂) ∩ upperHalfPlaneSet) := hS₁ ⟨h₁ hz.1, hz.2⟩
  -- the nonzero real boundary values lie on the two bounding rays
  have hray (z : ℂ) (hz : z ∈ ball (x : ℂ) (min r₁ r₂)) (hz0 : z.im = 0) (hgz : g z ≠ 0) :=
    have hzfar := hfar z (ball_subset_ball (min_le_right _ _) hz) hz0.ge hgz
    re_nonneg_and_im_eq_zero_or_eq_pi_of_inverted_coordinate hgc hgf hgi hb hS hfS' hz hz0 hgz
      ((le_max_left _ _).trans_lt hzfar) ((le_max_right _ _).trans_lt hzfar)
  -- so a second real zero is impossible, and in the open upper half-plane `g` has no zeros
  refine ⟨min r₁ r₂, hr, hfS', fun z hz hzH hgz => ?_⟩
  have hz0 : z.im = 0 := (hzH.eq_or_lt.resolve_right fun h => hgne z h hgz).symm
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
  rw [hz'] at hz hgz ⊢
  rcases lt_trichotomy z.re x with h | h | h
  · exact (false_of_inverted_coordinate_eq_zero_of_rays hgc hgd hgne hgi hb hray h hz
      (mem_ball_self hr) hgz hx).elim
  · rw [h]
  · exact (false_of_inverted_coordinate_eq_zero_of_rays hgc hgd hgne hgi hb hray h
      (mem_ball_self hr) hz hx hgz).elim

/-- Far from `c`, the end `E` lies in the image under `F = q + g⁻¹` of an upper half-disc
`A` about `x`, provided `f` maps `A` into `E` and `F` is bounded on the bounding semicircle.
Indeed far out `E` lies in a preconnected subset of `E` avoiding the image of the semicircle,
which meets `F '' A`, lies in the image of the upper half-plane, and is therefore not separated by
the semicircle from `F '' A`. -/
private theorem exists_lt_norm_mem_image_ball_of_halfStripExterior
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x : ℝ} (hx : g x = 0)
    {r ρ M : ℝ} {c b : ℂ} (hb : b ≠ 0) (hr : 0 < r)
    (hS : {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆
      f '' upperHalfPlaneSet)
    (hfS : ∀ z ∈ ball (x : ℂ) r ∩ upperHalfPlaneSet, f z ∈
      {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)})
    (hM : ∀ z ∈ sphere (x : ℂ) r ∩ upperHalfPlaneSet, ‖q + (g z)⁻¹ - c‖ ≤ M) :
    ∃ R : ℝ, ∀ w : ℂ, R < ‖w - c‖ →
      (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi) →
      w ∈ (fun z => q + (g z)⁻¹) '' (ball (x : ℂ) r ∩ upperHalfPlaneSet) := by
  set F : ℂ → ℂ := fun z => q + (g z)⁻¹
  set A := ball (x : ℂ) r ∩ upperHalfPlaneSet
  set B := upperHalfPlaneSet \ closedBall (x : ℂ) r
  have hFd : DifferentiableOn ℂ F upperHalfPlaneSet :=
    (differentiableOn_const q).add (hgd.inv hgne)
  have hFi : InjOn F upperHalfPlaneSet := ((add_right_injective q).comp inv_injective).comp_injOn
    (hgi.mono fun z (hz : 0 < z.im) => by exact ⟨hz.le, hgne z hz⟩)
  have hAo : IsOpen (F '' A) := isOpen_image_of_differentiableOn_of_injOn
    (isOpen_ball.inter isOpen_upperHalfPlaneSet) (hFd.mono inter_subset_right)
    (hFi.mono inter_subset_right)
  have hBo : IsOpen (F '' B) := isOpen_image_of_differentiableOn_of_injOn
    (isOpen_upperHalfPlaneSet.sdiff isClosed_closedBall) (hFd.mono sdiff_subset)
    (hFi.mono sdiff_subset)
  have hAB : Disjoint (F '' A) (F '' B) := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨y, hy, hyz⟩
    exact hy.2 (hFi hy.1 hz.2 hyz ▸ ball_subset_closedBall hz.1)
  -- far out, `E` lies in a preconnected subset `C` of `E` avoiding the image of the semicircle
  obtain ⟨C, hCE, hCc, hCM, hEC⟩ := isPreconnectedAtInfinityIn_iff.1
    (isPreconnectedAtInfinityIn_halfStripExterior ρ (c := c) hb) (closedBall c M)
    isBounded_closedBall
  have hsub : C ⊆ F '' A ∪ F '' B := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := hS (hCE hw)
    rw [eq_add_inv_of_inverted_coordinate hgf hz] at hzw
    rcases lt_trichotomy (dist z x) r with h | h | h
    · exact Or.inl ⟨z, ⟨h, hz⟩, hzw⟩
    · refine absurd (hM z ⟨h, hz⟩) fun hzM => disjoint_left.mp hCM hw ?_
      rwa [mem_closedBall, dist_eq_norm, ← hzw]
    · exact Or.inr ⟨z, ⟨hz, not_le.mpr h⟩, hzw⟩
  -- points of the half-disc near `x` are mapped far into the end, hence into `C`
  have hmeet : (C ∩ F '' A).Nonempty := by
    have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
    obtain ⟨z, hzr, hzC, hzH⟩ := ((eventually_mem_set.mpr
      (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (x : ℂ) hr))).and
        (((tendsto_cobounded_of_inverted_boundary_eq_zero (hgc _ (by simp)) hgf hgne
          hx).eventually hEC).and self_mem_nhdsWithin)).exists
    exact ⟨f z, hzC (hfS z ⟨hzr, hzH⟩), z, ⟨hzr, hzH⟩,
      (eq_add_inv_of_inverted_coordinate hgf hzH).symm⟩
  have hCA := hCc.subset_left_of_subset_union hAo hBo hAB hsub hmeet
  obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall c).eventually_iff.mp hEC
  refine ⟨max ρ R, fun w hw hX => hCA (hR ?_ ⟨(le_max_left _ _).trans_lt hw, hX⟩)⟩
  rw [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
  exact (le_max_right _ _).trans_lt hw

/-- **The end condition at a half-strip-exterior end.**  Let `g = (f - q)⁻¹` be the inverted
coordinate of a map `f` of the upper half-plane: `g` is continuous on the closed upper
half-plane, holomorphic and nonzero in its interior, and injective away from its zeros.  Let `x`
be a real zero of `g`, and suppose that `f` maps the points of the upper half-plane near `x` into
the far part `E = {ρ < ‖w - c‖, re ((w - c) / b) < 0 ∨ im ((w - c) / b) ∉ [0, π]}` of the
exterior of a closed half-strip, and that `E` lies in the image of `f`.  Then on a closed upper
half-disc about `x` with `x` removed, the recovered map `F = q + g⁻¹` is continuous and
injective, it tends to infinity at `x`, and far from `c` the image under `F` of the open upper
half-disc is exactly the exterior of the closed half-strip
`{0 ≤ re ((w - c) / b), 0 ≤ im ((w - c) / b) ≤ π}`.

These are the local conditions of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` for `F` at a
vertex at infinity of opening `2 * π`, with turning exponent `-3`. -/
theorem exists_ball_halfStripExterior_end_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x : ℝ} (hx : g x = 0)
    {ρ : ℝ} {c b : ℂ} (hb : b ≠ 0)
    (hS : {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆
      f '' upperHalfPlaneSet)
    (hfS : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ), f z ∈
      {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)}) :
    ∃ r > 0, ∃ ρ' : ℝ,
      ContinuousOn (fun z => q + (g z)⁻¹)
        ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}) ∧
      InjOn (fun z => q + (g z)⁻¹) ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}) ∧
      Tendsto (fun z => q + (g z)⁻¹) (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ))
        (cobounded ℂ) ∧
      ∀ w : ℂ, ρ' < ‖w - c‖ →
        (w ∈ (fun z => q + (g z)⁻¹) '' (ball (x : ℂ) r ∩ upperHalfPlaneSet) ↔
          ((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi) := by
  obtain ⟨r₀, hr₀, hfS', hzero⟩ :=
    exists_ball_eq_of_inverted_coordinate_eq_zero hgc hgd hgf hgne hgi hx hb hS hfS
  -- work on the closed half-disc of half the radius, on which `x` is the only zero of `g`
  set r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hrr₀ : closedBall (x : ℂ) r ⊆ ball (x : ℂ) r₀ := closedBall_subset_ball (half_lt_self hr₀)
  set P := (closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}
  have hgP (z : ℂ) (hz : z ∈ P) : g z ≠ 0 := fun h => hz.2 (hzero z (hrr₀ hz.1.1) hz.1.2 h)
  have hFc : ContinuousOn (fun z => q + (g z)⁻¹) P :=
    continuousOn_const.add ((hgc.mono fun z (hz : z ∈ P) => hz.1.2).inv₀ hgP)
  have hFt : Tendsto (fun z => q + (g z)⁻¹) (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ))
      (cobounded ℂ) := by
    refine (tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp ?_)
    refine tendsto_nhdsWithin_iff.mpr ⟨hx ▸ ((hgc _ (by simp)).mono sdiff_subset).tendsto, ?_⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hr₀), self_mem_nhdsWithin]
      with z hz hz' using fun h => hz'.2 (hzero z hz hz'.1 h)
  -- `F` is bounded on the closed semicircle of radius `r` about `x`
  obtain ⟨M, hM⟩ := ((isCompact_sphere (x : ℂ) r).inter_right
    (isClosed_le continuous_const continuous_im)).exists_bound_of_continuousOn
      ((hFc.mono fun z (hz : z ∈ sphere (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) =>
        ⟨⟨sphere_subset_closedBall hz.1, hz.2⟩, fun h => hr.ne' (by
          rw [← mem_sphere.mp hz.1, mem_singleton_iff.mp h, dist_self])⟩).sub continuousOn_const)
  have hfS'' (z : ℂ) (hz : z ∈ ball (x : ℂ) r ∩ upperHalfPlaneSet) :=
    hfS' z ⟨(ball_subset_closedBall.trans hrr₀) hz.1, hz.2⟩
  obtain ⟨R, hR⟩ := exists_lt_norm_mem_image_ball_of_halfStripExterior hgc hgd hgf hgne hgi hx hb
    hr hS hfS'' fun z hz => hM z ⟨hz.1, le_of_lt hz.2⟩
  refine ⟨r, hr, R, hFc, ((add_right_injective q).comp inv_injective).comp_injOn
    (hgi.mono fun z hz => by exact ⟨hz.1.2, hgP z hz⟩), hFt, fun w hw => ⟨?_, hR w hw⟩⟩
  rintro ⟨z, hz, rfl⟩
  simpa only [eq_add_inv_of_inverted_coordinate hgf hz.2] using (hfS'' z hz).2

end TauCeti
