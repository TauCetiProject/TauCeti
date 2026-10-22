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
import TauCeti.Analysis.Complex.Conformal.LocalFrontier
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Ends at infinity of an inverted coordinate

Let `f` be a conformal map of the upper half-plane onto an unbounded domain with several accesses
to infinity, and let `g = (f - q)⁻¹` be its inverted coordinate, continuous on the closed upper
half-plane.  The real zeros of `g` are the boundary parameters at which `f` tends to infinity.

This file describes the boundary behaviour of `f` at such a zero `x`.  First, if far out the domain
is covered by pairwise disjoint open ends, then `f` maps a whole upper half-disc about `x` into a
single one of them.  Second, if that end is an open half-strip contained in the domain, between
two parallel sides, then the exponential coordinate `exp ((f - c) / b)` of the half-strip, for
suitable constants `c` and `b`, extends continuously and injectively across `x` with value `0`
there, has real boundary values, and carries the upper half-disc into the upper half-plane.  These
are the local conditions at a vertex at infinity of opening `0` in the Schwarz--Christoffel formula
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary`, so they apply to
polygonal domains, such as strips, with several parallel-sided ends.

## Main results

* `TauCeti.exists_eventually_mem_of_inverted_coordinate_eq_zero`: near a zero of the inverted
  coordinate, `f` takes values in a single end.
* `TauCeti.exists_ball_halfStrip_end_of_inverted_coordinate`: at a zero of the inverted coordinate
  whose end is a half-strip, the exponential coordinate of that half-strip satisfies the local
  conditions at a parallel-sided vertex at infinity.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {f g : ℂ → ℂ} {q : ℂ}

/-- **Each access to infinity lies in one end.**  Let `g = (f - q)⁻¹` be the inverted coordinate
of a map `f` of the upper half-plane into `U`, continuous on the closed upper half-plane and
nonzero in its interior, and let `x` be a real zero of `g`.  If far out `U` is covered by pairwise
disjoint open sets `E i`, then near `x` the map `f` takes its values in the upper half-plane in a
single one of them. -/
theorem exists_eventually_mem_of_inverted_coordinate_eq_zero {ι : Type*} {U : Set ℂ}
    {E : ι → Set ℂ} {x R : ℝ} (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hx : g x = 0) (hfU : MapsTo f upperHalfPlaneSet U)
    (hEo : ∀ i, IsOpen (E i)) (hEd : Pairwise (Disjoint on E))
    (hE : ∀ w ∈ U, R < ‖w‖ → ∃ i, w ∈ E i) :
    ∃ i, ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ), f z ∈ E i := by
  -- near `x` the map is far out, on a preconnected upper half-disc
  have hf : Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (cobounded ℂ) :=
    tendsto_cobounded_of_inverted_boundary_eq_zero (hgc _ (by simp)) hgf hgne hx
  obtain ⟨r, hr, hfar⟩ := Metric.mem_nhdsWithin_iff.mp
    ((tendsto_norm_cobounded_atTop.comp hf).eventually_gt_atTop R)
  set A := ball (x : ℂ) r ∩ upperHalfPlaneSet
  have hfc : ContinuousOn f upperHalfPlaneSet :=
    (continuousOn_const.add ((hgc.mono (ofPred_subset_ofPred.mpr fun _ => le_of_lt)).inv₀
      hgne)).congr fun z hz => eq_add_inv_of_inverted_coordinate hgf hz
  have hA : IsPreconnected (f '' A) :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected.image _
      (hfc.mono inter_subset_right)
  have hcover (z : ℂ) (hz : z ∈ A) : ∃ i, f z ∈ E i :=
    hE _ (hfU hz.2) (hfar hz)
  have hz₀ : (x : ℂ) + (r / 2 : ℝ) * Complex.I ∈ A :=
    ⟨by simp [dist_eq_norm, abs_of_pos hr, hr], by simp [hr]⟩
  obtain ⟨i, hi⟩ := hcover _ hz₀
  -- the other ends form an open set disjoint from `E i`
  have hsub : f '' A ⊆ E i := by
    refine hA.subset_left_of_subset_union (v := ⋃ j ∈ ({i}ᶜ : Set ι), E j) (hEo i)
      (isOpen_biUnion fun j _ => hEo j)
      (disjoint_iUnion₂_right.mpr fun j (hj : j ≠ i) => hEd hj.symm) ?_
      ⟨f _, mem_image_of_mem f hz₀, hi⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨j, hj⟩ := hcover z hz
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_biUnion (x := j) hji hj)
  exact ⟨i, Metric.mem_nhdsWithin_iff.mpr ⟨r, hr, fun z hz => hsub (mem_image_of_mem f hz)⟩⟩

/-- Near a zero of the inverted coordinate whose end is the half-strip
`{ρ < re ζ, 0 < im ζ < π}`, `ζ = (w - c) / b`, the normalized coordinate
`ζ = (q + g⁻¹ - c) / b` lies in the closed half-strip `{0 ≤ re ζ, 0 ≤ im ζ ≤ π}` wherever `g` is
nonzero: in the open half-strip on the upper half-plane, and on its two bounding rays
`im ζ ∈ {0, π}` at real points. -/
private theorem exists_ball_halfStrip_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x : ℝ} (hx : g x = 0)
    {ρ : ℝ} {c b : ℂ} (hb : b ≠ 0)
    (hS : {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} ⊆
      f '' upperHalfPlaneSet)
    (hfS : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ),
      f z ∈ {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi}) :
    ∃ r > 0, ∀ z ∈ ball (x : ℂ) r, 0 ≤ z.im → g z ≠ 0 →
      0 ≤ ((q + (g z)⁻¹ - c) / b).re ∧ ((q + (g z)⁻¹ - c) / b).im ∈ Icc 0 Real.pi ∧
      (0 < z.im → ((q + (g z)⁻¹ - c) / b).im ∈ Ioo 0 Real.pi) ∧
      (z.im = 0 → ((q + (g z)⁻¹ - c) / b).im = 0 ∨ ((q + (g z)⁻¹ - c) / b).im = Real.pi) := by
  set φ : ℂ → ℂ := fun z => (q + (g z)⁻¹ - c) / b
  obtain ⟨r₁, hr₁, hS₁⟩ := Metric.mem_nhdsWithin_iff.mp hfS
  have hφS {z : ℂ} (hz : z ∈ ball (x : ℂ) r₁) (hzH : 0 < z.im) :
      ρ < (φ z).re ∧ (φ z).im ∈ Ioo 0 Real.pi := by
    simpa [φ, eq_add_inv_of_inverted_coordinate hgf hzH] using hS₁ ⟨hz, hzH⟩
  -- near `x` the coordinate `φ` is far out wherever `g` does not vanish
  have hg : Tendsto g (𝓝[{z : ℂ | 0 ≤ z.im} ∩ {z | g z ≠ 0}] (x : ℂ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx ▸ ((hgc _ (by simp)).mono inter_subset_left).tendsto,
      eventually_nhdsWithin_of_forall fun z hz => hz.2⟩
  obtain ⟨r₂, hr₂, hfar⟩ := Metric.mem_nhdsWithin_iff.mp ((tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_div_of_tendsto_nhdsNE_zero (q := q) (c := c) hb hg)).eventually_gt_atTop
      (|ρ| + Real.pi))
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz hzH hgz => ?_⟩
  have hz₁ : z ∈ ball (x : ℂ) r₁ := ball_subset_ball (min_le_left _ _) hz
  have hzfar : |ρ| + Real.pi < ‖φ z‖ := hfar ⟨ball_subset_ball (min_le_right _ _) hz, hzH, hgz⟩
  obtain ⟨hre, him⟩ : ρ ≤ (φ z).re ∧ (φ z).im ∈ Icc 0 Real.pi := by
    rcases hzH.lt_or_eq with hzH | hzH
    · exact ⟨(hφS hz₁ hzH).1.le, Ioo_subset_Icc_self (hφS hz₁ hzH).2⟩
    -- a real point lies in the closure of the half-strip
    have hT : IsClosed {ζ : ℂ | ρ ≤ ζ.re ∧ ζ.im ∈ Icc 0 Real.pi} :=
      (isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    have hφc : ContinuousWithinAt φ (ball (x : ℂ) r₁ ∩ upperHalfPlaneSet) z :=
      (ContinuousWithinAt.div_const ((continuousWithinAt_const.add
        ((hgc z hzH.le).inv₀ hgz)).sub continuousWithinAt_const) b).mono fun w hw =>
        mem_ofPred.mpr (le_of_lt hw.2)
    have hzcl : z ∈ closure (ball (x : ℂ) r₁ ∩ upperHalfPlaneSet) :=
      isOpen_ball.inter_closure ⟨hz₁, by simp [upperHalfPlaneSet, ← hzH]⟩
    have : (𝓝[ball (x : ℂ) r₁ ∩ upperHalfPlaneSet] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hzcl
    exact hT.mem_of_tendsto hφc.tendsto (eventually_nhdsWithin_of_forall fun w hw =>
      ⟨(hφS hw.1 hw.2).1.le, Ioo_subset_Icc_self (hφS hw.1 hw.2).2⟩)
  -- far out in the closed half-strip the real part exceeds `|ρ|`
  have hlt : |ρ| < (φ z).re := by
    rcases lt_abs.mp ((add_lt_add_iff_right Real.pi).mp
        (hzfar.trans_le (norm_le_abs_re_add_pi_of_im_mem_Icc him))) with h | h
    · exact h
    · linarith [neg_abs_le ρ]
  refine ⟨(abs_nonneg ρ).trans hlt.le, him, fun hzH => (hφS hz₁ hzH).2, fun hzH => ?_⟩
  -- a real point is not in the half-strip itself
  by_contra hne
  rw [not_or] at hne
  -- otherwise the boundary value would be a value of `f` at an interior point
  exact add_inv_notMem_image_of_inverted_coordinate hgf hgi hzH hgz
    (hS ⟨(le_abs_self ρ).trans_lt hlt, him.1.lt_of_ne (Ne.symm hne.1), him.2.lt_of_ne hne.2⟩)

/-- The exponential coordinate `exp (π * I - ζ)` of the normalized half-strip coordinate
`ζ = (q + g⁻¹ - c) / b`, filled in with `0` at the zeros of `g`, is continuous wherever `ζ` stays
in the closed half-strip `{0 ≤ re ζ, 0 ≤ im ζ ≤ π}` off the zeros of `g`. -/
private theorem continuousOn_exp_halfStrip_of_inverted_coordinate [∀ z, Decidable (g z = 0)]
    {c b : ℂ} (hb : b ≠ 0) {B : Set ℂ} (hgc : ContinuousOn g B)
    (hB : ∀ z ∈ B, g z ≠ 0 → 0 ≤ ((q + (g z)⁻¹ - c) / b).re ∧
      ((q + (g z)⁻¹ - c) / b).im ∈ Icc 0 Real.pi) :
    ContinuousOn
      (fun z => if g z = 0 then 0 else exp (Real.pi * Complex.I - (q + (g z)⁻¹ - c) / b)) B := by
  intro z hz
  by_cases hgz : g z = 0
  · -- at a zero of `g` the coordinate tends to `0`, since `ζ` tends to infinity in the half-strip
    simp only [ContinuousWithinAt, hgz, ite_true]
    refine Tendsto.if tendsto_const_nhds ?_
    rw [← nhdsWithin_inter']
    have hg : Tendsto g (𝓝[B ∩ {z | ¬g z = 0}] z) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hgz ▸ ((hgc z hz).mono inter_subset_left).tendsto,
        eventually_nhdsWithin_of_forall fun w hw => hw.2⟩
    exact tendsto_exp_pi_mul_I_sub_of_tendsto_cobounded
      (tendsto_cobounded_div_of_tendsto_nhdsNE_zero hb hg)
      (eventually_nhdsWithin_of_forall fun w hw => hB w hw.1 hw.2)
  · -- away from the zeros of `g` the coordinate is a composition of continuous maps
    refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun z =>
      exp (Real.pi * Complex.I - (q + (g z)⁻¹ - c) / b)) ?_ ?_ (ite_eq_right hgz)
    · exact (continuousWithinAt_const.sub (ContinuousWithinAt.div_const
        ((continuousWithinAt_const.add ((hgc z hz).inv₀ hgz)).sub continuousWithinAt_const)
          b)).cexp
    · filter_upwards [(hgc z hz).eventually_ne hgz] with w hw using ite_eq_right hw

/-- The exponential coordinate `exp (π * I - ζ)` of the normalized half-strip coordinate
`ζ = (q + g⁻¹ - c) / b`, filled in with `0` at the zeros of `g`, is injective wherever `ζ` stays in
the closed strip `0 ≤ im ζ ≤ π` off the zeros of `g`, provided `g` is injective off its zeros and
has at most one zero there. -/
private theorem injOn_exp_halfStrip_of_inverted_coordinate [∀ z, Decidable (g z = 0)]
    {c b : ℂ} (hb : b ≠ 0) {B : Set ℂ} (hgi : InjOn g (B ∩ {z | g z ≠ 0}))
    (hzero : (B ∩ {z | g z = 0}).Subsingleton)
    (hB : ∀ z ∈ B, g z ≠ 0 → ((q + (g z)⁻¹ - c) / b).im ∈ Icc 0 Real.pi) :
    InjOn
      (fun z => if g z = 0 then 0 else exp (Real.pi * Complex.I - (q + (g z)⁻¹ - c) / b)) B := by
  intro z hz w hw hzw
  by_cases hgz : g z = 0 <;> by_cases hgw : g w = 0 <;>
    simp only [hgz, hgw, ite_true, ite_false] at hzw
  · exact hzero ⟨hz, hgz⟩ ⟨hw, hgw⟩
  · exact absurd hzw.symm (exp_ne_zero _)
  · exact absurd hzw (exp_ne_zero _)
  · have hφ := injOn_exp_pi_mul_I_sub (hB z hz hgz) (hB w hw hgw) hzw
    simp only [div_left_inj' hb, sub_left_inj, add_right_inj, inv_inj] at hφ
    exact hgi ⟨hz, hgz⟩ ⟨hw, hgw⟩ hφ

/-- **The exponential coordinate at a parallel-sided end.**  Let `g = (f - q)⁻¹` be the inverted
coordinate of a holomorphic map `f` of the upper half-plane: `g` is continuous on the closed upper
half-plane, holomorphic and nonzero in its interior, and injective away from its zeros.  Let `x` be
a real zero of `g`, and suppose that near `x` the map `f` takes its values in the upper half-plane
in the open half-strip `S = {ρ < re ((w - c) / b), 0 < im ((w - c) / b) < π}`, which lies in the
image of `f`.  Then, for suitable constants `c'` and `b' ≠ 0`, the exponential coordinate
`exp ((f - c') / b')` of the half-strip extends to a function `G` on a closed upper half-disc about
`x` which is continuous and injective, vanishes at `x`, is real on the diameter and maps the open
upper half-disc into the upper half-plane.

These are the local conditions of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` at a vertex at
infinity between two parallel sides. -/
theorem exists_ball_halfStrip_end_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x : ℝ} (hx : g x = 0)
    {ρ : ℝ} {c b : ℂ} (hb : b ≠ 0)
    (hS : {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} ⊆
      f '' upperHalfPlaneSet)
    (hfS : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ),
      f z ∈ {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi}) :
    ∃ r > 0, ∃ c' b' : ℂ, b' ≠ 0 ∧ ∃ G : ℂ → ℂ,
      EqOn G (fun z => exp ((f z - c') / b')) (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      G (x : ℂ) = 0 ∧
      ContinuousOn G (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (x : ℂ) r, z.im = 0 → (G z).im = 0) ∧
      MapsTo G (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} ∧
      InjOn G (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) := by
  classical
  obtain ⟨r, hr, hstrip⟩ := exists_ball_halfStrip_of_inverted_coordinate hgc hgf hgi hx hb hS hfS
  set φ : ℂ → ℂ := fun z => (q + (g z)⁻¹ - c) / b
  set G : ℂ → ℂ := fun z => if g z = 0 then 0 else exp (Real.pi * Complex.I - φ z)
  have hGne {z : ℂ} (hgz : g z ≠ 0) : G z = exp (Real.pi * Complex.I - φ z) := ite_eq_right hgz
  have hGim {z : ℂ} (hgz : g z ≠ 0) :
      (G z).im = Real.exp (-(φ z).re) * Real.sin (φ z).im := by
    rw [hGne hgz, im_exp_pi_mul_I_sub]
  have hGc : ContinuousOn G (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) :=
    continuousOn_exp_halfStrip_of_inverted_coordinate hb (hgc.mono inter_subset_right)
      fun z hz hgz => ⟨(hstrip z hz.1 hz.2 hgz).1, (hstrip z hz.1 hz.2 hgz).2.1⟩
  have hGR (z : ℂ) (hz : z ∈ ball (x : ℂ) r) (hz0 : z.im = 0) : (G z).im = 0 := by
    by_cases hgz : g z = 0
    · simp [G, hgz]
    · rw [hGim hgz]
      rcases (hstrip z hz hz0.ge hgz).2.2.2 hz0 with h | h <;> simp [φ, h]
  have hGH (z : ℂ) (hz : z ∈ ball (x : ℂ) r) (hzH : 0 < z.im) : 0 < (G z).im := by
    have hH := (hstrip z hz hzH.le (hgne z hzH)).2.2.1 hzH
    rw [hGim (hgne z hzH)]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hH.1 hH.2)
  -- reflection across the diameter shows that `x` is an isolated zero of `G`
  have hGd : DifferentiableOn ℂ G (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) := by
    refine DifferentiableOn.congr (f := fun z => exp (Real.pi * Complex.I - φ z)) ?_
      fun z hz => hGne (hgne z hz.2)
    refine ((differentiableOn_const _).sub (DifferentiableOn.div_const ?_ b)).cexp
    exact ((differentiableOn_const q).add ((hgd.mono inter_subset_right).inv
      fun z hz => hgne z hz.2)).sub_const c
  obtain ⟨r', hr', hiso⟩ := Metric.mem_nhdsWithin_iff.mp <| eventually_ne_zero_of_real_on_axis hr
    hGc hGd hGR fun z hz hzH h => (hGH z hz hzH).ne' (by rw [h, zero_im])
  have hball : ball (x : ℂ) (min r r') ⊆ ball (x : ℂ) r := ball_subset_ball (min_le_left _ _)
  have hzero {z : ℂ} (hz : z ∈ ball (x : ℂ) (min r r') ∩ {z : ℂ | 0 ≤ z.im}) (hgz : g z = 0) :
      z = x := by
    by_contra hzx
    exact hiso ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2, hzx⟩ (ite_eq_left hgz)
  refine ⟨min r r', lt_min hr hr', c + Real.pi * Complex.I * b, -b, neg_ne_zero.mpr hb, G,
    fun z hz => ?_, ite_eq_left hx, hGc.mono (inter_subset_inter_left _ hball),
    fun z hz hz0 => hGR z (hball hz) hz0, fun z hz => hGH z (hball hz.1) hz.2,
    injOn_exp_halfStrip_of_inverted_coordinate hb (hgi.mono fun z hz => by exact ⟨hz.1.2, hz.2⟩)
      (fun z hz w hw => (hzero hz.1 hz.2).trans (hzero hw.1 hw.2).symm)
      fun z hz hgz => (hstrip z (hball hz.1) hz.2 hgz).2.1⟩
  rw [hGne (hgne z hz.2)]
  dsimp only
  rw [eq_add_inv_of_inverted_coordinate hgf hz.2]
  exact exp_pi_mul_I_sub_div hb

end TauCeti
