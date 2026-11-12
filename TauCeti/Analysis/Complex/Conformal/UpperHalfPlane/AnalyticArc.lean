/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import TauCeti.Analysis.Complex.Conformal.Reflection.Arc

/-!
# Conformal continuation across an analytic boundary arc

Let `f` be a conformal map of the upper half-plane onto `U` which extends continuously and
injectively to the closed upper half-plane. By Carathéodory's theorem the Riemann map of a Jordan
domain has this form; see
`TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier`.

Suppose that near the boundary value `f x` at a real point `x`, the domain `U` is the positive
side of an analytic arc. Concretely, there is a holomorphic open partial homeomorphism `d` with
`f x ∈ d.source` and conjugation-invariant target, such that
`d.source ∩ U = d.source ∩ d ⁻¹' {w | 0 < w.im}`. The arc is then `d.source ∩ d ⁻¹' ℝ`. Under
these hypotheses `f` continues to a holomorphic injection of a disc about `x`, and the derivative
of the continuation vanishes nowhere on that disc. In particular, the continuation is conformal at
the boundary point `x` itself. This is the boundary regularity of conformal maps along analytic
boundary arcs.

The continuation is the charted Schwarz reflection `TauCeti.chartedSchwarzReflection` of `f`. Its
source chart is the identity on a small disc about `x`, and its target chart is `d`. Near `x`, the
boundary values of `f` lie on the arc. They lie in the closure of `U` by continuity, and they lie
outside `U` because `f` is injective up to the real axis.

## Main results

* `TauCeti.exists_differentiableOn_injOn_eqOn_ball_of_analyticArc`: a conformal map of the closed
  upper half-plane continues across every real point whose boundary value lies on an analytic arc
  of the frontier. The continuation is holomorphic and injective with nonvanishing derivative, and
  it intertwines conjugation with the reflection in the arc.

## References

* L. Ahlfors, *Complex Analysis*, Chapters 4 and 6.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 3.
-/

public section

open Complex Metric Set UpperHalfPlane

namespace TauCeti

/-- Near a real point whose boundary value lies in the chart domain, the boundary values of a
conformal map of the closed upper half-plane lie on the arc `d ⁻¹' ℝ`. They lie in the closure of
the positive side by continuity, and outside it because `f` is injective up to the real axis. -/
private theorem im_apply_eq_zero_of_analyticArc {f : ℂ → ℂ} {U : Set ℂ}
    (d : OpenPartialHomeomorph ℂ ℂ)
    (hdU : d.source ∩ U = d.source ∩ d ⁻¹' {w : ℂ | 0 < w.im})
    (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (hfi : InjOn f {z : ℂ | 0 ≤ z.im})
    (hfU : f '' upperHalfPlaneSet = U) {V : Set ℂ} (hV : IsOpen V)
    (hVd : V ∩ {z : ℂ | 0 ≤ z.im} ⊆ f ⁻¹' d.source) {z : ℂ} (hz : z ∈ V) (him : z.im = 0) :
    (d (f z)).im = 0 := by
  have hfz : f z ∈ d.source := hVd ⟨hz, him.ge⟩
  -- On the open upper part of `V` the map lands on the positive side of the arc.
  have hpos : ∀ w ∈ V ∩ upperHalfPlaneSet, 0 < (d (f w)).im := fun w hw => by
    have hw0 : 0 ≤ w.im := (show 0 < w.im from hw.2).le
    have hw' : f w ∈ d.source ∩ U := ⟨hVd ⟨hw.1, hw0⟩, hfU ▸ mem_image_of_mem f hw.2⟩
    rw [hdU] at hw'
    exact hw'.2
  -- The value at `z` is not in `U`: it would then be a value at a point of the upper half-plane.
  have hnotU : f z ∉ U := by
    rintro hU
    rw [← hfU] at hU
    obtain ⟨w, hw, hwz⟩ := hU
    have hw0 : 0 < w.im := hw
    have hwz' : w = z := hfi (show 0 ≤ w.im from hw0.le) (show 0 ≤ z.im from him.ge) hwz
    exact hw0.ne' (hwz' ▸ him)
  have hnot : ¬ 0 < (d (f z)).im := fun h =>
    hnotU (hdU.symm.subset ⟨hfz, h⟩).2
  -- The value at `z` is a limit of values on the positive side of the arc.
  have hzcl : z ∈ closure (V ∩ upperHalfPlaneSet) :=
    hV.inter_closure ⟨hz, by rw [closure_setOfPred_lt_im]; exact him.ge⟩
  have hcont : ContinuousWithinAt (fun w => (d (f w)).im) (V ∩ upperHalfPlaneSet) z :=
    continuous_im.continuousAt.comp_continuousWithinAt <|
      (d.continuousAt hfz).comp_continuousWithinAt <|
        (hfc z him.ge).mono fun w hw => (le_of_lt hw.2 : 0 ≤ w.im)
  have hge : 0 ≤ (d (f z)).im :=
    closure_minimal (s := (fun w => (d (f w)).im) '' (V ∩ upperHalfPlaneSet))
      (by rintro _ ⟨w, hw, rfl⟩; exact (hpos w hw).le) isClosed_Ici
      (hcont.mem_closure_image hzcl)
  exact le_antisymm (not_lt.mp hnot) hge

/-- **Conformal continuation across an analytic boundary arc.** Let `f` be holomorphic on the
upper half-plane with image `U`, and continuous and injective on the closed upper half-plane. Let
`d` be a holomorphic open partial homeomorphism with conjugation-invariant target, such that near
the arc `d ⁻¹' ℝ` the domain `U` is the positive side `d ⁻¹' {w | 0 < w.im}`. If the boundary value
`f x` at a real point `x` lies in the chart domain, then `f` continues across `x`: on some disc
about `x` there is a holomorphic injection `F` that agrees with `f` on the closed upper half of the
disc, has nonvanishing derivative throughout the disc, and intertwines conjugation with the
reflection `v ↦ d.symm (conj (d v))` in the arc.

The derivative of `F` does not vanish at the real points of the disc either, although `f` is only
assumed continuous there. -/
theorem exists_differentiableOn_injOn_eqOn_ball_of_analyticArc {f : ℂ → ℂ} {U : Set ℂ}
    (d : OpenPartialHomeomorph ℂ ℂ) (hd : DifferentiableOn ℂ d d.source)
    (hd_symm : MapsTo (starRingEnd ℂ) d.target d.target)
    (hdU : d.source ∩ U = d.source ∩ d ⁻¹' {w : ℂ | 0 < w.im})
    (hfd : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U)
    {x : ℝ} (hx : f x ∈ d.source) :
    ∃ r > 0, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (x : ℂ) r) ∧ InjOn F (ball (x : ℂ) r) ∧
      EqOn F f (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (x : ℂ) r, deriv F z ≠ 0) ∧
      ∀ z ∈ ball (x : ℂ) r, F ((starRingEnd ℂ) z) = d.symm ((starRingEnd ℂ) (d (F z))) := by
  -- A disc about `x` whose closed upper half `f` maps into the chart domain of `d`.
  obtain ⟨r, hr, hrd⟩ : ∃ r > 0, ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im} ⊆ f ⁻¹' d.source :=
    mem_nhdsWithin_iff.mp
      ((hfc _ (by simp)).preimage_mem_nhdsWithin (d.open_source.mem_nhds hx))
  -- The source chart is the identity on that disc.
  let e := OpenPartialHomeomorph.ofSet (ball (x : ℂ) r) isOpen_ball
  have he_src : e.source = ball (x : ℂ) r := OpenPartialHomeomorph.ofSet_source _ _
  have he_tgt : e.target = ball (x : ℂ) r := OpenPartialHomeomorph.ofSet_target _ _
  have he_apply : ∀ z, e z = z := fun z => by rw [OpenPartialHomeomorph.ofSet_apply, id]
  have he_symm_apply : ∀ z, e.symm z = z := fun z => by
    rw [OpenPartialHomeomorph.ofSet_symm, OpenPartialHomeomorph.ofSet_apply, id]
  have hhalf : ∀ P : ℝ → Prop,
      e.source ∩ {z : ℂ | P (e z).im} = ball (x : ℂ) r ∩ {z : ℂ | P z.im} := fun P => by
    simp only [he_src, he_apply]
  have he : DifferentiableOn ℂ e e.source :=
    differentiableOn_id.congr fun z _ => he_apply z
  have he_conj : MapsTo (starRingEnd ℂ) e.target e.target := fun z hz => by
    rw [he_tgt] at hz ⊢
    rwa [mem_ball, ← Complex.conj_ofReal, Complex.dist_conj_conj]
  -- The hypotheses of charted Schwarz reflection, read through the identity chart.
  have hf_maps : MapsTo f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) d.source := by
    rw [hhalf (0 ≤ ·)]; exact hrd
  have hf_cont : ContinuousOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) := by
    rw [hhalf (0 ≤ ·)]; exact hfc.mono inter_subset_right
  have hf_diff : DifferentiableOn ℂ f (e.source ∩ {z : ℂ | 0 < (e z).im}) := by
    rw [hhalf (0 < ·)]; exact hfd.mono inter_subset_right
  have hf_inj : InjOn f (e.source ∩ {z : ℂ | 0 ≤ (e z).im}) := by
    rw [hhalf (0 ≤ ·)]; exact hfi.mono inter_subset_right
  have hf_real : ∀ z ∈ e.source, (e z).im = 0 → (d (f z)).im = 0 := fun z hz him => by
    rw [he_src] at hz; rw [he_apply] at him
    exact im_apply_eq_zero_of_analyticArc d hdU hfc hfi hfU isOpen_ball hrd hz him
  have hf_upper : ∀ z ∈ e.source, 0 < (e z).im → 0 < (d (f z)).im := fun z hz him => by
    rw [he_src] at hz; rw [he_apply] at him
    have hz' : f z ∈ d.source ∩ U := ⟨hrd ⟨hz, him.le⟩, hfU ▸ mem_image_of_mem f him⟩
    rw [hdU] at hz'
    exact hz'.2
  -- The continuation is the charted Schwarz reflection of `f`.
  refine ⟨r, hr, chartedSchwarzReflection e d f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← he_src]
    exact differentiableOn_chartedSchwarzReflection_of_symmetric e d f he hd he_conj hd_symm
      hf_maps hf_cont hf_diff hf_real
  · rw [← he_src]
    exact injOn_chartedSchwarzReflection_of_symmetric e d f he_conj hd_symm hf_maps hf_upper
      (fun z hz him => (hf_real z hz him).ge) hf_inj
  · rintro z ⟨hz, him⟩
    exact chartedSchwarzReflection_of_coord_im_nonneg e d f hf_maps (he_src ▸ hz)
      (by rwa [he_apply])
  · intro z hz
    exact deriv_chartedSchwarzReflection_ne_zero e d f he hd he_conj hd_symm hf_maps hf_cont
      hf_diff hf_real hf_upper hf_inj (he_src ▸ hz)
  · intro z hz
    have h := chartedSchwarzReflection_sourceReflection e d f he_conj hd_symm hf_maps hf_real
      (he_src ▸ hz)
    rwa [he_apply, he_symm_apply] at h

end TauCeti
