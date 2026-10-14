/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Complex
public import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle

/-!
# Schwarz reflection with a totally real linear boundary condition

A holomorphic map into a finite-dimensional complex normed space, continuous up to the real
axis and taking its boundary values in an affine maximal totally real subspace, extends
holomorphically across the axis. In particular it is smooth up to the boundary, without any
boundary differentiability assumption. This is the constant-coefficient local model for
Cauchy--Riemann boundary regularity.

The extension domain can be any conjugation-invariant open subset of `ℂ`; smoothness up to the
boundary holds on any open domain. The target boundary condition is `f z - q ∈ L`, where `L`
is complementary to `i L`; neither a symplectic form nor a choice
of inner product is needed. A real basis of `L` gives complex coordinates on the target via
`TauCeti.IsMaximalTotallyReal.complexBasis`. Coordinatewise application of
`TauCeti.differentiableOn_schwarzReflection_of_symmetric` gives the extension.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  AMS Colloquium Publications **52**, 2012, Appendix B (reflection for totally real boundary
  conditions).
-/

public section

namespace TauCeti

open Complex Set Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {L : Submodule ℝ E} {Ω : Set ℂ} {f : ℂ → E} {q : E}

/-- **Schwarz reflection for an affine maximal totally real subspace.** A map holomorphic on
the open upper part of a conjugation-invariant open domain, continuous on its closed upper
part, and with boundary values in `q + L`, has an analytic extension to the whole domain. -/
theorem IsMaximalTotallyReal.exists_analyticOnNhd_eqOn_of_boundary_mem
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E I).restrictScalars ℝ) L)
    (hΩopen : IsOpen Ω) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hboundary : ∀ z ∈ Ω, z.im = 0 → f z - q ∈ L) :
    ∃ F : ℂ → E, AnalyticOnNhd ℂ F Ω ∧ EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
  classical
  let : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  let b := Module.finBasis ℝ L
  let e := (hL.complexBasis b).equivFunL
  let g : ℂ → Fin (Module.finrank ℝ L) → ℂ := fun z ↦ e (f z - q)
  have hgcont : ContinuousOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}) :=
    e.continuous.comp_continuousOn (hcont.sub continuousOn_const)
  have hgholo : DifferentiableOn ℂ g (Ω ∩ {z : ℂ | 0 < z.im}) :=
    e.differentiable.comp_differentiableOn (hholo.sub_const q)
  have hgreal (z : ℂ) (hz : z ∈ Ω) (him : z.im = 0) (i : Fin (Module.finrank ℝ L)) :
      (g z i).im = 0 := by
    have h := hL.complexBasis_repr_coe b ⟨f z - q, hboundary z hz him⟩ i
    simpa only [g, e, Module.Basis.equivFunL_apply, Module.Basis.equivFun_apply,
      Complex.ofReal_im] using congrArg Complex.im h
  let G : ℂ → Fin (Module.finrank ℝ L) → ℂ :=
    fun z i ↦ schwarzReflection (fun w ↦ g w i) z
  have hG : DifferentiableOn ℂ G Ω := by
    apply differentiableOn_pi.mpr
    intro i
    exact differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ
      ((continuous_apply i).comp_continuousOn hgcont)
      (differentiableOn_pi.mp hgholo i) (fun z hz him ↦ hgreal z hz him i)
  refine ⟨fun z ↦ e.symm (G z) + q, ?_, ?_⟩
  · exact (e.symm.differentiable.comp_differentiableOn hG |>.add_const q).analyticOnNhd hΩopen
  · intro z hz
    have hGz : G z = g z := by
      funext i
      exact schwarzReflection_of_im_nonneg hz.2
    simp [hGz, g]

/-- A holomorphic map with a constant affine maximal totally real boundary condition is
`C^∞` on the closed upper part of its domain, including the real axis. -/
theorem IsMaximalTotallyReal.contDiffOn_of_boundary_mem
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E I).restrictScalars ℝ) L)
    (hΩopen : IsOpen Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hboundary : ∀ z ∈ Ω, z.im = 0 → f z - q ∈ L) :
    ContDiffOn ℝ ∞ f (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  intro z hz
  by_cases him : z.im = 0
  · -- Near an axis point, intersecting with the reflected domain gives a symmetric neighborhood.
    let U := Ω ∩ (starRingEnd ℂ) ⁻¹' Ω
    have hUopen : IsOpen U := hΩopen.inter (hΩopen.preimage continuous_conj)
    have hzU : z ∈ U := ⟨hz.1, by simpa [Complex.conj_eq_iff_im.mpr him] using hz.1⟩
    have hU : MapsTo (starRingEnd ℂ) U U := fun w hw ↦
      ⟨hw.2, by simpa using hw.1⟩
    obtain ⟨F, hF, hEq⟩ := hL.exists_analyticOnNhd_eqOn_of_boundary_mem hUopen hU
      (hcont.mono (inter_subset_inter_left _ inter_subset_left))
      (hholo.mono (inter_subset_inter_left _ inter_subset_left))
      (fun w hw ↦ hboundary w hw.1)
    have hFz : ContDiffAt ℝ ∞ F z := (hF z hzU).contDiffAt.restrict_scalars ℝ
    apply hFz.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hzU)] with w hw hwU
    exact (hEq ⟨hwU, hw.2⟩).symm
  · have hzpos : 0 < z.im := lt_of_le_of_ne hz.2 (Ne.symm him)
    have hupper : IsOpen (Ω ∩ {w : ℂ | 0 < w.im}) :=
      hΩopen.inter (isOpen_lt continuous_const continuous_im)
    have hfz : ContDiffAt ℂ ∞ f z :=
      (hholo.analyticAt (hupper.mem_nhds ⟨hz.1, hzpos⟩)).contDiffAt
    exact (hfz.restrict_scalars ℝ).contDiffWithinAt

end TauCeti
