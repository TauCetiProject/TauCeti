/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.Analysis.Green.HalfPlane
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Tangential derivatives of weak `\bar∂` solutions with a real boundary condition

This file proves the tangential step of the boundary regularity induction for the model
operator `\bar∂ = ½ (∂_s + i ∂_t)` on the closed upper half-plane, with the boundary condition
that the solution is real on the real axis. The weak formulation is
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η`, whose tests are smooth, compactly
supported in `Ω`, real on the real axis and need not vanish there.

The direction `∂_s` is tangent to the boundary, so translating a test function along `ℝ` keeps it
admissible, and differentiating a test function along `ℝ` keeps it real on `ℝ`. Hence real
translates and difference quotients of a solution are again solutions, and a tangential weak
derivative `∂_s ξ` solves the differentiated equation with the same boundary condition. A
*tangential weak derivative up to the boundary* is a weak derivative in the direction `1` for the
Lebesgue measure restricted to `{0 ≤ im}`, written
`HasWeakLineDerivOn (volume.restrict {z | 0 ≤ z.im}) Ω ξ ξ' 1`: it is tested against all test
functions on `Ω`, not only those vanishing on `ℝ`, which is the right notion because integrating
by parts in `s` produces no boundary term.

## Main results

* `ContDiffOn.hasWeakLineDerivOn_restrict_im_nonneg_one`: a map of class `C¹` on `Ω` has its
  classical tangential derivative as tangential weak derivative up to the boundary.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.comp_add_ofReal`: real translation
  invariance.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.differenceQuotient`: tangential difference
  quotients are solutions.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.weakLineDeriv_one`: **tangential derivatives
  preserve the boundary condition.** If `ξ` and `η` have tangential weak derivatives `∂_s ξ` and
  `∂_s η` up to the boundary, then `∂_s ξ` solves `\bar∂ (∂_s ξ) = ∂_s η` with the real boundary
  condition.
  Combined with the weak Schwarz reflection
  `HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_starSchwarzReflection` of
  `Analysis/Complex/Wirtinger/RealBoundary/Reflection.lean`, this gives
  `\bar∂ (R ∂_s ξ) = R ∂_s η` on the doubled domain.
* Check: the tangential derivative `2z` of the solution `z²` is again a solution with `η = 0`,
  obtained from `TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_sq` through
  `HasWeakConjWirtingerDerivRealBoundaryOn.weakLineDeriv_one`.

This is the constant-structure model `J = i`, `S = 0` of the tangential step of
McDuff–Salamon, Lemma B.4.6 and Proposition B.4.9.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace Set Filter Topology LineDeriv
open scoped ContDiff Distributions ComplexConjugate ComplexStarModule InnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {Ω Ω' : Opens ℂ}

/-! ### Preliminaries -/

/-- The Cauchy–Riemann test function `∂_s χ + i ∂_t χ` paired with the solution in the weak
formulation. -/
private def crTest (χ : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) := ∂_{(1 : ℂ)} χ + I • ∂_{I} χ

private theorem crTest_apply (χ : 𝓓(Ω, ℂ)) (z : ℂ) :
    crTest χ z = lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I := by
  simp [crTest]

variable [StarAddMonoid F] [StarModule ℂ F] {ξ η ξ' η' : ℂ → F}

/-- The weak real-boundary equation, stated with `crTest`. -/
private theorem HasWeakConjWirtingerDerivRealBoundaryOn.crTest_eq
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (χ : 𝓓(Ω, ℂ))
    (hχ : ∀ x : ℝ, (χ (x : ℂ)).im = 0) :
    ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, crTest χ z • ξ z) =
      -(2 : ℝ) • ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z) := by
  simpa only [crTest_apply] using h.realPart_setIntegral_eq χ hχ

/-- A constructor for the weak real-boundary equation, stated with `crTest`. -/
private theorem hasWeakConjWirtingerDerivRealBoundaryOn_of_crTest [CompleteSpace F]
    (hξ : LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hη : LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hw : ∀ χ : 𝓓(Ω, ℂ), (∀ x : ℝ, (χ (x : ℂ)).im = 0) →
      ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, crTest χ z • ξ z) =
        -(2 : ℝ) • ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z)) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η :=
  hasWeakConjWirtingerDerivRealBoundaryOn_iff.2
    ⟨‹_›, hξ, hη, fun χ hχ ↦ by simpa only [crTest_apply] using hw χ hχ⟩

omit [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F] in
/-- **Classical tangential derivatives up to the boundary.** A map `f` of class `C¹` on `Ω` has
its classical derivative `∂_s f` in the direction `1` as weak derivative in that direction for the
Lebesgue measure restricted to `{0 ≤ im}`, tested against all test functions on `Ω`. -/
theorem _root_.ContDiffOn.hasWeakLineDerivOn_restrict_im_nonneg_one {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {f : ℂ → G}
    (hf : ContDiffOn ℝ 1 f Ω) :
    HasWeakLineDerivOn (volume.restrict {z : ℂ | 0 ≤ z.im}) Ω f (fun z ↦ fderiv ℝ f z 1) 1 := by
  have hH : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hD : ContinuousOn (fun z ↦ fderiv ℝ f z 1) Ω :=
    (hf.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply continuousOn_const
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance,
    ((hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet).mono_set
      inter_subset_left).restrict_of_inter Ω.isOpen hH,
    ((hD.locallyIntegrableOn Ω.isOpen.measurableSet).mono_set
      inter_subset_left).restrict_of_inter Ω.isOpen hH, fun φ ↦ ?_⟩
  set L : G →L[ℝ] ℝ →L[ℝ] G := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  set g : ℂ → G := fun z ↦ L (f z) (φ z)
  have hg : ContDiff ℝ 1 g := L.contDiff_of_tsupport_subset_right hf
    (φ.contDiff.of_le (by simp)).contDiffOn Ω.isOpen φ.tsupport_subset
  have hgc : HasCompactSupport g := φ.hasCompactSupport.mono fun z hz h0 ↦ hz (by simp [g, h0])
  have hgd (z : ℂ) :
      fderiv ℝ g z 1 = lineDeriv ℝ (φ : ℂ → ℝ) z 1 • f z + φ z • fderiv ℝ f z 1 := by
    rw [L.fderiv_of_tsupport_subset_right (hf.differentiableOn one_ne_zero)
      (φ.contDiff.differentiable (by simp)) Ω.isOpen φ.tsupport_subset, φ.lineDeriv_eq_fderiv]
    simp [L]
  have hint : Integrable fun z ↦ fderiv ℝ g z 1 :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) 1)
  have hint' : Integrable fun z ↦ φ z • fderiv ℝ f z 1 :=
    ((φ.continuous.continuousOn.smul hD).continuous_of_tsupport_subset Ω.isOpen
      ((tsupport_smul_subset_left _ _).trans φ.tsupport_subset)).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.mono fun z hz h0 ↦ hz (by simp [h0]))
  have hpt (z : ℂ) :
      lineDeriv ℝ (φ : ℂ → ℝ) z 1 • f z = fderiv ℝ g z 1 - φ z • fderiv ℝ f z 1 := by
    rw [hgd, add_sub_cancel_right]
  have hae : {z : ℂ | 0 < z.im} =ᵐ[volume] {z : ℂ | 0 ≤ z.im} :=
    (Complex.setOf_le_im_ae_eq 0).symm
  simp_rw [hpt]
  rw [← setIntegral_congr_set hae, ← setIntegral_congr_set hae,
    integral_sub (f := fun z ↦ fderiv ℝ g z 1) (g := fun z ↦ φ z • fderiv ℝ f z 1)
      hint.integrableOn hint'.integrableOn,
    setIntegral_im_pos_fderiv_one_eq_zero hg hgc, zero_sub]

namespace HasWeakConjWirtingerDerivRealBoundaryOn

/-! ### Real translations and difference quotients -/

/-- **Real translation invariance.** If `Ω' + a ⊆ Ω` for a real `a`, then `z ↦ ξ (z + a)` solves
the weak real-boundary equation on `Ω'` with right-hand side `z ↦ η (z + a)`. -/
theorem comp_add_ofReal (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (a : ℝ)
    (hΩ' : MapsTo (· + (a : ℂ)) Ω' Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω' (fun z ↦ ξ (z + a)) (fun z ↦ η (z + a)) := by
  have := h.completeSpace
  have hmaps : MapsTo (· + (a : ℂ)) ((Ω' : Set ℂ) ∩ {z | 0 ≤ z.im})
      ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := fun y hy ↦ ⟨hΩ' hy.1, by simpa using hy.2⟩
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_crTest
    (h.locallyIntegrableOn.comp_add_right_of_mapsTo hmaps)
    (h.locallyIntegrableOn_deriv.comp_add_right_of_mapsTo hmaps) fun χ hχ ↦ ?_
  set χ' : 𝓓(Ω, ℂ) := translateTestFunction hΩ' χ
  have hχ' : ∀ x : ℝ, (χ' (x : ℂ)).im = 0 := fun x ↦ by
    simpa [χ'] using hχ (x - a)
  have key := h.crTest_eq χ' hχ'
  have hpre : (· + (a : ℂ)) ⁻¹' {z : ℂ | 0 ≤ z.im} = {z : ℂ | 0 ≤ z.im} := by
    ext z
    simp
  have ht (g : ℂ → F) :
      ∫ z in {z : ℂ | 0 ≤ z.im}, g (z + a) = ∫ z in {z : ℂ | 0 ≤ z.im}, g z := by
    have := (measurePreserving_add_right volume (a : ℂ)).setIntegral_preimage_emb
      (measurableEmbedding_addRight _) g {z : ℂ | 0 ≤ z.im}
    rwa [hpre] at this
  rw [← ht (fun z ↦ crTest χ' z • ξ z), ← ht (fun z ↦ χ' z • η z)] at key
  have hc (z : ℂ) : crTest χ' (z + a) = crTest χ z := by
    simp [crTest_apply, χ', lineDeriv_translateTestFunction]
  have hv (z : ℂ) : χ' (z + a) = χ z := by
    simp [χ']
  simpa only [hc, hv] using key

/-- **Tangential difference quotients are solutions.** If `Ω' ⊆ Ω` and `Ω' + a ⊆ Ω` for a real
`a`, the difference quotient `a⁻¹ (ξ (z + a) - ξ z)` solves the weak real-boundary equation on
`Ω'` with right-hand side the difference quotient of `η`. -/
theorem differenceQuotient (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) {a : ℝ}
    (hΩ'Ω : Ω' ≤ Ω) (hΩ' : MapsTo (· + (a : ℂ)) Ω' Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω' (fun z ↦ a⁻¹ • (ξ (z + a) - ξ z))
      (fun z ↦ a⁻¹ • (η (z + a) - η z)) :=
  ((h.comp_add_ofReal a hΩ').sub (h.mono hΩ'Ω)).const_smul a⁻¹

/-! ### Tangential derivatives -/

/-- **Tangential derivatives preserve the real boundary condition.** If `ξ` solves
`\bar∂ ξ = η` on `Ω ∩ {0 ≤ im}` with `ξ` real on `ℝ`, and `ξ` and `η` have tangential weak
derivatives `ξ' = ∂_s ξ` and `η' = ∂_s η` up to the boundary, that is weak derivatives in the
direction `1` for the Lebesgue measure restricted to `{0 ≤ im}`, tested against all test functions
on `Ω`, then `ξ'` solves `\bar∂ ξ' = η'` on `Ω ∩ {0 ≤ im}` with `ξ'` real on `ℝ`. -/
theorem weakLineDeriv_one (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (hξ : HasWeakLineDerivOn (volume.restrict {z : ℂ | 0 ≤ z.im}) Ω ξ ξ' 1)
    (hη : HasWeakLineDerivOn (volume.restrict {z : ℂ | 0 ≤ z.im}) Ω η η' 1) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ' η' := by
  have := h.completeSpace
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_crTest
    hξ.locallyIntegrableOn_deriv.inter_of_restrict hη.locallyIntegrableOn_deriv.inter_of_restrict
    fun χ hχ ↦ ?_
  have hχs : ∀ x : ℝ, ((∂_{(1 : ℂ)} χ : 𝓓(Ω, ℂ)) (x : ℂ)).im = 0 := fun x ↦ by
    rw [TestFunction.lineDerivOp_apply]
    exact TestFunction.map_lineDeriv_eq_zero_of_forall Complex.imCLM χ fun t ↦ by
      simpa using hχ (x + t)
  have key := h.crTest_eq (∂_{(1 : ℂ)} χ) hχs
  have hcomm (z : ℂ) : lineDeriv ℝ (crTest χ : ℂ → ℂ) z 1 = crTest (∂_{(1 : ℂ)} χ) z := by
    rw [← TestFunction.lineDerivOp_apply, crTest, crTest, LineDeriv.lineDerivOp_add,
      LineDeriv.lineDerivOp_smul, TestFunction.lineDerivOp_comm χ 1 I]
  have hL := hξ.integral_lineDeriv_smul_eq_neg_integral_smul_complex (crTest χ)
  have hR := hη.integral_lineDeriv_smul_eq_neg_integral_smul_complex χ
  simp only [hcomm] at hL
  simp only [TestFunction.lineDerivOp_apply] at key
  rwa [hR, hL, map_neg, map_neg, smul_neg, neg_inj] at key

end HasWeakConjWirtingerDerivRealBoundaryOn

/-! ### Checks -/

/-- **Check.** The tangential derivative `2z` of the solution `z²` is again real on `ℝ` and solves
the weak real-boundary equation with `η = 0`. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_two_mul :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ 2 * z) 0 := by
  have hd (z : ℂ) : fderiv ℝ (fun w : ℂ ↦ w ^ 2) z 1 = 2 * z := by
    rw [((hasDerivAt_pow 2 z).hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have h := hasWeakConjWirtingerDerivRealBoundaryOn_sq.weakLineDeriv_one
    (by fun_prop : ContDiffOn ℝ 1 (fun w : ℂ ↦ w ^ 2) Ω).hasWeakLineDerivOn_restrict_im_nonneg_one
    (hasWeakLineDerivOn_zero (μ := volume.restrict {z : ℂ | 0 ≤ z.im}) (Ω := Ω))
  simpa only [hd] using h

end TauCeti
