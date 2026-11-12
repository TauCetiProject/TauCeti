/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
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

* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.comp_add_ofReal`: real translation
  invariance.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.differenceQuotient`: tangential difference
  quotients are solutions.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.weakLineDeriv_one`: **tangential derivatives
  preserve the boundary condition.** If `ξ` and `η` have tangential weak derivatives `∂_s ξ` and
  `∂_s η` up to the boundary, then `∂_s ξ` solves `\bar∂ (∂_s ξ) = ∂_s η` with the real boundary
  condition.
  Combined with the weak Schwarz reflection
  `HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_starSchwarzReflection`, this
  gives `\bar∂ (R ∂_s ξ) = R ∂_s η` on the doubled domain.
* Checks: `z²` and its tangential derivative `2z` are solutions with `η = 0`, while `i z` and its
  tangential derivative `i`, which are not real on `ℝ`, are not. These follow from the holomorphic
  criteria `TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_of_differentiableOn` and
  `TauCeti.not_hasWeakConjWirtingerDerivRealBoundaryOn_of_im_pos`.

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

/-- The tangential derivative of a test function real on `ℝ` is real on `ℝ`. -/
private theorem im_lineDeriv_one_eq_zero (χ : 𝓓(Ω, ℂ)) (hχ : ∀ x : ℝ, (χ (x : ℂ)).im = 0)
    (x : ℝ) : (lineDeriv ℝ (χ : ℂ → ℂ) (x : ℂ) 1).im = 0 := by
  have hd : HasLineDerivAt ℝ (χ : ℂ → ℂ) (lineDeriv ℝ (χ : ℂ → ℂ) (x : ℂ) 1) (x : ℂ) 1 :=
    (χ.contDiff.differentiable (by simp) _).lineDifferentiableAt.hasLineDerivAt
  have h2 : HasDerivAt (fun t : ℝ ↦ (χ ((x : ℂ) + t • (1 : ℂ))).im)
      (lineDeriv ℝ (χ : ℂ → ℂ) (x : ℂ) 1).im 0 := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt _ hd
  have h3 : (fun t : ℝ ↦ (χ ((x : ℂ) + t • (1 : ℂ))).im) = fun _ ↦ 0 :=
    funext fun t ↦ by simpa using hχ (x + t)
  rw [h3] at h2
  exact h2.unique (hasDerivAt_const _ _)

variable [StarAddMonoid F] [StarModule ℂ F] {ξ η ξ' η' : ℂ → F}

/-- The weak real-boundary equation, stated with `crTest`. -/
private theorem HasWeakConjWirtingerDerivRealBoundaryOn.crTest_eq
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (χ : 𝓓(Ω, ℂ))
    (hχ : ∀ x : ℝ, (χ (x : ℂ)).im = 0) :
    ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, crTest χ z • ξ z) =
      -(2 : ℝ) • ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z) := by
  simpa only [crTest_apply] using (hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h).2.2.2 χ hχ

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

namespace HasWeakConjWirtingerDerivRealBoundaryOn

/-! ### Real translations and difference quotients -/

/-- **Real translation invariance.** If `Ω' + a ⊆ Ω` for a real `a`, then `z ↦ ξ (z + a)` solves
the weak real-boundary equation on `Ω'` with right-hand side `z ↦ η (z + a)`. -/
theorem comp_add_ofReal (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (a : ℝ)
    (hΩ' : MapsTo (· + (a : ℂ)) Ω' Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω' (fun z ↦ ξ (z + a)) (fun z ↦ η (z + a)) := by
  obtain ⟨hF, hξ, hη, -⟩ := hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h
  have hmaps : MapsTo (· + (a : ℂ)) ((Ω' : Set ℂ) ∩ {z | 0 ≤ z.im})
      ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := fun y hy ↦ ⟨hΩ' hy.1, by simpa using hy.2⟩
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_crTest
    (hξ.comp_add_right_of_mapsTo hmaps) (hη.comp_add_right_of_mapsTo hmaps) fun χ hχ ↦ ?_
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
  have hF := (hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h).1
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_crTest
    hξ.locallyIntegrableOn_deriv.inter_of_restrict hη.locallyIntegrableOn_deriv.inter_of_restrict
    fun χ hχ ↦ ?_
  have hχs : ∀ x : ℝ, ((∂_{(1 : ℂ)} χ : 𝓓(Ω, ℂ)) (x : ℂ)).im = 0 := fun x ↦ by
    rw [TestFunction.lineDerivOp_apply]
    exact im_lineDeriv_one_eq_zero χ hχ x
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

/-- **Check.** `z ↦ z²` is real on `ℝ` and solves the weak real-boundary equation with `η = 0`. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_sq :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ z ^ 2) 0 :=
  hasWeakConjWirtingerDerivRealBoundaryOn_of_differentiableOn
    (differentiable_id.pow 2).differentiableOn fun x _ ↦ by simp [pow_two]

/-- **Check.** The tangential derivative `2z` of `z²` is again real on `ℝ` and solves the weak
real-boundary equation with `η = 0`, as
`HasWeakConjWirtingerDerivRealBoundaryOn.weakLineDeriv_one` predicts. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_two_mul :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ 2 * z) 0 :=
  hasWeakConjWirtingerDerivRealBoundaryOn_of_differentiableOn
    ((differentiable_const 2).mul differentiable_id).differentiableOn fun x _ ↦ by simp

/-- **Check.** `z ↦ i z` is holomorphic but imaginary on `ℝ`, and does not solve the weak
real-boundary equation on any `Ω` meeting the positive real axis. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_I_mul {x : ℝ} (hx : (x : ℂ) ∈ Ω)
    (hx0 : 0 < x) : ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ I * z) 0 :=
  not_hasWeakConjWirtingerDerivRealBoundaryOn_of_im_pos
    ((differentiable_const I).mul differentiable_id).differentiableOn hx (by simpa using hx0)

/-- **Check.** The tangential derivative `i` of `i z` does not solve the weak real-boundary
equation either, on any `Ω` meeting `ℝ`. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_const_I {x : ℝ} (hx : (x : ℂ) ∈ Ω) :
    ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun _ : ℂ ↦ I) 0 :=
  not_hasWeakConjWirtingerDerivRealBoundaryOn_of_im_pos
    (differentiable_const I).differentiableOn hx (by simp)

end TauCeti
