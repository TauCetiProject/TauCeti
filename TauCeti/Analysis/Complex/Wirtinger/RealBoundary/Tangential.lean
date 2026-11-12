/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.CauchyIntegral

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
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.of_tendsto`: closure under `L¹` convergence on
  compact subsets of `Ω ∩ {0 ≤ im}`.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.tangential`: **tangential derivatives preserve
  the boundary condition.** If `ξ` and `η` have tangential weak derivatives `∂_s ξ` and `∂_s η` up
  to the boundary, then `∂_s ξ` solves `\bar∂ (∂_s ξ) = ∂_s η` with the real boundary condition.
  Combined with the weak Schwarz reflection
  `HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_starSchwarzReflection`, this
  gives `\bar∂ (R ∂_s ξ) = R ∂_s η` on the doubled domain.
* Checks: `z²` and its tangential derivative `2z` are solutions with `η = 0`, while `i z` and its
  tangential derivative `i`, which are not real on `ℝ`, are not.

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

private theorem isClosed_im_nonneg : IsClosed {z : ℂ | 0 ≤ z.im} :=
  isClosed_le continuous_const Complex.continuous_im

/-- The Cauchy–Riemann test function `∂_s χ + i ∂_t χ` paired with the solution in the weak
formulation. -/
private def crTest (χ : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) := ∂_{(1 : ℂ)} χ + I • ∂_{I} χ

private theorem crTest_apply (χ : 𝓓(Ω, ℂ)) (z : ℂ) :
    crTest χ z = lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I := by
  simp [crTest]

/-- `L¹` convergence on compact subsets of `Ω ∩ {0 ≤ im}` passes to the half-plane pairings with
a complex test function. -/
private theorem tendsto_setIntegral_smul {ι : Type*} {l : Filter ι} {ws : ι → ℂ → F}
    {w : ℂ → F} (hws : ∀ i, LocallyIntegrableOn (ws i) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hw : LocallyIntegrableOn w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (ht : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun i ↦ ∫ z in K, ‖ws i z - w z‖) l (𝓝 0))
    (ψ : 𝓓(Ω, ℂ)) :
    Tendsto (fun i ↦ ∫ z in {z : ℂ | 0 ≤ z.im}, ψ z • ws i z) l
      (𝓝 (∫ z in {z : ℂ | 0 ≤ z.im}, ψ z • w z)) := by
  have hint {v : ℂ → F} (hv : LocallyIntegrableOn v ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :
      Integrable (fun z ↦ ψ z • v z) (volume.restrict {z : ℂ | 0 ≤ z.im}) := by
    simpa using ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F)
      (hv.restrict_of_inter Ω.isOpen isClosed_im_nonneg)
  have hK : IsCompact (tsupport (ψ : ℂ → ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
    ψ.hasCompactSupport.isCompact.inter_right isClosed_im_nonneg
  have hKΩ : tsupport (ψ : ℂ → ℂ) ∩ {z : ℂ | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ ψ.tsupport_subset
  obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  refine MeasureTheory.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub
    (s := tsupport (ψ : ℂ → ℂ)) (ae_of_all _ hC)
    (ae_of_all _ fun _ hz ↦ image_eq_zero_of_notMem_tsupport hz)
    (Eventually.of_forall fun i ↦ hint (hws i)) (hint hw).aestronglyMeasurable ?_
  rw [Measure.restrict_restrict (isClosed_tsupport _).measurableSet]
  exact MeasureTheory.tendsto_lintegral_enorm_of_tendsto_integral_norm
    (Eventually.of_forall fun i ↦ ((hws i).integrableOn_compact_subset hKΩ hK).sub
      (hw.integrableOn_compact_subset hKΩ hK)) (ht _ hKΩ hK)

/-- The tangential derivative of a test function real on `ℝ` is real on `ℝ`. -/
private theorem im_lineDeriv_one_eq_zero (χ : 𝓓(Ω, ℂ)) (hχ : ∀ x : ℝ, (χ (x : ℂ)).im = 0)
    (x : ℝ) : (lineDeriv ℝ (χ : ℂ → ℂ) (x : ℂ) 1).im = 0 := by
  have hd : HasLineDerivAt ℝ (χ : ℂ → ℂ) (lineDeriv ℝ (χ : ℂ → ℂ) (x : ℂ) 1) (x : ℂ) 1 :=
    (χ.contDiff.differentiable (by simp) _).lineDifferentiableAt.hasLineDerivAt
  have h2 : HasDerivAt (fun t : ℝ ↦ (χ ((x : ℂ) + t • (1 : ℂ))).im)
      (lineDeriv ℝ (χ : ℂ → ℂ) (x : ℂ) 1).im 0 :=
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

/-- **Real translation invariance.** Translating a solution along the real axis gives a solution:
translation by a real number preserves the closed upper half-plane, its measure, and the
realness of test functions on `ℝ`. -/
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

/-! ### Limits -/

/-- **Closure under `L¹` limits up to the boundary.** If solutions `ξᵢ`, `ηᵢ` converge to locally
integrable `ξ`, `η` in `L¹` on every compact subset of `Ω ∩ {0 ≤ im}`, then `ξ`, `η` is a
solution. -/
theorem of_tendsto [ContinuousStar F] {ι : Type*} {l : Filter ι} [l.NeBot]
    {ξs ηs : ι → ℂ → F} (h : ∀ i, HasWeakConjWirtingerDerivRealBoundaryOn Ω (ξs i) (ηs i))
    (hξ : LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hη : LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξt : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun i ↦ ∫ z in K, ‖ξs i z - ξ z‖) l (𝓝 0))
    (hηt : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun i ↦ ∫ z in K, ‖ηs i z - η z‖) l (𝓝 0)) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η := by
  obtain ⟨i₀⟩ := l.nonempty_of_neBot
  have hF := (hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 (h i₀)).1
  have hξs i := (hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 (h i)).2.1
  have hηs i := (hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 (h i)).2.2.1
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_crTest hξ hη fun χ hχ ↦ ?_
  have hL := (continuous_selfAdjointPart ℝ F).continuousAt.tendsto.comp
    (tendsto_setIntegral_smul hξs hξ hξt (crTest χ))
  have hR := ((continuous_selfAdjointPart ℝ F).continuousAt.tendsto.comp
    (tendsto_setIntegral_smul hηs hη hηt χ)).const_smul (-(2 : ℝ))
  exact tendsto_nhds_unique hL (hR.congr fun i ↦ ((h i).crTest_eq χ hχ).symm)

/-! ### Tangential derivatives -/

/-- **Tangential derivatives preserve the real boundary condition.** If `ξ` solves
`\bar∂ ξ = η` on `Ω ∩ {0 ≤ im}` with `ξ` real on `ℝ`, and `ξ` and `η` have tangential weak
derivatives `ξ' = ∂_s ξ` and `η' = ∂_s η` up to the boundary, that is weak derivatives in the
direction `1` for the Lebesgue measure restricted to `{0 ≤ im}`, tested against all test functions
on `Ω`, then `ξ'` solves `\bar∂ ξ' = η'` on `Ω ∩ {0 ≤ im}` with `ξ'` real on `ℝ`.

The proof tests the equation for `ξ` against `∂_s χ`, which is again real on `ℝ`, and moves `∂_s`
across: tangential derivatives commute with `∂_s + i ∂_t` and produce no boundary term. -/
theorem tangential (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
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

/-- For a scalar function `u` holomorphic on `Ω` and any complex test function `χ` on `Ω`, the real
part of the half-plane pairing in the weak formulation is the boundary integral
`∫_ℝ Im (χ u) ds`. This is the half-plane integration by parts of
`TauCeti.setIntegral_im_pos_re_inner_cauchyRiemann` with the antiholomorphic weight `conj u`. -/
private theorem re_setIntegral_crTest_mul (χ : 𝓓(Ω, ℂ)) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u Ω) :
    (∫ z in {z : ℂ | 0 ≤ z.im}, crTest χ z • u z).re = ∫ s : ℝ, (χ s * u s).im := by
  have hint : Integrable fun z ↦ crTest χ z • u z :=
    (hu.continuousOn.locallyIntegrableOn
      Ω.isOpen.measurableSet).integrable_smul_left_of_hasCompactSupport (crTest χ).continuous
      (crTest χ).hasCompactSupport (crTest χ).tsupport_subset
  have hae : {z : ℂ | 0 < z.im} =ᵐ[volume] {z : ℂ | 0 ≤ z.im} := by
    simpa [Complex.inner, neg_nonpos, neg_neg_iff_pos] using
      (setOf_inner_le_ae_eq_setOf_inner_lt (μ := volume) (neg_ne_zero.2 I_ne_zero) 0).symm
  have hd {z : ℂ} (hz : z ∈ (Ω : Set ℂ)) (v : ℂ) :
      fderiv ℝ (fun w ↦ conj (u w)) z v = conj (deriv u z * v) := by
    have h1 : HasFDerivAt (fun w ↦ conj (u w)) ((conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp
        ((ContinuousLinearMap.toSpanSingleton ℂ (deriv u z)).restrictScalars ℝ)) z :=
      (conjCLE.toContinuousLinearMap.hasFDerivAt (x := u z)).comp z
        ((hu.differentiableAt (Ω.isOpen.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ)
    rw [h1.fderiv]
    simp [mul_comm]
  have hcr (z : ℂ) : re ⟪-fderiv ℝ (fun w ↦ conj (u w)) z 1 +
      I • fderiv ℝ (fun w ↦ conj (u w)) z I, χ z⟫_ℂ = 0 := by
    by_cases hz : z ∈ (Ω : Set ℂ)
    · have h0 : -fderiv ℝ (fun w ↦ conj (u w)) z 1 +
          I • fderiv ℝ (fun w ↦ conj (u w)) z I = 0 := by
        rw [hd hz, hd hz, smul_eq_mul]
        simp only [map_mul, conj_I, mul_one]
        linear_combination (-(conj (deriv u z))) * I_sq
      rw [h0, inner_zero_left, Complex.zero_re]
    · rw [image_eq_zero_of_notMem_tsupport fun h' ↦ hz (χ.tsupport_subset h'), inner_zero_right,
        Complex.zero_re]
  have hη : ContDiffOn ℝ 1 (fun w ↦ conj (u w)) Ω :=
    conjCLE.contDiff.comp_contDiffOn ((hu.contDiffOn (n := 1) Ω.isOpen).restrict_scalars ℝ)
  have key := setIntegral_im_pos_re_inner_cauchyRiemann (ξ := (χ : ℂ → ℂ))
    (η := fun w ↦ conj (u w)) (χ.contDiff.of_le (by simp)) χ.hasCompactSupport
    Ω.isOpen hη χ.tsupport_subset
  simp only [hcr, integral_zero, zero_sub] at key
  have hl (z : ℂ) : re ⟪conj (u z), fderiv ℝ (χ : ℂ → ℂ) z 1 +
      I • fderiv ℝ (χ : ℂ → ℂ) z I⟫_ℂ = (crTest χ z • u z).re := by
    rw [crTest_apply, (χ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv,
      (χ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv, RCLike.inner_apply',
      conj_conj, smul_eq_mul, smul_eq_mul, mul_comm]
  have hb (s : ℝ) : re ⟪I • χ s, conj (u s)⟫_ℂ = -(χ s * u s).im := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  simp only [hl, hb, integral_neg, neg_neg] at key
  rw [← setIntegral_congr_set hae, ← key, ← reCLM_apply,
    ← reCLM.integral_comp_comm hint.integrableOn]
  rfl

/-- A scalar function holomorphic on `Ω` and real on `Ω ∩ ℝ` solves the weak real-boundary
equation with `η = 0`. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_of_differentiableOn {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u Ω) (hreal : ∀ x : ℝ, (x : ℂ) ∈ Ω → (u x).im = 0) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω u 0 := by
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_crTest
    ((hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet).mono_set inter_subset_left)
    locallyIntegrableOn_zero fun χ hχ ↦ ?_
  simp only [Pi.zero_apply, smul_zero, integral_zero, map_zero]
  ext
  rw [Complex.coe_realPart, re_setIntegral_crTest_mul χ hu]
  have h0 (s : ℝ) : (χ s * u s).im = 0 := by
    by_cases hs : (s : ℂ) ∈ Ω
    · simp [Complex.mul_im, hχ, hreal s hs]
    · simp [image_eq_zero_of_notMem_tsupport fun h' ↦ hs (χ.tsupport_subset h')]
  simp [h0]

/-- A scalar function holomorphic on `Ω` with positive imaginary part at a point of `Ω ∩ ℝ` does
not solve the weak real-boundary equation with `η = 0`: testing against a nonnegative bump at that
point makes the boundary integral `∫_ℝ χ Im u ds` positive. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_of_im_pos {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u Ω) {x : ℝ} (hx : (x : ℂ) ∈ Ω) (hux : 0 < (u x).im) :
    ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω u 0 := by
  intro h
  have hU : IsOpen ((Ω : Set ℂ) ∩ u ⁻¹' {w | 0 < w.im}) :=
    hu.continuousOn.isOpen_inter_preimage Ω.isOpen
      (isOpen_lt continuous_const Complex.continuous_im)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x ⟨hx, hux⟩
  let b : ContDiffBump (x : ℂ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hbs : tsupport b ⊆ Metric.ball (x : ℂ) ε := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by simp only [b]; linarith)
  let χ : 𝓓(Ω, ℂ) := ⟨fun z ↦ (b z : ℂ), ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left ofReal_zero,
    (tsupport_comp_subset ofReal_zero _).trans (hbs.trans fun z hz ↦ (hball hz).1)⟩
  have key := h.crTest_eq χ fun s ↦ ofReal_im _
  simp only [Pi.zero_apply, smul_zero, integral_zero, map_zero] at key
  have hre := congrArg (fun w : selfAdjoint ℂ ↦ (w : ℂ).re) key
  simp only [Complex.coe_realPart, ofReal_re, re_setIntegral_crTest_mul χ hu,
    ZeroMemClass.coe_zero, Complex.zero_re] at hre
  have hχv (z : ℂ) : χ z = (b z : ℂ) := rfl
  have hfun : (fun s : ℝ ↦ (χ s * u s).im) = fun s : ℝ ↦ b (s : ℂ) * (u s).im := funext fun s ↦ by
    simp [hχv, Complex.mul_im]
  have hcont : Continuous fun z : ℂ ↦ b z * (u z).im :=
    (b.continuous.continuousOn.mul (Complex.continuous_im.comp_continuousOn hu.continuousOn))
      |>.continuous_of_tsupport_subset Ω.isOpen
        ((tsupport_mul_subset_left).trans (hbs.trans fun z hz ↦ (hball hz).1))
  have hpos : 0 < ∫ s : ℝ, b (s : ℂ) * (u s).im := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := x)
      (hcont.comp continuous_ofReal)
      (HasCompactSupport.mul_right
        (b.hasCompactSupport.comp_isClosedEmbedding Complex.isometry_ofReal.isClosedEmbedding))
      (fun s ↦ ?_) ?_
    · by_cases hs : b s = 0
      · simp [hs]
      · exact mul_nonneg b.nonneg (hball (hbs (subset_tsupport _ hs))).2.le
    · rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
      exact hux.ne'
  rw [hfun] at hre
  linarith

/-- **Check.** `z ↦ z²` is real on `ℝ` and solves the weak real-boundary equation with `η = 0`. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_sq :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ z ^ 2) 0 :=
  hasWeakConjWirtingerDerivRealBoundaryOn_of_differentiableOn
    (differentiable_id.pow 2).differentiableOn fun x _ ↦ by simp [pow_two]

/-- **Check.** The tangential derivative `2z` of `z²` is again real on `ℝ` and solves the weak
real-boundary equation with `η = 0`, as `HasWeakConjWirtingerDerivRealBoundaryOn.tangential`
predicts. -/
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
equation either, on any `Ω` meeting `ℝ`: this is the test `φ = iχ`, `ξ = 1` of the weak
formulation, transposed. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_const_I {x : ℝ} (hx : (x : ℂ) ∈ Ω) :
    ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun _ : ℂ ↦ I) 0 :=
  not_hasWeakConjWirtingerDerivRealBoundaryOn_of_im_pos
    (differentiable_const I).differentiableOn hx (by simp)

end TauCeti
