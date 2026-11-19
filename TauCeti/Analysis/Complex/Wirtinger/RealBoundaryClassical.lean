/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.RealBoundaryReflection
import TauCeti.Analysis.Green.HalfPlane
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Examples
import TauCeti.MeasureTheory.Integral.Bochner.Star
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Classical solutions with real boundary values are weak solutions

Let `Ω ⊆ ℂ` be open and let `ξ : ℂ → F` be `C¹` up to the real axis on the closed upper part
`Ω ∩ {0 ≤ im}`, with `\bar∂ξ = η` at the points of `Ω` off the axis. Integrating by parts over the
closed upper half-plane against a smooth complex test function `χ` compactly supported in `Ω`
gives

`∫_{0 ≤ t} (∂_s χ + i ∂_t χ) ξ = -2 ∫_{0 ≤ t} χ η - i ∫_ℝ χ(s) ξ(s) ds`,

the half-plane identity behind McDuff–Salamon (B.4.3) with `J = i`, together with its boundary
term. When `χ` is real on the real axis and `ξ` takes real values there, where `x : F` is real if
`star x = x`, the boundary integral is real, so its product with `i` has real part zero. Hence
`ξ` is a weak solution of `\bar∂ξ = η` with real boundary values in the sense of
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn`.

## Main results

* `TauCeti.setIntegral_im_nonneg_lineDeriv_add_I_mul_smul_eq`: the half-plane integration by
  parts formula above, with its boundary term.
* `TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn`: a map `C¹` up to the real axis
  on `Ω ∩ {0 ≤ im}`, solving `\bar∂ξ = η` off the axis and real on `Ω ∩ ℝ`, is a weak solution with
  real boundary values.
* Checks: `z²` solves `\bar∂ξ = 0` and `z e^{-conj z}` solves `\bar∂ξ = -ξ`, the equation
  `∂_s ξ + i ∂_t ξ + 2ξ = 0`, weakly with real boundary values
  (`TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_sq`,
  `TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_mul_cexp_neg_conj`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Appendix B.4, equation (B.4.3).
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace Set Filter Topology
open scoped ContDiff Distributions ComplexConjugate ComplexStarModule

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {Ω : Opens ℂ} {ξ η : ℂ → F}

private theorem measurableSet_im_pos : MeasurableSet {z : ℂ | 0 < z.im} :=
  measurableSet_lt measurable_const Complex.measurable_im

private theorem measurableSet_im_nonneg' : MeasurableSet {z : ℂ | 0 ≤ z.im} :=
  measurableSet_le measurable_const Complex.measurable_im

/-- `Ω ∩ {0 ≤ im}` is a neighbourhood of every point of `Ω` off the real axis in the upper
half-plane. -/
private theorem inter_im_nonneg_mem_nhds {z : ℂ} (hz : z ∈ (Ω : Set ℂ)) (hz' : 0 < z.im) :
    (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ∈ 𝓝 z :=
  inter_mem (Ω.isOpen.mem_nhds hz)
    (mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
      fun _ hw ↦ le_of_lt hw)

omit [NormedSpace ℂ F] in
/-- A map continuous on `Ω ∩ {0 ≤ im}` and vanishing outside the support of a test function is
integrable on the closed upper half-plane. -/
private theorem integrableOn_im_nonneg_of_continuousOn (χ : 𝓓(Ω, ℂ)) {h : ℂ → F}
    (hh : ContinuousOn h ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h0 : ∀ z, z ∉ tsupport (χ : ℂ → ℂ) → h z = 0) :
    IntegrableOn h {z : ℂ | 0 ≤ z.im} := by
  have hK : IsCompact (tsupport (χ : ℂ → ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
    χ.hasCompactSupport.isCompact.inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKΩ : tsupport (χ : ℂ → ℂ) ∩ {z : ℂ | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz ↦ ⟨χ.tsupport_subset hz.1, hz.2⟩
  exact ((hh.mono hKΩ).integrableOn_compact hK).of_forall_sdiff_eq_zero measurableSet_im_nonneg'
    fun z hz ↦ h0 z fun h ↦ hz.2 ⟨h, hz.1⟩

section ClassicalSolution

variable (hξ : ContDiffOn ℝ 1 ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
  (hη : ∀ z ∈ (Ω : Set ℂ), 0 < z.im → conjWirtingerDeriv ξ z 1 = η z)

include hξ in
/-- The product of a test function with `ξ` is `C¹` up to the real axis on the closed half-plane. -/
private theorem contDiffOn_smul (χ : 𝓓(Ω, ℂ)) :
    ContDiffOn ℝ 1 (fun z ↦ χ z • ξ z) {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · have h := ((χ.contDiff.of_le (by simp)).contDiffOn.smul hξ) z ⟨hzΩ, hz⟩
    rwa [inter_comm, contDiffWithinAt_inter (Ω.isOpen.mem_nhds hzΩ)] at h
  · have h0 : (fun z ↦ χ z • ξ z) =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1
        fun h ↦ hzΩ (χ.tsupport_subset h)] with w hw
      simp [hw]
    exact (contDiffAt_const.congr_of_eventuallyEq h0).contDiffWithinAt

private theorem hasCompactSupport_smul (χ : 𝓓(Ω, ℂ)) :
    HasCompactSupport (fun z ↦ χ z • ξ z) :=
  χ.hasCompactSupport.smul_right

include hξ hη in
/-- Off the real axis, the integrand of the weak equation is the Cauchy–Riemann operator of the
product `χ ξ` minus `2 χ η`. -/
private theorem lineDeriv_add_I_mul_smul_eq (χ : 𝓓(Ω, ℂ)) {z : ℂ} (hz : 0 < z.im) :
    (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z =
      (fderiv ℝ (fun z ↦ χ z • ξ z) z 1 + I • fderiv ℝ (fun z ↦ χ z • ξ z) z I) -
        (2 : ℂ) • (χ z • η z) := by
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · have hχd : DifferentiableAt ℝ (χ : ℂ → ℂ) z := χ.contDiff.differentiable (by simp) z
    have hξd : DifferentiableAt ℝ ξ z :=
      (hξ.differentiableOn one_ne_zero).differentiableAt (inter_im_nonneg_mem_nhds hzΩ hz)
    have hη' := hη z hzΩ hz
    rw [conjWirtingerDeriv_apply] at hη'
    have hfd : HasFDerivAt (fun z ↦ χ z • ξ z)
        (χ z • fderiv ℝ ξ z + (fderiv ℝ (χ : ℂ → ℂ) z).smulRight (ξ z)) z :=
      hχd.hasFDerivAt.smul hξd.hasFDerivAt
    rw [hfd.fderiv, hχd.lineDeriv_eq_fderiv,
      hχd.lineDeriv_eq_fderiv, ← hη']
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_one]
    module
  · have ht : z ∉ tsupport (χ : ℂ → ℂ) := fun h ↦ hzΩ (χ.tsupport_subset h)
    have ht' : z ∉ tsupport (fun z ↦ χ z • ξ z) := fun h ↦
      ht (tsupport_smul_subset_left (fun z ↦ χ z) ξ h)
    simp [lineDeriv_of_notMem_tsupport ht, fderiv_of_notMem_tsupport ℝ ht',
      image_eq_zero_of_notMem_tsupport ht]

include hξ hη in
/-- **Integration by parts on the closed upper half-plane, with its boundary term.** For `ξ` that
is `C¹` up to the real axis on `Ω ∩ {0 ≤ im}` with `\bar∂ξ = η` off the axis, and a smooth complex
test function `χ` compactly supported in `Ω`,
`∫_{0 ≤ t} (∂_s χ + i ∂_t χ) ξ = -2 ∫_{0 ≤ t} χ η - i ∫_ℝ χ(s) ξ(s) ds`. -/
theorem setIntegral_im_nonneg_lineDeriv_add_I_mul_smul_eq (χ : 𝓓(Ω, ℂ)) :
    ∫ z in {z : ℂ | 0 ≤ z.im},
        (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z =
      -(2 : ℂ) • (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z) - I • ∫ s : ℝ, χ s • ξ s := by
  by_cases hF : CompleteSpace F
  swap
  · simp only [integral_of_not_completeSpace hF, smul_zero, sub_zero]
  set f : ℂ → F := fun z ↦ χ z • ξ z
  have hf := contDiffOn_smul hξ χ
  have hfc : HasCompactSupport f := hasCompactSupport_smul χ
  have h1 := integrableOn_im_pos_fderiv_apply_of_contDiffOn hf hfc 1
  have hI := integrableOn_im_pos_fderiv_apply_of_contDiffOn hf hfc I
  have hL : IntegrableOn
      (fun z ↦ (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z)
      {z : ℂ | 0 < z.im} := by
    refine (integrableOn_im_nonneg_of_continuousOn χ ?_ fun z hz ↦ ?_).mono_set
      fun z (hz : 0 < z.im) ↦ le_of_lt hz
    · simp_rw [← TestFunction.lineDerivOp_apply]
      exact (((LineDeriv.lineDerivOp (1 : ℂ) χ).continuous.add
        (continuous_const.mul (LineDeriv.lineDerivOp I χ).continuous)).continuousOn).smul
          hξ.continuousOn
    · simp [lineDeriv_of_notMem_tsupport hz]
  have hIs : IntegrableOn (fun z ↦ I • fderiv ℝ f z I) {z : ℂ | 0 < z.im} := hI.smul I
  have hA : IntegrableOn (fun z ↦ fderiv ℝ f z 1 + I • fderiv ℝ f z I) {z : ℂ | 0 < z.im} :=
    h1.add hIs
  have hB : IntegrableOn (fun z ↦ χ z • η z) {z : ℂ | 0 < z.im} := by
    refine IntegrableOn.congr_fun ((hA.sub hL).smul ((2 : ℂ)⁻¹))
      (fun z (hz : 0 < z.im) ↦ ?_) measurableSet_im_pos
    simp only [Pi.sub_apply, Pi.smul_apply, lineDeriv_add_I_mul_smul_eq hξ hη χ hz]
    module
  have hB2 : IntegrableOn (fun z ↦ (2 : ℂ) • (χ z • η z)) {z : ℂ | 0 < z.im} := hB.smul 2
  have hae := setOf_le_im_ae_eq (0 : ℝ)
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae,
    setIntegral_congr_fun measurableSet_im_pos fun z hz ↦ lineDeriv_add_I_mul_smul_eq hξ hη χ hz,
    integral_sub hA hB2, integral_add h1 hIs, integral_smul, integral_smul,
    setIntegral_im_pos_fderiv_one_eq_zero_of_contDiffOn hf hfc,
    setIntegral_im_pos_fderiv_I_eq_neg_integral_of_contDiffOn hf hfc]
  module

variable [CompleteSpace F] [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F]

include hξ hη in
/-- **Classical solutions with real boundary values are weak solutions.** A map `ξ` that is `C¹`
up to the real axis on `Ω ∩ {0 ≤ im}`, solves `\bar∂ξ = η` at the points of `Ω` off the axis, and
takes real values on `Ω ∩ ℝ` (`star (ξ x) = ξ x`), is a weak solution of `\bar∂ξ = η` with real
boundary values. The values of `η` on the axis are irrelevant. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ (Ω : Set ℂ) → star (ξ x) = ξ x) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η := by
  have hm : MeasurableSet ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    Ω.isOpen.measurableSet.inter measurableSet_im_nonneg'
  have hD := hξ.continuousOn_fderivWithin
    (by rw [inter_comm]; exact (uniqueDiffOn_setOfPred_le_im 0).inter Ω.isOpen) le_rfl
  have hηc : ContinuousOn
      (fun z ↦ (2 : ℂ)⁻¹ • (fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z 1 +
        I • fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z I))
      ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    continuousOn_const.smul ((hD.clm_apply continuousOn_const).add
      (continuousOn_const.smul (hD.clm_apply continuousOn_const)))
  have hηae : (fun z ↦ (2 : ℂ)⁻¹ • (fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z 1 +
        I • fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z I)) =ᵐ[
      volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] η := by
    rw [EventuallyEq, ae_restrict_iff' hm]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_setOf_im_eq 0)] with z hz hzΩ
    have hz' : 0 < z.im := lt_of_le_of_ne hzΩ.2 (Ne.symm hz)
    rw [← hη z hzΩ.1 hz', conjWirtingerDeriv_apply, smul_eq_mul, mul_one,
      fderivWithin_of_mem_nhds (inter_im_nonneg_mem_nhds hzΩ.1 hz')]
  refine hasWeakConjWirtingerDerivRealBoundaryOn_iff.2 ⟨inferInstance,
    hξ.continuousOn.locallyIntegrableOn hm,
    (hηc.locallyIntegrableOn hm).congr hηae, fun χ hχ ↦ ?_⟩
  have hB : IsSelfAdjoint (∫ s : ℝ, χ s • ξ s) := by
    rw [IsSelfAdjoint, ← integral_star]
    congr 1
    funext s
    by_cases hs : (s : ℂ) ∈ (Ω : Set ℂ)
    · rw [star_smul, hreal s hs, Complex.star_def, conj_eq_iff_im.2 (hχ s)]
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hs (χ.tsupport_subset h)]
      simp
  rw [setIntegral_im_nonneg_lineDeriv_add_I_mul_smul_eq hξ hη χ, map_sub, realPart_I_smul,
    hB.imaginaryPart, realPart_smul]
  simp

end ClassicalSolution

/-! ### Checks -/

/-- **Check.** `z²` is holomorphic and real on the real axis, so it solves `\bar∂ξ = 0` weakly
with real boundary values on every open set. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_sq :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ z ^ 2) 0 := by
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn
    (((contDiff_id (𝕜 := ℂ)).pow 2).restrict_scalars ℝ).contDiffOn (fun z _ _ ↦ ?_) fun x _ ↦ ?_
  · simp
  · simp [conj_ofReal]

/-- **Check.** `z e^{-conj z}` solves `\bar∂ξ = -ξ`, that is `∂_s ξ + i ∂_t ξ + 2ξ = 0`, and is
real on the real axis, so it is a weak solution with real boundary values on every open set. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_mul_cexp_neg_conj :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ z * cexp (-conj z))
      fun z ↦ -(z * cexp (-conj z)) := by
  have hd : ContDiff ℝ 1 fun z : ℂ ↦ z * cexp (-conj z) := by
    simpa only [Complex.conjCLE_apply, id_eq] using contDiff_id.mul conjCLE.contDiff.neg.cexp
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn hd.contDiffOn
    (fun z _ _ ↦ conjWirtingerDeriv_mul_cexp_neg_conj z) fun x _ ↦ ?_
  rw [Complex.star_def, map_mul, ← Complex.exp_conj, map_neg, conj_conj, conj_ofReal]

end TauCeti
