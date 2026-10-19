/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.MeasureTheory.Measure.Mixture.Basic
public import TauCeti.Probability.Density

/-!
# Probability mixtures

This file supplies distribution-level formulas for measures mixed through kernels.  Cumulative
distribution functions, moment-generating functions, and characteristic functions are the
corresponding integrals of the component quantities under their natural hypotheses.  It also
connects a jointly measurable family of component densities to `HasPDF` and the Radon--Nikodym
derivative of the mixed law.

The density results allow the component presentation to hold only almost everywhere for the
mixing measure.  This is useful for kernels whose values away from the valid parameter set are an
arbitrary measurable extension.

## Main results

* `ProbabilityTheory.Kernel.cdf_comp` computes the cdf of a real-valued probability mixture.
* `ProbabilityTheory.Kernel.mem_integrableExpSet_comp_iff` characterizes the exact exponential
  integrability domain by an iterated nonnegative integral.
* `ProbabilityTheory.Kernel.mgf_comp`, `ProbabilityTheory.Kernel.cgf_comp`, and
  `ProbabilityTheory.Kernel.charFun_comp` express its transforms in terms of the components.
* `TauCeti.Probability.hasPDF_of_hasLaw_bind_withDensity` gives the density interface for a random
  variable whose law is a mixture of densities.
* `MeasureTheory.Measure.rnDeriv_bind_withDensity` identifies the corresponding
  Radon--Nikodym derivative.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {A : Type*} [MeasurableSpace A]

/-- The cdf of a mixture of real probability laws is the integral of their cdfs. -/
theorem cdf_comp (kappa : Kernel A ℝ) [IsMarkovKernel kappa]
    (rho : Measure A) [IsProbabilityMeasure rho] (x : ℝ) :
    cdf (kappa ∘ₘ rho) x = ∫ a, cdf (kappa a) x ∂rho := by
  rw [cdf_eq_real, measureReal_def,
    Measure.bind_apply measurableSet_Iic kappa.aemeasurable,
    ← integral_toReal (kappa.measurable_coe measurableSet_Iic).aemeasurable
      (ae_of_all rho fun a ↦ measure_lt_top (kappa a) (Iic x))]
  simp_rw [← measureReal_def, cdf_eq_real]

/-- Exponential integrability under a mixture is equivalent to finiteness of the iterated
nonnegative exponential integral.  This formulation remains meaningful before passing to real
mgfs and records the exact integrability domain without relying on totalized real integration. -/
theorem mem_integrableExpSet_comp_iff (kappa : Kernel A ℝ) (rho : Measure A) (t : ℝ) :
    t ∈ integrableExpSet id (kappa ∘ₘ rho) ↔
      (∫⁻ a, ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂kappa a ∂rho) < ∞ := by
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq]
  constructor
  · intro h
    rw [← Measure.lintegral_bind kappa.aemeasurable (by fun_prop)]
    exact h.lintegral_lt_top
  · intro h
    refine ⟨(by fun_prop), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
    rw [Measure.lintegral_bind kappa.aemeasurable (by fun_prop)]
    exact h

/-- On its integrability domain, the mgf of a mixture is the integral of the component mgfs. -/
theorem mgf_comp (kappa : Kernel A ℝ) (rho : Measure A) (t : ℝ)
    (ht : t ∈ integrableExpSet id (kappa ∘ₘ rho)) :
    mgf id (kappa ∘ₘ rho) t = ∫ a, mgf id (kappa a) t ∂rho := by
  unfold ProbabilityTheory.mgf
  rw [Measure.comp_eq_comp_const_apply] at ht ⊢
  rw [integral_comp (κ := Kernel.const Unit rho) (η := kappa) (a := ()) ht,
    Kernel.const_apply]

/-- The cgf of a mixture is the logarithm of the integral of the component mgfs, rather than the
integral of their cgfs. -/
theorem cgf_comp (kappa : Kernel A ℝ) (rho : Measure A) (t : ℝ)
    (ht : t ∈ integrableExpSet id (kappa ∘ₘ rho)) :
    cgf id (kappa ∘ₘ rho) t = Real.log (∫ a, mgf id (kappa a) t ∂rho) := by
  rw [cgf, mgf_comp kappa rho t ht]

/-- The characteristic function of a mixture is the integral of the component characteristic
functions. -/
theorem charFun_comp (kappa : Kernel A ℝ) [IsFiniteKernel kappa]
    (rho : Measure A) [IsFiniteMeasure rho] (t : ℝ) :
    charFun (kappa ∘ₘ rho) t = ∫ a, charFun (kappa a) t ∂rho := by
  have hInt : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) (kappa ∘ₘ rho) :=
    (integrable_const (1 : ℂ)).mono (by fun_prop) <| by
      filter_upwards with x
      simp [← Complex.ofReal_mul]
  rw [charFun_apply_real, Measure.comp_eq_comp_const_apply]
  rw [Measure.comp_eq_comp_const_apply] at hInt
  rw [integral_comp (κ := Kernel.const Unit rho) (η := kappa) (a := ()) hInt,
    Kernel.const_apply]
  simp_rw [charFun_apply_real]

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {rho : Measure A} {nu : Measure B} {K : A → Measure B} {f : A → B → ℝ≥0∞}

/-- The Radon--Nikodym derivative of a mixture of densities is the pointwise integral of the
component densities. -/
theorem rnDeriv_bind_withDensity [SFinite rho] [SigmaFinite nu]
    (hf : Measurable f.uncurry) (hKf : K =ᵐ[rho] fun a ↦ nu.withDensity (f a)) :
    (rho.bind K).rnDeriv nu =ᵐ[nu] fun b ↦ ∫⁻ a, f a b ∂rho := by
  rw [bind_eq_withDensity_of_ae_eq rho nu hf hKf]
  exact rnDeriv_withDensity nu hf.lintegral_prod_left

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {Omega A B : Type*} [MeasurableSpace Omega] [MeasurableSpace A] [MeasurableSpace B]
  {P : Measure Omega} {rho : Measure A} {nu : Measure B} {K : A → Measure B}
  {f : A → B → ℝ≥0∞} {X : Omega → B}

/-- A random variable whose law is a mixture of jointly measurable component densities has the
integrated component density. -/
theorem hasPDF_of_hasLaw_bind_withDensity [SFinite rho] [SFinite nu]
    (hf : Measurable f.uncurry) (hKf : K =ᵐ[rho] fun a ↦ nu.withDensity (f a))
    (hX : HasLaw X (rho.bind K) P) : HasPDF X P nu := by
  apply hasPDF_of_hasLaw_withDensity (f := fun b ↦ ∫⁻ a, f a b ∂rho)
    hf.lintegral_prod_left.aemeasurable
  rwa [← Measure.bind_eq_withDensity_of_ae_eq rho nu hf hKf]

/-- The pdf selected by Mathlib for a mixture of component densities agrees almost everywhere
with their pointwise integral. -/
theorem pdf_eq_of_hasLaw_bind_withDensity [SFinite rho] [SigmaFinite nu]
    (hf : Measurable f.uncurry) (hKf : K =ᵐ[rho] fun a ↦ nu.withDensity (f a))
    (hX : HasLaw X (rho.bind K) P) :
    pdf X P nu =ᵐ[nu] fun b ↦ ∫⁻ a, f a b ∂rho := by
  apply pdf_eq_of_hasLaw_withDensity (f := fun b ↦ ∫⁻ a, f a b ∂rho)
    hf.lintegral_prod_left.aemeasurable
  rwa [← Measure.bind_eq_withDensity_of_ae_eq rho nu hf hKf]

end TauCeti.Probability
