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

This file supplies distribution-level formulas for mixtures of measurable families of measures.
Cumulative distribution functions, moment-generating functions, and characteristic functions are
the corresponding integrals of the component quantities under their natural hypotheses.  It also
connects a jointly measurable family of component densities to `HasPDF`.

The density results allow the component presentation to hold only almost everywhere for the
mixing measure.  This is useful for kernels whose values away from the valid parameter set are an
arbitrary measurable extension.

## Main results

* `MeasureTheory.Measure.cdf_bind` computes the cdf of a real-valued probability mixture whose
  components are probability measures almost everywhere.
* `ProbabilityTheory.Kernel.mem_integrableExpSet_comp_iff` characterizes the exact exponential
  integrability domain by an iterated nonnegative integral.
* `ProbabilityTheory.Kernel.mgf_comp`, `ProbabilityTheory.Kernel.cgf_comp`, and
  `ProbabilityTheory.Kernel.charFun_comp` express its transforms in terms of the components.
* `MeasureTheory.Measure.charFun_bind` gives characteristic-function linearity under almost
  everywhere component hypotheses.
* `TauCeti.Probability.hasPDF_of_hasLaw_bind_withDensity` gives the density interface for a random
  variable whose law is a mixture of densities.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace MeasureTheory.Measure

variable {A : Type*} [MeasurableSpace A]

/-- The cdf of a mixture of real probability laws is the integral of their cdfs. -/
theorem cdf_bind (rho : Measure A) [IsProbabilityMeasure rho]
    (K : A → Measure ℝ) (hK : AEMeasurable K rho)
    (hprob : ∀ᵐ a ∂rho, IsProbabilityMeasure (K a)) (x : ℝ) :
    cdf (rho.bind K) x = ∫ a, cdf (K a) x ∂rho := by
  let _ : IsProbabilityMeasure (rho.bind K) := isProbabilityMeasure_bind hK hprob
  rw [cdf_eq_real, measureReal_def, bind_apply measurableSet_Iic hK,
    ← integral_toReal (f := fun a ↦ K a (Iic x))
      ((Measure.measurable_coe measurableSet_Iic).comp_aemeasurable hK)
      (hprob.mono fun a ha ↦ by
        let _ := ha
        exact measure_lt_top (K a) (Iic x))]
  apply integral_congr_ae
  filter_upwards [hprob] with a ha
  let _ := ha
  rw [← measureReal_def, cdf_eq_real]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The characteristic function of a probability mixture is the integral of the component
characteristic functions when the components are probability measures almost everywhere. -/
theorem charFun_bind (rho : Measure A) [IsProbabilityMeasure rho]
    (K : A → Measure E) (hK : AEMeasurable K rho)
    (hprob : ∀ᵐ a ∂rho, IsProbabilityMeasure (K a)) (t : E) :
    charFun (rho.bind K) t = ∫ a, charFun (K a) t ∂rho := by
  let _ : IsProbabilityMeasure (rho.bind K) := isProbabilityMeasure_bind hK hprob
  have hInt : Integrable (fun x : E ↦ Complex.exp (inner ℝ x t * Complex.I)) (rho.bind K) :=
    (integrable_const (1 : ℂ)).mono (by fun_prop) <| by
      filter_upwards with x
      simp
  rw [charFun_apply, integral_bind rho hK hInt]
  simp_rw [charFun_apply]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {A : Type*} [MeasurableSpace A]

/-- The cdf of a mixture of real probability laws is the integral of their cdfs. -/
theorem cdf_comp (kappa : Kernel A ℝ) [IsMarkovKernel kappa]
    (rho : Measure A) [IsProbabilityMeasure rho] (x : ℝ) :
    cdf (kappa ∘ₘ rho) x = ∫ a, cdf (kappa a) x ∂rho := by
  exact Measure.cdf_bind rho kappa kappa.aemeasurable
    (ae_of_all rho fun _ ↦ inferInstance) x

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
  exact Measure.integral_bind rho kappa.aemeasurable ht

/-- The cgf of a mixture is the logarithm of the integral of the component mgfs, rather than the
integral of their cgfs. -/
theorem cgf_comp (kappa : Kernel A ℝ) (rho : Measure A) (t : ℝ)
    (ht : t ∈ integrableExpSet id (kappa ∘ₘ rho)) :
    cgf id (kappa ∘ₘ rho) t = Real.log (∫ a, mgf id (kappa a) t ∂rho) := by
  rw [cgf, mgf_comp kappa rho t ht]

/-- The characteristic function of a finite mixture on a real inner product space is the integral
of the component characteristic functions. -/
theorem charFun_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (kappa : Kernel A E) [IsFiniteKernel kappa]
    (rho : Measure A) [IsFiniteMeasure rho] (t : E) :
    charFun (kappa ∘ₘ rho) t = ∫ a, charFun (kappa a) t ∂rho := by
  have hInt : Integrable (fun x : E ↦ Complex.exp (inner ℝ x t * Complex.I)) (kappa ∘ₘ rho) :=
    (integrable_const (1 : ℂ)).mono (by fun_prop) <| by
      filter_upwards with x
      simp
  rw [charFun_apply, Measure.integral_bind rho kappa.aemeasurable hInt]
  simp_rw [charFun_apply]

end ProbabilityTheory.Kernel

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
