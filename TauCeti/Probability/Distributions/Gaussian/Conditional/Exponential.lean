/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.CondExp
public import TauCeti.Probability.Distributions.Gaussian.Transforms

/-!
# Gaussian exponential moments with a random known coefficient

If a Gaussian variable `Y` is independent of a sigma algebra `m`, an
`m`-measurable coefficient `a` may be frozen when computing its exponential moment.
The unnormalized results require integrability of the resulting known exponential moment.
For normalized exponentials, any integrable `m`-measurable multiplier `X` is allowed,
without a height bound. These give one-step normalization for predictable grid likelihoods.

The conditional computation uses `TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep`
(the independence lemma). No Gaussian law is asserted for the product `a * Y`.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X a Y : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}

/-- A Gaussian exponential with known coefficient and multiplier is integrable when
its known exponential moment is integrable. -/
theorem integrable_mul_exp_of_indep_gaussian (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (ha : Measurable[m] a) (hY : Measurable Y) (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal μ v) P)
    (hi : Integrable (fun ω ↦ X ω * exp (μ * a ω + (v : ℝ) * a ω ^ 2 / 2)) P) :
    Integrable (fun ω ↦ X ω * exp (a ω * Y ω)) P := by
  have := hlaw.isProbabilityMeasure
  let f := fun z : (ℝ × ℝ) × ℝ ↦ z.1.1 * exp (z.1.2 * z.2)
  have hf : StronglyMeasurable f := by fun_prop
  have hpair := (hX.prodMk ha).mono hm le_rfl
  have hprod := map_restrict_prodMk_eq_prod_of_indep hm (hX.prodMk ha) hY hind
    MeasurableSet.univ
  simp only [Measure.restrict_univ, hlaw.map_eq] at hprod
  have hfi : Integrable f ((P.map (fun ω ↦ (X ω, a ω))).prod (gaussianReal μ v)) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun x ↦ (integrable_exp_mul_gaussianReal x.2).const_mul x.1
    · have heq (x : ℝ × ℝ) : (∫ y, ‖f (x, y)‖ ∂gaussianReal μ v) =
          |x.1 * exp (μ * x.2 + (v : ℝ) * x.2 ^ 2 / 2)| := by
        simp only [f, norm_mul, Real.norm_eq_abs, abs_exp, integral_const_mul, abs_mul]
        congr 1
        simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := μ) (v := v)) x.2
      simp_rw [heq]
      exact (integrable_map_measure (by fun_prop) hpair.aemeasurable).mpr hi.abs
  rw [← hprod, integrable_map_measure hf.aestronglyMeasurable
    (hpair.prodMk hY).aemeasurable] at hfi
  exact hfi

/-- **Conditional Gaussian exponential moment with a known multiplier.** Both the
coefficient and the multiplier are measurable in the conditioning sigma algebra, whereas
`Y` is independent of it, with mean `μ` and variance `v`. The resulting known
exponential moment must be integrable; no coefficient bound is required. -/
theorem condExp_mul_exp_of_indep_gaussian (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (ha : Measurable[m] a) (hY : Measurable Y) (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal μ v) P)
    (hi : Integrable (fun ω ↦ X ω * exp (μ * a ω + (v : ℝ) * a ω ^ 2 / 2)) P) :
    P[fun ω ↦ X ω * exp (a ω * Y ω) | m] =ᵐ[P]
      fun ω ↦ X ω * exp (μ * a ω + (v : ℝ) * a ω ^ 2 / 2) := by
  have := hlaw.isProbabilityMeasure
  have h := condExp_comp_prodMk_ae_eq_integral_of_indep hm (hX.prodMk ha) hY hind
    (f := fun z : (ℝ × ℝ) × ℝ ↦ z.1.1 * exp (z.1.2 * z.2))
    (by fun_prop) (integrable_mul_exp_of_indep_gaussian hm hX ha hY hind hlaw hi)
  have hi (b : ℝ) : ∫ y, exp (b * y) ∂gaussianReal μ v =
      exp (μ * b + (v : ℝ) * b ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := μ) (v := v)) b
  simpa only [hlaw.map_eq, integral_const_mul, hi] using h

/-- A normalized independent Gaussian exponential with a known coefficient preserves
integrability of any integrable known multiplier, without a coefficient bound. -/
theorem integrable_mul_exp_sub_of_indep_gaussian (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (ha : Measurable[m] a) (hY : Measurable Y) (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal μ v) P) (hi : Integrable X P) :
    Integrable (fun ω ↦ X ω *
      exp (a ω * Y ω - (μ * a ω + (v : ℝ) * a ω ^ 2 / 2))) P := by
  have hmX : Measurable[m] (fun ω ↦ X ω * exp (-(μ * a ω + (v : ℝ) * a ω ^ 2 / 2))) :=
    hX.mul (((ha.const_mul μ).add (((ha.pow_const 2).const_mul _).div_const 2)).neg.exp)
  have hiX : Integrable (fun ω ↦
      (X ω * exp (-(μ * a ω + (v : ℝ) * a ω ^ 2 / 2))) *
        exp (μ * a ω + (v : ℝ) * a ω ^ 2 / 2)) P := by
    simpa only [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one] using hi
  simpa only [mul_assoc, ← exp_add, neg_add_eq_sub] using
    integrable_mul_exp_of_indep_gaussian hm hmX ha hY hind hlaw hiX

/-- Multiplication by a normalized independent Gaussian exponential with known coefficient
leaves the conditional expectation of an integrable known multiplier unchanged. -/
theorem condExp_mul_exp_sub_of_indep_gaussian (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (ha : Measurable[m] a) (hY : Measurable Y) (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal μ v) P) (hi : Integrable X P) :
    P[fun ω ↦ X ω * exp (a ω * Y ω - (μ * a ω + (v : ℝ) * a ω ^ 2 / 2)) | m]
      =ᵐ[P] X := by
  have := hlaw.isProbabilityMeasure
  have h := condExp_comp_prodMk_ae_eq_integral_of_indep hm (hX.prodMk ha) hY hind
    (f := fun z : (ℝ × ℝ) × ℝ ↦
      z.1.1 * exp (z.1.2 * z.2 - (μ * z.1.2 + (v : ℝ) * z.1.2 ^ 2 / 2)))
    (by fun_prop) (integrable_mul_exp_sub_of_indep_gaussian hm hX ha hY hind hlaw hi)
  simpa only [hlaw.map_eq, integral_const_mul, integral_exp_mul_sub_gaussianReal,
    mul_one] using h

end TauCeti.Probability
