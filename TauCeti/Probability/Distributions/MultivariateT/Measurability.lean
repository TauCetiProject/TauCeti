/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateT.Basic
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Parameter measurability of multivariate t laws

The multivariate t law is jointly measurable in its location, scale entries and real degrees
of freedom, for the Giry measurable structure on measures. This includes singular and zero
scales, empty coordinate types, and the zero measures assigned to invalid parameters.
Consequently, measurable parameter families can be used as kernels; restricting to positive
degrees and positive semidefinite scales gives probability kernels.

The proof uses the Gaussian--chi-squared construction and the general measurability theorem
for a jointly varying probability measure and measurable pushforward map.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full totalized multivariate t family is jointly measurable in its location, scale
entries and degrees of freedom. No validity or nonsingularity assumption is needed. -/
@[fun_prop]
theorem measurable_multivariateTMeasure :
    Measurable fun p : EuclideanSpace ℝ ι × (ι → ι → ℝ) × ℝ =>
      multivariateTMeasure p.1 (Matrix.of p.2.1) p.2.2 := by
  classical
  -- Absolute degrees provide probability measures at every parameter, including outside
  -- the valid set. On the valid set they agree with the original chi-squared factor.
  have hG : Measurable fun S : ι → ι → ℝ =>
      (⟨multivariateGaussian (0 : EuclideanSpace ℝ ι) (Matrix.of S), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ ι)) :=
    (measurable_multivariateGaussian.comp (measurable_const.prodMk measurable_id)).subtype_mk
  have hV : Measurable fun ν : ℝ =>
      (⟨chiSquaredMeasure |ν|, isProbabilityMeasure_chiSquaredMeasure (abs_nonneg ν)⟩ :
        ProbabilityMeasure ℝ) :=
    (measurable_chiSquaredMeasure.comp (by fun_prop)).subtype_mk
  have hprod : Measurable fun p : EuclideanSpace ℝ ι × (ι → ι → ℝ) × ℝ =>
      (⟨(multivariateGaussian 0 (Matrix.of p.2.1)).prod (chiSquaredMeasure |p.2.2|), by
        let _ := isProbabilityMeasure_chiSquaredMeasure (abs_nonneg p.2.2)
        infer_instance⟩ : ProbabilityMeasure (EuclideanSpace ℝ ι × ℝ)) :=
    (ProbabilityMeasure.measurable_fun_prod.comp
      ((hG.comp measurable_snd.fst).prodMk (hV.comp measurable_snd.snd))).subtype_mk
  have hmap := TauCeti.MeasureTheory.measurable_probabilityMeasure_map_of_measurable_uncurry
    (f := fun (p : EuclideanSpace ℝ ι × (ι → ι → ℝ) × ℝ)
      (z : EuclideanSpace ℝ ι × ℝ) => p.1 + √(p.2.2 / z.2) • z.1) (by fun_prop)
  have hmix : Measurable fun p : EuclideanSpace ℝ ι × (ι → ι → ℝ) × ℝ =>
      ((multivariateGaussian 0 (Matrix.of p.2.1)).prod (chiSquaredMeasure |p.2.2|)).map
        (fun z => p.1 + √(p.2.2 / z.2) • z.1) :=
    measurable_subtype_coe.comp (hmap.comp (hprod.prodMk measurable_id))
  have hvalid : MeasurableSet {p : EuclideanSpace ℝ ι × (ι → ι → ℝ) × ℝ |
      0 < p.2.2 ∧ (Matrix.of p.2.1).PosSemidef} :=
    (measurableSet_lt measurable_const measurable_snd.snd).inter
      ((Matrix.posSemidef_is_closed (n := ι) (𝕜 := ℝ)).measurableSet.preimage
        measurable_snd.fst)
  have h : Measurable fun p : EuclideanSpace ℝ ι × (ι → ι → ℝ) × ℝ =>
      if 0 < p.2.2 ∧ (Matrix.of p.2.1).PosSemidef then
        ((multivariateGaussian 0 (Matrix.of p.2.1)).prod (chiSquaredMeasure |p.2.2|)).map
          (fun z => p.1 + √(p.2.2 / z.2) • z.1)
      else 0 :=
    Measurable.ite hvalid hmix measurable_const
  convert h using 1
  funext p
  by_cases hp : 0 < p.2.2 ∧ (Matrix.of p.2.1).PosSemidef
  · simp [multivariateTMeasure_of_posSemidef p.1 hp.1 hp.2, hp, abs_of_pos hp.1]
  · rcases not_and_or.mp hp with hν | hS
    · simp [hp, multivariateTMeasure_of_nonpos _ _ (not_lt.mp hν)]
    · simp [hp, multivariateTMeasure_of_not_posSemidef _ _ hS]

end TauCeti.Probability
