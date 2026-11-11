/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# The Wigner semicircle distribution

The unit-radius semicircle distribution is the image of the beta distribution with shape
parameters `(3 / 2, 3 / 2)` under the affine map `x ↦ -1 + 2 * x`. This file develops the
measure-level construction and its elementary consequences: normalization, exact topological
support, the almost-sure carrier `(-1, 1)`, natural moments as a binomial expansion of beta
moments, mean, variance, and exponential-integrability domain.

This is the semicircle law of radius one: it is supported on `[-1, 1]` and has variance `1 / 4`.
Semicircle laws with other centres and variances, including the radius-two, variance-one law
`semicircleReal 0 1`, are built from it in
`TauCeti.Probability.Distributions.Semicircle.LocationScale`.

## Main definitions

* `semicircleMeasure`: the unit-radius semicircle law, the image of the beta `(3 / 2, 3 / 2)` law
  under `x ↦ -1 + 2 * x` (`semicircleMeasure_eq_map_betaMeasure`).

## Main results

* `isProbabilityMeasure_semicircleMeasure`: the semicircle law is a probability measure.
* `ae_mem_Ioo_semicircleMeasure`: it is carried by the open interval `(-1, 1)`.
* `support_semicircleMeasure`: its topological support is `[-1, 1]`.
* `integral_pow_semicircleMeasure`: its `n`-th moment, as the binomial expansion of the moments
  of the beta `(3 / 2, 3 / 2)` law.
* `integral_id_semicircleMeasure`, `variance_id_semicircleMeasure`: its mean is `0` and its
  variance is `1 / 4`.
* `integrableExpSet_id_semicircleMeasure`: every exponential moment is finite.
* `integrable_pow_semicircleMeasure`: every natural power is integrable.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The unit-radius Wigner semicircle law, as an affine image of a symmetric beta law. -/
def semicircleMeasure : Measure ℝ :=
  (betaMeasure (3 / 2) (3 / 2)).map fun x ↦ -1 + 2 * x

/-- The semicircle law is the affine image of the beta `(3 / 2, 3 / 2)` law. -/
theorem semicircleMeasure_eq_map_betaMeasure :
    semicircleMeasure = (betaMeasure (3 / 2) (3 / 2)).map fun x ↦ -1 + 2 * x :=
  (rfl)

/-- The semicircle law is a probability measure. -/
instance isProbabilityMeasure_semicircleMeasure :
    IsProbabilityMeasure semicircleMeasure := by
  rw [semicircleMeasure]
  let _ : IsProbabilityMeasure (betaMeasure (3 / 2) (3 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  infer_instance

/-- A semicircle variable lies almost everywhere in the open interval `(-1, 1)`. -/
theorem ae_mem_Ioo_semicircleMeasure : ∀ᵐ x ∂semicircleMeasure, x ∈ Ioo (-1 : ℝ) 1 := by
  rw [semicircleMeasure]
  apply (ae_map_iff (by fun_prop) measurableSet_Ioo).2
  filter_upwards [ae_mem_Ioo_betaMeasure (3 / 2) (3 / 2)] with x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The topological support of the unit-radius semicircle law is `[-1, 1]`. -/
@[simp]
theorem support_semicircleMeasure : semicircleMeasure.support = Icc (-1) 1 := by
  rw [semicircleMeasure, support_map_affine (by norm_num),
    support_betaMeasure (show (0 : ℝ) < 3 / 2 by norm_num)
      (show (0 : ℝ) < 3 / 2 by norm_num)]
  simp only [add_comm (-1 : ℝ), image_affine_Icc' (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The natural moments of the semicircle law, as the affine binomial expansion of the moments
of its beta realization. -/
theorem integral_pow_semicircleMeasure (n : ℕ) :
    ∫ x, x ^ n ∂semicircleMeasure =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (-1) ^ (n - k) * 2 ^ k *
        (Real.Gamma (3 / 2 + k) * 2 / (Real.Gamma (3 / 2) * (k + 2).factorial)) := by
  let μ := betaMeasure (3 / 2) (3 / 2)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have habs : Integrable (fun x : ℝ ↦ |x| ^ n) μ := by
    exact integrable_pow_abs_betaMeasure (show (0 : ℝ) < 3 / 2 by norm_num)
      (show (0 : ℝ) < 3 / 2 by norm_num) n
  have hΓ (k : ℕ) : Real.Gamma (3 / 2 + 3 / 2 + k) = (k + 2).factorial := by
    rw [show (3 / 2 + 3 / 2 + k : ℝ) = ((k + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have hΓ₀ : Real.Gamma (3 / 2 + 3 / 2) = 2 := by simp
  have hmoment := moment_id_map_affine (μ := μ) (a := -1) (b := 2) habs
  simpa only [semicircleMeasure, moment, Pi.pow_apply, id_eq, μ, hΓ, hΓ₀,
    integral_pow_betaMeasure (show (0 : ℝ) < 3 / 2 by norm_num)
      (show (0 : ℝ) < 3 / 2 by norm_num)] using hmoment

/-- The mean of the unit-radius semicircle law is zero. -/
@[simp]
theorem integral_id_semicircleMeasure : ∫ x, x ∂semicircleMeasure = 0 := by
  let μ := betaMeasure (3 / 2) (3 / 2)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hmem : MemLp id 2 μ :=
    memLp_of_bounded (ae_mem_Icc_betaMeasure (3 / 2) (3 / 2))
      measurable_id.aestronglyMeasurable 2
  rw [semicircleMeasure, integral_id_map_affine (μ := μ) (a := -1) (b := 2)
    (hmem.integrable one_le_two)]
  simp only [μ, integral_id_betaMeasure (show (0 : ℝ) < 3 / 2 by norm_num)
    (show (0 : ℝ) < 3 / 2 by norm_num)]
  norm_num

/-- The variance of the unit-radius semicircle law is one quarter. -/
@[simp]
theorem variance_id_semicircleMeasure : variance id semicircleMeasure = 1 / 4 := by
  let _ : IsProbabilityMeasure (betaMeasure (3 / 2) (3 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  rw [semicircleMeasure, variance_id_map_affine,
    variance_id_betaMeasure (show (0 : ℝ) < 3 / 2 by norm_num)
      (show (0 : ℝ) < 3 / 2 by norm_num)]
  norm_num

/-- Every exponential moment of the unit-radius semicircle law exists. -/
@[simp]
theorem integrableExpSet_id_semicircleMeasure :
    integrableExpSet id semicircleMeasure = univ := by
  rw [semicircleMeasure, integrableExpSet_id_map_affine,
    integrableExpSet_id_betaMeasure (show (0 : ℝ) < 3 / 2 by norm_num)
      (show (0 : ℝ) < 3 / 2 by norm_num)]
  simp

/-- Every natural power is integrable against the semicircle law. -/
theorem integrable_pow_semicircleMeasure (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) semicircleMeasure := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) _ n
  simp only [integrableExpSet_id_semicircleMeasure, interior_univ, mem_univ]

end TauCeti.Probability
