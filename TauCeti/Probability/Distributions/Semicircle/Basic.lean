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
support, mean, variance, and exponential-integrability domain. The affine realization is the
bridge to later density, cdf, quantile, and unit-ball coordinate formulas.

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
noncomputable instance isProbabilityMeasure_semicircleMeasure :
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
  refine subset_antisymm (Measure.support_subset_of_isClosed isClosed_Icc
    (ae_mem_Ioo_semicircleMeasure.mono fun _ hx ↦ Ioo_subset_Icc_self hx)) fun x hx ↦ ?_
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
  let y := (x + 1) / 2
  have hy : y ∈ Icc (0 : ℝ) 1 := by
    dsimp [y]
    constructor <;> linarith [hx.1, hx.2]
  have hySupport : y ∈ (betaMeasure (3 / 2) (3 / 2)).support := by
    rw [support_betaMeasure (show (0 : ℝ) < 3 / 2 by norm_num)
      (show (0 : ℝ) < 3 / 2 by norm_num)]
    exact hy
  have hpreOpen : IsOpen ((fun z : ℝ ↦ -1 + 2 * z) ⁻¹' V) := hVo.preimage (by fun_prop)
  have hyPre : y ∈ (fun z : ℝ ↦ -1 + 2 * z) ⁻¹' V := by
    change -1 + 2 * y ∈ V
    convert hxV using 1
    dsimp [y]
    ring
  rw [Measure.support_eq_forall_isOpen] at hySupport
  have hpos : 0 < betaMeasure (3 / 2) (3 / 2) ((fun z : ℝ ↦ -1 + 2 * z) ⁻¹' V) :=
    hySupport _ hyPre hpreOpen
  refine lt_of_lt_of_le ?_ (measure_mono hVU)
  rw [semicircleMeasure, Measure.map_apply (by fun_prop) hVo.measurableSet]
  exact hpos

/-- Every natural power is integrable against the semicircle law. -/
theorem integrable_pow_semicircleMeasure (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) semicircleMeasure := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [ae_mem_Ioo_semicircleMeasure] with x hx
  simpa only [norm_pow, Real.norm_eq_abs, norm_one] using
    pow_le_one₀ (abs_nonneg x) (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)

/-- The natural moments of the semicircle law, as the affine binomial expansion of the moments
of its beta realization. -/
theorem integral_pow_semicircleMeasure (n : ℕ) :
    ∫ x, x ^ n ∂semicircleMeasure =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (-1) ^ (n - k) * 2 ^ k *
        (Real.Gamma (3 / 2 + k) * Real.Gamma (3 / 2 + 3 / 2) /
          (Real.Gamma (3 / 2) * Real.Gamma (3 / 2 + 3 / 2 + k))) := by
  let μ := betaMeasure (3 / 2) (3 / 2)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have habs : Integrable (fun x : ℝ ↦ |x| ^ n) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    filter_upwards [ae_mem_Icc_betaMeasure (3 / 2) (3 / 2)] with x hx
    simpa [Real.norm_eq_abs] using
      pow_le_one₀ (abs_nonneg x)
        (abs_le.mpr ⟨(show (-1 : ℝ) ≤ 0 by norm_num).trans hx.1, hx.2⟩)
  have hmoment := moment_id_map_affine (μ := μ) (a := -1) (b := 2) habs
  simpa only [semicircleMeasure, moment, Pi.pow_apply, id_eq, μ,
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

end TauCeti.Probability
