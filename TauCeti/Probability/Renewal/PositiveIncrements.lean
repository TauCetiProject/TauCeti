/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.ConditionalProbability
public import TauCeti.Probability.Renewal.Equation

/-!
# Removing zero increments from a renewal law

For an interarrival law `μ` on the half-line, conditioning on a nonzero increment removes
zero-increment clusters. If `q = μ {0}ᶜ > 0`, the renewal measures satisfy

`(μ[|{0}ᶜ]).renewalMeasure = q • μ.renewalMeasure`.

Thus the original renewal measure is `q⁻¹` times that of the strictly positive gap law.
This identity holds as an equality of measures, including at zero and at every atom, and
requires no finite-mean or lattice hypothesis. In a lattice renewal process it accounts for
the zero-cluster factor when renewal masses are represented by return probabilities.

The proof uses uniqueness of the locally bounded renewal equation for the cumulative masses.
Conditioning removes the atom at zero from the convolution term, and multiplication by `q`
normalizes the forcing term back to one.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

open TauCeti.Probability

variable {μ : Measure ℝ≥0} [IsProbabilityMeasure μ]

/-- The cumulative renewal masses, after removing zero increments, are multiplied by the
probability of a positive increment. -/
private theorem renewalMeasure_cond_compl_zero_real_Iic (hμ : μ {0} < 1) (t : ℝ≥0) :
    (μ[|{0}ᶜ]).renewalMeasure.real (Iic t) =
      μ.real {0}ᶜ * μ.renewalMeasure.real (Iic t) := by
  let ν := μ[|{0}ᶜ]
  let q := μ.real {0}ᶜ
  have hν : IsProbabilityMeasure ν := isProbabilityMeasure_cond_compl_singleton hμ.ne
  have hν0 : ν {0} < 1 := by simp [ν]
  have := isLocallyFiniteMeasure_renewalMeasure μ hμ
  have := isLocallyFiniteMeasure_renewalMeasure ν hν0
  have hqeq : q = 1 - μ.real {0} := probReal_compl_eq_one_sub (measurableSet_singleton 0)
  have hq : 0 < q := by
    rw [hqeq]
    have hp : μ.real {0} < 1 := by
      simpa [measureReal_def] using
        (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.one_ne_top).2 hμ
    linarith
  -- The cumulative renewal mass solves the equation with constant forcing one.
  let u := renewalConv (fun _ ↦ (1 : ℝ)) μ.renewalMeasure
  have hu : Measurable u := measurable_renewalConv measurable_const _
  have hub : ∀ T, ∃ C, ∀ s ≤ T, |u s| ≤ C := fun T ↦
    ⟨μ.renewalMeasure.real (Iic T), fun s hs ↦ by
      simpa [u] using abs_renewalConv_le (h := fun _ ↦ (1 : ℝ)) (μ := μ.renewalMeasure) (C := 1)
        (fun _ _ ↦ by norm_num) measure_Iic_lt_top.ne hs⟩
  have hrec (s : ℝ≥0) : u s = 1 + renewalConv u μ s :=
    renewalConv_renewalMeasure_eq_add measurable_const (C := 1) (by simp)
  -- Conditioning subtracts exactly the atom's contribution at the current time.
  have hcond (s : ℝ≥0) : renewalConv u ν s =
      q⁻¹ * (renewalConv u μ s - μ.real {0} * u s) := by
    obtain ⟨C, hC⟩ := hub s
    have hint := integrableOn_Iic_sub hu hC (measure_ne_top μ _)
    simpa [ν, q, renewalConv_eq_integral_indicator, hqeq, smul_eq_mul] using
      (integral_cond_compl_singleton (a := (0 : ℝ≥0))
        ((integrable_indicator_iff measurableSet_Iic).2 hint))
  have hsol : q • u = (fun _ ↦ (1 : ℝ)) + renewalConv (q • u) ν := by
    rw [renewalConv_smul]
    ext s
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rw [hcond, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    rw [hqeq]
    nlinarith [hrec s]
  -- Uniqueness identifies the rescaled cumulative mass with that of the positive-gap law.
  have heq := eq_renewalConv_renewalMeasure (μ := ν) (g := q • u) measurable_const
    (fun _ ↦ ⟨1, by simp⟩) (measurable_const.smul hu)
    (fun T ↦ by
      obtain ⟨C, hC⟩ := hub T
      refine ⟨q * C, fun s hs ↦ ?_⟩
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hq] using
        mul_le_mul_of_nonneg_left (hC s hs) hq.le) hsol
  simpa [u, q] using (congrFun heq t).symm

/-- Removing the atom at zero from an interarrival law multiplies its renewal measure by
the probability of a positive increment. The equality includes zero-time clusters and atoms
at positive times, and allows infinite mean. -/
theorem renewalMeasure_cond_compl_zero (hμ : μ {0} < 1) :
    (μ[|{0}ᶜ]).renewalMeasure = μ {0}ᶜ • μ.renewalMeasure := by
  have := isProbabilityMeasure_cond_compl_singleton hμ.ne
  have hν0 : μ[|{0}ᶜ] {0} < 1 := by simp
  have := isLocallyFiniteMeasure_renewalMeasure μ hμ
  have := isLocallyFiniteMeasure_renewalMeasure μ[|{0}ᶜ] hν0
  have hmass (t : ℝ≥0) : (μ[|{0}ᶜ]).renewalMeasure (Iic t) =
      (μ {0}ᶜ • μ.renewalMeasure) (Iic t) := by
    apply (ENNReal.toReal_eq_toReal_iff' measure_Iic_lt_top.ne ?_).mp
    · simpa [measureReal_def] using renewalMeasure_cond_compl_zero_real_Iic hμ t
    · simp only [smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top (measure_ne_top μ _) measure_Iic_lt_top.ne
  -- The half-lines generate the Borel sets and admit a finite-mass countable cover.
  apply ext_of_generateFrom_of_iUnion (Set.range (Iic : ℝ≥0 → Set ℝ≥0))
    (fun n ↦ Iic (n : ℝ≥0))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic ℝ≥0)) isPiSystem_Iic
  · apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact mem_iUnion.2 ⟨n, hn⟩
  · intro n
    exact ⟨n, rfl⟩
  · intro n
    exact measure_Iic_lt_top.ne
  · rintro _ ⟨t, rfl⟩
    exact hmass t

/-- The original renewal measure is the renewal measure of its positive-gap law scaled by
the reciprocal probability of a positive gap. -/
theorem renewalMeasure_eq_inv_smul_cond_compl_zero (hμ : μ {0} < 1) :
    μ.renewalMeasure = (μ {0}ᶜ)⁻¹ • (μ[|{0}ᶜ]).renewalMeasure := by
  have hq : μ {0}ᶜ ≠ 0 := by
    rw [prob_compl_eq_one_sub (measurableSet_singleton 0)]
    exact (tsub_pos_of_lt hμ).ne'
  rw [renewalMeasure_cond_compl_zero hμ, smul_smul,
    ENNReal.inv_mul_cancel hq (measure_ne_top μ _), one_smul]

end MeasureTheory.Measure
