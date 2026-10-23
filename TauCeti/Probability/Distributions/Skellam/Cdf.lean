/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Skellam.Basic
public import TauCeti.Probability.Cdf

/-!
# Cumulative probabilities of Skellam laws

The cumulative mass of a difference of independent Poisson counts is a convergent series:
condition on the subtracted count and sum the first Poisson law through the resulting cutoff.
A negative cutoff contributes zero before natural-number conversion. The real-cast CDF uses
integer floor, so the formula also applies at negative real arguments. The equivalent bilateral
series sums the explicit singleton masses over all integers below the cutoff.

## References

* J. G. Skellam, *The frequency distribution of the difference between two Poisson variates
  belonging to different populations*, Journal of the Royal Statistical Society 109 (1946), 296.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace TauCeti.Probability

/-- The bilateral cumulative mass series over integers converges absolutely. Each integer
mass is expanded as its convergent Poisson-product series. -/
theorem hasSum_skellamMeasure_real_Iic_mass (r₁ r₂ : ℝ≥0) (k : ℤ) :
    HasSum (fun n : ℤ ↦ if n ≤ k then
      ∑' j : ℕ,
        (exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ (j + n.toNat) / (j + n.toNat).factorial) *
        (exp (-(r₂ : ℝ)) * (r₂ : ℝ) ^ (j + (-n).toNat) / (j + (-n).toNat).factorial)
      else 0) ((skellamMeasure r₁ r₂).real (Iic k)) := by
  have hmass := (skellamMeasure r₁ r₂).tsum_indicator_apply_singleton (Iic k)
    measurableSet_Iic
  have hsum := (ENNReal.summable.hasSum_iff.mpr hmass).toReal (measure_ne_top _ _)
  rw [← measureReal_def] at hsum
  convert hsum using 1
  funext n
  simp only [indicator_apply, mem_Iic]
  split_ifs <;> simp [← measureReal_def, skellamMeasure_real_singleton_eq_tsum]

/-- The cumulative Skellam series converges to the native cumulative mass. Its terms are
nonnegative, so this is also absolute convergence. The guard precedes natural conversion. -/
theorem hasSum_skellamMeasure_real_Iic (r₁ r₂ : ℝ≥0) (k : ℤ) :
    HasSum (fun j : ℕ ↦ (exp (-(r₂ : ℝ)) * (r₂ : ℝ) ^ j / j.factorial) *
      if 0 ≤ k + j then
        ∑ i ∈ Finset.range ((k + j).toNat + 1),
          exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ i / i.factorial
      else 0) ((skellamMeasure r₁ r₂).real (Iic k)) := by
  have hpre (j : ℕ) :
      (fun i : ℕ ↦ (i, j)) ⁻¹' (fun z : ℕ × ℕ ↦ (z.1 : ℤ) - z.2) ⁻¹' Iic k =
        if 0 ≤ k + j then Iic (k + j).toNat else ∅ := by
    split_ifs with hj <;> ext i <;>
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
    · omega
    · omega
  have hmass : skellamMeasure r₁ r₂ (Iic k) =
      ∑' j : ℕ, (if 0 ≤ k + j then poissonMeasure r₁ (Iic (k + j).toNat) else 0) *
        poissonMeasure r₂ {j} := by
    rw [skellamMeasure_def, Measure.map_apply (by fun_prop) measurableSet_Iic,
      Measure.prod_apply_symm (by measurability), lintegral_countable']
    refine tsum_congr fun j ↦ ?_
    rw [hpre]
    split_ifs <;> simp
  have hsum := (ENNReal.summable.hasSum_iff.mpr hmass.symm).toReal (measure_ne_top _ _)
  rw [← measureReal_def] at hsum
  convert hsum using 1
  funext j
  rw [ENNReal.toReal_mul, ← measureReal_def, poissonMeasure_real_singleton]
  split_ifs with hj
  · have hIic : (Iic (k + j).toNat : Set ℕ) =
        (Finset.range ((k + j).toNat + 1) : Set ℕ) := by
      ext i
      simp
    rw [← measureReal_def, hIic, ← sum_measureReal_singleton]
    simp_rw [poissonMeasure_real_singleton]
    exact mul_comm _ _
  · simp

/-- The cumulative mass is the sum of the absolutely convergent Poisson-conditioned series. -/
theorem skellamMeasure_real_Iic (r₁ r₂ : ℝ≥0) (k : ℤ) :
    (skellamMeasure r₁ r₂).real (Iic k) =
      ∑' j : ℕ, (exp (-(r₂ : ℝ)) * (r₂ : ℝ) ^ j / j.factorial) *
        if 0 ≤ k + j then
          ∑ i ∈ Finset.range ((k + j).toNat + 1),
            exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ i / i.factorial
        else 0 :=
  (hasSum_skellamMeasure_real_Iic r₁ r₂ k).tsum_eq.symm

/-- The real-cast Skellam CDF is the cumulative series through the integer floor of the cutoff. -/
theorem cdf_map_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) (x : ℝ) :
    cdf ((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)) x =
      ∑' j : ℕ, (exp (-(r₂ : ℝ)) * (r₂ : ℝ) ^ j / j.factorial) *
        if 0 ≤ ⌊x⌋ + j then
          ∑ i ∈ Finset.range ((⌊x⌋ + j).toNat + 1),
            exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ i / i.factorial
        else 0 := by
  rw [Measure.cdf_map_intCast, skellamMeasure_real_Iic]

/-- A positive subtracted rate gives positive cumulative mass at every integer cutoff. -/
theorem skellamMeasure_real_Iic_pos (r₁ : ℝ≥0) {r₂ : ℝ≥0} (h₂ : 0 < r₂) (k : ℤ) :
    0 < (skellamMeasure r₁ r₂).real (Iic k) := by
  rw [skellamMeasure_real_Iic]
  have hsum := (hasSum_skellamMeasure_real_Iic r₁ r₂ k).summable
  refine hsum.tsum_pos (fun j ↦ ?_) (-k).toNat ?_
  · split_ifs <;> positivity
  · have hk : 0 ≤ k + ((-k).toNat : ℤ) := by omega
    rw [ite_eq_left hk]
    apply mul_pos (by have : 0 < (r₂ : ℝ) := NNReal.coe_pos.mpr h₂; positivity)
    apply lt_of_lt_of_le (exp_pos (-(r₁ : ℝ)))
    simpa using (Finset.single_le_sum (f := fun i : ℕ ↦
      exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ i / i.factorial)
      (fun i _ ↦ by positivity) (Finset.mem_range.mpr (by omega :
        0 < (k + ((-k).toNat : ℤ)).toNat + 1)))

/-- Reflection exchanges the rates; the predecessor accounts for the atom at the cutoff. -/
theorem skellamMeasure_real_Iic_eq_one_sub (r₁ r₂ : ℝ≥0) (k : ℤ) :
    (skellamMeasure r₁ r₂).real (Iic k) =
      1 - (skellamMeasure r₂ r₁).real (Iic (-k - 1)) := by
  have hpre : (Neg.neg : ℤ → ℤ) ⁻¹' Iic (-k - 1) = (Iic k)ᶜ := by
    ext j
    simp only [mem_preimage, mem_Iic, mem_compl_iff, not_le]
    omega
  rw [← map_neg_skellamMeasure r₁ r₂,
    map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
    measureReal_compl measurableSet_Iic, probReal_univ]
  ring

/-- A positive first rate leaves positive mass above every integer cutoff. -/
theorem skellamMeasure_real_Iic_lt_one {r₁ : ℝ≥0} (h₁ : 0 < r₁) (r₂ : ℝ≥0) (k : ℤ) :
    (skellamMeasure r₁ r₂).real (Iic k) < 1 := by
  rw [skellamMeasure_real_Iic_eq_one_sub]
  exact sub_lt_self _ (skellamMeasure_real_Iic_pos r₂ h₁ _)

end TauCeti.Probability
