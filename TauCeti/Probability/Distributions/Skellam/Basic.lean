/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.Poisson.Measurability
public import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The Skellam distribution

The Skellam law is the integer difference of independent Poisson counts. Its singleton masses
are convergent sums of products of Poisson masses; reflection exchanges the two rates.
The construction includes zero rates and is measurable jointly in both rates.

## References

* J. G. Skellam, *The frequency distribution of the difference between two Poisson variates
  belonging to different populations*, Journal of the Royal Statistical Society 109 (1946), 296.

The measure construction reuses Mathlib's `ProbabilityTheory.poissonMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability

/-- The integer difference of independent Poisson counts with the two specified rates. -/
def skellamMeasure (r₁ r₂ : ℝ≥0) : Measure ℤ :=
  ((poissonMeasure r₁).prod (poissonMeasure r₂)).map
    (fun z : ℕ × ℕ => (z.1 : ℤ) - (z.2 : ℤ))

/-- The defining product-measure construction of the Skellam law. -/
theorem skellamMeasure_def (r₁ r₂ : ℝ≥0) :
    skellamMeasure r₁ r₂ = ((poissonMeasure r₁).prod (poissonMeasure r₂)).map
      (fun z : ℕ × ℕ => (z.1 : ℤ) - (z.2 : ℤ)) := (rfl)

/-- Every pair of nonnegative rates defines a Skellam probability measure. -/
instance (r₁ r₂ : ℝ≥0) : IsProbabilityMeasure (skellamMeasure r₁ r₂) := by
  rw [skellamMeasure_def]
  infer_instance

/-- Reflection of a Skellam law exchanges its rates. -/
@[simp]
theorem map_neg_skellamMeasure (r₁ r₂ : ℝ≥0) :
    (skellamMeasure r₁ r₂).map Neg.neg = skellamMeasure r₂ r₁ := by
  rw [skellamMeasure_def, Measure.map_map (by fun_prop) (by fun_prop), skellamMeasure_def]
  conv_rhs => rw [← Measure.prod_swap]
  rw [Measure.map_map (by fun_prop) measurable_swap]
  congr 1
  funext z
  simp

/-- The mass of a nonnegative integer is a sum over the possible subtracted counts. -/
theorem skellamMeasure_singleton_natCast (r₁ r₂ : ℝ≥0) (k : ℕ) :
    skellamMeasure r₁ r₂ {(k : ℤ)} =
      ∑' j : ℕ, poissonMeasure r₁ {j + k} * poissonMeasure r₂ {j} := by
  rw [skellamMeasure_def, Measure.map_apply (by fun_prop) (by measurability),
    Measure.prod_apply_symm (by measurability), lintegral_countable']
  refine tsum_congr fun j => ?_
  have hpre : (fun n : ℕ => (n : ℤ) - (j : ℤ)) ⁻¹' {(k : ℤ)} = {j + k} := by
    ext n
    simp only [mem_preimage, mem_singleton_iff]
    omega
  simp only [preimage_preimage, hpre]

/-- Negative masses are obtained by exchanging the rates. This also holds at zero. -/
theorem skellamMeasure_singleton_neg (r₁ r₂ : ℝ≥0) (k : ℤ) :
    skellamMeasure r₁ r₂ {-k} = skellamMeasure r₂ r₁ {k} := by
  rw [← map_neg_skellamMeasure, Measure.map_apply (by fun_prop) (by measurability)]
  congr 1
  ext x
  simp

/-- The Skellam mass series, with its Poisson factors written explicitly. -/
theorem skellamMeasure_singleton_natCast_eq_tsum (r₁ r₂ : ℝ≥0) (k : ℕ) :
    skellamMeasure r₁ r₂ {(k : ℤ)} =
      ENNReal.ofReal (Real.exp (-(r₁ : ℝ) - r₂)) *
        ∑' j : ℕ, ENNReal.ofReal
          ((r₁ : ℝ) ^ (j + k) * (r₂ : ℝ) ^ j / ((j + k).factorial * j.factorial)) := by
  rw [skellamMeasure_singleton_natCast, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [poissonMeasure_singleton, poissonMeasure_singleton,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [sub_eq_add_neg, Real.exp_add]
  ring

/-- The real mass series converges absolutely to the singleton mass. -/
theorem hasSum_skellamMeasure_mass (r₁ r₂ : ℝ≥0) (k : ℕ) :
    HasSum (fun j : ℕ =>
      (Real.exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ (j + k) / (j + k).factorial) *
        (Real.exp (-(r₂ : ℝ)) * (r₂ : ℝ) ^ j / j.factorial))
      ((skellamMeasure r₁ r₂).real {(k : ℤ)}) := by
  have hsum := (ENNReal.summable.hasSum_iff.mpr
    (skellamMeasure_singleton_natCast r₁ r₂ k).symm).toReal (measure_ne_top _ _)
  simpa only [ENNReal.toReal_mul, ← measureReal_def, poissonMeasure_real_singleton] using hsum

/-- The real singleton mass as a Poisson-product series, uniformly for positive and negative
integers. The two natural offsets are the positive and negative parts of the integer. -/
theorem skellamMeasure_real_singleton_eq_tsum (r₁ r₂ : ℝ≥0) (k : ℤ) :
    (skellamMeasure r₁ r₂).real {k} =
      ∑' j : ℕ,
        (Real.exp (-(r₁ : ℝ)) * (r₁ : ℝ) ^ (j + k.toNat) / (j + k.toNat).factorial) *
        (Real.exp (-(r₂ : ℝ)) * (r₂ : ℝ) ^ (j + (-k).toNat) / (j + (-k).toNat).factorial) := by
  cases k with
  | ofNat n => simpa using (hasSum_skellamMeasure_mass r₁ r₂ n).tsum_eq.symm
  | negSucc n =>
    have hmass : (skellamMeasure r₁ r₂).real {Int.negSucc n} =
        (skellamMeasure r₂ r₁).real {((n + 1 : ℕ) : ℤ)} := by
      simp only [measureReal_def, Int.negSucc_eq, skellamMeasure_singleton_neg,
        Nat.cast_add, Nat.cast_one]
    rw [hmass]
    simpa [mul_comm] using (hasSum_skellamMeasure_mass r₂ r₁ (n + 1)).tsum_eq.symm

/-- Every integer has positive mass when both rates are positive. -/
theorem skellamMeasure_singleton_pos {r₁ r₂ : ℝ≥0} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (k : ℤ) : 0 < skellamMeasure r₁ r₂ {k} := by
  have hnat (s₁ s₂ : ℝ≥0) (h : 0 < s₁) (n : ℕ) :
      0 < skellamMeasure s₁ s₂ {(n : ℤ)} := by
    rw [skellamMeasure_singleton_natCast]
    apply lt_of_lt_of_le _ (ENNReal.le_tsum 0)
    simp only [zero_add, poissonMeasure_singleton, pow_zero, Nat.factorial_zero]
    have hs : (0 : ℝ) < s₁ := h
    positivity
  cases k with
  | ofNat n => exact hnat r₁ r₂ h₁ n
  | negSucc n =>
    rw [Int.negSucc_eq, skellamMeasure_singleton_neg]
    exact hnat r₂ r₁ h₂ (n + 1)

/-- Positive rates give full topological support on the integer carrier. -/
theorem support_skellamMeasure {r₁ r₂ : ℝ≥0} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    (skellamMeasure r₁ r₂).support = Set.univ := by
  ext k
  simp only [Set.mem_univ, iff_true, Measure.mem_support_iff_forall]
  intro U hU
  exact (skellamMeasure_singleton_pos h₁ h₂ k).trans_le
    (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- With zero second rate the Skellam law is the natural Poisson law cast to integers. -/
@[simp]
theorem skellamMeasure_zero_right (r : ℝ≥0) :
    skellamMeasure r 0 = (poissonMeasure r).map (Nat.cast : ℕ → ℤ) := by
  have hzero : poissonMeasure 0 = Measure.dirac 0 := by
    apply Measure.ext_of_singleton
    intro n
    cases n <;> simp [poissonMeasure_singleton, Measure.dirac_apply']
  rw [skellamMeasure_def, hzero, Measure.prod_dirac,
    Measure.map_map (by fun_prop) measurable_prodMk_right]
  rfl

/-- With zero first rate the law is the negative of an integer-valued Poisson count. -/
@[simp]
theorem skellamMeasure_zero_left (r : ℝ≥0) :
    skellamMeasure 0 r = (poissonMeasure r).map (fun n : ℕ => -(n : ℤ)) := by
  rw [← map_neg_skellamMeasure r 0, skellamMeasure_zero_right,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Both zero rates give the Dirac mass at zero. -/
@[simp high]
theorem skellamMeasure_zero_zero : skellamMeasure 0 0 = Measure.dirac 0 := by
  have hzero : poissonMeasure 0 = Measure.dirac 0 := by
    apply Measure.ext_of_singleton
    intro n
    cases n <;> simp [poissonMeasure_singleton, Measure.dirac_apply']
  rw [skellamMeasure_zero_right, hzero, Measure.map_dirac' (by fun_prop)]
  rfl

/-- Joint Giry measurability of the two-rate Skellam family. -/
@[fun_prop]
theorem measurable_skellamMeasure :
    Measurable fun r : ℝ≥0 × ℝ≥0 => skellamMeasure r.1 r.2 := by
  have hp : Measurable fun r : ℝ≥0 => (⟨poissonMeasure r, inferInstance⟩ :
      ProbabilityMeasure ℕ) := measurable_poissonMeasure.subtype_mk
  exact (Measure.measurable_map _ (by fun_prop)).comp
    (ProbabilityMeasure.measurable_fun_prod.comp
      ((hp.comp measurable_fst).prodMk (hp.comp measurable_snd)))

end TauCeti.Probability

namespace ProbabilityTheory.IndepFun

/-- Independent Poisson counts have a Skellam integer difference. -/
theorem hasLaw_sub_skellamMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℕ} {r₁ r₂ : ℝ≥0} (hXY : IndepFun X Y P)
    (hX : HasLaw X (poissonMeasure r₁) P) (hY : HasLaw Y (poissonMeasure r₂) P) :
    HasLaw (fun ω => (X ω : ℤ) - (Y ω : ℤ))
      (TauCeti.Probability.skellamMeasure r₁ r₂) P := by
  let _ := hX.isProbabilityMeasure
  exact (hasLaw_map (by fun_prop) : HasLaw
    (fun z : ℕ × ℕ => (z.1 : ℤ) - (z.2 : ℤ)) _ _).fun_comp (hXY.hasLaw_prod hX hY)

end ProbabilityTheory.IndepFun
