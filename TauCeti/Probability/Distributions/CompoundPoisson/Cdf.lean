/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.Probability.Cdf
import TauCeti.Probability.Distributions.Dirac
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Compound Poisson cumulative probabilities and masses

The cdf of a real compound Poisson law is the Poisson-weighted series of the cdfs of its
convolution powers. The empty sum contributes an atom of mass at least `exp (-r)` at zero;
nonempty sums may contribute further mass there. No density or absence of other atoms is assumed.

The same series computes native singleton masses and cumulative probabilities for natural and
integer jumps. Real casts use natural floor only at nonnegative cutoffs, and integer floor at
arbitrary cutoffs. The `HasSum` statements certify convergence of these nonnegative series.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, ch. XII, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [AddMonoid α]

/-- The Poisson-weighted series of convolution-power probabilities converges to the compound
probability of every measurable set. Its nonnegative terms also give absolute convergence. -/
theorem hasSum_compoundPoissonMeasure_real_apply (r : ℝ≥0) (μ : Measure α)
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) :
    HasSum (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
      (μ.convolutionPower n).real s) ((compoundPoissonMeasure r μ).real s) := by
  have hsum := (ENNReal.summable.hasSum_iff.mpr
    (compoundPoissonMeasure_apply_eq_tsum r μ hs).symm).toReal (measure_ne_top _ _)
  rw [← measureReal_def] at hsum
  convert hsum using 1
  funext n
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

/-- Native singleton masses are the absolutely convergent Poisson-weighted series of the
singleton masses of the convolution powers. This applies in particular to `ℕ` and `ℤ` jumps. -/
theorem compoundPoissonMeasure_real_singleton [MeasurableSingletonClass α]
    (r : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ] (k : α) :
    (compoundPoissonMeasure r μ).real {k} =
      ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
        (μ.convolutionPower n).real {k} :=
  (hasSum_compoundPoissonMeasure_real_apply r μ (measurableSet_singleton k)).tsum_eq.symm

/-- The probability of no jumps gives a lower bound for the atom at zero. Nonempty sums can
also vanish, so equality need not hold for a general jump law. -/
theorem exp_neg_le_compoundPoissonMeasure_real_singleton_zero [MeasurableSingletonClass α]
    (r : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ] :
    exp (-(r : ℝ)) ≤ (compoundPoissonMeasure r μ).real {0} := by
  have hsum := hasSum_compoundPoissonMeasure_real_apply r μ (measurableSet_singleton 0)
  rw [← hsum.tsum_eq]
  simpa using hsum.summable.le_tsum 0 (fun _ _ => by positivity)

/-- The Poisson-weighted convolution-power cdf series converges to the compound Poisson cdf,
including the zeroth convolution power, which is a point mass at zero. -/
theorem hasSum_cdf_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    HasSum (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
      cdf (μ.convolutionPower n) x) (cdf (compoundPoissonMeasure r μ) x) := by
  simpa only [cdf_eq_real] using
    hasSum_compoundPoissonMeasure_real_apply r μ (s := Iic x) measurableSet_Iic

/-- The compound Poisson cdf, with the empty-sum atom separated from the nonempty sums. -/
theorem cdf_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (compoundPoissonMeasure r μ) x = (if 0 ≤ x then exp (-(r : ℝ)) else 0) +
      ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1) !) *
        cdf (μ.convolutionPower (n + 1)) x := by
  rw [← (hasSum_cdf_compoundPoissonMeasure r μ x).tsum_eq,
    (hasSum_cdf_compoundPoissonMeasure r μ x).summable.tsum_eq_zero_add]
  simp [cdf_dirac, mul_ite]

/-- The cdf of the real cast of a natural-valued compound Poisson law. The negative branch is
taken before applying natural floor. -/
theorem cdf_map_natCast_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf ((compoundPoissonMeasure r μ).map (Nat.cast : ℕ → ℝ)) x =
      if 0 ≤ x then
        ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
          (μ.convolutionPower n).real (Iic ⌊x⌋₊)
      else 0 := by
  split_ifs with hx
  · rw [Measure.cdf_map_natCast _ hx]
    exact (hasSum_compoundPoissonMeasure_real_apply r μ measurableSet_Iic).tsum_eq.symm
  · exact Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)

/-- The cdf of the real cast of an integer-valued compound Poisson law, using integer floor
also for negative cutoffs. -/
theorem cdf_map_intCast_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℤ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf ((compoundPoissonMeasure r μ).map (Int.cast : ℤ → ℝ)) x =
      ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
        (μ.convolutionPower n).real (Iic ⌊x⌋) := by
  rw [Measure.cdf_map_intCast]
  exact (hasSum_compoundPoissonMeasure_real_apply r μ measurableSet_Iic).tsum_eq.symm

end TauCeti.Probability
