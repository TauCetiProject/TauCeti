/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.PoissonBinomial.Basic
import TauCeti.Probability.Distributions.Binomial.StochasticOrder
import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Probability.Distributions.PoissonBinomial.Count

/-!
# Upper-tail comparison for Poisson-binomial laws

Increasing the success probabilities increases every upper tail of a Poisson-binomial law.
In particular, a binomial law dominates the count of independent trials when it has at least
as many trials and its common probability bounds all the original probabilities.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- Increasing each trial's success probability increases the upper tail at any natural cutoff.
This includes deterministic trials and empty families. -/
theorem poissonBinomialMeasure_real_Ici_mono {ι : Type*} [Fintype ι]
    {p q : ι → unitInterval} (hpq : p ≤ q) (k : ℕ) :
    (poissonBinomialMeasure p).real (Ici k) ≤ (poissonBinomialMeasure q).real (Ici k) := by
  let μ := Measure.pi fun _ : ι ↦ uniformMeasure 0 1
  have hmass (r : unitInterval) : (uniformMeasure 0 1).real (Iio (r : ℝ)) = r := by
    rw [measureReal_def, uniformMeasure_Iio zero_lt_one r.property.2]
    simp [ENNReal.toReal_ofReal r.property.1]
  have hlaw (r : ι → unitInterval) :
      HasLaw (fun x : ι → ℝ ↦ (Finset.univ.filter fun i ↦ x i < r i).card)
        (poissonBinomialMeasure r) μ := by
    simpa only [μ, mem_Iio, hmass, Subtype.coe_eta] using
      (hasLaw_card_filter_mem_pi (fun _ : ι ↦ uniformMeasure 0 1)
        (s := fun i ↦ Iio (r i : ℝ)) (fun _ ↦ measurableSet_Iio))
  simp only [Ici]
  rw [← (hlaw p).measureReal_eq (p := fun j ↦ k ≤ j) .of_discrete,
    ← (hlaw q).measureReal_eq (p := fun j ↦ k ≤ j) .of_discrete]
  exact measureReal_mono fun x hx ↦ le_trans hx <| Finset.card_le_card <|
    Finset.monotone_filter_right _ (fun i _ hi ↦ hi.trans_le (hpq i))

/-- If the number of trials is at most `n` and every success probability is at most `δ`,
the count's upper tail is bounded by that of `Bin(n, δ)`. -/
theorem poissonBinomialMeasure_real_Ici_le_binomial {ι : Type*} [Fintype ι]
    {p : ι → unitInterval} {δ : unitInterval} {n : ℕ}
    (hn : Fintype.card ι ≤ n) (hp : ∀ i, p i ≤ δ) (k : ℕ) :
    (poissonBinomialMeasure p).real (Ici k) ≤ (binomial n δ).real (Ici k) := by
  refine (poissonBinomialMeasure_real_Ici_mono (q := fun _ ↦ δ) hp k).trans ?_
  rw [poissonBinomialMeasure_const]
  cases k with
  | zero => simp
  | succ j =>
    have hc := cdf_map_cast_binomial_le_of_le_trials hn δ j
    rw [Measure.cdf_map_natCast _ (Nat.cast_nonneg _),
      Measure.cdf_map_natCast _ (Nat.cast_nonneg _), Nat.floor_natCast] at hc
    have hI : Ici (j + 1) = (Iic j)ᶜ := by ext; simp
    simpa only [hI, probReal_compl_eq_one_sub MeasurableSet.of_discrete, sub_le_sub_iff_left]
      using hc

end TauCeti.Probability
