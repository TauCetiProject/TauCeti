/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.PoissonBinomial.Basic

/-!
# Counts of independent events

The number of independent coordinates belonging to prescribed measurable sets has a
Poisson-binomial law. Both the coordinate laws and the sets may vary. In particular, counting
real coordinates below a threshold supplies the distribution function of an order statistic
without requiring identical distributions or excluding atoms.

The construction uses Mathlib's `hasLaw_indicator_one_bernoulliMeasure` and the independent
Bernoulli-sum characterization `iIndepFun.hasLaw_sum_poissonBinomialMeasure`.

## References

* Y. H. Wang, “On the number of successes in independent trials”, *Statistica Sinica* 3 (1993),
  295–312.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace ProbabilityTheory

open TauCeti.Probability

/-- The number of independent coordinates belonging to their prescribed measurable sets has
the Poisson-binomial law with success probabilities given by the coordinate event masses.
The coordinate spaces, laws, and sets may all vary with the index. -/
theorem iIndepFun.hasLaw_card_filter_mem
    {ι Ω : Type*} {α : ι → Type*} [Fintype ι] [MeasurableSpace Ω]
    [∀ i, MeasurableSpace (α i)] {P : Measure Ω} {μ : ∀ i, Measure (α i)}
    [∀ i, IsProbabilityMeasure (μ i)] {X : ∀ i, Ω → α i}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P)
    {s : ∀ i, Set (α i)} [∀ i, DecidablePred (· ∈ s i)]
    (hs : ∀ i, MeasurableSet (s i)) :
    HasLaw (fun ω ↦ #{i | X i ω ∈ s i})
      (poissonBinomialMeasure fun i ↦ ⟨(μ i).real (s i), by simp⟩) P := by
  have hI := hindep.comp (fun i ↦ (s i).indicator (1 : α i → ℕ))
    (fun i ↦ measurable_one.indicator (hs i))
  have hlaw (i : ι) : HasLaw (fun ω ↦ (s i).indicator (1 : α i → ℕ) (X i ω))
      Ber((1 : ℕ), 0, ⟨(μ i).real (s i), by simp⟩) P :=
    (hasLaw_indicator_one_bernoulliMeasure (hs i).nullMeasurableSet).comp (hX i)
  refine (hI.hasLaw_sum_poissonBinomialMeasure hlaw).congr (ae_of_all _ fun ω ↦ ?_)
  simp [Set.indicator_apply]

end ProbabilityTheory

namespace TauCeti.Probability

/-- Under a product of probability laws, counting coordinates in prescribed measurable sets
gives the Poisson-binomial law of their event masses. Empty products give the count zero. -/
theorem hasLaw_card_filter_mem_pi
    {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {s : ∀ i, Set (α i)} [∀ i, DecidablePred (· ∈ s i)]
    (hs : ∀ i, MeasurableSet (s i)) :
    HasLaw (fun x ↦ #{i | x i ∈ s i})
      (poissonBinomialMeasure fun i ↦ ⟨(μ i).real (s i), by simp⟩) (Measure.pi μ) := by
  exact (iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id).hasLaw_card_filter_mem
    (fun i ↦ (measurePreserving_eval μ i).hasLaw) hs

end TauCeti.Probability
