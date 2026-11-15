/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.Probability.Independence.ConvolutionPower

/-!
# Compound Poisson laws as random sums

A Poisson-distributed count, independent of an iid jump sequence, selects a prefix whose sum
has the compound Poisson law. The product-measure identity realizes this construction on
the space of a count and an infinite jump sequence. The random-variable theorem transfers
it to any probability space, requiring only almost-everywhere measurable jumps.

The jump law may be discrete, continuous, or singular, and need not have any moments.
Rate zero and the empty sum are included.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [AddCommMonoid α] [MeasurableAdd₂ α]

/-- The product-measure construction of a compound Poisson law: independently draw a Poisson
count and an iid jump sequence, and sum the prefix selected by the count. -/
@[simp]
theorem map_sum_range_prod_poissonMeasure (r : ℝ≥0) (μ : Measure α)
    [IsProbabilityMeasure μ] :
    ((poissonMeasure r).prod (Measure.infinitePi fun _ : ℕ => μ)).map
        (fun z => ∑ i ∈ Finset.range z.1, z.2 i) = compoundPoissonMeasure r μ := by
  rw [Measure.map_sum_range_prod_infinitePi, compoundPoissonMeasure_def]

end TauCeti.Probability

namespace ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [AddCommMonoid α]
  [MeasurableAdd₂ α] {P : Measure Ω} {μ : Measure α} {r : ℝ≥0}
  {X : ℕ → Ω → α} {N : Ω → ℕ}

/-- A Poisson number of iid jumps has a compound Poisson law when the count is independent
of the entire sequence. This includes zero intensity and needs no jump moments. -/
theorem iIndepFun.hasLaw_sum_range_compoundPoissonMeasure (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) μ P) (hN : HasLaw N (poissonMeasure r) P)
    (hNX : IndepFun N (fun ω i => X i ω) P) :
    HasLaw (fun ω => ∑ i ∈ Finset.range (N ω), X i ω)
      (TauCeti.Probability.compoundPoissonMeasure r μ) P := by
  rw [TauCeti.Probability.compoundPoissonMeasure_def]
  exact hindep.hasLaw_sum_range_bind hX hN hNX

end ProbabilityTheory
