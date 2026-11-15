/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.RelationalLaw.Basic
public import Mathlib.Analysis.Convex.Basic
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# The convex set of exchangeable relational laws

The exchangeable probability measures on relational configurations over `ℕ` form a convex set.
This unbundled presentation of `InfiniteExchangeableRelationalLaw` allows extremality to be
stated using `Set.extremePoints`. No countability assumption on the language is needed.

## Main definitions

* `TauCeti.Probability.exchangeableRelationalProbabilityMeasures` is the set of probability
  measures invariant under every permutation of the vertices.

## Main results

* `TauCeti.Probability.convex_exchangeableRelationalProbabilityMeasures` proves convexity.
* `TauCeti.Probability.InfiniteExchangeableRelationalLaw.law_mem` places a bundled law in this set.
-/

public section

open MeasureTheory Set
open _root_.FirstOrder (Language)
open scoped ENNReal

namespace TauCeti.Probability

open RelationalConfiguration

/-- The convex set of exchangeable probability measures on configurations of `L` over `ℕ`. -/
def exchangeableRelationalProbabilityMeasures (L : Language) :
    Set (Measure (RelationalConfiguration L ℕ)) :=
  {μ | (∀ σ : Equiv.Perm ℕ, μ.map (restrict ⇑σ) = μ) ∧ IsProbabilityMeasure μ}

/-- Membership is permutation invariance together with total mass one. -/
@[simp]
theorem mem_exchangeableRelationalProbabilityMeasures_iff {L : Language}
    {μ : Measure (RelationalConfiguration L ℕ)} :
    μ ∈ exchangeableRelationalProbabilityMeasures L ↔
      (∀ σ : Equiv.Perm ℕ, μ.map (restrict ⇑σ) = μ) ∧ IsProbabilityMeasure μ :=
  Iff.rfl

/-- Exchangeable probability measures on relational configurations form a convex set. -/
theorem convex_exchangeableRelationalProbabilityMeasures {L : Language} :
    Convex ℝ≥0∞ (exchangeableRelationalProbabilityMeasures L) := by
  rintro μ ⟨hμ, hμp⟩ ν ⟨hν, hνp⟩ a b _ _ hab
  have := hμp
  have := hνp
  refine ⟨fun σ => ?_, TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul hab μ ν⟩
  rw [Measure.map_add _ _ (measurable_restrict _),
    Measure.map_smul a (measurable_restrict _).aemeasurable,
    Measure.map_smul b (measurable_restrict _).aemeasurable, hμ σ, hν σ]

/-- The underlying measure of an exchangeable relational law belongs to the corresponding
convex set. -/
theorem InfiniteExchangeableRelationalLaw.law_mem {L : Language}
    (μ : InfiniteExchangeableRelationalLaw L) :
    μ.law ∈ exchangeableRelationalProbabilityMeasures L :=
  ⟨μ.exchangeable, μ.prob⟩

end TauCeti.Probability
