/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Mixing

/-!
# Checks for mixing of actions along a filter

Checks for `TauCeti.MixingAlong` and `TauCeti.WeakMixingSMul`.

* Mixing along `⊥` is vacuous (`TauCeti.mixingAlong_bot`), so the theorems deducing ergodicity
  assume a nontrivial filter.
* Mixing along the principal filter `pure m₀` of an invariant measure forces `μ(B) ∈ {0, 1}` for
  every measurable `B`: testing `A = (m₀ • ·)⁻¹' B` gives `μ(B) = μ(B)²` by invariance. Since
  `pure m₀` is nontrivial, such a probability measure is weakly mixing.
-/

public section

open Filter MeasureTheory Set

namespace TauCeti.Examples.Mixing

variable {M X : Type*} [MeasurableSpace X] [SMul M X] {μ : Measure X}

/-- Every action is mixing along `⊥`, whatever the measure. -/
example : MixingAlong M X μ ⊥ := mixingAlong_bot

/-- Mixing along the principal filter `pure m₀` of an invariant measure forces every measurable
set to have real measure `0` or `1`. -/
theorem measureReal_eq_zero_or_one_of_mixingAlong_pure [MeasurableConstSMul M X]
    [SMulInvariantMeasure M X μ] {m₀ : M} (h : MixingAlong M X μ (pure m₀)) {B : Set X}
    (hB : MeasurableSet B) : μ.real B = 0 ∨ μ.real B = 1 := by
  have h1 := tendsto_nhds_unique (tendsto_pure_nhds _ m₀)
    (h.tendsto (hB.preimage (measurable_const_smul m₀)) hB)
  simp only [inter_self,
    (measurePreserving_smul m₀ μ).measureReal_preimage hB.nullMeasurableSet] at h1
  exact eq_zero_or_one_of_sq_eq_self (by rw [pow_two, ← h1])

/-- A probability measure invariant under an action mixing along `pure m₀` is weakly mixing. -/
example [MeasurableConstSMul M X] [IsProbabilityMeasure μ] [SMulInvariantMeasure M X μ] {m₀ : M}
    (h : MixingAlong M X μ (pure m₀)) : WeakMixingSMul M X μ :=
  h.weakMixingSMul

end TauCeti.Examples.Mixing
