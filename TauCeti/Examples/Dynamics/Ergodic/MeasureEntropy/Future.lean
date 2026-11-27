/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Dynamics.Ergodic.MeasureEntropy.Bernoulli
public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Future

/-!
# Worked example: the future formula for the fair Bernoulli shift

For the fair Bernoulli shift and the coordinate label `x ↦ x 0`, the label is independent of its
future, so every future conditional entropy is `log 2`, and the conditional entropy of `x 0` given
the whole future `σ(x 1, x 2, …)` is the entropy rate `log 2`.
-/

public section

open MeasureTheory Real TauCeti TauCeti.Probability
open scoped ENNReal

namespace TauCeti.MeasureEntropyExamples

/-- **Check.** For the fair Bernoulli shift every future conditional entropy of the coordinate
label is `log 2`: `H(x 0 | x 1, …, x n) = log 2`. -/
theorem conditionalPartitionEntropy_future_fairBernoulli (n : ℕ) :
    conditionalPartitionEntropy fairBernoulli coordZero
      (fun x ↦ iteratedPartitionLabel (shift Bool) coordZero n (shift Bool x)) =
        ENNReal.ofReal (log 2) := by
  have h := countablePartitionEntropy_iteratedPartitionLabel_succ
    measurePreserving_shift_fairBernoulli measurable_coordZero n
  rw [countablePartitionEntropy_iteratedPartitionLabel_fairBernoulli,
    countablePartitionEntropy_iteratedPartitionLabel_fairBernoulli] at h
  have hsplit : ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * log 2) =
      ENNReal.ofReal (n * log 2) + ENNReal.ofReal (log 2) := by
    have h2 : 0 ≤ log 2 := log_nonneg one_le_two
    rw [← ENNReal.ofReal_add (by positivity) h2]
    push_cast
    ring_nf
  exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 (h.symm.trans hsplit)

/-- **Check.** For the fair Bernoulli shift the conditional entropy of the coordinate `x 0` given
the whole future `σ(x 1, x 2, …)` is `log 2`, the entropy rate. -/
theorem condExpPartitionEntropy_future_fairBernoulli :
    condExpPartitionEntropy fairBernoulli
      (⨆ j : ℕ, MeasurableSpace.comap (coordZero ∘ (shift Bool)^[j + 1]) inferInstance)
        coordZero = log 2 := by
  rw [← toReal_partitionEntropyRate_eq_condExpPartitionEntropy_future
    measurePreserving_shift_fairBernoulli measurable_coordZero, partitionEntropyRate_fairBernoulli,
    ENNReal.toReal_ofReal (log_nonneg one_le_two)]

end TauCeti.MeasureEntropyExamples
