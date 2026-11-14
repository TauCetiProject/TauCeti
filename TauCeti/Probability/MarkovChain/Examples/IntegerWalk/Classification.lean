/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Classification
public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Recurrence
public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.ReturnMean

/-!
# Classification of nearest-neighbor integer walks

The nearest-neighbor integer walk is null recurrent exactly when its right-step
probability is `1 / 2` and has no positive recurrent state for any parameter.
Together with the transience results in `IntegerWalk.Recurrence`, these results
complete the state classification, including the deterministic endpoint parameters.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.5–1.7.
-/

public section

open ProbabilityTheory

namespace TauCeti.Probability

/-- The nearest-neighbor integer walk is null recurrent exactly at the symmetric
parameter, at every starting state. -/
@[simp↓]
theorem integerWalk_isNullRecurrent_iff (p : unitInterval) (x : ℤ) :
    (integerWalk p).IsNullRecurrent x ↔ (p : ℝ) = 1 / 2 := by
  constructor
  · intro hx
    exact (integerWalk_isRecurrent_iff p x).mp hx.isRecurrent
  · intro hp
    exact Kernel.isNullRecurrent_iff.mpr
      ⟨(integerWalk_isRecurrent_iff p x).mpr hp, integerWalk_meanReturnTime_eq_top p hp x⟩

/-- No nearest-neighbor integer walk has a positive recurrent state, including
at the deterministic endpoint parameters. -/
@[simp↓]
theorem integerWalk_not_isPositiveRecurrent (p : unitInterval) (x : ℤ) :
    ¬ (integerWalk p).IsPositiveRecurrent x := by
  intro hx
  have hp := (integerWalk_isRecurrent_iff p x).mp hx.isRecurrent
  exact ((integerWalk_isNullRecurrent_iff p x).mpr hp).not_isPositiveRecurrent hx

end TauCeti.Probability
