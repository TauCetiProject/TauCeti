/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Poisson.Support
public import TauCeti.Probability.Distributions.Zero.Hurdle

/-!
# Supports of zero-modified Poisson laws

Zero truncation removes zero from the native Poisson support. Zero inflation retains zero,
whereas a hurdle law retains it exactly when its atom weight is positive. Positive counts remain
in the support exactly when the rate is positive and the atom weight is less than one.

At rate zero the truncated law vanishes. Its hurdle modification has empty support at weight
zero and support `{0}` at every positive weight, even when its total mass is less than one.
After casting to the reals these supports remain discrete sets of integers.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, sections 4.10.1 and 8.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal unitInterval

namespace TauCeti.Probability

/-- A zero-truncated Poisson law has support the positive naturals at positive rate and empty
support at rate zero. -/
-- Compute the family support before simplifying the measure at a Dirac boundary.
@[simp↓]
theorem support_poissonMeasure_cond_compl_zero (r : ℝ≥0) :
    ((poissonMeasure r)[|{0}ᶜ]).support = if r = 0 then ∅ else Ioi 0 := by
  rw [Measure.support_cond _ _ (measure_ne_top _ _), support_poissonMeasure]
  split_ifs <;> ext n <;> simp [Nat.pos_iff_ne_zero]

/-- A zero-inflated Poisson law has full native support unless it is a point mass at zero. -/
@[simp↓]
theorem support_poissonMeasure_atomMixture_zero (r : ℝ≥0) (w : unitInterval) :
    ((poissonMeasure r).atomMixture 0 w).support =
      if r = 0 ∨ w = 1 then {0} else univ := by
  rw [Measure.support_atomMixture, support_poissonMeasure]
  by_cases hr : r = 0 <;> by_cases hw0 : w = 0 <;> by_cases hw1 : w = 1 <;>
    simp_all

/-- The support of a Poisson hurdle law consists of its positive-weight zero atom and, when
the rate is positive and the weight is less than one, all positive counts. This includes the
zero-base cases, which need not be probability laws. -/
@[simp↓]
theorem support_poissonMeasure_cond_compl_zero_atomMixture_zero (r : ℝ≥0)
    (w : unitInterval) :
    (((poissonMeasure r)[|{0}ᶜ]).atomMixture 0 w).support =
      (if w = 0 then ∅ else {0}) ∪ (if w = 1 ∨ r = 0 then ∅ else Ioi 0) := by
  rw [Measure.support_atomMixture, support_poissonMeasure_cond_compl_zero]
  by_cases hr : r = 0 <;> by_cases hw0 : w = 0 <;> by_cases hw1 : w = 1 <;>
    simp_all

end TauCeti.Probability
