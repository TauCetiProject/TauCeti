/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Support
public import TauCeti.Probability.Distributions.Zero.Hurdle

/-!
# Supports of zero-modified negative-binomial laws

For positive shape and success probability strictly between zero and one, zero truncation
leaves all positive counts. Zero inflation also retains zero; a hurdle law retains zero
exactly when its atom weight is positive. Weight one removes the positive-count component.

At shape zero or success probability one, the base law is Dirac at zero and its zero truncation
vanishes. The support formulas include both boundaries, including the subprobability hurdle
laws obtained from this vanishing base. Real casting produces discrete integer supports.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, sections 5.11 and 8.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace TauCeti.Probability

variable {r p : ℝ}

/-- A valid zero-truncated negative-binomial law has all positive counts in its support,
except when the base law is Dirac at zero and truncation removes all mass. -/
-- Compute the family support before simplifying the measure at a Dirac boundary.
@[simp↓]
theorem support_negativeBinomialMeasure_cond_compl_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) :
    ((negativeBinomialMeasure r p)[|{0}ᶜ]).support =
      if r = 0 ∨ p = 1 then ∅ else Ioi 0 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.support_cond _ _ (measure_ne_top _ _),
    support_negativeBinomialMeasure hr hp hp1]
  split_ifs <;> ext n <;> simp [Nat.pos_iff_ne_zero]

/-- A valid zero-inflated negative-binomial law has full native support unless the shape is
zero, the success probability is one, or the entire weight is on the zero atom. -/
@[simp↓]
theorem support_negativeBinomialMeasure_atomMixture_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) (w : unitInterval) :
    ((negativeBinomialMeasure r p).atomMixture 0 w).support =
      if r = 0 ∨ p = 1 ∨ w = 1 then {0} else univ := by
  rw [Measure.support_atomMixture, support_negativeBinomialMeasure hr hp hp1]
  by_cases hdeg : r = 0 ∨ p = 1 <;> by_cases hw0 : w = 0 <;> by_cases hw1 : w = 1 <;>
    simp_all

/-- A negative-binomial hurdle law retains zero exactly at positive atom weight and retains
the positive counts exactly when the base is nondegenerate and the atom weight is below one. -/
@[simp↓]
theorem support_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero (hr : 0 ≤ r)
    (hp : 0 < p) (hp1 : p ≤ 1) (w : unitInterval) :
    (((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).support =
      (if w = 0 then ∅ else {0}) ∪
        (if w = 1 ∨ r = 0 ∨ p = 1 then ∅ else Ioi 0) := by
  rw [Measure.support_atomMixture, support_negativeBinomialMeasure_cond_compl_zero hr hp hp1]
  by_cases hdeg : r = 0 ∨ p = 1 <;> by_cases hw0 : w = 0 <;> by_cases hw1 : w = 1 <;>
    simp_all

end TauCeti.Probability
