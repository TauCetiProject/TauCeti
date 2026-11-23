/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Images of rays under the negated real exponential

Mathlib records `Real.image_exp_Iio : exp '' Iio a = Ioo 0 (exp a)`. Composing with negation gives
the image of `(a, ∞)` under `u ↦ exp (-u)`, used when pulling unit-interval logarithmic integrals
back to the positive half-line via `t = exp (-u)`.

## Main results

* `Real.image_exp_neg_Ioi`: `(fun u : ℝ ↦ exp (-u)) '' Set.Ioi a = Set.Ioo 0 (exp (-a))`.
-/

public section

namespace Real

/-- Negating and exponentiating maps the open ray `(a, ∞)` onto `(0, exp (-a))`. -/
@[simp]
theorem image_exp_neg_Ioi (a : ℝ) :
    (fun u : ℝ ↦ exp (-u)) '' Set.Ioi a = Set.Ioo 0 (exp (-a)) := by
  rw [← Function.comp_def exp Neg.neg, Set.image_comp, Set.image_neg_Ioi, image_exp_Iio]

end Real
