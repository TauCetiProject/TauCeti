/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Evaluating polynomial remainders over a field

At a root of the divisor, evaluating a field remainder gives the same value as
evaluating the dividend. This supplies the remainder evaluation used in the
local sign-change law for Sturm variations.
-/

public section

namespace TauCeti.Polynomial

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- At a root of the divisor, the remainder and dividend have the same value. -/
theorem eval_mod_of_eval_eq_zero {p q : K[X]} {x : K} (hq : q.eval x = 0) :
    (p % q).eval x = p.eval x := by
  simp [EuclideanDomain.mod_eq_sub_mul_div, hq]

end TauCeti.Polynomial
