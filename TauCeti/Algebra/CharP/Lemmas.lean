/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas

/-!
# Negation and `p`-power maps in exponential characteristic `p`

In a ring of exponential characteristic `p`, raising to the power `q = p ^ n` commutes with
negation. Mathlib records the special case `(-1) ^ q = -1` (`neg_one_pow_expChar_pow`) and the
additive laws `add_pow_expChar_pow` and `sub_pow_expChar_pow`; this file adds the general negation
law.

## Main results

* `TauCeti.neg_pow_expChar_pow`: `(-x) ^ p ^ n = -x ^ p ^ n`.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] (p n : ℕ) [ExpChar R p]

/-- Raising to the power `q = p ^ n` commutes with negation in exponential characteristic `p`. -/
theorem neg_pow_expChar_pow (x : R) : (-x) ^ p ^ n = -x ^ p ^ n := by
  rw [neg_pow, neg_one_pow_expChar_pow, neg_one_mul]

end TauCeti
