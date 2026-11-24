/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect

/-!
# Perfect rings

Supplements to Mathlib's `PerfectRing` API.

## Main results

* `frobeniusEquiv_symm_sub_one_pow`: in a perfect ring of characteristic `p`, `x ^ (1 / p) - 1`
  is a `p`-th root of `x - 1`.
-/

public section

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]

/-- In a perfect ring of characteristic `p`, `x ^ (1 / p) - 1` is a `p`-th root of `x - 1`. -/
theorem frobeniusEquiv_symm_sub_one_pow (x : R) :
    ((frobeniusEquiv R p).symm x - 1) ^ p = x - 1 := by
  rw [sub_pow_char, one_pow, frobeniusEquiv_symm_pow_p]
