/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Evaluating `ℤ ⧸ aℤ ≃+ ZMod |a|` on a class

Mathlib's `Int.quotientZMultiplesEquivZMod a` identifies `ℤ` modulo the multiples of `a` with
`ZMod |a|`. This file records that it sends the class of `n` to `n mod |a|`.

## Main results

* `Int.quotientZMultiplesEquivZMod_mk`: `Int.quotientZMultiplesEquivZMod a n = n`.
-/

public section

/-- `ℤ` modulo the multiples of `a` is `ZMod |a|`, sending the class of `n` to `n mod |a|`. -/
@[simp]
theorem Int.quotientZMultiplesEquivZMod_mk (a n : ℤ) :
    Int.quotientZMultiplesEquivZMod a n = n :=
  -- Both quotient equivalences composed in `Int.quotientZMultiplesEquivZMod` are induced by maps
  -- on representatives, the last of which is the cast `ℤ → ZMod |a|`.
  rfl
