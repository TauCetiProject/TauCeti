/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Init
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Coe

/-!
# Extending functions on `ℕ` along the cast to `ℤ`

A function `a` on `ℕ` extends to `ℤ` along the cast `ℕ → ℤ` by `Function.extend`, with a
fallback function `e` supplying the values off the range of the cast. This file records that the
negative integers lie off that range, so the extension agrees with the fallback there.

## Main results

* `Function.extend_natCast_of_neg`: the extension of `a` along `ℕ → ℤ` with fallback `e` takes
  the value `e n` at every negative integer `n`.
-/

public section

namespace Function

/-- The extension of a function on `ℕ` along the cast to `ℤ` agrees with the fallback at
negative integers. -/
theorem extend_natCast_of_neg {α : Sort*} (a : ℕ → α) (e : ℤ → α) {n : ℤ} (hn : n < 0) :
    extend ((↑) : ℕ → ℤ) a e n = e n :=
  extend_apply' _ _ _ fun ⟨m, hm⟩ => by omega

end Function
