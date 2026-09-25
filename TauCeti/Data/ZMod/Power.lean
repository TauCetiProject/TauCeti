/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Powers of the standard generator modulo `n`

In the multiplicative tag of `ZMod n`, the element corresponding to `1` generates the group.
Its `n`-th power is the multiplicative identity because `n` is zero modulo `n`; the same holds
for its inverse.

## Main results

* `TauCeti.ZMod.ofAdd_one_pow`: the `n`-th power of the standard generator is trivial.
-/

public section

namespace TauCeti

namespace ZMod

/-- In the multiplicative tag of `ZMod n`, the `n`-th power of `Multiplicative.ofAdd 1` is
trivial. -/
@[simp]
theorem ofAdd_one_pow (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod n)) ^ n = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow]
  simp

end ZMod

end TauCeti
