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
* `TauCeti.ZMod.ofAdd_one_inv_pow`: the same statement for its inverse.
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

/-- In the multiplicative tag of `ZMod n`, the `n`-th power of the inverse of
`Multiplicative.ofAdd 1` is trivial. -/
@[simp]
theorem ofAdd_one_inv_pow (n : ℕ) :
    ((Multiplicative.ofAdd (1 : ZMod n))⁻¹) ^ n = 1 := by
  rw [inv_pow, ofAdd_one_pow, inv_one]

end ZMod

end TauCeti
