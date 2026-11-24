/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite products and sums of updated functions

Modifying a single coordinate `k ∈ s` of a function by multiplying by `m` (or adding `m`) multiplies
the product over `s` by `m` (or increases the sum over `s` by `m`).
-/

public section

namespace Finset

/-- Multiplying coordinate `k ∈ s` by `m` multiplies the product over `s` by `m`. -/
@[to_additive /-- Adding `m` at coordinate `k ∈ s` increases the sum over `s` by `m`. -/]
theorem prod_update_mul_of_mem {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    {s : Finset ι} {k : ι} (hk : k ∈ s) (d : ι → M) (m : M) :
    ∏ i ∈ s, Function.update d k (d k * m) i = (∏ i ∈ s, d i) * m := by
  rw [Finset.prod_update_of_mem hk, Finset.sdiff_singleton_eq_erase, mul_right_comm,
    Finset.mul_prod_erase s d hk]

end Finset
