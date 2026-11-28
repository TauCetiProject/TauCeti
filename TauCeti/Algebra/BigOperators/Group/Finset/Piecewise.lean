/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite products and sums of piecewise and updated functions

* `Finset.prod_update_mul_of_mem` / `Finset.sum_update_add_of_mem`: modifying a single coordinate
  `k ∈ s` of a function by multiplying by `m` (or adding `m`) multiplies the product over `s` by
  `m` (or increases the sum over `s` by `m`).
* `Finset.prod_prod_ite_mul_pow`: splits a weighted double product of two singleton-supported
  factors into one product per selected index, using `Finset.prod_comm` and `Finset.prod_ite_eq'`.
  The indices may coincide, and an index outside the outer finset contributes `1`.
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

/-- The double product of two weighted singleton-supported factors splits into one
product for each selected index that belongs to `s`, even if the indices coincide. -/
theorem prod_prod_ite_mul_pow {M ι κ : Type*} [CommMonoid M] [DecidableEq ι]
    (s : Finset ι) (t : Finset κ) (u v : ι) (f g : κ → M) (a : ι → κ → ℕ) :
    (∏ i ∈ s, ∏ j ∈ t, ((if i = u then f j else 1) * (if i = v then g j else 1)) ^ a i j) =
      (if u ∈ s then ∏ j ∈ t, f j ^ a u j else 1) *
      (if v ∈ s then ∏ j ∈ t, g j ^ a v j else 1) := by
  rw [prod_comm]
  simp_rw [mul_pow, prod_mul_distrib, ite_pow, one_pow, prod_ite_eq', prod_ite_irrel,
    prod_const_one]

end Finset
