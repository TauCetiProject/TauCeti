/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Rat

/-!
# Iterates of additive and linear maps

Mathlib records that the iterates `f^[n]` of an additive map preserve zero, addition, negation
and integer multiples (`iterate_map_zero`, `iterate_map_add`, ...). This file adds finite sums
and rational scalar multiplication, telescoping products and sums of iterates, and the fact that
once an iterate kills a vector, every later iterate kills it too.

## Main results

* `TauCeti.iterate_map_eq_zero_of_le`: an iterate killing a vector is followed by iterates
  killing it.
* `TauCeti.iterate_map_sum`: the iterates of an additive map preserve finite sums.
* `TauCeti.iterate_map_rat_smul`: the iterates of an additive map between `ℚ`-modules preserve
  rational scalar multiplication.
-/

public section

namespace TauCeti

/-- The quotient of the image of the product of the first `n` iterates by that product
is the quotient of the last iterate by the initial value. -/
@[to_additive /-- Applying an additive endomorphism to the sum of the first `n` iterates
and subtracting that sum gives the last iterate minus the initial value. -/]
theorem map_prod_iterate_div {F M : Type*} [CommGroup M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) :
    f (∏ i ∈ Finset.range n, f^[i] x) / ∏ i ∈ Finset.range n, f^[i] x = f^[n] x / x := by
  simp only [map_prod, ← Finset.prod_div_distrib, ← Function.iterate_succ_apply']
  exact Finset.prod_range_div (fun i ↦ f^[i] x) n

variable {F M : Type*} [FunLike F M M]

/-- Once an iterate of a zero-preserving map kills a vector, every later iterate kills it too. -/
theorem iterate_map_eq_zero_of_le [Zero M] [ZeroHomClass F M M] (f : F) {x : M} {n m : ℕ}
    (hn : f^[n] x = 0) (hnm : n ≤ m) : f^[m] x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [add_comm, Function.iterate_add_apply, hn, iterate_map_zero]

/-- The iterates of an additive map preserve finite sums. -/
theorem iterate_map_sum [AddCommMonoid M] [AddMonoidHomClass F M M] (f : F) {ι : Type*}
    (n : ℕ) (s : Finset ι) (g : ι → M) : f^[n] (∑ i ∈ s, g i) = ∑ i ∈ s, f^[n] (g i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sum]

/-- The iterates of an additive map between `ℚ`-modules preserve rational scalar
multiplication. -/
theorem iterate_map_rat_smul [AddCommGroup M] [Module ℚ M] [AddMonoidHomClass F M M] (f : F)
    (n : ℕ) (q : ℚ) (x : M) : f^[n] (q • x) = q • f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_rat_smul, Function.iterate_succ_apply']

end TauCeti
