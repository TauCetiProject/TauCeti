/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Basic results about finite ordinal types

This file collects elementary facts about finite ordinal types, including the classification of
permutations of `Fin 2`, indicator sums indexed by `Fin n`, and the final value of a partial
product.

`Fintype.sum_ite_eq` evaluates a sum whose indicator compares two elements of the index type.
When the comparison is instead between a natural number and the `Fin.val` of the index — as it is
whenever a family is indexed by `ℕ` and summed over `Fin n` — the index may fall outside the
range, so the value is a `dite` rather than a plain application.

## Main results

* `TauCeti.perm_fin_two_eq_one_or_swap`: every permutation of `Fin 2` is the identity or the
  transposition.
* `Fin.rev_finRotate_rev` and `Fin.rev_finRotate_symm`: reversal carries forward rotation to
  backward rotation and conversely.
* `Fin.partialProd_last`: the final partial product is the product of all the entries.
* `Fin.partialSum_last`: the final partial sum is the sum of all the entries.
* `TauCeti.add_one_add_one_ne_self`: adding one twice in `Fin n` is nontrivial when `3 ≤ n`.
* `TauCeti.neg_one_pow_val_add_one`: for `n` even, adding one in `Fin n` flips the sign `(-1) ^ ·`
  read off the value.
* `TauCeti.sum_ite_val_add`: a sum against the indicator of `b = k + j` picks out the summand at
  `b - j`, or vanishes when there is no such index.
-/

public section

namespace Fin

/-- The final partial product is the product of all the entries. -/
@[to_additive /-- The final partial sum is the sum of all the entries. -/]
theorem partialProd_last {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    Fin.partialProd f (Fin.last n) = ∏ i, f i := by
  rw [Fin.partialProd, Fin.val_last]
  rw [(List.take_eq_self_iff _).mpr (by simp), Fin.prod_ofFn]

/-- Conjugating forward rotation of a finite ordinal by reversal gives backward rotation. -/
@[simp]
theorem rev_finRotate_rev {n : ℕ} (i : Fin n) :
    haveI := i.neZero
    Fin.rev (Fin.rev i + 1) = (finRotate n).symm i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [finRotate_symm_apply, ← Fin.last_sub, ← Fin.last_sub]
    have hlast : Fin.last n = (-1 : Fin (n + 1)) := by
      apply Fin.ext
      simp
    simp [sub_eq_add_neg, hlast, add_comm, add_left_comm]

/-- Reversal carries backward rotation of a finite ordinal to forward rotation. -/
@[simp]
theorem rev_finRotate_symm {n : ℕ} (i : Fin n) :
    haveI := i.neZero
    Fin.rev (i - 1) = finRotate n (Fin.rev i) := by
  apply Fin.rev_injective
  simp only [Fin.rev_rev]
  simpa only [finRotate_apply, finRotate_symm_apply] using (rev_finRotate_rev i).symm

end Fin

namespace TauCeti

/-- **Adding one twice in `Fin n` never returns to the same element** when `3 ≤ n`. -/
theorem add_one_add_one_ne_self {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) :
    i + 1 + 1 ≠ i := by
  intro h
  have htwo : (1 + 1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa [add_assoc] using h
  have hval := congrArg Fin.val htwo
  simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n)] at hval

/-- **Adding one in `Fin n` flips the sign `(-1) ^ ·` read off the value** when `n` is even.  The
wraparound at the last index respects the sign exactly because `n` is even. -/
theorem neg_one_pow_val_add_one {M : Type*} [Monoid M] [HasDistribNeg M] {n : ℕ} [NeZero n]
    (hn : Even n) (i : Fin n) : (-1 : M) ^ ((i + 1 : Fin n) : ℕ) = -(-1 : M) ^ (i : ℕ) := by
  have hval : ((i + 1 : Fin n) : ℕ) = (i.val + 1) % n := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hval]
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_succ, mul_neg_one]
  · have hi : i.val + 1 = n := by have := i.isLt; omega
    have hn' : Even (i.val + 1) := by rw [hi]; exact hn
    have hodd : Odd i.val := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn')
    rw [hi, Nat.mod_self, pow_zero, hodd.neg_one_pow, neg_neg]

/-- A permutation of `Fin 2` is either the identity or the transposition. -/
theorem perm_fin_two_eq_one_or_swap (e : Equiv.Perm (Fin 2)) :
    e = 1 ∨ e = Equiv.swap 0 1 := by
  by_cases h0 : e 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · apply Fin.eq_one_of_ne_zero
      intro h1
      exact Fin.zero_ne_one (e.injective (h1.trans h0.symm)).symm
  · right
    have h0' : e 0 = 1 := Fin.eq_one_of_ne_zero _ h0
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using h0'
    · have h1 : e 1 = 0 := by
        by_contra h
        have h1' : e 1 = 1 := Fin.eq_one_of_ne_zero _ h
        exact Fin.zero_ne_one (e.injective (h1'.trans h0'.symm)).symm
      simpa using h1

/-- **A shifted indicator picks out one summand.** Summing `f` over `Fin n` against the indicator
of `b = k + j` gives `f` at the index `b - j` when that is a valid index and `j ≤ b`, and `0`
otherwise. -/
theorem sum_ite_val_add {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (b j : ℕ) :
    ∑ k : Fin n, (if b = (k : ℕ) + j then f k else 0)
      = if h : b - j < n ∧ j ≤ b then f ⟨b - j, h.1⟩ else 0 := by
  by_cases h : b - j < n ∧ j ≤ b
  · have hb : ∀ k : Fin n, (b = (k : ℕ) + j) = (k = (⟨b - j, h.1⟩ : Fin n)) := by
      intro k
      have := h.2
      simp only [Fin.ext_iff, eq_iff_iff]
      omega
    simp only [hb, dite_eq_left h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [dite_eq_right h, Finset.sum_eq_zero]
    intro k _
    have := k.isLt
    exact ite_eq_right (by omega)

end TauCeti
