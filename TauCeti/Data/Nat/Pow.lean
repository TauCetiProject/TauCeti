/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Basic

/-!
# Natural numbers that are powers

A natural number `n ≠ 1` either is not a power of `b`, or is a power `b ^ k` with a positive
exponent `k`, because `b ^ 0 = 1`.

## Main results

* `Nat.forall_ne_pow_or_exists_pos_eq_pow`: the dichotomy above. Its consumer is the case split
  on the coefficients of the universal normalised logarithm in
  `TauCeti/RingTheory/FormalGroup/ExponentTwo/Universal.lean`, whose free coefficients sit in the
  degrees `n ≥ 2` that are not powers of two.
* `Nat.eq_of_prod_pow_eq_of_le`: if two exponent families on bases above `1` are ordered and the
  products agree, the families agree. Its consumer is the comparison of the numbers of maps
  between finite semisimple modules in `TauCeti/RingTheory/Semisimple/Multiplicity.lean`.
-/

public section

namespace Nat

/-- A natural number `n ≠ 1` either is not a power of `b`, or is `b ^ k` for some `k > 0`. -/
theorem forall_ne_pow_or_exists_pos_eq_pow {b n : ℕ} (hn : n ≠ 1) :
    (∀ k : ℕ, n ≠ b ^ k) ∨ ∃ k, 0 < k ∧ n = b ^ k := by
  refine or_iff_not_imp_left.2 fun h ↦ ?_
  obtain ⟨k, hk⟩ := not_forall_not.mp h
  exact ⟨k, Nat.pos_of_ne_zero fun h0 ↦ hn (by rw [hk, h0, Nat.pow_zero]), hk⟩

/-- If the bases `C i` exceed `1` and `f ≤ g` pointwise, then `∏ C i ^ f i = ∏ C i ^ g i` forces
`f = g`: raising a base to a larger exponent strictly increases the product. -/
theorem eq_of_prod_pow_eq_of_le {ι : Type*} {s : Finset ι} {C f g : ι → ℕ}
    (hC : ∀ i ∈ s, 1 < C i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (h : ∏ i ∈ s, C i ^ f i = ∏ i ∈ s, C i ^ g i) (i : ι) (hi : i ∈ s) : f i = g i := by
  by_contra hne
  refine (Finset.prod_lt_prod₀ (fun j hj ↦ Nat.pow_pos (zero_lt_one.trans (hC j hj)))
    (fun j hj ↦ Nat.pow_le_pow_right (zero_lt_one.trans (hC j hj)) (hfg j hj))
    ⟨i, hi, Nat.pow_lt_pow_right (hC i hi) ((hfg i hi).lt_of_ne hne)⟩).ne h

end Nat
