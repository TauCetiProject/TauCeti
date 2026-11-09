/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Comparing exponents in finite products

`Nat.eq_of_prod_pow_eq_of_le` shows that ordered exponent families on natural-number bases
above `1` agree on a finite set if their products of powers over that set agree. It is used to
compare the numbers of maps between finite semisimple modules in
`TauCeti/RingTheory/Semisimple/Multiplicity.lean`.
-/

public section

namespace Nat

/-- If `1 < C i` and `f i ≤ g i` for every `i ∈ s`, and
`∏ i ∈ s, C i ^ f i = ∏ i ∈ s, C i ^ g i`, then `f i = g i` for every `i ∈ s`. -/
theorem eq_of_prod_pow_eq_of_le {ι : Type*} {s : Finset ι} {C f g : ι → ℕ}
    (hC : ∀ i ∈ s, 1 < C i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (h : ∏ i ∈ s, C i ^ f i = ∏ i ∈ s, C i ^ g i) (i : ι) (hi : i ∈ s) : f i = g i := by
  by_contra hne
  refine (Finset.prod_lt_prod₀ (fun j hj ↦ Nat.pow_pos (zero_lt_one.trans (hC j hj)))
    (fun j hj ↦ Nat.pow_le_pow_right (zero_lt_one.trans (hC j hj)) (hfg j hj))
    ⟨i, hi, Nat.pow_lt_pow_right (hC i hi) ((hfg i hi).lt_of_ne hne)⟩).ne h

end Nat
