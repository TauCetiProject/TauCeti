/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin

/-!
# The sign of a permutation of `Fin n` as the parity of its inversions

An *inversion* of `σ : Equiv.Perm (Fin n)` is a pair of indices `i < j` with `σ j < σ i`. The
sign of `σ` is `(-1)` raised to the number of inversions. Mathlib exposes the sign as the product
`Equiv.Perm.sign_eq_prod_prod_Ioi`; this file turns that product into the cardinality of the
finite set of inversions, which is the form met by combinatorial permutation counts.

## Main results

* `TauCeti.sign_eq_neg_one_pow_card_inversion`: the sign of a permutation of `Fin n` is
  `(-1)` to the number of its inversions.
* `TauCeti.sign_finAddFlip_trans_finCongr`: the block swap of `Fin (m + n)`, which exchanges the
  first `m` indices with the last `n`, has sign `(-1) ^ (m * n)`.

This result was first proved on the earlier Tau Ceti split branch at commit `05c2722248` and is
adapted here to current `main`.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- The sign of a permutation of `Fin n` is `(-1)` raised to the number of its inversions, the
pairs of columns `i < j` whose values are in the opposite order. -/
theorem sign_eq_neg_one_pow_card_inversion (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ =
      (-1 : ℤˣ) ^ (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ σ p.2 < σ p.1).card := by
  classical
  have hIoi : ∀ i : Fin n, Finset.Ioi i = Finset.univ.filter fun j : Fin n => i < j := by
    intro i
    ext j
    simp
  have hprod :
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1)) =
        ∏ p ∈ Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2,
          (if σ p.1 < σ p.2 then (1 : ℤˣ) else -1) := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => by rw [hIoi i, Finset.prod_filter]
  have hinv :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).filter
          (fun p => ¬ σ p.1 < σ p.2) =
        Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1 := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun p _ => ?_
    constructor
    · rintro ⟨hlt, hnot⟩
      have hne : σ p.1 ≠ σ p.2 := fun h => (ne_of_lt hlt) (σ.injective h)
      exact ⟨hlt, lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hne)⟩
    · rintro ⟨hlt, hgt⟩
      exact ⟨hlt, not_lt.mpr (le_of_lt hgt)⟩
  rw [σ.sign_eq_prod_prod_Ioi, hprod, Finset.prod_ite]
  simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
  rw [hinv]

/-- The block swap of `Fin (m + n)`, exchanging the first `m` indices with the last `n` while
preserving the order within each block, has sign `(-1) ^ (m * n)`: its inversions are exactly the
`m * n` pairs taken from different blocks. -/
theorem sign_finAddFlip_trans_finCongr (m n : ℕ) :
    Equiv.Perm.sign (finAddFlip.trans (finCongr (add_comm n m))) = (-1) ^ (m * n) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  simp only [finAddFlip, Equiv.trans_apply, finCongr_apply, Fin.cast_lt_cast]
  simp_rw [← finSumFinEquiv.prod_comp, ← Finset.prod_map_equiv finSumFinEquiv.symm]
  simp only [Equiv.symm_apply_apply, ← Fin.val_fin_lt, Equiv.symm_symm, Function.comp_apply,
    ← Finset.prod_ite_mem_eq (Finset.map _ _), Finset.mem_map_equiv, Finset.mem_Ioi,
    Fintype.prod_sum_type, finSumFinEquiv_apply_left, Fin.val_castAdd,
    finSumFinEquiv_apply_right, Fin.val_natAdd, add_lt_add_iff_left,
    ← ite_not (α := ℤˣ) (p := _ < _) (y := 1), ← ite_and]
  simp [(Fin.isLt _).trans_le, (Fin.isLt _).le.trans, pow_mul',
    fun a b : Fin _ => iff_false_intro fun h : a < b ∧ b ≤ a => h.1.not_ge h.2]

end TauCeti
