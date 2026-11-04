/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Suprema in complete lattices

This file adds supremum identities for complete lattices that are not in Mathlib.

## Main declarations

* `TauCeti.iSup_int_eq_sup_pos_mul_sup_zero_sup_pos_mul_neg`: for `c ≠ 0`, a supremum over
  the integers splits by the sign of `n * c` into the parts with `n * c` positive, `n = 0`, and
  `n * c` negative.
* `TauCeti.biSup_Iic_ite_tsub_eq_biSup_Icc`: reversing the indices up to `m` turns a supremum
  over `k ≤ m - n` into one over `i ∈ [n, m]`.
* `TauCeti.biSup_Ici_eq_biSup_Icc`: a supremum over `i ≥ k` of a family vanishing above `m` is
  the supremum over `i ∈ [k, m]`.
-/

public section

namespace TauCeti

/-- **Splitting a supremum over `ℤ` by the sign of `n * c`.** For `c ≠ 0`, the supremum of
`f n` over all integers `n` is the join of the suprema over `0 < n * c` and over `0 < n * -c`
with the middle term `f 0`. -/
theorem iSup_int_eq_sup_pos_mul_sup_zero_sup_pos_mul_neg {α : Type*} [CompleteLattice α]
    (f : ℤ → α) {c : ℤ} (hc : c ≠ 0) :
    ⨆ n : ℤ, f n = (⨆ (n : ℤ) (_ : 0 < n * c), f n) ⊔ f 0 ⊔ ⨆ (n : ℤ) (_ : 0 < n * -c), f n := by
  refine le_antisymm (iSup_le fun n ↦ ?_) (sup_le (sup_le (iSup₂_le fun n _ ↦ le_iSup f n)
    (le_iSup f 0)) (iSup₂_le fun n _ ↦ le_iSup f n))
  rcases lt_trichotomy (n * c) 0 with h | h | h
  · exact le_sup_of_le_right (le_iSup₂_of_le n (by rwa [mul_neg, neg_pos]) le_rfl)
  · obtain rfl : n = 0 := (mul_eq_zero.mp h).resolve_right hc
    exact le_sup_of_le_left le_sup_right
  · exact le_sup_of_le_left (le_sup_of_le_left (le_iSup₂_of_le n h le_rfl))

/-- **Reversing the indices up to `m`.** For `n ≤ m`, the supremum over `k ≤ m - n` of the family
`k ↦ f (m - k)`, extended by `⊥` beyond `m`, is the supremum of `f` over `[n, m]`. -/
theorem biSup_Iic_ite_tsub_eq_biSup_Icc {α : Type*} [CompleteLattice α] (f : ℕ → α) {n m : ℕ}
    (hnm : n ≤ m) :
    ⨆ k ∈ Set.Iic (m - n), (if k ≤ m then f (m - k) else ⊥) = ⨆ i ∈ Set.Icc n m, f i := by
  refine le_antisymm (iSup₂_le fun k hk ↦ ?_) (iSup₂_le fun i hi ↦ ?_)
  · simp only [Set.mem_Iic] at hk
    simp only [show k ≤ m by omega, ↓reduceIte]
    exact le_biSup f (by simp only [Set.mem_Icc]; omega)
  · simp only [Set.mem_Icc] at hi
    have := le_biSup (fun k ↦ if k ≤ m then f (m - k) else ⊥)
      (show m - i ∈ Set.Iic (m - n) by simp only [Set.mem_Iic]; omega)
    simpa [show m - i ≤ m by omega, Nat.sub_sub_self hi.2] using this

/-- **Cutting a supremum over `Set.Ici k` at `m`.** If `f` vanishes above `m`, its supremum over
`i ≥ k` is its supremum over `[k, m]`. -/
theorem biSup_Ici_eq_biSup_Icc {ι α : Type*} [LinearOrder ι] [CompleteLattice α] (f : ι → α)
    {k m : ι} (hf : ∀ i, m < i → f i = ⊥) : ⨆ i ∈ Set.Ici k, f i = ⨆ i ∈ Set.Icc k m, f i := by
  refine le_antisymm (iSup₂_le fun i hi ↦ ?_) (biSup_mono fun i hi ↦ hi.1)
  rcases le_or_gt i m with him | him
  · exact le_biSup f ⟨hi, him⟩
  · rw [hf i him]
    exact bot_le

end TauCeti
