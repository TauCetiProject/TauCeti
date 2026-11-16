/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.SuccPred.Fin
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Antitone functions on `Fin (n + 1)`

For an antitone function `g` on `Fin (n + 1)`, the open intervals `(g i.succ, g i.castSucc)`
between consecutive values are pairwise disjoint (`Antitone.pairwise_disjoint_on_Ioo_succ`), so
a value lies strictly between consecutive values for at most one step `i : Fin n`. This locates a
level crossed by a chain along which a function decreases.

For every set `S` of adjacent positions `i.castSucc, i.succ` in `Fin (n + 1)` there is a
decreasing integer function on `Fin (n + 1)` whose adjacent values agree exactly at the positions
in `S`: start at `0` and subtract one at each step not in `S`. Such functions label the standard
block-triangular subgroups of `GLₙ₊₁` by the adjacent coordinates lying in a common block.

## Main results

* `Fin.eq_of_mem_Ioo_succ_castSucc`: a value lies in `(g i.succ, g i.castSucc)` for at most one
  step `i` of an antitone `g`.
* `Fin.exists_antitone_castSucc_eq_succ_iff_mem`: a decreasing `w : Fin (n + 1) → ℤ` with
  `w i.castSucc = w i.succ` exactly for `i ∈ S`.
-/

public section

namespace Fin

/-- For an antitone function on `Fin (n + 1)`, a value lies strictly between `g i.succ` and
`g i.castSucc` for at most one step `i`. -/
theorem eq_of_mem_Ioo_succ_castSucc {α : Type*} [Preorder α] {n : ℕ} {g : Fin (n + 1) → α}
    (hg : Antitone g) {c : α} {i j : Fin n} (hi : c ∈ Set.Ioo (g i.succ) (g i.castSucc))
    (hj : c ∈ Set.Ioo (g j.succ) (g j.castSucc)) : i = j := by
  by_contra hne
  have h := hg.pairwise_disjoint_on_Ioo_succ ((castSucc_injective n).ne hne)
  simp only [Function.onFun, orderSucc_castSucc] at h
  exact h.ne_of_mem hi hj rfl

/-- For every set `S` of adjacent positions there is a decreasing integer weight on
`Fin (n + 1)` whose adjacent values are equal exactly at `S`: subtract one at each step not in
`S`. -/
theorem exists_antitone_castSucc_eq_succ_iff_mem {n : ℕ} (S : Set (Fin n)) :
    ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ ∀ i : Fin n, w i.castSucc = w i.succ ↔ i ∈ S := by
  classical
  let c (i : Fin (n + 1)) : Finset (Fin n) := Finset.univ.filter fun j ↦ (j : ℕ) < i ∧ j ∉ S
  have hc {i i' : Fin (n + 1)} (h : i ≤ i') : c i ⊆ c i' := fun j hj ↦ by
    simp only [c, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1.trans_le (Fin.le_iff_val_le_val.mp h), hj.2⟩
  refine ⟨fun i ↦ -((c i).card : ℤ), fun i i' h ↦ by simpa using Finset.card_le_card (hc h),
    fun i ↦ ?_⟩
  simp only [neg_inj, Int.natCast_inj]
  constructor
  · -- If `i ∉ S`, then `i` is counted at `i.succ` but not at `i.castSucc`.
    intro h
    by_contra hi
    have hlt : c i.castSucc ⊂ c i.succ :=
      (Finset.ssubset_iff_of_subset (hc (Fin.castSucc_le_succ i))).mpr ⟨i, by simp [c, hi]⟩
    exact (Finset.card_lt_card hlt).ne h
  · intro hi
    congr 1
    ext j
    simp only [c, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, Fin.val_castSucc]
    refine ⟨fun ⟨_, hjS⟩ ↦ ⟨by omega, hjS⟩, fun ⟨_, hjS⟩ ↦ ⟨?_, hjS⟩⟩
    exact lt_of_le_of_ne (by omega) fun h ↦ hjS (Fin.ext h ▸ hi)

end Fin
