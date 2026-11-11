/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Exchanging two adjacent entries of a list

The lists `u ++ b :: a :: v` and `u ++ a :: b :: v` have the same entries, except that the two
adjacent entries `a` and `b` trade places. This file records the induced identification of their
index types, which exchanges the two positions `u.length` and `u.length + 1` and fixes every other
position. It is used to compare a construction built from a list with the same construction built
after exchanging two adjacent entries.

## Main definitions

* `List.swapIndexEquiv`: identify the entries of `u ++ b :: a :: v` with those of
  `u ++ a :: b :: v`.

## Main results

* `List.val_swapIndexEquiv`: the swap exchanges the positions `u.length` and `u.length + 1`.
* `List.getElem_swapIndexEquiv`: the identification sends each entry to the same entry.
* `List.getElem?_swap_append_cons_cons`: the same statement for optional lookups at arbitrary
  natural-number positions, translated by the swap of `u.length` and `u.length + 1`.
-/

public section

namespace List

variable {α : Type*}

/-- The equivalence which sends the index of an entry of `u ++ b :: a :: v` to the index of the
same entry of `u ++ a :: b :: v`. It exchanges the positions `u.length` and `u.length + 1` of the
two entries `a` and `b` and fixes every other position. -/
def swapIndexEquiv (u v : List α) (a b : α) :
    Fin (u ++ b :: a :: v).length ≃ Fin (u ++ a :: b :: v).length :=
  (finCongr (by simp)).trans (Equiv.swap ⟨u.length, by simp⟩ ⟨u.length + 1, by simp⟩)

/-- The swap of indices exchanges the positions `u.length` and `u.length + 1` and fixes every
other position. -/
@[simp]
theorem val_swapIndexEquiv (u v : List α) (a b : α) (j : Fin (u ++ b :: a :: v).length) :
    (swapIndexEquiv u v a b j : ℕ) = Equiv.swap u.length (u.length + 1) (j : ℕ) := by
  simp only [swapIndexEquiv, Equiv.trans_apply, Equiv.swap_apply_def, Fin.ext_iff,
    finCongr_apply, Fin.val_cast]
  split_ifs <;> simp_all

/-- Looking up an entry of `u ++ b :: a :: v` and translating its index gives the same entry of
`u ++ a :: b :: v`. -/
theorem getElem_swapIndexEquiv (u v : List α) (a b : α) (j : Fin (u ++ b :: a :: v).length) :
    (u ++ b :: a :: v)[j.1] = (u ++ a :: b :: v)[(swapIndexEquiv u v a b j).1] := by
  grind [val_swapIndexEquiv]

/-- The swap of indices of `u ++ b :: a :: v` is inverse to the swap of indices of
`u ++ a :: b :: v`. -/
@[simp]
theorem swapIndexEquiv_symm (u v : List α) (a b : α) :
    (swapIndexEquiv u v a b).symm = swapIndexEquiv u v b a := by
  refine Equiv.ext fun j ↦ (swapIndexEquiv u v a b).injective (Fin.ext ?_)
  simp

/-- Looking up position `k` of `u ++ a :: b :: v` gives the same result as looking up the swapped
position of `u ++ b :: a :: v`, where the swap exchanges `u.length` and `u.length + 1`. -/
theorem getElem?_swap_append_cons_cons (u v : List α) (a b : α) (k : ℕ) :
    (u ++ b :: a :: v)[Equiv.swap u.length (u.length + 1) k]? = (u ++ a :: b :: v)[k]? := by
  grind

end List
