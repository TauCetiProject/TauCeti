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
theorem val_swapIndexEquiv (u v : List α) (a b : α) (j : Fin (u ++ b :: a :: v).length) :
    (swapIndexEquiv u v a b j : ℕ) =
      if (j : ℕ) = u.length then u.length + 1
      else if (j : ℕ) = u.length + 1 then u.length else j := by
  simp only [swapIndexEquiv, Equiv.trans_apply, Equiv.swap_apply_def, Fin.ext_iff,
    finCongr_apply, Fin.val_cast]
  split_ifs <;> simp_all

/-- Looking up an entry of `u ++ b :: a :: v` and translating its index gives the same entry of
`u ++ a :: b :: v`. -/
theorem getElem_swapIndexEquiv (u v : List α) (a b : α) (j : Fin (u ++ b :: a :: v).length) :
    (u ++ b :: a :: v)[j.1] = (u ++ a :: b :: v)[(swapIndexEquiv u v a b j).1] := by
  have hj := j.isLt
  simp only [length_append, length_cons] at hj
  simp only [val_swapIndexEquiv, getElem_append, getElem_cons]
  split_ifs <;> first | rfl | omega

/-- The swap of indices of `u ++ b :: a :: v` is inverse to the swap of indices of
`u ++ a :: b :: v`. -/
@[simp]
theorem swapIndexEquiv_symm (u v : List α) (a b : α) :
    (swapIndexEquiv u v a b).symm = swapIndexEquiv u v b a := by
  refine Equiv.ext fun j ↦ (swapIndexEquiv u v a b).injective ?_
  rw [Equiv.apply_symm_apply]
  ext
  simp only [val_swapIndexEquiv]
  split_ifs <;> omega

end List
