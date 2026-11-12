/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Basic

/-!
# Cutting a list at an entry and inserting two entries

Replacing the entry `l[j₁]` of a list by two entries `a`, `b` gives the list
`l.take j₁ ++ a :: b :: l.drop (j₁ + 1)`. Its length, its entries before, at and after the cut, and
the partial sums of any function of its entries are recorded here
(`List.length_take_append_cons_cons`, `List.getElem_take_append_of_lt`,
`List.getElem_take_append_cons_self`, `List.getElem_take_append_cons_cons_succ`,
`List.sum_take_map_take_append_of_le`, `List.sum_take_succ_map_take_append_cons`); the last four
hold for an arbitrary list in place of the suffix `l.drop (j₁ + 1)`.
-/

public section

namespace List

variable {β : Type*} {l m : List β} {j₁ : ℕ} {a b : β}

theorem length_take_append_cons_cons (hj₁ : j₁ < l.length) :
    (l.take j₁ ++ a :: b :: l.drop (j₁ + 1)).length = l.length + 1 := by
  simp; omega

/-- The entries before the cut are those of `l`. -/
theorem getElem_take_append_of_lt {k : ℕ} (hj₁ : j₁ ≤ l.length) (hkj : k < j₁)
    (hk : k < (l.take j₁ ++ m).length) : (l.take j₁ ++ m)[k] = l[k]'(by omega) := by
  have hlen : (l.take j₁).length = j₁ := by simp; omega
  rw [List.getElem_append_left (by rw [hlen]; omega), List.getElem_take]

/-- The entry at the cut is `a`. -/
theorem getElem_take_append_cons_self (hj₁ : j₁ ≤ l.length)
    (h : j₁ < (l.take j₁ ++ a :: m).length) : (l.take j₁ ++ a :: m)[j₁] = a := by
  have hlen : (l.take j₁).length = j₁ := by simp; omega
  rw [List.getElem_append_right (by omega)]
  simp [hlen]

/-- The entry after the cut is `b`. -/
theorem getElem_take_append_cons_cons_succ (hj₁ : j₁ ≤ l.length)
    (h : j₁ + 1 < (l.take j₁ ++ a :: b :: m).length) :
    (l.take j₁ ++ a :: b :: m)[j₁ + 1] = b := by
  have hlen : (l.take j₁).length = j₁ := by simp; omega
  rw [List.getElem_append_right (by omega)]
  simp [hlen]

/-- Partial sums up to the cut are those of `l`. -/
theorem sum_take_map_take_append_of_le {M : Type*} [AddMonoid M] (f : β → M)
    (hj₁ : j₁ ≤ l.length) {k : ℕ} (hk : k ≤ j₁) :
    (((l.take j₁ ++ m).take k).map f).sum = ((l.take k).map f).sum := by
  have hlen : (l.take j₁).length = j₁ := by simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_take, show k ⊓ j₁ = k by simp [hk]]

/-- The partial sum through the entry `a` is that of `l` up to the cut plus `f a`. -/
theorem sum_take_succ_map_take_append_cons {M : Type*} [AddMonoid M] (f : β → M)
    (hj₁ : j₁ ≤ l.length) :
    (((l.take j₁ ++ a :: m).take (j₁ + 1)).map f).sum =
      ((l.take j₁).map f).sum + f a := by
  have hlen : (l.take j₁).length = j₁ := by simp; omega
  rw [List.take_append, List.take_of_length_le (by omega), hlen,
    show j₁ + 1 - j₁ = 1 by omega]
  simp

end List
