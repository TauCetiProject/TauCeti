/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even

/-!
# Off-diagonal sums of a symmetric function

The off-diagonal sum of `f : α → α → M` over a finite set `s` is
`∑ i ∈ s, ∑ j ∈ s.erase i, f i j`: every ordered pair of distinct elements of `s` contributes
once. When `f` is symmetric the two members of each unordered pair contribute equal terms, so the
whole sum is even; this is `Finset.even_sum_sum_erase`, proved by induction on `s`.

## Main results

* `Finset.even_sum_sum_erase`: the off-diagonal sum of a symmetric function over a finite set is
  even.
-/

public section

namespace Finset

/-- **The off-diagonal sum of a symmetric function is even.** The ordered pairs of distinct
elements of `s` come in transposed couples contributing equal terms, so `f` need only be
symmetric on `s`. -/
theorem even_sum_sum_erase {α M : Type*} [DecidableEq α] [AddCommMonoid M] {f : α → α → M}
    (s : Finset α) (hf : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i) :
    Even (∑ i ∈ s, ∑ j ∈ s.erase i, f i j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hstep : ∀ i ∈ s, ∑ j ∈ (insert a s).erase i, f i j = f i a + ∑ j ∈ s.erase i, f i j := by
      intro i hi
      have hai : a ≠ i := fun h ↦ ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hai,
        Finset.sum_insert (fun h ↦ ha (Finset.mem_of_mem_erase h))]
    rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.sum_congr rfl hstep,
      Finset.sum_add_distrib, ← add_assoc]
    refine Even.add ?_ (ih fun i hi j hj ↦
      hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_congr rfl fun i hi ↦
      hf i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)]
    exact ⟨_, rfl⟩

end Finset
