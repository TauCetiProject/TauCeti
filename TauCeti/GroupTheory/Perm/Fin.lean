/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Permutations of `Fin n`

This file supplements Mathlib's `Mathlib.GroupTheory.Perm.Fin`.

## Main results

* `Fin.coe_cycleRange`: the value of the cycle `Fin.cycleRange i = (0 1 ⋯ i)` at `j`, as a
  natural number, read off the comparison of the values of `j` and `i`. Unlike
  `Fin.cycleRange_apply` it needs no `NeZero n` instance, and both its case split and its result
  are stated on natural numbers, ready for `omega`.
* `List.formPerm_finRange`, `Fin.formPerm_sort_univ`: the cycle through the points of `Fin n` in
  increasing order is the rotation `finRotate n`, that is `i ↦ i + 1` modulo `n`.
* `TauCeti.isCycleOn_finRotate`: the rotation `finRotate n` is a single cycle on all of `Fin n`.
* `Equiv.Perm.eq_one_of_rows`: a permutation of `Fin (m * n)` that fixes every point of each
  row `finProdFinEquiv (i, ·)` is the identity. Checking one row at a time keeps each
  `decide +kernel` certificate small.
* `Equiv.Perm.sum_comp_symm_apply_zero`: summing a function of `σ⁻¹ 0` over all permutations of
  `Fin (n + 1)` counts each value `n!` times.
-/

public section

namespace Fin

/-- The value of the cycle `(0 1 ⋯ i)` at `j`: one more than `j` below `i`, `0` at `i`, and `j`
above `i`. -/
theorem coe_cycleRange {n : ℕ} (i j : Fin n) :
    (cycleRange i j : ℕ) = if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else j := by
  rcases le_or_gt j i with h | h
  · rw [coe_cycleRange_of_le h]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [cycleRange_of_gt h]
    split_ifs <;> omega

/-- The cycle through the points of `Fin n` in increasing order is the rotation `i ↦ i + 1`
modulo `n`. -/
@[simp]
theorem _root_.List.formPerm_finRange (n : ℕ) : (List.finRange n).formPerm = finRotate n := by
  ext x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := x.pos; omega⟩
  have hx : (List.finRange (m + 1))[(x : ℕ)]'(by simp [x.isLt]) = x := by simp
  rw [← hx, List.formPerm_apply_getElem _ (List.nodup_finRange _)]
  simp only [List.getElem_finRange, Fin.val_cast, List.length_finRange, coe_finRotate, Fin.ext_iff,
    Fin.val_last]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cycle through the points of `Fin n`, enumerated in increasing order by `Finset.sort`, is
the rotation `i ↦ i + 1` modulo `n`. -/
@[simp]
theorem formPerm_sort_univ (n : ℕ) :
    (Finset.univ : Finset (Fin n)).sort.formPerm = finRotate n := by
  rw [sort_univ, List.formPerm_finRange]

end Fin

namespace TauCeti

/-- The rotation `i ↦ i + 1` of `Fin n` is a single cycle on all of `Fin n`. -/
theorem isCycleOn_finRotate : ∀ {n : ℕ}, (finRotate n).IsCycleOn Set.univ
  | 0 => Equiv.Perm.isCycleOn_of_subsingleton _ _
  | 1 => Equiv.Perm.isCycleOn_of_subsingleton _ _
  | _ + 2 => by
    convert isCycle_finRotate.isCycleOn using 1
    ext x
    simp

end TauCeti

namespace Equiv.Perm

/-- A permutation of `Fin (m * n)` is the identity once it fixes every point of each row
`finProdFinEquiv (i, ·)`. Splitting a kernel decision over the rows keeps each certificate small. -/
theorem eq_one_of_rows {m n : ℕ} (p : Equiv.Perm (Fin (m * n)))
    (h : ∀ i j, p (finProdFinEquiv (i, j)) = finProdFinEquiv (i, j)) : p = 1 := by
  refine Equiv.ext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  exact h i j

/-- A product over all permutations of `Fin (n + 1)` of a function of `σ⁻¹ 0` takes each value
`n!` times. -/
@[to_additive /-- A sum over all permutations of `Fin (n + 1)` of a function of `σ⁻¹ 0` takes each
value `n!` times. -/]
theorem prod_comp_symm_apply_zero {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    ∏ σ : Perm (Fin (n + 1)), f (σ.symm 0) = (∏ p, f p) ^ n.factorial := by
  rw [← Fintype.prod_equiv (Equiv.inv (Perm (Fin (n + 1)))) (fun σ ↦ f (σ 0))
    (fun σ ↦ f (σ.symm 0)) fun σ ↦ rfl,
    ← Fintype.prod_equiv (decomposeFin.symm : Fin (n + 1) × Perm (Fin n) ≃ _)
      (fun pe ↦ f pe.1) (fun σ ↦ f (σ 0)) fun pe ↦ by rw [decomposeFin_symm_apply_zero]]
  simp [Fintype.prod_prod_type, Finset.prod_const, Fintype.card_perm, Finset.prod_pow]

end Equiv.Perm
