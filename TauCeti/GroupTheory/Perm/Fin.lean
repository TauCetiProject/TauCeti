/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Fin
-- Non-public: a cycle and an adjacent transposition generate the permutation group.
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.Tactic.FinCases

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
* `Fin.swap_apply_lt_swap_apply`: an adjacent transposition `(a a+1)` of `Fin n` keeps every
  strict pair in order except `a < a + 1` itself.
* `TauCeti.isCycleOn_finRotate`: the rotation `finRotate n` is a single cycle on all of `Fin n`.
* `TauCeti.closure_finRotate_swap_eq_top`: the rotation `finRotate n` and the transposition `(0 1)`
  generate the permutations of `Fin n`.
* `Equiv.Perm.eq_one_of_rows`: a permutation of `Fin (m * n)` that fixes every point of each
  row `finProdFinEquiv (i, ·)` is the identity. Checking one row at a time keeps each
  `decide +kernel` certificate small.
* `Equiv.Perm.sum_comp_symm_apply_zero`: summing a function of `σ⁻¹ 0` over all permutations of
  `Fin (n + 1)` counts each value `n!` times.
* `Equiv.Perm.card_filter_val_lt`: a permutation of `Fin n` maps `min n m` indices below `m`.
* `Equiv.Perm.eq_one_or_swap_fin_two`, `Equiv.Perm.univ_fin_two`, and
  `Equiv.Perm.eq_ite_ne_one_fin_two`: every permutation of `Fin 2` is the identity or the
  transposition, and these form the set of all permutations.
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

/-- An adjacent transposition `(a b)`, with `b = a + 1`, preserves the strict order of every pair
of elements of `Fin n` other than the pair `a < b` itself. -/
theorem swap_apply_lt_swap_apply {n : ℕ} {a b i j : Fin n} (hab : (a : ℕ) + 1 = b) (hij : i < j)
    (hne : ¬(i = a ∧ j = b)) : Equiv.swap a b i < Equiv.swap a b j := by
  simp only [Equiv.swap_apply_def]
  simp only [Fin.lt_def, Fin.ext_iff] at hij hne ⊢
  split_ifs <;> simp_all <;> omega

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

/-- **The rotation `finRotate n` and the transposition `(0 1)` generate the permutations of
`Fin n`.** -/
theorem closure_finRotate_swap_eq_top : ∀ {n : ℕ} [NeZero n],
    Subgroup.closure {finRotate n, Equiv.swap (0 : Fin n) 1} = ⊤
  | 0, h => absurd rfl h.out
  | 1, _ => eq_top_iff.2 fun g _ => Subsingleton.elim g 1 ▸ one_mem _
  | n + 2, _ => by
    simpa using Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate (n + 2)) isCycle_finRotate
      support_finRotate 0

end TauCeti

namespace Equiv.Perm

/-- A permutation preserving consecutive adjacency and fixing the last point of a finite
chain is the identity. Only forward preservation of adjacency is needed. -/
theorem eq_one_of_adjacent_of_apply_last_eq_self {n : ℕ} {σ : Perm (Fin (n + 1))}
    (hadj : ∀ i j, i.val + 1 = j.val →
      (σ i).val + 1 = (σ j).val ∨ (σ j).val + 1 = (σ i).val)
    (hlast : σ (Fin.last n) = Fin.last n) : σ = 1 := by
  have hfix : ∀ k : ℕ, ∀ j : Fin (n + 1), n - j.val ≤ k → σ j = j := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hjlast : j = Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
        simpa [hjlast] using hlast
    | succ k ih =>
        intro j hj
        by_cases hj' : n - j.val ≤ k
        · exact ih j hj'
        let s : Fin (n + 1) := ⟨j.val + 1, by omega⟩
        have hs : σ s = s := ih s (by dsimp only [s, Fin.val_mk]; omega)
        have hstep := hadj j s rfl
        rw [hs] at hstep
        have hne : (σ j).val ≠ j.val + 2 := by
          intro he
          have hfixed := ih (σ j) (by omega)
          have hjfix : σ j = j := σ.injective hfixed
          have := congrArg Fin.val hjfix
          omega
        apply Fin.ext
        dsimp only [s, Fin.val_mk] at hstep
        omega
  exact Equiv.ext fun j ↦ hfix (n - j.val) j le_rfl

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

section

open _root_.Finset

/-- A permutation of `Fin n` maps `min n m` indices below `m`. -/
theorem card_filter_val_lt {n m : ℕ} (σ : Perm (Fin n)) :
    #{i : Fin n | (σ i : ℕ) < m} = min n m :=
  (card_equiv σ fun _ => by simp).trans Fin.card_filter_val_lt

end

/-- A permutation of `Fin 2` is either the identity or the transposition. -/
theorem eq_one_or_swap_fin_two (e : Equiv.Perm (Fin 2)) :
    e = 1 ∨ e = Equiv.swap 0 1 := by
  by_cases h0 : e 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · apply Fin.eq_one_of_ne_zero
      intro h1
      exact Fin.zero_ne_one (e.injective (h1.trans h0.symm)).symm
  · right
    have h0' : e 0 = 1 := Fin.eq_one_of_ne_zero _ h0
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using h0'
    · have h1 : e 1 = 0 := by
        by_contra h
        have h1' : e 1 = 1 := Fin.eq_one_of_ne_zero _ h
        exact Fin.zero_ne_one (e.injective (h1'.trans h0'.symm)).symm
      simpa using h1

/-- The permutations of `Fin 2`, as a finite set, are the identity and the transposition. -/
theorem univ_fin_two :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
    {1, Equiv.swap 0 1} := by
  classical
  ext e
  simpa using e.eq_one_or_swap_fin_two

/-- Every permutation of `Fin 2` equals `Equiv.swap 0 1` when non-identity and `1` otherwise. -/
theorem eq_ite_ne_one_fin_two (σ : Equiv.Perm (Fin 2)) :
    σ = if σ ≠ 1 then Equiv.swap 0 1 else 1 := by
  rcases σ.eq_one_or_swap_fin_two with rfl | rfl <;> decide

end Equiv.Perm
