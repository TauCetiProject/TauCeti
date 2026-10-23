/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Preorder.Finite

/-!
# Signed counts of the permutations carrying one antitone sequence above another

Let `β` and `η` be antitone sequences indexed by `Fin n` with values in a preorder.  Say that a
permutation `τ` of `Fin n` **dominates** `β` by `η` when `β j ≤ η (τ j)` for every `j`.
The signed count of the dominating permutations is `1` when the comparisons `β j ≤ η i` cut out
exactly the initial segments `i ≤ j`, and `0` otherwise.

The signed count is the determinant of the `0`/`1` matrix of the comparisons `β j ≤ η i`.  Because
`η` decreases, each row of that matrix is the indicator of an initial segment of `Fin n`; because
`β` decreases, those initial segments grow with the row.  A chain of `n` nested initial segments of
`Fin n` either repeats a term — and two rows coincide — or starts empty — and a row vanishes — or
is the complete flag, in which case the matrix is lower triangular with unit diagonal.

The three cases are the cancellation behind the Pieri rule for Schur polynomials: adding a monomial
to the beta-numbers of a shape and sorting the result back into decreasing order leaves exactly the
shapes obtained by adding a horizontal strip, every other arrangement of the same values cancelling
against the opposite one.

## Main results

* `TauCeti.sum_sign_filter_forall_le_of_antitone`: the signed count of the permutations
  dominating one antitone sequence by another.
-/

public section

namespace TauCeti

open Equiv Finset

variable {n : ℕ} {α : Type*} [Preorder α] [DecidableLE α] {β η : Fin n → α}

/-- **The signed count of the permutations carrying `β` above `η`.**  For antitone `β` and `η`
indexed by `Fin n`, the sum of the signs of the permutations `τ` with `β j ≤ η (τ j)` for every `j`
is `1` when the comparisons `β j ≤ η i` hold exactly for `i ≤ j`, and `0` otherwise. -/
theorem sum_sign_filter_forall_le_of_antitone (hβ : Antitone β) (hη : Antitone η) :
    ∑ τ : Perm (Fin n) with (∀ j, β j ≤ η (τ j)), (Perm.sign τ : ℤ) =
      if ∀ i j, β j ≤ η i ↔ i ≤ j then 1 else 0 := by
  classical
  set M : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun j i => if β j ≤ η i then 1 else 0 with hM
  -- The signed count is the determinant of the matrix of comparisons.
  have hdet : M.det = ∑ τ : Perm (Fin n) with (∀ j, β j ≤ η (τ j)), (Perm.sign τ : ℤ) := by
    rw [← M.det_transpose, Matrix.det_apply', Finset.sum_filter]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hprod : ∏ i, M.transpose (τ i) i = if ∀ j, β j ≤ η (τ j) then (1 : ℤ) else 0 := by
      simp [hM, Fintype.prod_boole]
    rw [hprod]
    split_ifs <;> simp
  rw [← hdet]
  split_ifs with h
  · -- The complete flag: the matrix is lower triangular with unit diagonal.
    have hlow : M.IsLowerTriangular := by
      intro r c hrc
      have hne : ¬ β r ≤ η c := (h c r).not.mpr (not_le.mpr (OrderDual.toDual_lt_toDual.mp hrc))
      simp [hM, hne]
    rw [Matrix.det_of_isLowerTriangular M hlow]
    exact Finset.prod_eq_one fun j _ => by simp [hM, (h j j).mpr le_rfl]
  by_cases hempty : ∃ j, ∀ i, ¬ β j ≤ η i
  · -- Some row vanishes.
    obtain ⟨j, hj⟩ := hempty
    exact Matrix.det_eq_zero_of_row_eq_zero j fun i => by simp [hM, hj i]
  -- Every row is a nonempty initial segment, so it has a largest element.
  simp only [not_exists, not_forall, not_not] at hempty
  set S : Fin n → Finset (Fin n) := fun j => univ.filter fun i => β j ≤ η i
  have hSne : ∀ j, (S j).Nonempty := fun j => by
    obtain ⟨i, hi⟩ := hempty j
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  set c : Fin n → Fin n := fun j => (S j).max' (hSne j)
  have hmem : ∀ i j : Fin n, β j ≤ η i ↔ i ≤ c j := by
    refine fun i j => ⟨fun hij => (S j).le_max' i (mem_filter.mpr ⟨mem_univ _, hij⟩), fun hij => ?_⟩
    have hcj : β j ≤ η (c j) := (mem_filter.mp ((S j).max'_mem (hSne j))).2
    exact hcj.trans (hη hij)
  have hmono : Monotone c := fun j j' hjj' =>
    (hmem (c j) j').mp ((hβ hjj').trans ((hmem (c j) j).mpr le_rfl))
  -- Injectivity of the largest elements would force the complete flag, which is excluded.
  by_cases hinj : Function.Injective c
  · refine absurd (fun i j => ?_) h
    rw [hmem i j, (hmono.strictMono_of_injective hinj).apply_eq]
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨j, j', hcjj', hjj'⟩ := hinj
    refine Matrix.det_zero_of_row_eq hjj' (funext fun i => ?_)
    have hiff : β j ≤ η i ↔ β j' ≤ η i := by rw [hmem i j, hmem i j', hcjj']
    simp only [hM, Matrix.of_apply]
    exact if_congr hiff rfl rfl

end TauCeti
