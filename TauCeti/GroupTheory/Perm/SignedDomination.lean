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

Let `β` and `η` be antitone sequences indexed by a finite linear order `ι` with values in a
preorder.  Say that a permutation `τ` of `ι` **dominates** `β` by `η` when `β j ≤ η (τ j)` for
every `j`.  The signed count of the dominating permutations is `1` when the comparisons
`β j ≤ η i` cut out exactly the initial segments `i ≤ j`, and `0` otherwise.

The signed count is the determinant of the `0`/`1` matrix of the comparisons `β j ≤ η i`.  Because
`η` decreases, each row of that matrix is the indicator of an initial segment of `ι`; because
`β` decreases, those initial segments grow with the row.  A chain of `Fintype.card ι` nested initial
segments of `ι` either repeats a term — and two rows coincide — or starts empty — and a row
vanishes — or is the complete flag, in which case the matrix is lower triangular with unit
diagonal.

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

variable {ι α : Type*} [Fintype ι] [LinearOrder ι] [Preorder α] {β η : ι → α}

/-- **The signed count of the permutations carrying `β` above `η`.**  For antitone `β` and `η`
indexed by a finite linear order `ι`, the sum of the signs of the permutations `τ` with
`β j ≤ η (τ j)` for every `j` is `1` when the comparisons `β j ≤ η i` hold exactly for `i ≤ j`,
and `0` otherwise. -/
theorem sum_sign_filter_forall_le_of_antitone [DecidablePred fun τ : Perm ι => ∀ j, β j ≤ η (τ j)]
    [Decidable (∀ i j, β j ≤ η i ↔ i ≤ j)] (hβ : Antitone β) (hη : Antitone η) :
    ∑ τ : Perm ι with (∀ j, β j ≤ η (τ j)), (Perm.sign τ : ℤ) =
      if ∀ i j, β j ≤ η i ↔ i ≤ j then 1 else 0 := by
  classical
  set M : Matrix ι ι ℤ := Matrix.of fun j i => if β j ≤ η i then 1 else 0 with hM
  -- The signed count is the determinant of the matrix of comparisons.
  have hdet : M.det = ∑ τ : Perm ι with (∀ j, β j ≤ η (τ j)), (Perm.sign τ : ℤ) := by
    rw [← M.det_transpose, Matrix.det_apply', Finset.sum_filter]
    exact Finset.sum_congr rfl fun τ _ => by simp [hM, Fintype.prod_boole]
  rw [← hdet]
  split_ifs with h
  · -- The complete flag: the matrix is lower triangular with unit diagonal.
    have hlow : M.IsLowerTriangular := fun r c hrc => by
      simp [hM, h, not_le.mpr (OrderDual.toDual_lt_toDual.mp hrc)]
    rw [Matrix.det_of_isLowerTriangular M hlow]
    exact Finset.prod_eq_one fun j _ => by simp [hM, h]
  by_cases hempty : ∃ j, ∀ i, ¬ β j ≤ η i
  · -- Some row vanishes.
    obtain ⟨j, hj⟩ := hempty
    exact Matrix.det_eq_zero_of_row_eq_zero j fun i => by simp [hM, hj i]
  -- Every row is a nonempty initial segment, so it has a largest element.
  push Not at hempty
  set S : ι → Finset ι := fun j => univ.filter fun i => β j ≤ η i
  have hSne : ∀ j, (S j).Nonempty := fun j => by simpa [S, Finset.Nonempty] using hempty j
  set c : ι → ι := fun j => (S j).max' (hSne j)
  have hmem : ∀ i j, β j ≤ η i ↔ i ≤ c j := by
    refine fun i j => ⟨fun hij => (S j).le_max' i (mem_filter.mpr ⟨mem_univ _, hij⟩), fun hij => ?_⟩
    exact (mem_filter.mp ((S j).max'_mem (hSne j))).2.trans (hη hij)
  have hmono : Monotone c := fun j j' hjj' =>
    (hmem (c j) j').mp ((hβ hjj').trans ((hmem (c j) j).mpr le_rfl))
  -- Injectivity of the largest elements would force the complete flag, which is excluded.
  by_cases hinj : Function.Injective c
  · refine absurd (fun i j => ?_) h
    rw [hmem i j, (hmono.strictMono_of_injective hinj).apply_eq]
  · obtain ⟨j, j', hcjj', hjj'⟩ := Function.not_injective_iff.mp hinj
    exact Matrix.det_zero_of_row_eq hjj' (funext fun i => by simp [hM, hmem, hcjj'])

end TauCeti
