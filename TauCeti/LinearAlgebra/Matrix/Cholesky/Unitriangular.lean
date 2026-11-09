/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.WellFoundedSet

/-!
# Uniqueness of unitriangular Gram factors

Let `ι` be a finite partially ordered set. Call a square matrix `U` indexed by `ι`
*unitriangular* when its diagonal entries are `1` and `U i j = 0` unless `j ≤ i`. Such a factor
is determined by its Gram matrix `Uᵀ * U`: if `U` and `V` are unitriangular and
`Uᵀ * U = Vᵀ * V`, then `U = V` (`Matrix.transpose_mul_self_inj`). This is the uniqueness
half of the `LDLᵀ` decomposition with trivial diagonal, for a partial rather than a linear order.
The coefficients only need cancellative commutative addition and a multiplication with identity `1`
and absorbing zero; neither associativity nor distributivity of multiplication is required.

The entries are recovered row by row, from the top of the order down. In the `(j, i)` entry
`∑ₗ U l j * U l i` of the Gram matrix, the term `l = i` is `U i j`, and every other nonzero term has
`i < l`, so it involves only rows above `i`.

A typical use compares two transition matrices that are unitriangular for the dominance order on
partitions and have the same Gram matrix, as in the proof of Young's rule.

## Main results

* `Matrix.transpose_mul_self_inj`: unitriangular matrices have the same Gram matrix if and only
  if they are equal.
-/

public section

namespace Matrix

/-- **A unitriangular matrix is determined by its Gram matrix**: if `U` and `V` have diagonal
entries `1` and vanish at `(i, j)` unless `j ≤ i` for a partial order on the finite index type,
then `Uᵀ * U = Vᵀ * V` if and only if `U = V`. -/
theorem transpose_mul_self_inj {ι R : Type*} [Fintype ι] [PartialOrder ι]
    [AddCancelCommMonoid R] [MulZeroOneClass R]
    {U V : Matrix ι ι R} (hU : ∀ i j, U i j ≠ 0 → j ≤ i) (hV : ∀ i j, V i j ≠ 0 → j ≤ i)
    (hU₁ : ∀ i, U i i = 1) (hV₁ : ∀ i, V i i = 1) :
    Uᵀ * U = Vᵀ * V ↔ U = V := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i j
  -- induction on the row, downwards: all rows above `i` agree
  induction i using WellFoundedGT.induction generalizing j with
  | _ i ih =>
  -- read the `(j, i)` entry of the Gram identity, isolating the term `l = i`
  have hj := Matrix.ext_iff.mpr h j i
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hU₁, hV₁, _root_.mul_one] at hj
  have hrest : ∑ l ∈ Finset.univ.erase i, U l j * U l i =
      ∑ l ∈ Finset.univ.erase i, V l j * V l i := Finset.sum_congr rfl fun l hl => by
    by_cases hil : i ≤ l
    · simp only [ih l (hil.lt_of_ne' (Finset.ne_of_mem_erase hl))]
    · simp [Not.imp_symm (hU l i) hil, Not.imp_symm (hV l i) hil]
  rw [hrest] at hj
  exact add_right_cancel hj

end Matrix
