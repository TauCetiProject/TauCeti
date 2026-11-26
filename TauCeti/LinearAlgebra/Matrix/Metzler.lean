/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Mul

/-!
# Metzler matrices and Q-matrices

A square matrix `B` is **Metzler** (`Matrix.IsMetzler`) when its off-diagonal entries are
nonnegative; nothing is required of the diagonal. A **Q-matrix** (`Matrix.IsQMatrix`) is a Metzler
matrix whose rows sum to zero. A Q-matrix is the matrix of jump rates of a continuous-time Markov
chain on a finite set of states: the entry `Q i j`, `i ≠ j`, is the rate of jumps from `i` to `j`,
and the diagonal entry `Q i i` is minus the total rate of leaving `i`.

On finitely many states, the Metzler matrices are exactly the matrices that become entrywise
nonnegative after a large enough multiple of the identity is added to them
(`Matrix.isMetzler_iff_exists_add_smul_one_nonneg`).
This is what makes the exponential `exp (t • B)` of a Metzler matrix entrywise nonnegative for
`t ≥ 0`, and, for a Q-matrix, a stochastic matrix; see
`TauCeti/Analysis/Matrix/Exponential/Metzler.lean`.

## Main definitions

* `Matrix.IsMetzler`: every off-diagonal entry is nonnegative.
* `Matrix.IsQMatrix`: a Metzler matrix whose rows sum to zero.

## Main results

* `Matrix.isMetzler_iff_exists_add_smul_one_nonneg`: on a finite index type, a matrix over a
  linearly ordered ring is Metzler if and only if `B + c • 1` is entrywise nonnegative for some
  `c`.
* `Matrix.IsQMatrix.apply_self_eq_neg_sum`, `Matrix.IsQMatrix.apply_self_nonpos`: the diagonal
  entry of a Q-matrix is minus the sum of the off-diagonal entries of its row, hence nonpositive.
* `Matrix.isQMatrix_iff_isMetzler_and_mulVec_one_eq_zero`: a matrix is a Q-matrix if and only if
  it is Metzler and kills the all-ones column vector.
* `Matrix.IsQMatrix.eq_zero`: on at most one state, the only Q-matrix is the zero matrix.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Section 2.1, for Q-matrices.
-/

public section

open Finset

namespace Matrix

variable {n R : Type*}

section IsMetzler

variable [Zero R] [LE R]

/-- A square matrix is **Metzler** when every off-diagonal entry is nonnegative. The diagonal
entries are unconstrained. -/
def IsMetzler (B : Matrix n n R) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → 0 ≤ B i j

theorem isMetzler_iff {B : Matrix n n R} : B.IsMetzler ↔ ∀ i j, i ≠ j → 0 ≤ B i j :=
  Iff.rfl

/-- An off-diagonal entry of a Metzler matrix is nonnegative. -/
theorem IsMetzler.apply_nonneg {B : Matrix n n R} (hB : B.IsMetzler) {i j : n} (hij : i ≠ j) :
    0 ≤ B i j :=
  hB hij

/-- An entrywise nonnegative matrix is Metzler. -/
theorem isMetzler_of_nonneg {B : Matrix n n R} (hB : ∀ i j, 0 ≤ B i j) : B.IsMetzler :=
  fun i j _ ↦ hB i j

theorem IsMetzler.transpose {B : Matrix n n R} (hB : B.IsMetzler) : Bᵀ.IsMetzler :=
  fun _ _ hij ↦ hB hij.symm

@[simp]
theorem isMetzler_transpose {B : Matrix n n R} : Bᵀ.IsMetzler ↔ B.IsMetzler :=
  ⟨fun h ↦ h.transpose, fun h ↦ h.transpose⟩

end IsMetzler

section Preorder

variable [Zero R] [Preorder R]

@[simp]
theorem isMetzler_zero : (0 : Matrix n n R).IsMetzler :=
  isMetzler_of_nonneg fun _ _ ↦ le_rfl

/-- Every diagonal matrix is Metzler. -/
@[simp]
theorem isMetzler_diagonal [DecidableEq n] (d : n → R) : (diagonal d).IsMetzler :=
  fun _ _ hij ↦ by rw [diagonal_apply_ne d hij]

end Preorder

/-- Adding a diagonal matrix does not change whether a matrix is Metzler. -/
@[simp]
theorem isMetzler_add_diagonal_iff [AddZeroClass R] [LE R] [DecidableEq n] {B : Matrix n n R}
    (d : n → R) : (B + diagonal d).IsMetzler ↔ B.IsMetzler := by
  refine forall₂_congr fun i j ↦ imp_congr_right fun hij ↦ ?_
  rw [Matrix.add_apply, diagonal_apply_ne d hij, add_zero]

theorem IsMetzler.add [AddZeroClass R] [Preorder R] [AddLeftMono R] {A B : Matrix n n R}
    (hA : A.IsMetzler) (hB : B.IsMetzler) : (A + B).IsMetzler :=
  fun _ _ hij ↦ add_nonneg (hA hij) (hB hij)

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-- A nonnegative multiple of a Metzler matrix is Metzler. -/
theorem IsMetzler.smul {B : Matrix n n R} (hB : B.IsMetzler) {c : R} (hc : 0 ≤ c) :
    (c • B).IsMetzler :=
  fun _ _ hij ↦ mul_nonneg hc (hB hij)

end OrderedSemiring

/-- On a finite index type, a matrix over a linearly ordered ring is Metzler if and only if it
becomes entrywise nonnegative once a suitable multiple of the identity is added. -/
theorem isMetzler_iff_exists_add_smul_one_nonneg [Finite n] [DecidableEq n] [Ring R]
    [LinearOrder R] [IsOrderedRing R] {B : Matrix n n R} :
    B.IsMetzler ↔ ∃ c : R, ∀ i j, 0 ≤ (B + c • 1) i j := by
  have := Fintype.ofFinite n
  refine ⟨fun hB ↦ ⟨∑ i, |B i i|, fun i j ↦ ?_⟩, fun ⟨c, hc⟩ ↦ ?_⟩
  · rw [smul_one_eq_diagonal, Matrix.add_apply]
    rcases eq_or_ne i j with rfl | hij
    · -- The diagonal entry is at least `-|B i i|`, and the shift is at least `|B i i|`.
      rw [diagonal_apply_eq]
      have hle : |B i i| ≤ ∑ k, |B k k| :=
        single_le_sum (f := fun k ↦ |B k k|) (fun k _ ↦ abs_nonneg _) (mem_univ i)
      exact (neg_le_iff_add_nonneg.mp (neg_abs_le (B i i))).trans (add_le_add_right hle _)
    · rw [diagonal_apply_ne _ hij, add_zero]
      exact hB hij
  · rw [← isMetzler_add_diagonal_iff (fun _ ↦ c), ← smul_one_eq_diagonal]
    exact isMetzler_of_nonneg hc

section IsQMatrix

variable [Fintype n]

/-- A **Q-matrix** (a rate matrix, or generator, of a continuous-time Markov chain on finitely
many states) is a Metzler matrix whose rows sum to zero. -/
structure IsQMatrix [AddCommMonoid R] [LE R] (Q : Matrix n n R) : Prop where
  /-- The off-diagonal entries of a Q-matrix, the jump rates, are nonnegative. -/
  isMetzler : Q.IsMetzler
  /-- Each row of a Q-matrix sums to zero. -/
  sum_apply_eq_zero : ∀ i, ∑ j, Q i j = 0

section AddCommMonoid

variable [AddCommMonoid R]

theorem isQMatrix_iff [LE R] {Q : Matrix n n R} :
    Q.IsQMatrix ↔ Q.IsMetzler ∧ ∀ i, ∑ j, Q i j = 0 :=
  ⟨fun h ↦ ⟨h.isMetzler, h.sum_apply_eq_zero⟩, fun h ↦ ⟨h.1, h.2⟩⟩

@[simp]
theorem isQMatrix_zero [Preorder R] : (0 : Matrix n n R).IsQMatrix :=
  ⟨isMetzler_zero, fun _ ↦ by simp⟩

/-- On a type with at most one element, the only Q-matrix is the zero matrix. -/
theorem IsQMatrix.eq_zero [LE R] [Subsingleton n] {Q : Matrix n n R} (hQ : Q.IsQMatrix) :
    Q = 0 := by
  ext i j
  obtain rfl := Subsingleton.elim i j
  rw [Matrix.zero_apply, ← hQ.sum_apply_eq_zero i, Fintype.sum_subsingleton _ i]

theorem IsQMatrix.add [Preorder R] [AddLeftMono R] {P Q : Matrix n n R} (hP : P.IsQMatrix)
    (hQ : Q.IsQMatrix) : (P + Q).IsQMatrix :=
  ⟨hP.isMetzler.add hQ.isMetzler, fun i ↦ by
    simp [sum_add_distrib, hP.sum_apply_eq_zero i, hQ.sum_apply_eq_zero i]⟩

end AddCommMonoid

section NonAssocSemiring

variable [NonAssocSemiring R] [LE R]

/-- A Q-matrix kills the all-ones column vector. -/
theorem IsQMatrix.mulVec_one_eq_zero {Q : Matrix n n R} (hQ : Q.IsQMatrix) : Q *ᵥ 1 = 0 := by
  ext i
  simpa [mulVec, dotProduct] using hQ.sum_apply_eq_zero i

/-- A matrix is a Q-matrix if and only if it is Metzler and kills the all-ones column vector. -/
theorem isQMatrix_iff_isMetzler_and_mulVec_one_eq_zero {Q : Matrix n n R} :
    Q.IsQMatrix ↔ Q.IsMetzler ∧ Q *ᵥ 1 = 0 := by
  refine ⟨fun h ↦ ⟨h.isMetzler, h.mulVec_one_eq_zero⟩, fun ⟨hM, h1⟩ ↦ ⟨hM, fun i ↦ ?_⟩⟩
  simpa [mulVec, dotProduct] using congrFun h1 i

end NonAssocSemiring

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-- A nonnegative multiple of a Q-matrix is a Q-matrix. -/
theorem IsQMatrix.smul {Q : Matrix n n R} (hQ : Q.IsQMatrix) {c : R} (hc : 0 ≤ c) :
    (c • Q).IsQMatrix :=
  ⟨hQ.isMetzler.smul hc, fun i ↦ by simp [← mul_sum, hQ.sum_apply_eq_zero i]⟩

end OrderedSemiring

section AddCommGroup

variable [AddCommGroup R]

/-- The diagonal entry of a Q-matrix is minus the total rate of leaving that state, the sum of
the off-diagonal entries of its row. -/
theorem IsQMatrix.apply_self_eq_neg_sum [DecidableEq n] [LE R] {Q : Matrix n n R}
    (hQ : Q.IsQMatrix) (i : n) : Q i i = -∑ j ∈ univ.erase i, Q i j := by
  rw [eq_neg_iff_add_eq_zero, add_sum_erase _ _ (mem_univ i), hQ.sum_apply_eq_zero i]

/-- The diagonal entries of a Q-matrix are nonpositive. -/
theorem IsQMatrix.apply_self_nonpos [PartialOrder R] [IsOrderedAddMonoid R] {Q : Matrix n n R}
    (hQ : Q.IsQMatrix) (i : n) : Q i i ≤ 0 := by
  classical
  rw [hQ.apply_self_eq_neg_sum i, neg_nonpos]
  exact sum_nonneg fun j hj ↦ hQ.isMetzler (ne_of_mem_erase hj).symm

end AddCommGroup

end IsQMatrix

end Matrix
