/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Stochastic

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

The **uniformized matrix** `Matrix.uniformized Q r = 1 + r⁻¹ • Q` at a rate `r > 0` is
row-stochastic exactly when `Q` is a Q-matrix whose total jump rates `-Q i i` are at most `r`
(`Matrix.uniformized_mem_rowStochastic_iff`). It is the transition matrix of the discrete chain
that jumps at the rings of a clock of rate `r`; for `t ≥ 0`, the exponential `exp (t • Q)` is the
average of its powers under the Poisson law of mean `r t`, see
`TauCeti/Analysis/Matrix/Exponential/Uniformization.lean`.

## Main definitions

* `Matrix.IsMetzler`: every off-diagonal entry is nonnegative.
* `Matrix.IsQMatrix`: a Metzler matrix whose rows sum to zero.
* `Matrix.uniformized`: the matrix `1 + r⁻¹ • Q`.

## Main results

* `Matrix.isMetzler_iff_exists_add_smul_one_nonneg`: on a finite index type, a matrix over a
  linearly ordered ring is Metzler if and only if `B + c • 1` is entrywise nonnegative for some
  `c`.
* `Matrix.IsQMatrix.apply_self_eq_neg_sum`, `Matrix.IsQMatrix.apply_self_nonpos`: the diagonal
  entry of a Q-matrix is minus the sum of the off-diagonal entries of its row, hence nonpositive.
* `Matrix.isQMatrix_iff_isMetzler_and_mulVec_one_eq_zero`: a matrix is a Q-matrix if and only if
  it is Metzler and kills the all-ones column vector.
* `Matrix.IsQMatrix.eq_zero`: on at most one state, the only Q-matrix is the zero matrix.
* `Matrix.uniformized_mem_rowStochastic_iff`: for `r > 0`, the uniformized matrix `1 + r⁻¹ • Q` is
  row-stochastic if and only if `Q` is a Q-matrix with `-Q i i ≤ r` for every `i`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Section 2.1, for Q-matrices.
* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, second edition, American
  Mathematical Society, 2017, Section 20.1, p. 281, for the uniformized matrix of a Q-matrix.
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

section Uniformized

variable [DecidableEq n]

section DivisionRing

variable [DivisionRing R] {Q : Matrix n n R} {r : R} {i j : n}

/-- The **uniformized matrix** `1 + r⁻¹ • Q` of a square matrix `Q` at a rate `r`. When `Q` is a
Q-matrix and `r > 0` bounds every total jump rate `-Q i i`, it is the stochastic matrix of the
discrete chain that jumps at the rings of a clock of rate `r`
(`Matrix.uniformized_mem_rowStochastic_iff`). For `r = 0` it is the identity matrix, since
`0⁻¹ = 0`. -/
def uniformized (Q : Matrix n n R) (r : R) : Matrix n n R :=
  1 + r⁻¹ • Q

theorem uniformized_def (Q : Matrix n n R) (r : R) : Q.uniformized r = 1 + r⁻¹ • Q :=
  (rfl)

theorem uniformized_apply (Q : Matrix n n R) (r : R) (i j : n) :
    Q.uniformized r i j = (1 : Matrix n n R) i j + r⁻¹ * Q i j :=
  (rfl)

@[simp]
theorem uniformized_apply_self (Q : Matrix n n R) (r : R) (i : n) :
    Q.uniformized r i i = 1 + r⁻¹ * Q i i := by
  rw [uniformized_apply, one_apply_eq]

@[simp]
theorem uniformized_apply_of_ne (Q : Matrix n n R) (r : R) (hij : i ≠ j) :
    Q.uniformized r i j = r⁻¹ * Q i j := by
  rw [uniformized_apply, one_apply_ne hij, zero_add]

@[simp]
theorem uniformized_zero_left (r : R) : (0 : Matrix n n R).uniformized r = 1 := by
  rw [uniformized_def, smul_zero, add_zero]

/-- At the rate `r = 0` the uniformized matrix is the identity, because `0⁻¹ = 0`. -/
@[simp]
theorem uniformized_zero_right (Q : Matrix n n R) : Q.uniformized 0 = 1 := by
  simp [uniformized_def]

/-- For a nonzero rate `r`, the matrix `Q` is recovered from its uniformized matrix as
`r • (K - 1)`. -/
theorem smul_uniformized_sub_one (hr : r ≠ 0) : r • (Q.uniformized r - 1) = Q := by
  rw [uniformized_def, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr, one_smul]

end DivisionRing

/-- **The uniformized matrix is stochastic.** For a rate `r > 0`, the matrix `1 + r⁻¹ • Q` is
row-stochastic if and only if `Q` is a Q-matrix whose total jump rates `-Q i i` are at most `r`. -/
theorem uniformized_mem_rowStochastic_iff [Fintype n] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {Q : Matrix n n R} {r : R} (hr : 0 < r) :
    Q.uniformized r ∈ rowStochastic R n ↔ Q.IsQMatrix ∧ ∀ i, -Q i i ≤ r := by
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  -- A diagonal entry `1 + r⁻¹ * Q i i` is nonnegative exactly when `-Q i i ≤ r`.
  have hdiag (i : n) : 0 ≤ Q.uniformized r i i ↔ -Q i i ≤ r := by
    have h : 1 + r⁻¹ * Q i i = r⁻¹ * (r + Q i i) := by rw [mul_add, inv_mul_cancel₀ hr.ne']
    rw [uniformized_apply_self, h, mul_nonneg_iff_of_pos_left hr', neg_le_iff_add_nonneg]
  have hoff {i j : n} (hij : i ≠ j) : 0 ≤ Q.uniformized r i j ↔ 0 ≤ Q i j := by
    rw [uniformized_apply_of_ne Q r hij, mul_nonneg_iff_of_pos_left hr']
  -- `(1 + r⁻¹ • Q) *ᵥ 1 = 1 + r⁻¹ • (Q *ᵥ 1)`, so the rows sum to one exactly when those of `Q`
  -- sum to zero.
  have hrow : Q.uniformized r *ᵥ 1 = 1 ↔ Q *ᵥ 1 = 0 := by
    rw [uniformized_def, add_mulVec, one_mulVec, smul_mulVec, add_eq_left, smul_eq_zero]
    simp [hr.ne']
  rw [mem_rowStochastic, isQMatrix_iff_isMetzler_and_mulVec_one_eq_zero, hrow]
  refine ⟨fun ⟨hnn, hsum⟩ ↦ ⟨⟨isMetzler_iff.mpr fun i j hij ↦ (hoff hij).mp (hnn i j), hsum⟩,
    fun i ↦ (hdiag i).mp (hnn i i)⟩, fun ⟨⟨hM, hsum⟩, hd⟩ ↦ ⟨fun i j ↦ ?_, hsum⟩⟩
  rcases eq_or_ne i j with rfl | hij
  · exact (hdiag i).mpr (hd i)
  · exact (hoff hij).mpr (hM hij)

end Uniformized

end Matrix
