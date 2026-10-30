/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generators
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Space
import TauCeti.Data.Matrix.Basis
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# Root generators of the split even orthogonal Lie algebra

Relative to the split diagonal Cartan, the roots of the even orthogonal Lie algebra have the
three matrix shapes

```text
εᵢ - εⱼ,    εᵢ + εⱼ,    and    -εᵢ - εⱼ,
```

where `i ≠ j`. This file defines a standard generator for every root of each shape. The
difference-root generator has paired entries in its diagonal blocks, while the two sum-root
generators have a skew pair in the upper-right or lower-left block. The block description makes
membership in the split type-`D` Lie algebra immediate from `Matrix.fromBlocks_mem_typeD`.

The entry-support criterion for the diagonal Cartan then places each generator in its named root
space over an arbitrary commutative ring. At the simple roots, these families agree with the
previously defined Bourbaki-numbered raising and lowering generators.

The bracket table covers all pairs of generator families and all index collisions, including
diagonal difference-root generators. It holds over every commutative ring and identifies the
diagonal generators with the coordinate vectors of the split Cartan.

## Main declarations

* `TauCeti.TypeDStd.differenceRootGenerator`: a generator of weight `εᵢ - εⱼ`.
* `TauCeti.TypeDStd.sumRootGenerator`: a generator of weight `εᵢ + εⱼ`.
* `TauCeti.TypeDStd.negSumRootGenerator`: a generator of weight `-εᵢ - εⱼ`.
* The six general bracket identities, from
  `TauCeti.TypeDStd.lie_differenceRootGenerator_differenceRootGenerator_eq_ite` to
  `TauCeti.TypeDStd.lie_negSumRootGenerator_negSumRootGenerator`, give the full table.
* `TauCeti.TypeDStd.differenceRootGenerator_self_eq_typeDDiagonalEquiv` identifies the
  diagonal members with Cartan coordinate vectors.
* `TauCeti.TypeDStd.lie_differenceRootGenerator_differenceRootGenerator` and
  `TauCeti.TypeDStd.lie_differenceRootGenerator_sumRootGenerator`: bracket identities for
  consecutive standard root generators.
* `TauCeti.TypeDStd.differenceRootGenerator_mem_rootSpace` and the two sum-root analogues:
  membership in the corresponding root spaces.
* The chain and fork comparison theorems at the end of the file identify these vectors with the
  numbered raising and lowering generators at the simple roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8, 12.
-/

public section

namespace TauCeti.TypeDStd

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [DecidableEq ι]

/-! ## Ambient matrices -/

section Ambient

variable [AddGroupWithOne K]

/-- The ambient root matrix of weight `εᵢ - εⱼ`. -/
def differenceRootMatrix (i j : ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) K :=
  let A : Matrix ι ι K := Matrix.single i j 1
  Matrix.fromBlocks A 0 0 (-A.transpose)

/-- The ambient root matrix of weight `εᵢ + εⱼ`. Swapping the indices negates the matrix. -/
def sumRootMatrix (i j : ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) K :=
  let B : Matrix ι ι K := Matrix.single i j 1 - Matrix.single j i 1
  Matrix.fromBlocks 0 B 0 0

/-- The ambient root matrix of weight `-εᵢ - εⱼ`. Swapping the indices negates the matrix. -/
def negSumRootMatrix (i j : ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) K :=
  let C : Matrix ι ι K := Matrix.single i j 1 - Matrix.single j i 1
  Matrix.fromBlocks 0 0 C 0

/-- The block formula for a difference-root matrix. -/
theorem differenceRootMatrix_def (i j : ι) :
    differenceRootMatrix (K := K) i j =
      let A : Matrix ι ι K := Matrix.single i j 1
      Matrix.fromBlocks A 0 0 (-A.transpose) :=
  (rfl)

/-- The block formula for a positive sum-root matrix. -/
theorem sumRootMatrix_def (i j : ι) :
    sumRootMatrix (K := K) i j =
      let B : Matrix ι ι K := Matrix.single i j 1 - Matrix.single j i 1
      Matrix.fromBlocks 0 B 0 0 :=
  (rfl)

/-- The block formula for a negative sum-root matrix. -/
theorem negSumRootMatrix_def (i j : ι) :
    negSumRootMatrix (K := K) i j =
      let C : Matrix ι ι K := Matrix.single i j 1 - Matrix.single j i 1
      Matrix.fromBlocks 0 0 C 0 :=
  (rfl)

/-- Swapping the coordinates negates a positive sum-root matrix. -/
theorem sumRootMatrix_swap (i j : ι) :
    sumRootMatrix (K := K) j i = -sumRootMatrix i j := by
  ext (a | a) (b | b) <;>
    simp [sumRootMatrix, Matrix.fromBlocks, Matrix.single_apply]

/-- Swapping the coordinates negates a negative sum-root matrix. -/
theorem negSumRootMatrix_swap (i j : ι) :
    negSumRootMatrix (K := K) j i = -negSumRootMatrix i j := by
  ext (a | a) (b | b) <;>
    simp [negSumRootMatrix, Matrix.fromBlocks, Matrix.single_apply]

/-- A positive sum-root matrix with equal coordinates is zero. -/
@[simp]
theorem sumRootMatrix_self (i : ι) : sumRootMatrix (K := K) i i = 0 := by
  simp [sumRootMatrix]

/-- A negative sum-root matrix with equal coordinates is zero. -/
@[simp]
theorem negSumRootMatrix_self (i : ι) : negSumRootMatrix (K := K) i i = 0 := by
  simp [negSumRootMatrix]

end Ambient

section Fintype

variable [CommRing K] [Fintype ι]

/-- A difference-root matrix is skew-adjoint for the split type-`D` Gram matrix. -/
theorem differenceRootMatrix_mem_typeD (i j : ι) :
    differenceRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeD ι K := by
  exact Matrix.fromBlocks_mem_typeD (ι := ι) _ 0 0 (by simp) (by simp)

/-- A positive sum-root matrix is skew-adjoint for the split type-`D` Gram matrix. -/
theorem sumRootMatrix_mem_typeD (i j : ι) :
    sumRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeD ι K := by
  rw [sumRootMatrix_def]
  simpa only [Matrix.transpose_zero, neg_zero] using
    Matrix.fromBlocks_mem_typeD (K := K) (ι := ι) 0
      (Matrix.single i j 1 - Matrix.single j i 1) 0
        (Matrix.transpose_single_sub_single i j (a := (1 : K))) (by simp)

/-- A negative sum-root matrix is skew-adjoint for the split type-`D` Gram matrix. -/
theorem negSumRootMatrix_mem_typeD (i j : ι) :
    negSumRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeD ι K := by
  rw [negSumRootMatrix_def]
  simpa only [Matrix.transpose_zero, neg_zero] using
    Matrix.fromBlocks_mem_typeD (K := K) (ι := ι) 0 0
      (Matrix.single i j 1 - Matrix.single j i 1) (by simp)
        (Matrix.transpose_single_sub_single i j (a := (1 : K)))

/-! ## Bundled generators -/

/-- The standard type-`D` matrix of weight `εᵢ - εⱼ`, bundled in the orthogonal Lie algebra. -/
def differenceRootGenerator (i j : ι) : LieAlgebra.Orthogonal.typeD ι K :=
  ⟨differenceRootMatrix i j, differenceRootMatrix_mem_typeD i j⟩

/-- The standard type-`D` matrix of weight `εᵢ + εⱼ`, bundled in the orthogonal Lie algebra. -/
def sumRootGenerator (i j : ι) : LieAlgebra.Orthogonal.typeD ι K :=
  ⟨sumRootMatrix i j, sumRootMatrix_mem_typeD i j⟩

/-- The standard type-`D` matrix of weight `-εᵢ - εⱼ`, bundled in the orthogonal Lie algebra. -/
def negSumRootGenerator (i j : ι) : LieAlgebra.Orthogonal.typeD ι K :=
  ⟨negSumRootMatrix i j, negSumRootMatrix_mem_typeD i j⟩

/-- The matrix underlying a difference-root generator. -/
@[simp]
theorem val_differenceRootGenerator (i j : ι) :
    (differenceRootGenerator (K := K) i j : Matrix (ι ⊕ ι) (ι ⊕ ι) K) =
      differenceRootMatrix i j :=
  by simp [differenceRootGenerator]

/-- The matrix underlying a positive sum-root generator. -/
@[simp]
theorem val_sumRootGenerator (i j : ι) :
    (sumRootGenerator (K := K) i j : Matrix (ι ⊕ ι) (ι ⊕ ι) K) =
      sumRootMatrix i j :=
  by simp [sumRootGenerator]

/-- The matrix underlying a negative sum-root generator. -/
@[simp]
theorem val_negSumRootGenerator (i j : ι) :
    (negSumRootGenerator (K := K) i j : Matrix (ι ⊕ ι) (ι ⊕ ι) K) =
      negSumRootMatrix i j :=
  by simp [negSumRootGenerator]

/-- Swapping the coordinates negates a positive sum-root generator. -/
theorem sumRootGenerator_swap (i j : ι) :
    sumRootGenerator (K := K) j i = -sumRootGenerator i j := by
  apply Subtype.ext
  simpa using sumRootMatrix_swap (K := K) i j

/-- Swapping the coordinates negates a negative sum-root generator. -/
theorem negSumRootGenerator_swap (i j : ι) :
    negSumRootGenerator (K := K) j i = -negSumRootGenerator i j := by
  apply Subtype.ext
  simpa using negSumRootMatrix_swap (K := K) i j

/-- A positive sum-root generator with equal coordinates is zero. -/
@[simp]
theorem sumRootGenerator_self (i : ι) : sumRootGenerator (K := K) i i = 0 := by
  apply Subtype.ext
  simp

/-- A negative sum-root generator with equal coordinates is zero. -/
@[simp]
theorem negSumRootGenerator_self (i : ι) : negSumRootGenerator (K := K) i i = 0 := by
  apply Subtype.ext
  simp

/-- A difference-root generator is nonzero over a nontrivial ring. -/
theorem differenceRootGenerator_ne_zero [Nontrivial K] (i j : ι) :
    differenceRootGenerator (K := K) i j ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inl i)) (.inl j)
  simp [differenceRootMatrix, Matrix.fromBlocks] at hentry

/-- A positive sum-root generator is nonzero over a nontrivial ring. -/
theorem sumRootGenerator_ne_zero [Nontrivial K] (i j : ι) (hij : i ≠ j) :
    sumRootGenerator (K := K) i j ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inl i)) (.inr j)
  simp [sumRootMatrix, Matrix.fromBlocks, hij] at hentry

/-- A negative sum-root generator is nonzero over a nontrivial ring. -/
theorem negSumRootGenerator_ne_zero [Nontrivial K] (i j : ι) (hij : i ≠ j) :
    negSumRootGenerator (K := K) i j ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inr i)) (.inl j)
  simp [negSumRootMatrix, Matrix.fromBlocks, hij] at hentry

/-! ## Brackets of standard root generators -/

/-- The diagonal member of the difference-root family is a Cartan coordinate vector. -/
theorem differenceRootGenerator_self_eq_typeDDiagonalEquiv (i : ι) :
    differenceRootGenerator (K := K) i i =
      (typeDDiagonalEquiv (K := K) (Pi.single i 1) : typeDDiagonalCartan K ι) := by
  apply Subtype.ext
  rw [val_differenceRootGenerator, coe_typeDDiagonalEquiv_apply]
  dsimp only
  ext (a | a) (b | b) <;>
    simp [differenceRootMatrix_def, Matrix.transpose_single, typeDDiagonalMatrix_apply,
      Matrix.single_apply, Pi.single_apply, eq_comm] <;>
    split_ifs <;> grind

/-- The bracket of two difference-root generators, including all index collisions. -/
theorem lie_differenceRootGenerator_differenceRootGenerator_eq_ite (i j k l : ι) :
    ⁅differenceRootGenerator (K := K) i j, differenceRootGenerator (K := K) k l⁆ =
      (if j = k then differenceRootGenerator (K := K) i l else 0) -
        (if l = i then differenceRootGenerator (K := K) k j else 0) := by
  apply Subtype.ext
  split_ifs with hjk hli
  all_goals
    simp only [LieSubalgebra.coe_bracket, AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero,
      val_differenceRootGenerator]
    simp only [LieRing.of_associative_ring_bracket, differenceRootMatrix_def,
      Matrix.fromBlocks_mul_sub_mul, Matrix.transpose_single, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg, Matrix.single_mul_single_eq_ite, one_mul, zero_mul, mul_zero,
      zero_add, add_zero]
    ext (a | a) (b | b) <;> simp_all [eq_comm]
  all_goals abel

/-- The bracket of a difference-root generator and a positive sum-root generator. -/
theorem lie_differenceRootGenerator_sumRootGenerator_eq_ite (i j k l : ι) :
    ⁅differenceRootGenerator (K := K) i j, sumRootGenerator (K := K) k l⁆ =
      (if j = k then sumRootGenerator (K := K) i l else 0) -
        (if j = l then sumRootGenerator (K := K) i k else 0) := by
  apply Subtype.ext
  split_ifs with hjk hjl
  all_goals
    simp only [LieSubalgebra.coe_bracket, AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero,
      val_differenceRootGenerator, val_sumRootGenerator]
    simp only [LieRing.of_associative_ring_bracket, differenceRootMatrix_def, sumRootMatrix_def,
      Matrix.fromBlocks_mul_sub_mul, Matrix.transpose_single, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_neg, Matrix.single_mul_single_eq_ite, one_mul, zero_mul, mul_zero,
      zero_add, add_zero]
    ext (a | a) (b | b) <;> simp_all [eq_comm]
  all_goals abel

/-- The bracket of a difference-root generator and a negative sum-root generator. -/
theorem lie_differenceRootGenerator_negSumRootGenerator_eq_ite (i j k l : ι) :
    ⁅differenceRootGenerator (K := K) i j, negSumRootGenerator (K := K) k l⁆ =
      -(if i = k then negSumRootGenerator (K := K) j l else 0) +
        (if i = l then negSumRootGenerator (K := K) j k else 0) := by
  apply Subtype.ext
  split_ifs with hik hil
  all_goals
    simp only [LieSubalgebra.coe_bracket, AddMemClass.coe_add, NegMemClass.coe_neg,
      ZeroMemClass.coe_zero, val_differenceRootGenerator, val_negSumRootGenerator]
    simp only [LieRing.of_associative_ring_bracket, differenceRootMatrix_def, negSumRootMatrix_def,
      Matrix.fromBlocks_mul_sub_mul, Matrix.transpose_single, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.single_mul_single_eq_ite, one_mul, zero_mul, mul_zero,
      zero_add, add_zero]
    ext (a | a) (b | b) <;> simp_all [eq_comm]
  all_goals abel

/-- The bracket of opposite sum-root families, with their native matrix signs. -/
theorem lie_sumRootGenerator_negSumRootGenerator_eq_ite (i j k l : ι) :
    ⁅sumRootGenerator (K := K) i j, negSumRootGenerator (K := K) k l⁆ =
      (if j = k then differenceRootGenerator (K := K) i l else 0) -
        (if j = l then differenceRootGenerator (K := K) i k else 0) -
        (if i = k then differenceRootGenerator (K := K) j l else 0) +
        (if i = l then differenceRootGenerator (K := K) j k else 0) := by
  apply Subtype.ext
  split_ifs with hjk hjl hik hil
  all_goals
    simp only [LieSubalgebra.coe_bracket, AddSubgroupClass.coe_sub, AddMemClass.coe_add,
      ZeroMemClass.coe_zero, val_differenceRootGenerator, val_sumRootGenerator,
      val_negSumRootGenerator]
    simp only [LieRing.of_associative_ring_bracket, differenceRootMatrix_def, sumRootMatrix_def,
      negSumRootMatrix_def, Matrix.fromBlocks_mul_sub_mul, Matrix.transpose_single, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.single_mul_single_eq_ite, one_mul, zero_mul, mul_zero,
      zero_add, add_zero]
    ext (a | a) (b | b) <;> simp_all [eq_comm]
  all_goals abel

/-- Any two positive sum-root generators commute. -/
@[simp]
theorem lie_sumRootGenerator_sumRootGenerator (i j k l : ι) :
    ⁅sumRootGenerator (K := K) i j, sumRootGenerator (K := K) k l⁆ =
      0 := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, val_sumRootGenerator, ZeroMemClass.coe_zero]
  simp [sumRootMatrix_def, LieRing.of_associative_ring_bracket,
    Matrix.fromBlocks_mul_sub_mul]

/-- Any two negative sum-root generators commute. -/
@[simp]
theorem lie_negSumRootGenerator_negSumRootGenerator (i j k l : ι) :
    ⁅negSumRootGenerator (K := K) i j, negSumRootGenerator (K := K) k l⁆ =
      0 := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, val_negSumRootGenerator, ZeroMemClass.coe_zero]
  simp [negSumRootMatrix_def, LieRing.of_associative_ring_bracket,
    Matrix.fromBlocks_mul_sub_mul]

/-- Bracketing two consecutive difference-root vectors concatenates their coordinate intervals.

Only the endpoints must be distinct; the identity remains valid when the intermediate coordinate
coincides with either endpoint. -/
@[simp]
theorem lie_differenceRootGenerator_differenceRootGenerator (i j k : ι) (hik : i ≠ k) :
    ⁅differenceRootGenerator (K := K) i j, differenceRootGenerator (K := K) j k⁆ =
      differenceRootGenerator (K := K) i k := by
  simp only [lie_differenceRootGenerator_differenceRootGenerator_eq_ite, ↓reduceIte,
    hik.symm, sub_zero]

/-- Bracketing a difference-root vector with a consecutive sum-root vector moves the latter's
first coordinate. The condition prevents the sum-root vector on the left from degenerating. -/
@[simp]
theorem lie_differenceRootGenerator_sumRootGenerator (i j k : ι) (hjk : j ≠ k) :
    ⁅differenceRootGenerator (K := K) i j, sumRootGenerator (K := K) j k⁆ =
      sumRootGenerator (K := K) i k := by
  simp only [lie_differenceRootGenerator_sumRootGenerator_eq_ite, ↓reduceIte,
    hjk, sub_zero]

/-! ## Root-space membership -/

/-- The standard difference-root generator has weight `εᵢ - εⱼ`. -/
theorem differenceRootGenerator_mem_rootSpace (i j : ι) :
    differenceRootGenerator (K := K) i j ∈
      LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightSub i j) := by
  apply mem_rootSpace_typeDDiagonalCartan_of_forall
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · by_cases hia : i = a
    · subst a
      by_cases hjb : j = b
      · subst b
        exact (hab (typeDMatrixWeight_inl_inl i j)).elim
      · simp [differenceRootGenerator, differenceRootMatrix, Matrix.fromBlocks, hjb]
    · simp [differenceRootGenerator, differenceRootMatrix, Matrix.fromBlocks, hia]
  · simp [differenceRootGenerator, differenceRootMatrix, Matrix.fromBlocks]
  · simp [differenceRootGenerator, differenceRootMatrix, Matrix.fromBlocks]
  · by_cases hib : i = b
    · subst b
      by_cases hja : j = a
      · subst a
        exact (hab (by simp)).elim
      · simp [differenceRootGenerator, differenceRootMatrix, Matrix.fromBlocks, hja]
    · simp [differenceRootGenerator, differenceRootMatrix, Matrix.fromBlocks, hib]

/-- The standard positive sum-root generator has weight `εᵢ + εⱼ`. -/
theorem sumRootGenerator_mem_rootSpace (i j : ι) :
    sumRootGenerator (K := K) i j ∈
      LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightAdd i j) := by
  apply mem_rootSpace_typeDDiagonalCartan_of_forall
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    simp [sumRootGenerator, sumRootMatrix, Matrix.fromBlocks, Matrix.single_apply] at hab ⊢
  all_goals split_ifs with h <;> simp_all [typeDWeightAdd_comm]

/-- The standard negative sum-root generator has weight `-εᵢ - εⱼ`. -/
theorem negSumRootGenerator_mem_rootSpace (i j : ι) :
    negSumRootGenerator (K := K) i j ∈
      LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (-typeDWeightAdd i j) := by
  apply mem_rootSpace_typeDDiagonalCartan_of_forall
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    simp [negSumRootGenerator, negSumRootMatrix, Matrix.fromBlocks, Matrix.single_apply] at hab ⊢
  all_goals split_ifs with h <;> simp_all [typeDWeightAdd_comm]

/-! ## Compatibility with the numbered simple generators -/

/-- On a chain node, the all-root difference generator is the numbered raising generator. -/
theorem differenceRootGenerator_chain_eq_rootGenerator (n : ℕ) (hn : 4 ≤ n)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    differenceRootGenerator (K := K) i (chainNext n i hi) =
      rootGenerator (K := K) n hn (.inl i) := by
  apply Subtype.ext
  rw [val_differenceRootGenerator, val_rootGenerator_inl, raisingMatrix_of_chain n hn hi]
  rfl

/-- At the fork node, the all-root positive sum generator is the numbered raising generator. -/
theorem sumRootGenerator_fork_eq_rootGenerator (n : ℕ) (hn : 4 ≤ n) :
    sumRootGenerator (K := K) (forkLeft n hn) (forkRight n hn) =
      rootGenerator (K := K) n hn (.inl (forkRight n hn)) := by
  apply Subtype.ext
  rw [val_sumRootGenerator, val_rootGenerator_inl]
  have hfork : ¬((forkRight n hn : Fin n) : ℕ) + 1 < n := by
    rw [forkRight_val]
    omega
  rw [raisingMatrix_of_fork n hn hfork]
  rfl

/-- On a chain node, the reversed difference generator is the numbered lowering generator. -/
theorem differenceRootGenerator_reverse_chain_eq_rootGenerator (n : ℕ) (hn : 4 ≤ n)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    differenceRootGenerator (K := K) (chainNext n i hi) i =
      rootGenerator (K := K) n hn (.inr i) := by
  apply Subtype.ext
  rw [val_differenceRootGenerator, val_rootGenerator_inr, loweringMatrix_of_chain n hn hi]
  ext (a | a) (b | b) <;>
    simp [differenceRootMatrix, Matrix.fromBlocks, Matrix.single_apply]

/-- At the fork node, the reversed negative sum generator is the numbered lowering generator. -/
theorem negSumRootGenerator_reverse_fork_eq_rootGenerator (n : ℕ) (hn : 4 ≤ n) :
    negSumRootGenerator (K := K) (forkRight n hn) (forkLeft n hn) =
      rootGenerator (K := K) n hn (.inr (forkRight n hn)) := by
  apply Subtype.ext
  rw [val_negSumRootGenerator, val_rootGenerator_inr]
  have hfork : ¬((forkRight n hn : Fin n) : ℕ) + 1 < n := by
    rw [forkRight_val]
    omega
  rw [loweringMatrix_of_fork n hn hfork]
  ext (a | a) (b | b) <;>
    simp [negSumRootMatrix, Matrix.fromBlocks, Matrix.single_apply]

end Fintype

end TauCeti.TypeDStd
