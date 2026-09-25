/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Generators
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Space

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
membership in the split type-`D` Lie algebra immediate from `TypeDStd.fromBlocks_mem_typeD`.

The entry-support criterion for the diagonal Cartan then places each generator in its named root
space over an arbitrary commutative ring. At the simple roots, the difference and positive-sum
families agree with the previously defined Bourbaki-numbered raising generators.

## Main declarations

* `TauCeti.TypeDStd.differenceRootGenerator`: a generator of weight `εᵢ - εⱼ`.
* `TauCeti.TypeDStd.sumRootGenerator`: a generator of weight `εᵢ + εⱼ`.
* `TauCeti.TypeDStd.negSumRootGenerator`: a generator of weight `-εᵢ - εⱼ`.
* `TauCeti.TypeDStd.differenceRootGenerator_mem_rootSpace` and the two sum-root analogues:
  membership in the corresponding root spaces.
* `TauCeti.TypeDStd.differenceRootGenerator_chain_eq_rootGenerator` and
  `TauCeti.TypeDStd.sumRootGenerator_fork_eq_rootGenerator`: compatibility with the numbered
  simple generators.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8, 12.
-/

public section

namespace TauCeti.TypeDStd

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι]

/-! ## Ambient matrices -/

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

private theorem transpose_single_sub_single (i j : ι) :
    (Matrix.single i j (1 : K) - Matrix.single j i 1).transpose =
      -(Matrix.single i j 1 - Matrix.single j i 1) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_single]
  abel

section Fintype

variable [Fintype ι]

/-- A difference-root matrix is skew-adjoint for the split type-`D` Gram matrix. -/
theorem differenceRootMatrix_mem_typeD (i j : ι) :
    differenceRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeD ι K := by
  exact fromBlocks_mem_typeD (ι := ι) _ 0 0 (by simp) (by simp)

/-- A positive sum-root matrix is skew-adjoint for the split type-`D` Gram matrix. -/
theorem sumRootMatrix_mem_typeD (i j : ι) :
    sumRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeD ι K := by
  rw [sumRootMatrix_def]
  simpa only [Matrix.transpose_zero, neg_zero] using
    fromBlocks_mem_typeD (K := K) (ι := ι) 0
      (Matrix.single i j 1 - Matrix.single j i 1) 0 (transpose_single_sub_single i j) (by simp)

/-- A negative sum-root matrix is skew-adjoint for the split type-`D` Gram matrix. -/
theorem negSumRootMatrix_mem_typeD (i j : ι) :
    negSumRootMatrix (K := K) i j ∈ LieAlgebra.Orthogonal.typeD ι K := by
  rw [negSumRootMatrix_def]
  simpa only [Matrix.transpose_zero, neg_zero] using
    fromBlocks_mem_typeD (K := K) (ι := ι) 0 0
      (Matrix.single i j 1 - Matrix.single j i 1) (by simp) (transpose_single_sub_single i j)

/-! ## Bundled generators -/

/-- The standard type-`D` root generator of weight `εᵢ - εⱼ`, for distinct indices. -/
def differenceRootGenerator (i j : ι) (_hij : i ≠ j) :
    LieAlgebra.Orthogonal.typeD ι K :=
  ⟨differenceRootMatrix i j, differenceRootMatrix_mem_typeD i j⟩

/-- The standard type-`D` root generator of weight `εᵢ + εⱼ`, for distinct indices. -/
def sumRootGenerator (i j : ι) (_hij : i ≠ j) : LieAlgebra.Orthogonal.typeD ι K :=
  ⟨sumRootMatrix i j, sumRootMatrix_mem_typeD i j⟩

/-- The standard type-`D` root generator of weight `-εᵢ - εⱼ`, for distinct indices. -/
def negSumRootGenerator (i j : ι) (_hij : i ≠ j) : LieAlgebra.Orthogonal.typeD ι K :=
  ⟨negSumRootMatrix i j, negSumRootMatrix_mem_typeD i j⟩

/-- The matrix underlying a difference-root generator. -/
@[simp]
theorem coe_differenceRootGenerator (i j : ι) (hij : i ≠ j) :
    (differenceRootGenerator (K := K) i j hij : Matrix (ι ⊕ ι) (ι ⊕ ι) K) =
      differenceRootMatrix i j :=
  by simp [differenceRootGenerator]

/-- The matrix underlying a positive sum-root generator. -/
@[simp]
theorem coe_sumRootGenerator (i j : ι) (hij : i ≠ j) :
    (sumRootGenerator (K := K) i j hij : Matrix (ι ⊕ ι) (ι ⊕ ι) K) =
      sumRootMatrix i j :=
  by simp [sumRootGenerator]

/-- The matrix underlying a negative sum-root generator. -/
@[simp]
theorem coe_negSumRootGenerator (i j : ι) (hij : i ≠ j) :
    (negSumRootGenerator (K := K) i j hij : Matrix (ι ⊕ ι) (ι ⊕ ι) K) =
      negSumRootMatrix i j :=
  by simp [negSumRootGenerator]

/-- A difference-root generator is nonzero over a nontrivial ring. -/
theorem differenceRootGenerator_ne_zero [Nontrivial K] (i j : ι) (hij : i ≠ j) :
    differenceRootGenerator (K := K) i j hij ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inl i)) (.inl j)
  simp [differenceRootMatrix, Matrix.fromBlocks] at hentry

/-- A positive sum-root generator is nonzero over a nontrivial ring. -/
theorem sumRootGenerator_ne_zero [Nontrivial K] (i j : ι) (hij : i ≠ j) :
    sumRootGenerator (K := K) i j hij ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inl i)) (.inr j)
  simp [sumRootMatrix, Matrix.fromBlocks, hij] at hentry

/-- A negative sum-root generator is nonzero over a nontrivial ring. -/
theorem negSumRootGenerator_ne_zero [Nontrivial K] (i j : ι) (hij : i ≠ j) :
    negSumRootGenerator (K := K) i j hij ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun (congrArg Subtype.val h) (.inr i)) (.inl j)
  simp [negSumRootMatrix, Matrix.fromBlocks, hij] at hentry

/-! ## Root-space membership -/

private theorem typeDWeightAdd_comm (i j : ι) :
    typeDWeightAdd (K := K) i j = typeDWeightAdd j i := by
  rw [typeDWeightAdd_def, typeDWeightAdd_def, add_comm]

/-- The standard difference-root generator has weight `εᵢ - εⱼ`. -/
theorem differenceRootGenerator_mem_rootSpace (i j : ι) (hij : i ≠ j) :
    differenceRootGenerator (K := K) i j hij ∈
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
theorem sumRootGenerator_mem_rootSpace (i j : ι) (hij : i ≠ j) :
    sumRootGenerator (K := K) i j hij ∈
      LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightAdd i j) := by
  apply mem_rootSpace_typeDDiagonalCartan_of_forall
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    simp [sumRootGenerator, sumRootMatrix, Matrix.fromBlocks, Matrix.single_apply] at hab ⊢
  all_goals split_ifs with h <;> simp_all [typeDWeightAdd_comm]

/-- The standard negative sum-root generator has weight `-εᵢ - εⱼ`. -/
theorem negSumRootGenerator_mem_rootSpace (i j : ι) (hij : i ≠ j) :
    negSumRootGenerator (K := K) i j hij ∈
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
    differenceRootGenerator (K := K) i (chainNext n i hi) (ne_chainNext n i hi) =
      rootGenerator (K := K) n hn (.inl i) := by
  apply Subtype.ext
  rw [coe_differenceRootGenerator, val_rootGenerator_inl, raisingMatrix_of_chain n hn hi]
  rfl

/-- At the fork node, the all-root positive sum generator is the numbered raising generator. -/
theorem sumRootGenerator_fork_eq_rootGenerator (n : ℕ) (hn : 4 ≤ n) :
    sumRootGenerator (K := K) (forkLeft n hn) (forkRight n hn)
        (forkLeft_ne_forkRight n hn) =
      rootGenerator (K := K) n hn (.inl (forkRight n hn)) := by
  apply Subtype.ext
  rw [coe_sumRootGenerator, val_rootGenerator_inl]
  have hfork : ¬((forkRight n hn : Fin n) : ℕ) + 1 < n := by
    rw [forkRight_val]
    omega
  rw [raisingMatrix_of_fork n hn hfork]
  rfl

end Fintype

end TauCeti.TypeDStd
