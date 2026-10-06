/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SumRootGenerators

/-!
# Generation of the split odd orthogonal Lie algebra

This file proves that the positive and negative Bourbaki simple-root generators of the split
type-`B` orthogonal Lie algebra generate the whole Lie algebra. Successive brackets along the
long-root chain first produce every difference-root vector. Bracketing these with the terminal
short-root vectors produces all short roots, and brackets between short roots then supply both
families of long sum roots. Matching positive and negative short roots span the diagonal Cartan.

Finally, the standard block description of a matrix skew-adjoint for
`LieAlgebra.Orthogonal.JB` decomposes an arbitrary element into the diagonal, short-root,
difference-root, and sum-root families. The resulting generation theorem is the spanning input
for the standard type-`B` Lie basis and its upper Borel.

## Main declaration

* `lieSpan_range_typeBSimpleRootGenerator_union_range_typeBSimpleNegativeRootGenerator_eq_top`:
  the numbered positive and negative simple root generators span the split type-`B` Lie algebra.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.
-/

open scoped BigOperators

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K]

private theorem lie_typeBDifferenceRootGenerator_chain
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅typeBDifferenceRootGenerator (K := K) i j hij,
      typeBDifferenceRootGenerator (K := K) j k hjk⁆ =
        typeBDifferenceRootGenerator (K := K) i k hik := by
  apply Subtype.ext
  simpa only [LieSubalgebra.coe_bracket, coe_typeBDifferenceRootGenerator] using
    typeBDifferenceRootMatrix_lie_differenceRootMatrix_chain
      (K := K) i j j k hij hjk rfl hik

private theorem differenceRootGenerator_mem_lieSpan_of_lt
    (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    typeBDifferenceRootGenerator (K := K) i j (ne_of_lt hij) ∈
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (Set.range (typeBSimpleRootGenerator (K := K)) ∪
          Set.range (typeBSimpleNegativeRootGenerator (K := K))) := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
    (Set.range (typeBSimpleRootGenerator (K := K)) ∪
      Set.range (typeBSimpleNegativeRootGenerator (K := K)))
  by_cases hadj : (i : ℕ) + 1 = (j : ℕ)
  · let a : Fin n := ⟨i, by omega⟩
    have hai : a.castSucc = i := Fin.ext rfl
    have haj : a.succ = j := Fin.ext hadj
    have ha : typeBSimpleRootGenerator (K := K) a.castSucc ∈ S :=
      LieSubalgebra.subset_lieSpan (Or.inl (Set.mem_range_self a.castSucc))
    rw [typeBSimpleRootGenerator_castSucc] at ha
    simpa only [hai, haj] using ha
  · let k : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
    have hik : i < k := by
      rw [Fin.lt_def]
      simp only [k]
      omega
    have hkj : k < j := by
      rw [Fin.lt_def]
      simp only [k]
      omega
    have hi : typeBDifferenceRootGenerator (K := K) i k (ne_of_lt hik) ∈ S := by
      let a : Fin n := ⟨i, by omega⟩
      have hai : a.castSucc = i := Fin.ext rfl
      have hak : a.succ = k := Fin.ext rfl
      have ha : typeBSimpleRootGenerator (K := K) a.castSucc ∈ S :=
        LieSubalgebra.subset_lieSpan (Or.inl (Set.mem_range_self a.castSucc))
      rw [typeBSimpleRootGenerator_castSucc] at ha
      simpa only [hai, hak] using ha
    have hj := differenceRootGenerator_mem_lieSpan_of_lt n k j hkj
    rw [← lie_typeBDifferenceRootGenerator_chain i k j
      (ne_of_lt hik) (ne_of_lt hkj) (ne_of_lt hij)]
    exact S.lie_mem hi hj
termination_by (j : ℕ) - (i : ℕ)
decreasing_by omega

private theorem reverseDifferenceRootGenerator_mem_lieSpan_of_lt
    (n : ℕ) (i j : Fin (n + 1)) (hij : i < j) :
    typeBDifferenceRootGenerator (K := K) j i (ne_of_gt hij) ∈
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (Set.range (typeBSimpleRootGenerator (K := K)) ∪
          Set.range (typeBSimpleNegativeRootGenerator (K := K))) := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
    (Set.range (typeBSimpleRootGenerator (K := K)) ∪
      Set.range (typeBSimpleNegativeRootGenerator (K := K)))
  by_cases hadj : (i : ℕ) + 1 = (j : ℕ)
  · let a : Fin n := ⟨i, by omega⟩
    have hai : a.castSucc = i := Fin.ext rfl
    have haj : a.succ = j := Fin.ext hadj
    have ha : typeBSimpleNegativeRootGenerator (K := K) a.castSucc ∈ S :=
      LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self a.castSucc))
    rw [typeBSimpleNegativeRootGenerator_castSucc] at ha
    simpa only [hai, haj] using ha
  · let k : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
    have hik : i < k := by
      rw [Fin.lt_def]
      simp only [k]
      omega
    have hkj : k < j := by
      rw [Fin.lt_def]
      simp only [k]
      omega
    have hj := reverseDifferenceRootGenerator_mem_lieSpan_of_lt n k j hkj
    have hi : typeBDifferenceRootGenerator (K := K) k i (ne_of_gt hik) ∈ S := by
      let a : Fin n := ⟨i, by omega⟩
      have hai : a.castSucc = i := Fin.ext rfl
      have hak : a.succ = k := Fin.ext rfl
      have ha : typeBSimpleNegativeRootGenerator (K := K) a.castSucc ∈ S :=
        LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self a.castSucc))
      rw [typeBSimpleNegativeRootGenerator_castSucc] at ha
      simpa only [hai, hak] using ha
    rw [← lie_typeBDifferenceRootGenerator_chain j k i
      (ne_of_gt hkj) (ne_of_gt hik) (ne_of_gt hij)]
    exact S.lie_mem hj hi
termination_by (j : ℕ) - (i : ℕ)
decreasing_by omega

private theorem lie_typeBDifferenceRootGenerator_shortRootGenerator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    ⁅typeBDifferenceRootGenerator (K := K) i j hij,
      typeBShortRootGenerator (K := K) j⁆ = typeBShortRootGenerator i := by
  apply Subtype.ext
  -- Expose the ambient-matrix equality so the matrix bracket lemma can rewrite it.
  simpa only [LieSubalgebra.coe_bracket, coe_typeBDifferenceRootGenerator,
    coe_typeBShortRootGenerator] using show
      ⁅typeBDifferenceRootMatrix (K := K) i j hij, typeBShortRootMatrix (K := K) j⁆ =
        typeBShortRootMatrix i from by
          rw [(lie_skew _ _).symm, typeBShortRootMatrix_lie_differenceRootMatrix]
          simp

private theorem lie_typeBShortNegativeRootGenerator_differenceRootGenerator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    ⁅typeBShortNegativeRootGenerator (K := K) j,
      typeBDifferenceRootGenerator (K := K) j i hij.symm⁆ =
        typeBShortNegativeRootGenerator i := by
  apply Subtype.ext
  -- Expose the ambient-matrix equality so the matrix bracket lemma can rewrite it.
  simpa only [LieSubalgebra.coe_bracket, coe_typeBShortNegativeRootGenerator,
    coe_typeBDifferenceRootGenerator] using show
      ⁅typeBShortNegativeRootMatrix (K := K) j,
        typeBDifferenceRootMatrix (K := K) j i hij.symm⁆ =
          typeBShortNegativeRootMatrix i from by
            rw [typeBShortNegativeRootMatrix_lie_differenceRootMatrix]
            simp

private theorem shortRootGenerator_mem_lieSpan (n : ℕ) (i : Fin (n + 1)) :
    typeBShortRootGenerator (K := K) i ∈
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (Set.range (typeBSimpleRootGenerator (K := K)) ∪
          Set.range (typeBSimpleNegativeRootGenerator (K := K))) := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
    (Set.range (typeBSimpleRootGenerator (K := K)) ∪
      Set.range (typeBSimpleNegativeRootGenerator (K := K)))
  by_cases hi : i = Fin.last n
  · subst i
    rw [← typeBSimpleRootGenerator_last]
    exact LieSubalgebra.subset_lieSpan (Or.inl (Set.mem_range_self (Fin.last n)))
  · have hilast : i < Fin.last n := by
      rw [Fin.lt_def, Fin.val_last]
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) (by
        intro h
        apply hi
        exact Fin.ext h)
    have hdiff := differenceRootGenerator_mem_lieSpan_of_lt (K := K) n i (Fin.last n) hilast
    have hlast : typeBShortRootGenerator (K := K) (Fin.last n) ∈ S := by
      rw [← typeBSimpleRootGenerator_last]
      exact LieSubalgebra.subset_lieSpan (Or.inl (Set.mem_range_self (Fin.last n)))
    rw [← lie_typeBDifferenceRootGenerator_shortRootGenerator i (Fin.last n) hi]
    exact S.lie_mem hdiff hlast

private theorem shortNegativeRootGenerator_mem_lieSpan (n : ℕ) (i : Fin (n + 1)) :
    typeBShortNegativeRootGenerator (K := K) i ∈
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (Set.range (typeBSimpleRootGenerator (K := K)) ∪
          Set.range (typeBSimpleNegativeRootGenerator (K := K))) := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
    (Set.range (typeBSimpleRootGenerator (K := K)) ∪
      Set.range (typeBSimpleNegativeRootGenerator (K := K)))
  by_cases hi : i = Fin.last n
  · subst i
    rw [← typeBSimpleNegativeRootGenerator_last]
    exact LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self (Fin.last n)))
  · have hilast : i < Fin.last n := by
      rw [Fin.lt_def, Fin.val_last]
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) (by
        intro h
        apply hi
        exact Fin.ext h)
    have hdiff := reverseDifferenceRootGenerator_mem_lieSpan_of_lt
      (K := K) n i (Fin.last n) hilast
    have hlast : typeBShortNegativeRootGenerator (K := K) (Fin.last n) ∈ S := by
      rw [← typeBSimpleNegativeRootGenerator_last]
      exact LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self (Fin.last n)))
    rw [← lie_typeBShortNegativeRootGenerator_differenceRootGenerator i (Fin.last n) hi]
    exact S.lie_mem hlast hdiff

private theorem lie_typeBShortRootGenerator_shortRootGenerator
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ⁅typeBShortRootGenerator (K := K) i, typeBShortRootGenerator (K := K) j⁆ =
      -((2 : K) • typeBSumRootGenerator i j) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, coe_typeBShortRootGenerator,
    coe_typeBSumRootGenerator, NegMemClass.coe_neg, SetLike.val_smul]
  simpa only [two_smul K, two_nsmul] using
    typeBShortRootMatrix_lie_shortRootMatrix (K := K) i j

private theorem lie_typeBShortNegativeRootGenerator_shortNegativeRootGenerator
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ⁅typeBShortNegativeRootGenerator (K := K) i,
      typeBShortNegativeRootGenerator (K := K) j⁆ =
        -((2 : K) • typeBSumNegativeRootGenerator i j) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, coe_typeBShortNegativeRootGenerator,
    coe_typeBSumNegativeRootGenerator, NegMemClass.coe_neg, SetLike.val_smul]
  simpa only [two_smul K, two_nsmul] using
    typeBShortNegativeRootMatrix_lie_shortNegativeRootMatrix (K := K) i j

private abbrev typeBIndex (n : ℕ) := Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)

/-- The type-`B` block matrix unit, using a Cartan basis vector on the diagonal and a
difference-root vector off the diagonal. -/
private def typeBBlockGenerator (n : ℕ) (i j : Fin (n + 1)) :
    LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K :=
  if hij : i = j then
    ⟨typeBDiagonalMatrix (Pi.single i 1), typeBDiagonalMatrix_mem_typeB _⟩
  else
    typeBDifferenceRootGenerator i j hij

private theorem coe_typeBBlockGenerator (n : ℕ) (i j : Fin (n + 1)) :
    (typeBBlockGenerator (K := K) n i j : Matrix (typeBIndex n) (typeBIndex n) K) =
      Matrix.single (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) 1 -
        Matrix.single (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inr i)) 1 := by
  by_cases hij : i = j
  · subst j
    simp only [typeBBlockGenerator, ↓reduceDIte]
    ext (a | (a | a)) (b | (b | b)) <;>
      simp [typeBDiagonalMatrix_apply, Pi.single_apply, Matrix.single_apply] <;> aesop
  · simp [typeBBlockGenerator, hij, coe_typeBDifferenceRootGenerator,
      typeBDifferenceRootMatrix_def]

private theorem decomposition [NeZero (2 : K)] (n : ℕ)
    (X : LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K) :
    X =
      (∑ i, (X : Matrix (typeBIndex n) (typeBIndex n) K)
        (Sum.inl ()) (Sum.inr (Sum.inl i)) •
        typeBShortNegativeRootGenerator i) +
      (∑ i, -((X : Matrix (typeBIndex n) (typeBIndex n) K)
        (Sum.inl ()) (Sum.inr (Sum.inr i))) •
        typeBShortRootGenerator i) +
      (∑ i, ∑ j,
        (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) •
          typeBBlockGenerator n i j) +
      (∑ i, ∑ j, ((2 : K)⁻¹ *
        (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j))) •
          typeBSumRootGenerator i j) +
      (∑ i, ∑ j, ((2 : K)⁻¹ *
        (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j))) •
          typeBSumNegativeRootGenerator i j) := by
  have hX := X.2
  -- The subtype witness is skew-adjointness for `JB`; expose its matrix equation blockwise.
  change (X : Matrix (typeBIndex n) (typeBIndex n) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JB (Fin (n + 1)) K) at hX
  rw [mem_skewAdjointMatricesSubmodule] at hX
  -- The anisotropic coordinate vanishes, while its row determines the two short-root columns.
  have hunit :
      (X : Matrix (typeBIndex n) (typeBIndex n) K) (Sum.inl ()) (Sum.inl ()) = 0 := by
    have h := congr_fun (congr_fun hX (Sum.inl ())) (Sum.inl ())
    have h' :
        (X : Matrix (typeBIndex n) (typeBIndex n) K) (Sum.inl ()) (Sum.inl ()) * 2 =
          -(2 * (X : Matrix (typeBIndex n) (typeBIndex n) K)
            (Sum.inl ()) (Sum.inl ())) := by
      simpa [LieAlgebra.Orthogonal.JB, Matrix.mul_apply, Matrix.one_apply] using h
    apply (mul_left_cancel₀ (NeZero.ne (2 : K)))
    apply (mul_left_cancel₀ (NeZero.ne (2 : K)))
    simp only [mul_zero]
    calc
      2 * (2 * (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inl ()) (Sum.inl ())) =
          (X : Matrix (typeBIndex n) (typeBIndex n) K) (Sum.inl ()) (Sum.inl ()) * 2 -
            (-(2 * (X : Matrix (typeBIndex n) (typeBIndex n) K)
              (Sum.inl ()) (Sum.inl ()))) := by ring
      _ = 0 := sub_eq_zero.mpr h'
  have hposUnit (i : Fin (n + 1)) :
      (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inl i)) (Sum.inl ()) =
        -(2 * (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inl ()) (Sum.inr (Sum.inr i))) := by
    have h := congr_fun (congr_fun hX (Sum.inl ())) (Sum.inr (Sum.inr i))
    simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
      Matrix.one_apply] using h
  have hnegUnit (i : Fin (n + 1)) :
      (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inr i)) (Sum.inl ()) =
        -(2 * (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inl ()) (Sum.inr (Sum.inl i))) := by
    have h := congr_fun (congr_fun hX (Sum.inl ())) (Sum.inr (Sum.inl i))
    simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
      Matrix.one_apply] using h
  -- The two off-diagonal square blocks are skew, and the final diagonal block is minus the
  -- transpose of the first one.
  have hsum (i j : Fin (n + 1)) :
      (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr i)) =
        -(X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) := by
    have h := congr_fun (congr_fun hX (Sum.inr (Sum.inr i))) (Sum.inr (Sum.inr j))
    simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
      Matrix.one_apply] using h
  have hsumNeg (i j : Fin (n + 1)) :
      (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl i)) =
        -(X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) := by
    have h := congr_fun (congr_fun hX (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inl j))
    simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
      Matrix.one_apply] using h
  have hblockNeg (i j : Fin (n + 1)) :
      (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) =
        -(X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i)) := by
    have h := congr_fun (congr_fun hX (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr j))
    simp [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
      Matrix.one_apply] at h
    linear_combination h
  -- Each antisymmetric block is recovered from the full double sum with coefficient `2⁻¹`.
  have hsumScaled (i j : Fin (n + 1)) :
      (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) =
        (2 : K)⁻¹ * (X : Matrix (typeBIndex n) (typeBIndex n) K)
            (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) -
          (2 : K)⁻¹ * (X : Matrix (typeBIndex n) (typeBIndex n) K)
            (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr i)) := by
    rw [hsum i j]
    field_simp
    ring
  have hsumNegScaled (i j : Fin (n + 1)) :
      (X : Matrix (typeBIndex n) (typeBIndex n) K)
          (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) =
        (2 : K)⁻¹ * (X : Matrix (typeBIndex n) (typeBIndex n) K)
            (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) -
          (2 : K)⁻¹ * (X : Matrix (typeBIndex n) (typeBIndex n) K)
            (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inl i)) := by
    rw [hsumNeg i j]
    field_simp
    ring
  apply Subtype.ext
  simp only [AddMemClass.coe_add, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
    coe_typeBShortNegativeRootGenerator, coe_typeBShortRootGenerator,
    coe_typeBBlockGenerator, coe_typeBSumRootGenerator,
    coe_typeBSumNegativeRootGenerator]
  -- Check the resulting `3 × 3` block matrix in row-major order: the first row and column are
  -- the short-root terms, the positive diagonal block is the block-generator sum, the two
  -- off-diagonal square blocks are the sum-root terms, and the last block is the forced transpose.
  ext (a | (a | a)) (b | (b | b))
  -- Anisotropic-anisotropic entry.
  · simpa [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply] using hunit
  -- Anisotropic-positive entry.
  · simp [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply]
  -- Anisotropic-negative entry.
  · simp [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply]
  -- Positive-anisotropic entry.
  · simpa [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply, mul_comm] using hposUnit a
  -- Positive-positive block.
  · simp [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply, ite_and, Finset.mem_univ]
  -- Positive-negative block.
  · simpa [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply, ite_and, Finset.mem_univ,
      mul_sub, Finset.sum_sub_distrib] using hsumScaled a b
  -- Negative-anisotropic entry.
  · simpa [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply, mul_comm] using hnegUnit a
  -- Negative-positive block.
  · simpa [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply, ite_and, Finset.mem_univ,
      mul_sub, Finset.sum_sub_distrib] using hsumNegScaled a b
  -- Negative-negative block.
  · simpa [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
      typeBSumRootMatrix_def, typeBSumNegativeRootMatrix_def, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.single_apply, ite_and] using hblockNeg a b

/-- The positive and negative Bourbaki simple-root generators generate the split odd orthogonal
Lie algebra of type `B`. -/
theorem lieSpan_range_typeBSimpleRootGenerator_union_range_typeBSimpleNegativeRootGenerator_eq_top
    [NeZero (2 : K)] (n : ℕ) :
    LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (Set.range (typeBSimpleRootGenerator (K := K)) ∪
        Set.range (typeBSimpleNegativeRootGenerator (K := K))) = ⊤ := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
    (Set.range (typeBSimpleRootGenerator (K := K)) ∪
      Set.range (typeBSimpleNegativeRootGenerator (K := K)))
  have hdiff (i j : Fin (n + 1)) (hij : i ≠ j) :
      typeBDifferenceRootGenerator (K := K) i j hij ∈ S := by
    rcases lt_trichotomy i j with hij' | hij' | hij'
    · simpa only [Subsingleton.elim hij (ne_of_lt hij')] using
        differenceRootGenerator_mem_lieSpan_of_lt (K := K) n i j hij'
    · exact (hij hij').elim
    · simpa only [Subsingleton.elim hij (ne_of_gt hij')] using
        reverseDifferenceRootGenerator_mem_lieSpan_of_lt (K := K) n j i hij'
  have hshort (i : Fin (n + 1)) : typeBShortRootGenerator (K := K) i ∈ S :=
    shortRootGenerator_mem_lieSpan n i
  have hshortNeg (i : Fin (n + 1)) : typeBShortNegativeRootGenerator (K := K) i ∈ S :=
    shortNegativeRootGenerator_mem_lieSpan n i
  have hsum (i j : Fin (n + 1)) : typeBSumRootGenerator (K := K) i j ∈ S := by
    have hbracket := S.lie_mem (hshort i) (hshort j)
    rw [lie_typeBShortRootGenerator_shortRootGenerator] at hbracket
    have hscaled := S.smul_mem (-(2 : K)⁻¹) hbracket
    convert hscaled using 1
    simp [smul_smul, NeZero.ne (2 : K)]
  have hsumNeg (i j : Fin (n + 1)) : typeBSumNegativeRootGenerator (K := K) i j ∈ S := by
    have hbracket := S.lie_mem (hshortNeg i) (hshortNeg j)
    rw [lie_typeBShortNegativeRootGenerator_shortNegativeRootGenerator] at hbracket
    have hscaled := S.smul_mem (-(2 : K)⁻¹) hbracket
    convert hscaled using 1
    simp [smul_smul, NeZero.ne (2 : K)]
  have hcartan : typeBDiagonalCartan K (Fin (n + 1)) ≤ S := by
    intro A hA
    let Ac : typeBDiagonalCartan K (Fin (n + 1)) := ⟨A, hA⟩
    -- Bundle the Cartan-membership witness so its coordinate basis can expand the ambient element.
    change (Ac : LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K) ∈ S
    let B := typeBDiagonalCartanBasis (K := K) (ι := Fin (n + 1))
    rw [← B.sum_repr Ac]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    apply S.sum_mem
    intro i _
    apply S.smul_mem
    have hbracket := S.lie_mem (hshort i) (hshortNeg i)
    rw [typeBShortRootGenerator_lie_negative, typeBShortCorootGenerator_eq_diagonal] at hbracket
    have hscaled := S.smul_mem ((2 : K)⁻¹) hbracket
    have hscale :
        (2 : K)⁻¹ •
            ((typeBDiagonalEquiv (K := K) (ι := Fin (n + 1)) (2 • Pi.single i 1) :
              typeBDiagonalCartan K (Fin (n + 1))) :
                LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K) =
          ((B i : typeBDiagonalCartan K (Fin (n + 1))) :
            LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K) := by
      apply Subtype.ext
      simp only [SetLike.val_smul, coe_typeBDiagonalEquiv_apply,
        B, coe_typeBDiagonalCartanBasis_apply]
      ext (a | (a | a)) (b | (b | b)) <;>
        simp [typeBDiagonalMatrix_apply, NeZero.ne (2 : K)]
    rw [hscale] at hscaled
    exact hscaled
  have hblock (i j : Fin (n + 1)) : typeBBlockGenerator (K := K) n i j ∈ S := by
    by_cases hij : i = j
    · subst j
      rw [typeBBlockGenerator, dite_eq_left rfl]
      apply hcartan
      rw [mem_typeBDiagonalCartan_iff]
      exact ⟨Pi.single i 1, rfl⟩
    · rw [typeBBlockGenerator, dite_eq_right hij]
      exact hdiff i j hij
  apply eq_top_iff.mpr
  intro X _
  rw [decomposition n X]
  apply S.add_mem
  · apply S.add_mem
    · apply S.add_mem
      · exact S.add_mem
          (S.sum_mem fun i _ => S.smul_mem _ (hshortNeg i))
          (S.sum_mem fun i _ => S.smul_mem _ (hshort i))
      · exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hblock i j)
    · exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hsum i j)
  · exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hsumNeg i j)

end TauCeti
