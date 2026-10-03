/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.PositiveSpan
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.CartanBasis

/-!
# Generation of the split even orthogonal Lie algebra

This file proves that the positive and negative simple root generators of the split type-D
orthogonal Lie algebra generate the whole Lie algebra. The proof first obtains every positive root
generator from the positive simple generators. Root-string brackets of the negative simple
generators then produce every negative root generator, while mixed simple brackets produce the
diagonal Cartan. Finally, the standard block description of the orthogonal Lie algebra decomposes
an arbitrary element into its three root-matrix families.

The resulting generation theorem supplies the spanning field for the standard type-D basis and
the Lie-algebraic input for its Borel subalgebra.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, §1.8
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25
-/

open scoped BigOperators

public section

namespace TauCeti.TypeDStd

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K]

private theorem sum_smul_differenceRootMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) :
    (∑ i : n, ∑ j : n, A i j • differenceRootMatrix (K := K) i j) =
      Matrix.fromBlocks A 0 0 (-A.transpose) := by
  have hA : (∑ i : n, ∑ j : n, A i j • Matrix.single i j (1 : K)) = A := by
    simpa [Matrix.smul_single] using (Matrix.matrix_eq_sum_single A).symm
  have hAT :
      (∑ i : n, ∑ j : n, A i j • (-(Matrix.single i j (1 : K)).transpose)) =
        -A.transpose := by
    simpa only [Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_neg_distrib,
        smul_neg] using congrArg (fun M : Matrix n n K => -M.transpose) hA
  simp_rw [differenceRootMatrix_def, Matrix.fromBlocks_smul]
  ext (i | i) (j | j)
  · simpa only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁] using
      congrFun (congrFun hA i) j
  · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₂,
      smul_zero, Matrix.zero_apply, Finset.sum_const_zero]
  · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₂₁,
      smul_zero, Matrix.zero_apply, Finset.sum_const_zero]
  · simpa only [Matrix.sum_apply, Matrix.fromBlocks_apply₂₂] using
      congrFun (congrFun hAT i) j

private theorem sum_half_smul_sumRootMatrices {n : Type*} [Fintype n] [DecidableEq n]
    [NeZero (2 : K)] (A : Matrix n n K) (hA : A.transpose = -A) :
    ((∑ i : n, ∑ j : n,
        ((2 : K)⁻¹ * A i j) • sumRootMatrix (K := K) i j) =
        Matrix.fromBlocks 0 A 0 0) ∧
      (∑ i : n, ∑ j : n,
        ((2 : K)⁻¹ * A i j) • negSumRootMatrix (K := K) i j) =
        Matrix.fromBlocks 0 0 A 0 := by
  have hsingle : (∑ i : n, ∑ j : n, A i j • Matrix.single i j (1 : K)) = A := by
    simpa [Matrix.smul_single] using (Matrix.matrix_eq_sum_single A).symm
  have hsingleTranspose :
      (∑ i : n, ∑ j : n, A i j • Matrix.single j i (1 : K)) = A.transpose := by
    simpa only [Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_single] using
      congrArg Matrix.transpose hsingle
  have hsum :
      (∑ i : n, ∑ j : n,
        ((2 : K)⁻¹ * A i j) •
          (Matrix.single i j (1 : K) - Matrix.single j i (1 : K))) = A := by
    calc
      _ = (2 : K)⁻¹ •
          ((∑ i : n, ∑ j : n, A i j • Matrix.single i j (1 : K)) -
            (∑ i : n, ∑ j : n, A i j • Matrix.single j i (1 : K))) := by
        simp only [mul_smul, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
      _ = (2 : K)⁻¹ • (A - A.transpose) := by
        rw [hsingle, hsingleTranspose]
      _ = A := by
        rw [hA]
        simp only [sub_neg_eq_add]
        rw [← two_smul K A, smul_smul]
        convert one_smul K A using 1
        field_simp
  constructor
  · simp_rw [sumRootMatrix_def, Matrix.fromBlocks_smul]
    ext (i | i) (j | j)
    · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁,
        smul_zero, Matrix.zero_apply, Finset.sum_const_zero]
    · simpa only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₂] using
        congrFun (congrFun hsum i) j
    · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₂₁,
        smul_zero, Matrix.zero_apply, Finset.sum_const_zero]
    · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₂₂,
        smul_zero, Matrix.zero_apply, Finset.sum_const_zero]
  · simp_rw [negSumRootMatrix_def, Matrix.fromBlocks_smul]
    ext (i | i) (j | j)
    · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁,
        smul_zero, Matrix.zero_apply, Finset.sum_const_zero]
    · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₂,
        smul_zero, Matrix.zero_apply, Finset.sum_const_zero]
    · simpa only [Matrix.sum_apply, Matrix.fromBlocks_apply₂₁] using
        congrFun (congrFun hsum i) j
    · simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₂₂,
        smul_zero, Matrix.zero_apply, Finset.sum_const_zero]

private theorem decomposition [NeZero (2 : K)] (n : ℕ)
    (X : LieAlgebra.Orthogonal.typeD (Fin n) K) :
    X =
      (∑ i : Fin n, ∑ j : Fin n,
        (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inl i) (.inl j) •
          differenceRootGenerator (K := K) i j) +
      (∑ i : Fin n, ∑ j : Fin n,
        ((2 : K)⁻¹ *
          (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inl i) (.inr j)) •
          sumRootGenerator (K := K) i j) +
      (∑ i : Fin n, ∑ j : Fin n,
        ((2 : K)⁻¹ *
          (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inr i) (.inl j)) •
          negSumRootGenerator (K := K) i j) := by
  apply Subtype.ext
  simp only [AddMemClass.coe_add, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
    val_differenceRootGenerator, val_sumRootGenerator, val_negSumRootGenerator]
  let A : Matrix (Fin n) (Fin n) K := fun i j =>
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inl i) (.inl j)
  let B : Matrix (Fin n) (Fin n) K := fun i j =>
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inl i) (.inr j)
  let C : Matrix (Fin n) (Fin n) K := fun i j =>
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inr i) (.inl j)
  have hB : B.transpose = -B := by
    ext i j
    exact LieAlgebra.Orthogonal.typeD.apply_inl_inr X j i
  have hC : C.transpose = -C := by
    ext i j
    exact LieAlgebra.Orthogonal.typeD.apply_inr_inl X j i
  have hX : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Matrix.fromBlocks A B C (-A.transpose) := by
    ext (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · exact LieAlgebra.Orthogonal.typeD.apply_inr_inr X i j
  -- Expose the local block abbreviations across the subtype's matrix coercion.
  change (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
    (∑ i : Fin n, ∑ j : Fin n, A i j • differenceRootMatrix (K := K) i j) +
    (∑ i : Fin n, ∑ j : Fin n,
      ((2 : K)⁻¹ * B i j) • sumRootMatrix (K := K) i j) +
    (∑ i : Fin n, ∑ j : Fin n,
      ((2 : K)⁻¹ * C i j) • negSumRootMatrix (K := K) i j)
  rw [sum_smul_differenceRootMatrix A, (sum_half_smul_sumRootMatrices B hB).1,
    (sum_half_smul_sumRootMatrices C hC).2, Matrix.fromBlocks_add, Matrix.fromBlocks_add]
  simpa using hX

private theorem lie_differenceRootGenerator_negSumRootGenerator
    {n : ℕ} (i j k : Fin n) (hjk : j ≠ k) :
    ⁅differenceRootGenerator (K := K) j i, negSumRootGenerator (K := K) j k⁆ =
      -negSumRootGenerator (K := K) i k := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, val_differenceRootGenerator,
    val_negSumRootGenerator, NegMemClass.coe_neg, val_negSumRootGenerator]
  -- Reduce the equality of bundled orthogonal elements to the root matrices it contains.
  change ⁅differenceRootMatrix (K := K) j i, negSumRootMatrix (K := K) j k⁆ =
    -negSumRootMatrix (K := K) i k
  rw [LieRing.of_associative_ring_bracket, differenceRootMatrix_def,
    negSumRootMatrix_def, negSumRootMatrix_def, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext (a | a) (b | b)
  all_goals
    simp [Matrix.fromBlocks, Matrix.transpose_single, Matrix.single_apply,
      Matrix.mul_sub, Matrix.sub_mul, hjk, hjk.symm] <;> ring

private theorem reverseDifferenceRootGenerator_mem_lieSpan
    (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) (hij : i < j) :
    differenceRootGenerator (K := K) j i ∈
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inl k)) ∪
          Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inr k))) := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
    (Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inl k)) ∪
      Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inr k)))
  by_cases hadj : (i : ℕ) + 1 = (j : ℕ)
  · have hi : (i : ℕ) + 1 < n := hadj.trans_lt j.isLt
    have hnext : chainNext n i hi = j := Fin.ext (by simp [hadj])
    rw [← hnext, differenceRootGenerator_reverse_chain_eq_rootGenerator n hn i hi]
    exact LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self i))
  · have hi : (i : ℕ) + 1 < n := by omega
    let k := chainNext n i hi
    have hkj : k < j := by
      rw [Fin.lt_def]
      simp only [k, chainNext_val]
      omega
    have hjk := reverseDifferenceRootGenerator_mem_lieSpan n hn k j hkj
    have hki : differenceRootGenerator (K := K) k i ∈ S := by
      rw [differenceRootGenerator_reverse_chain_eq_rootGenerator n hn i hi]
      exact LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self i))
    rw [← lie_differenceRootGenerator_differenceRootGenerator j k i (ne_of_gt hij)]
    exact LieSubalgebra.lie_mem S hjk hki
termination_by (j : ℕ) - (i : ℕ)
decreasing_by simp only [chainNext_val]; omega

private theorem negSumRootGenerator_last_mem_lieSpan
    (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (hi : i < forkRight n hn) :
    negSumRootGenerator (K := K) i (forkRight n hn) ∈
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inl k)) ∪
          Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inr k))) := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
    (Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inl k)) ∪
      Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inr k)))
  have hforkSimple : rootGenerator (K := K) n hn (.inr (forkRight n hn)) ∈ S :=
    LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self (forkRight n hn)))
  have hforkEq : negSumRootGenerator (K := K) (forkLeft n hn) (forkRight n hn) =
      -rootGenerator (K := K) n hn (.inr (forkRight n hn)) := by
    calc
      negSumRootGenerator (K := K) (forkLeft n hn) (forkRight n hn) =
          -negSumRootGenerator (K := K) (forkRight n hn) (forkLeft n hn) := by
        rw [negSumRootGenerator_swap]
      _ = -rootGenerator (K := K) n hn (.inr (forkRight n hn)) := by
        rw [negSumRootGenerator_reverse_fork_eq_rootGenerator]
  have hfork : negSumRootGenerator (K := K) (forkLeft n hn) (forkRight n hn) ∈ S := by
    rw [hforkEq]
    exact S.neg_mem hforkSimple
  by_cases hil : i = forkLeft n hn
  · simpa [hil] using hfork
  · have hilt : i < forkLeft n hn := by
      rw [Fin.lt_def] at hi ⊢
      rw [forkRight_val] at hi
      rw [forkLeft_val]
      have hneval : (i : ℕ) ≠ n - 2 := by
        intro h
        apply hil
        apply Fin.ext
        simpa using h
      omega
    have hdiff := reverseDifferenceRootGenerator_mem_lieSpan
      (K := K) n hn i (forkLeft n hn) hilt
    have hbracket := LieSubalgebra.lie_mem S hdiff hfork
    rw [lie_differenceRootGenerator_negSumRootGenerator
      i (forkLeft n hn) (forkRight n hn) (forkLeft_ne_forkRight n hn)] at hbracket
    -- Fold the target back into the local abbreviation for the generated subalgebra.
    change negSumRootGenerator (K := K) i (forkRight n hn) ∈ S
    have hneg := S.neg_mem hbracket
    rw [neg_neg] at hneg
    exact hneg

private theorem negSumRootGenerator_mem_lieSpan
    (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) (hij : i < j) :
    negSumRootGenerator (K := K) i j ∈
      LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
        (Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inl k)) ∪
          Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inr k))) := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
    (Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inl k)) ∪
      Set.range (fun k : Fin n => rootGenerator (K := K) n hn (.inr k)))
  have hjle : j ≤ forkRight n hn := by
    rw [Fin.le_iff_val_le_val, forkRight_val]
    omega
  rcases hjle.eq_or_lt with hj | hj
  · subst j
    exact negSumRootGenerator_last_mem_lieSpan n hn i hij
  · have hdiff := reverseDifferenceRootGenerator_mem_lieSpan
      (K := K) n hn j (forkRight n hn) hj
    have hsum := negSumRootGenerator_last_mem_lieSpan
      (K := K) n hn i (hij.trans hj)
    have hsum' : negSumRootGenerator (K := K) (forkRight n hn) i ∈ S := by
      rw [negSumRootGenerator_swap]
      exact S.neg_mem hsum
    have hbracket := LieSubalgebra.lie_mem S hdiff hsum'
    rw [lie_differenceRootGenerator_negSumRootGenerator
      j (forkRight n hn) i (ne_of_gt (hij.trans hj))] at hbracket
    simpa [negSumRootGenerator_swap i j] using hbracket

/-- The positive and negative simple root generators generate the split even orthogonal
Lie algebra. -/
theorem lieSpan_rootGenerator_eq_top [NeZero (2 : K)] (n : ℕ) (hn : 4 ≤ n) :
    LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (Set.range (fun i : Fin n => rootGenerator (K := K) n hn (.inl i)) ∪
        Set.range (fun i : Fin n => rootGenerator (K := K) n hn (.inr i))) = ⊤ := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeD (Fin n) K)
    (Set.range (fun i : Fin n => rootGenerator (K := K) n hn (.inl i)) ∪
      Set.range (fun i : Fin n => rootGenerator (K := K) n hn (.inr i)))
  have he (i : Fin n) : rootGenerator (K := K) n hn (.inl i) ∈ S :=
    LieSubalgebra.subset_lieSpan (Or.inl (Set.mem_range_self i))
  have hf (i : Fin n) : rootGenerator (K := K) n hn (.inr i) ∈ S :=
    LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self i))
  have hpos : positiveSimpleRootMatrixLieSpan (K := K) n hn ≤ S :=
    (positiveSimpleRootMatrixLieSpan_le_iff n hn S).2 he
  have hcartan : typeDDiagonalCartan K (Fin n) ≤ S := by
    rw [typeDDiagonalCartan_eq_lieSpan_cartanGenerator n hn]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    have hbracket := S.lie_mem (he i) (hf i)
    simpa using hbracket
  have hdiff (i j : Fin n) : differenceRootGenerator (K := K) i j ∈ S := by
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact hpos (differenceRootGenerator_mem_positiveSimpleRootMatrixLieSpan n hn i j hij)
    · apply hcartan
      rw [mem_typeDDiagonalCartan_iff_isDiag]
      intro a b hab
      rw [val_differenceRootGenerator, differenceRootMatrix_def]
      rcases a with a | a <;> rcases b with b | b
      all_goals
        simp [Matrix.fromBlocks, Matrix.single_apply] at hab ⊢
      all_goals aesop
    · exact reverseDifferenceRootGenerator_mem_lieSpan n hn j i hij
  have hsum (i j : Fin n) : sumRootGenerator (K := K) i j ∈ S := by
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact hpos (sumRootGenerator_mem_positiveSimpleRootMatrixLieSpan n hn i j hij)
    · simp
    · rw [sumRootGenerator_swap]
      exact S.neg_mem (hpos (sumRootGenerator_mem_positiveSimpleRootMatrixLieSpan n hn j i hij))
  have hneg (i j : Fin n) : negSumRootGenerator (K := K) i j ∈ S := by
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact negSumRootGenerator_mem_lieSpan n hn i j hij
    · simp
    · rw [negSumRootGenerator_swap]
      exact S.neg_mem (negSumRootGenerator_mem_lieSpan n hn j i hij)
  apply eq_top_iff.mpr
  intro X _
  rw [decomposition n X]
  exact S.add_mem (S.add_mem
    (S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hdiff i j))
    (S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hsum i j)))
    (S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem _ (hneg i j))

end TauCeti.TypeDStd
