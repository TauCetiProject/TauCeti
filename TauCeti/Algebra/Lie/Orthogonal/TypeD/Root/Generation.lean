/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.PositiveSpan
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Coordinates
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.CartanBasis

/-!
# Generation of the split even orthogonal Lie algebra

This file proves that the positive and negative simple root generators of the split type-D
orthogonal Lie algebra generate the whole Lie algebra. The proof first obtains every positive root
generator from the positive simple generators. Root-string brackets of the negative simple
generators then produce every negative root generator, while mixed simple brackets produce the
diagonal Cartan. Finally, the native entry-basis expansion writes an arbitrary element as a sum
of those three root-matrix families.

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

private theorem lie_differenceRootGenerator_negSumRootGenerator
    {n : ℕ} (i j k : Fin n) (hjk : j ≠ k) :
    ⁅differenceRootGenerator (K := K) j i, negSumRootGenerator (K := K) j k⁆ =
      -negSumRootGenerator (K := K) i k := by
  simp [lie_differenceRootGenerator_negSumRootGenerator_eq_ite, hjk]

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
  rw [eq_sum_rootEntryBasis (NeZero.ne (2 : K)).isUnit.eq_zero_of_add_self_eq_zero X]
  exact S.add_mem (S.add_mem
    (S.sum_mem fun p _ => S.smul_mem _ (hdiff p.1 p.2))
    (S.sum_mem fun p _ => S.smul_mem _ (hsum p.val.1 p.val.2)))
    (S.sum_mem fun p _ => S.smul_mem _ (hneg p.val.2 p.val.1))

end TauCeti.TypeDStd
