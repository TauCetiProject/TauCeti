/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Block
import TauCeti.Algebra.Lie.Orthogonal.TypeB.CartanBasis
import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Coordinates

/-!
# Generation of the split odd orthogonal Lie algebra

The positive and negative Bourbaki simple-root generators of the split type-`B` orthogonal Lie
algebra generate the whole Lie algebra over any commutative ring in which `2` is invertible.
Successive brackets along the long-root chain first produce every difference-root vector.
Bracketing these with the terminal short-root vectors produces all short roots, and brackets
between short roots then supply both families of long sum roots. Matching positive and negative
short roots span the diagonal Cartan.

Finally, `LieAlgebra.Orthogonal.typeB.blockEquiv` separates the short-root coordinates from the
even orthogonal block. The native expansion `TauCeti.TypeDStd.eq_sum_rootEntryBasis` supplies
the diagonal, difference-root, and sum-root families. The resulting generation theorem is the
spanning input for the standard type-`B` Lie basis and its upper Borel.

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

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [CommRing K]

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
    rw [← typeBDifferenceRootGenerator_lie_chain i k j
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
    rw [← typeBDifferenceRootGenerator_lie_chain j k i
      (ne_of_gt hkj) (ne_of_gt hik) (ne_of_gt hij)]
    exact S.lie_mem hj hi
termination_by (j : ℕ) - (i : ℕ)
decreasing_by omega

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
  · have hilast : i < Fin.last n := Fin.lt_last_iff_ne_last.mpr hi
    have hdiff := differenceRootGenerator_mem_lieSpan_of_lt (K := K) n i (Fin.last n) hilast
    have hlast : typeBShortRootGenerator (K := K) (Fin.last n) ∈ S := by
      rw [← typeBSimpleRootGenerator_last]
      exact LieSubalgebra.subset_lieSpan (Or.inl (Set.mem_range_self (Fin.last n)))
    rw [← typeBDifferenceRootGenerator_lie_shortRootGenerator i (Fin.last n) hi]
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
  · have hilast : i < Fin.last n := Fin.lt_last_iff_ne_last.mpr hi
    have hdiff := reverseDifferenceRootGenerator_mem_lieSpan_of_lt
      (K := K) n i (Fin.last n) hilast
    have hlast : typeBShortNegativeRootGenerator (K := K) (Fin.last n) ∈ S := by
      rw [← typeBSimpleNegativeRootGenerator_last]
      exact LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self (Fin.last n)))
    rw [← typeBShortNegativeRootGenerator_lie_differenceRootGenerator i (Fin.last n) hi]
    exact S.lie_mem hlast hdiff

/-- The positive and negative Bourbaki simple-root generators generate the split odd orthogonal
Lie algebra of type `B` over a commutative ring in which `2` is invertible. -/
theorem lieSpan_range_typeBSimpleRootGenerator_union_range_typeBSimpleNegativeRootGenerator_eq_top
    [Invertible (2 : K)] (n : ℕ) :
    LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (Set.range (typeBSimpleRootGenerator (K := K)) ∪
        Set.range (typeBSimpleNegativeRootGenerator (K := K))) = ⊤ := by
  let S := LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
    (Set.range (typeBSimpleRootGenerator (K := K)) ∪
      Set.range (typeBSimpleNegativeRootGenerator (K := K)))
  -- Recover all root families and the Cartan from the simple generators.
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
    rw [typeBShortRootGenerator_lie_shortRootGenerator] at hbracket
    exact (S.toSubmodule.smul_mem_iff'' (r := (2 : K))).mp
      (S.toSubmodule.neg_mem_iff.mp hbracket)
  have hsumNeg (i j : Fin (n + 1)) : typeBSumNegativeRootGenerator (K := K) i j ∈ S := by
    have hbracket := S.lie_mem (hshortNeg i) (hshortNeg j)
    rw [typeBShortNegativeRootGenerator_lie_shortNegativeRootGenerator] at hbracket
    exact (S.toSubmodule.smul_mem_iff'' (r := (2 : K))).mp
      (S.toSubmodule.neg_mem_iff.mp hbracket)
  have hcartan : typeBDiagonalCartan K (Fin (n + 1)) ≤ S := by
    rw [typeBDiagonalCartan_eq_lieSpan_typeBSimpleCorootGenerator, LieSubalgebra.lieSpan_le]
    rintro _ ⟨i, rfl⟩
    rw [← typeBSimpleRootGenerator_lie_negative]
    exact S.lie_mem (LieSubalgebra.subset_lieSpan (Or.inl ⟨i, rfl⟩))
      (LieSubalgebra.subset_lieSpan (Or.inr ⟨i, rfl⟩))
  have hblock (i j : Fin (n + 1)) :
      LieAlgebra.Orthogonal.typeB.ofTypeD (TypeDStd.differenceRootGenerator (K := K) i j) ∈ S := by
    by_cases hij : i = j
    · subst j
      rw [TypeDStd.differenceRootGenerator_self_eq_typeDDiagonalEquiv,
        coe_typeDDiagonalEquiv_apply, LieAlgebra.Orthogonal.typeB.ofTypeD_diagonal]
      simpa only [coe_typeBDiagonalEquiv_apply] using
        hcartan (typeBDiagonalEquiv (Pi.single i 1)).property
    · rw [LieAlgebra.Orthogonal.typeB.ofTypeD_differenceRootGenerator i j hij]
      exact hdiff i j hij
  -- Reconstruct the short-root coordinates and expand the even orthogonal block in its root basis.
  have h2 := (isUnit_of_invertible (2 : K)).isRegular
  apply eq_top_iff.mpr
  intro X _
  rcases hX : LieAlgebra.Orthogonal.typeB.blockEquiv h2 X with ⟨a, b, Y⟩
  rw [← (LieAlgebra.Orthogonal.typeB.blockEquiv h2).symm_apply_apply X, hX,
    LieAlgebra.Orthogonal.typeB.blockEquiv_symm_apply]
  refine S.add_mem (S.add_mem
    (S.sum_mem fun i _ => S.smul_mem _ (hshort i))
    (S.sum_mem fun i _ => S.smul_mem _ (hshortNeg i))) ?_
  rw [TypeDStd.eq_sum_rootEntryBasis
    (isUnit_of_invertible (2 : K)).eq_zero_of_add_self_eq_zero Y]
  simp only [map_add, map_sum, map_smul,
    LieAlgebra.Orthogonal.typeB.ofTypeD_sumRootGenerator,
    LieAlgebra.Orthogonal.typeB.ofTypeD_negSumRootGenerator]
  exact S.add_mem (S.add_mem
    (S.sum_mem fun p _ => S.smul_mem _ (hblock p.1 p.2))
    (S.sum_mem fun p _ => S.smul_mem _ (hsum p.val.1 p.val.2)))
    (S.sum_mem fun p _ => S.smul_mem _ (hsumNeg p.val.2 p.val.1))

end TauCeti
