/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Lie
import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.AllGenerators

/-!
# Lie generation by the standard symplectic simple roots

The Bourbaki-numbered positive and negative generators `TauCeti.SpStd.rootGenerator`
generate the rational symplectic Lie algebra. This is Lie-algebra generation, distinct
from generation of the symplectic group by its root subgroups. It supplies the generation
step when comparing a folded Chevalley frame with the native symplectic matrix algebra.

Brackets along the chain produce the difference roots. Bracketing these with the terminal
long root produces the sum roots, and a second bracket produces every long root, with
coefficient two. Opposite long roots produce the diagonal Cartan. The block equations
then show that these matrices span every symplectic matrix.

## Main result

* `TauCeti.SpStd.lieSpan_range_rootGenerator_eq_top`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate III.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.

The chain-generation argument follows the type-B matrix proof in
`TauCeti.Algebra.Lie.Orthogonal.TypeB.Generation`, with long and short roots interchanged.
The diagonal-block difference matrices and their chain-bracket identity are shared with
`TauCeti.TypeDStd.differenceRootMatrix` and
`TauCeti.TypeDStd.lie_differenceRootGenerator_differenceRootGenerator`.
-/

public section

open Matrix
open scoped BigOperators

namespace TauCeti.SpStd

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ

private abbrev difference (i j : Fin (n + 1)) : Mat n :=
  TypeDStd.differenceRootMatrix i j

open TypeDStd (differenceRootMatrix_eq_single_sub_single)

-- File-local shorthand for the existing normalized long-root tangent matrices.
private abbrev upper (i : Fin (n + 1)) : Mat n :=
  (GLSymplecticFin.RootSubgroupIndex.positiveLong i).tangentMatrix (1 : ℚ)

private abbrev lower (i : Fin (n + 1)) : Mat n :=
  (GLSymplecticFin.RootSubgroupIndex.negativeLong i).tangentMatrix (1 : ℚ)

private def upperPair (i j : Fin (n + 1)) : Mat n :=
  single (.inl i) (.inr j) 1 + single (.inl j) (.inr i) 1

private def lowerPair (i j : Fin (n + 1)) : Mat n :=
  single (.inr i) (.inl j) 1 + single (.inr j) (.inl i) 1

private theorem lie_difference_upper (i j : Fin (n + 1)) :
    ⁅difference i j, upper j⁆ = upperPair i j := by
  simp [difference, differenceRootMatrix_eq_single_sub_single, upper, upperPair,
    Ring.lie_def, sub_mul, mul_sub]

private theorem lie_difference_upperPair (i j : Fin (n + 1)) (hij : i ≠ j) :
    ⁅difference i j, upperPair i j⁆ = (2 : ℚ) • upper i := by
  simp [difference, differenceRootMatrix_eq_single_sub_single, upper, upperPair,
    Ring.lie_def, sub_mul, mul_sub, mul_add, add_mul,
    hij, Ne.symm hij, two_smul]

private theorem lie_lower_difference (i j : Fin (n + 1)) :
    ⁅lower j, difference j i⁆ = lowerPair i j := by
  simp [difference, differenceRootMatrix_eq_single_sub_single, lower, lowerPair,
    Ring.lie_def, sub_mul, mul_sub, add_comm]

private theorem lie_lowerPair_difference (i j : Fin (n + 1)) (hij : i ≠ j) :
    ⁅lowerPair i j, difference j i⁆ = (2 : ℚ) • lower i := by
  simp [difference, differenceRootMatrix_eq_single_sub_single, lower, lowerPair,
    Ring.lie_def, sub_mul, mul_sub, mul_add, add_mul,
    hij, Ne.symm hij, two_smul]

private theorem lie_upper_lower (i : Fin (n + 1)) :
    ⁅upper i, lower i⁆ = difference i i := by
  simp [upper, lower, difference, differenceRootMatrix_eq_single_sub_single, Ring.lie_def]

/-- If every off-diagonal difference matrix and the terminal long roots lie in a Lie subalgebra,
then every long root matrix does: the second bracket has coefficient two, which is invertible over
the rationals. -/
private theorem upper_lower_mem_of_difference_mem (S : LieSubalgebra ℚ (Mat n))
    (hd : ∀ i j : Fin (n + 1), i ≠ j → difference i j ∈ S)
    (hu : upper (Fin.last n) ∈ S) (hl : lower (Fin.last n) ∈ S) (i : Fin (n + 1)) :
    upper i ∈ S ∧ lower i ∈ S := by
  by_cases hi : i = Fin.last n
  · subst i
    exact ⟨hu, hl⟩
  · have hdu := S.lie_mem (hd i (Fin.last n) hi) hu
    rw [lie_difference_upper i (Fin.last n)] at hdu
    have hdl := S.lie_mem hl (hd (Fin.last n) i (Ne.symm hi))
    rw [lie_lower_difference i (Fin.last n)] at hdl
    have hu' := S.smul_mem (1 / 2 : ℚ) (S.lie_mem (hd i (Fin.last n) hi) hdu)
    have hl' := S.smul_mem (1 / 2 : ℚ) (S.lie_mem hdl (hd (Fin.last n) i (Ne.symm hi)))
    rw [lie_difference_upperPair i (Fin.last n) hi, smul_smul] at hu'
    rw [lie_lowerPair_difference i (Fin.last n) hi, smul_smul] at hl'
    norm_num at hu' hl'
    exact ⟨by simpa only [upper, GLSymplecticFin.RootSubgroupIndex.tangentMatrix_positiveLong]
        using hu',
      by simpa only [lower, GLSymplecticFin.RootSubgroupIndex.tangentMatrix_negativeLong]
        using hl'⟩

private theorem symplectic_le_of_simple_mem (S : LieSubalgebra ℚ (Mat n))
    (hpos : ∀ i : Fin n, difference i.castSucc i.succ ∈ S)
    (hneg : ∀ i : Fin n, difference i.succ i.castSucc ∈ S)
    (hu : upper (Fin.last n) ∈ S) (hl : lower (Fin.last n) ∈ S) :
    LieAlgebra.Symplectic.sp (Fin (n + 1)) ℚ ≤ S := by
  have hd (i j : Fin (n + 1)) (hij : i ≠ j) : difference i j ∈ S := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact (S.differenceRootMatrix_mem_of_lt hpos hneg i j h).1
    · exact (S.differenceRootMatrix_mem_of_lt hpos hneg j i h).2
  have hul := upper_lower_mem_of_difference_mem S hd hu hl
  have hdiag (i : Fin (n + 1)) : difference i i ∈ S := by
    rw [← lie_upper_lower]
    exact S.lie_mem (hul i).1 (hul i).2
  have hup (i j : Fin (n + 1)) : upperPair i j ∈ S := by
    by_cases hij : i = j
    · subst j
      simpa [upperPair, upper, two_smul] using S.smul_mem (2 : ℚ) (hul i).1
    · rw [← lie_difference_upper i j]
      exact S.lie_mem (hd i j hij) (hul j).1
  have hlo (i j : Fin (n + 1)) : lowerPair i j ∈ S := by
    by_cases hij : i = j
    · subst j
      simpa [lowerPair, lower, two_smul] using S.smul_mem (2 : ℚ) (hul i).2
    · rw [← lie_lower_difference i j]
      exact S.lie_mem (hul j).2 (hd j i (Ne.symm hij))
  -- Average the two ordered off-block entries, counting diagonal entries twice as well.
  intro X hX
  obtain ⟨hQ, hT, hD⟩ := (mem_symplecticLieAlgebra_iff X).mp hX
  have hexpand : X =
      (∑ i, ∑ j, X (.inl i) (.inl j) • difference i j) +
      (∑ i, ∑ j, (X (.inl i) (.inr j) / 2) • upperPair i j) +
      (∑ i, ∑ j, (X (.inr i) (.inl j) / 2) • lowerPair i j) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [difference, differenceRootMatrix_eq_single_sub_single, upperPair, lowerPair,
        Matrix.sum_apply, Matrix.smul_apply,
        single_apply, ite_and, Finset.sum_add_distrib, hQ a b, hT a b, hD a b]
  rw [hexpand]
  refine S.add_mem (S.add_mem ?_ ?_) ?_
  · exact S.sum_mem fun i _ ↦ S.sum_mem fun j _ ↦
      S.smul_mem _ (if hij : i = j then hij ▸ hdiag i else hd i j hij)
  · exact S.sum_mem fun i _ ↦ S.sum_mem fun j _ ↦ S.smul_mem _ (hup i j)
  · exact S.sum_mem fun i _ ↦ S.sum_mem fun j _ ↦ S.smul_mem _ (hlo i j)

/-- The numbered positive and negative simple-root generators generate the rational
symplectic Lie algebra, including rank one. -/
@[simp]
theorem lieSpan_range_rootGenerator_eq_top (n : ℕ) :
    LieSubalgebra.lieSpan ℚ (LieAlgebra.Symplectic.sp (Fin (n + 1)) ℚ)
      (Set.range (rootGenerator n)) = ⊤ := by
  let S := LieSubalgebra.lieSpan ℚ (LieAlgebra.Symplectic.sp (Fin (n + 1)) ℚ)
    (Set.range (rootGenerator n))
  let T := S.map (LieAlgebra.Symplectic.sp (Fin (n + 1)) ℚ).incl
  have hpos (i : Fin (n + 1)) : positiveRootMatrix n i ∈ T :=
    ⟨rootGenerator n (.inl i), LieSubalgebra.subset_lieSpan (Set.mem_range_self _),
      val_rootGenerator_inl n i⟩
  have hneg (i : Fin (n + 1)) : negativeRootMatrix n i ∈ T :=
    ⟨rootGenerator n (.inr i), LieSubalgebra.subset_lieSpan (Set.mem_range_self _),
      val_rootGenerator_inr n i⟩
  have hchain (i : Fin n) : difference i.castSucc i.succ ∈ T := by
    have h := hpos i.castSucc
    rw [positiveRootMatrix_of_ne_last n i.castSucc (Fin.castSucc_ne_last i),
      Fin.orderSucc_castSucc] at h
    convert h using 1
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [difference, differenceRootMatrix_eq_single_sub_single, single_apply]
  have hchain' (i : Fin n) : difference i.succ i.castSucc ∈ T := by
    have h := hneg i.castSucc
    rw [negativeRootMatrix_of_ne_last n i.castSucc (Fin.castSucc_ne_last i),
      Fin.orderSucc_castSucc] at h
    convert h using 1
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [difference, differenceRootMatrix_eq_single_sub_single, single_apply]
  have hu : upper (Fin.last n) ∈ T := by
    have h := hpos (Fin.last n)
    rw [positiveRootMatrix_last] at h
    convert h using 1
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [upper, single_apply]
  have hl : lower (Fin.last n) ∈ T := by
    have h := hneg (Fin.last n)
    rw [negativeRootMatrix_last] at h
    convert h using 1
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [lower, single_apply]
  apply top_unique
  intro x _
  obtain ⟨y, hy, heq⟩ := symplectic_le_of_simple_mem T hchain hchain' hu hl x.property
  have hxy : y = x := Subtype.ext heq
  exact hxy ▸ hy

end TauCeti.SpStd
