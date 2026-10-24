/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.Killing
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The Killing form of the split odd orthogonal Lie algebra

The split odd orthogonal Lie algebra has nondegenerate Killing form over every field of
characteristic zero, including when the index type is empty and the Lie algebra is zero.
The Killing certificate makes Mathlib's abstract root system available for the concrete
diagonal Cartan.

For a nonempty index type, this is the orthogonal Lie algebra of the nondegenerate symmetric
form with Gram matrix `LieAlgebra.Orthogonal.JB`. It therefore has trivial radical by
`TauCeti.hasTrivialRadical_skewAdjointMatricesLieSubalgebra`.

## References

* Mathlib's `LieAlgebra.HasTrivialRadical.instIsKilling` (Cartan's criterion).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§5, 6, 19.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate II.
-/

public section

namespace TauCeti

open LieAlgebra

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The Killing form of the split odd orthogonal Lie algebra is nondegenerate over any field
of characteristic zero, including when the index type is empty and the Lie algebra is zero. -/
instance isKilling_typeB [CharZero K] :
    LieAlgebra.IsKilling K (Orthogonal.typeB ι K) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have : Subsingleton (Orthogonal.typeB ι K) := by
      refine ⟨fun A B ↦ Subtype.ext ?_⟩
      ext (a | (i | i)) (b | (j | j))
      · cases a
        cases b
        rw [Orthogonal.typeB.apply_inl_inl A (IsRegular.of_ne_zero two_ne_zero),
          Orthogonal.typeB.apply_inl_inl B (IsRegular.of_ne_zero two_ne_zero)]
      all_goals exact isEmptyElim ‹ι›
    infer_instance
  | inr h =>
    have : HasTrivialRadical K (Orthogonal.typeB ι K) := by
      apply hasTrivialRadical_skewAdjointMatricesLieSubalgebra
      · simp [Orthogonal.JB, Orthogonal.JD, Matrix.isSymm_fromBlocks_iff]
      · rw [Orthogonal.JB, Matrix.isUnit_fromBlocks_zero₂₁]
        constructor
        · simpa only [Algebra.algebraMap_eq_smul_one] using
            (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : K) ≠ 0)).map
              (algebraMap K (Matrix Unit Unit K))
        · refine isUnit_iff_exists_inv.mpr ⟨Orthogonal.JD ι K, ?_⟩
          simp [Orthogonal.JD, Matrix.fromBlocks_multiply]
      · simp only [Fintype.card_sum, Fintype.card_unit]
        have := Fintype.card_pos_iff.mpr h
        omega
    infer_instance

end TauCeti
