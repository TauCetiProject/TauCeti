/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Reindex
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.GraphAutomorphism.Fixed

/-!
# The numbered type-D graph fixed algebra

For the involution on the last signed pair of `Fin (m + 1)`, the canonical fixed
Lie subalgebra is the native type-B Lie algebra on `Fin m`. The distinguished
norm-two coordinate is preserved by the reindexing.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti

variable (m : ℕ) (A : Type*) [CommRing A] [Invertible (2 : A)]

/-- The graph involution on the last signed pair has native type-B fixed algebra. -/
def typeDGraphFixedNumberedLieEquiv :
    (typeDGraphLieEquiv (Fin.last m) A).toLieHom.fixedSubalgebra ≃ₗ⁅A⁆ typeB (Fin m) A :=
  (typeDGraphFixedLieEquiv (Fin.last m) A).trans
    (typeBReindexLieEquiv A (finSuccAboveEquiv (Fin.last m)).symm)

/-- Compress to the invariant coordinates, then number the two complementary blocks. -/
@[simp]
theorem typeDGraphFixedNumberedLieEquiv_apply_val
    (X : (typeDGraphLieEquiv (Fin.last m) A).toLieHom.fixedSubalgebra) :
    (typeDGraphFixedNumberedLieEquiv m A X :
      Matrix (Unit ⊕ Fin m ⊕ Fin m) (Unit ⊕ Fin m ⊕ Fin m) A) =
      Matrix.reindex
        (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr
          (finSuccAboveEquiv (Fin.last m)).symm (finSuccAboveEquiv (Fin.last m)).symm))
        (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr
          (finSuccAboveEquiv (Fin.last m)).symm (finSuccAboveEquiv (Fin.last m)).symm))
        (typeDGraphProjection (Fin.last m) A * X.val.val *
          typeDGraphInclusion (Fin.last m) A) := by
  simp only [typeDGraphFixedNumberedLieEquiv, LieEquiv.trans_apply,
    typeBReindexLieEquiv_apply_val, typeDGraphFixedLieEquiv_apply_val]

/-- Restore the complementary indices, then extend by zero on the anti-invariant line. -/
@[simp]
theorem typeDGraphFixedNumberedLieEquiv_symm_apply_val (Y : typeB (Fin m) A) :
    ((typeDGraphFixedNumberedLieEquiv m A).symm Y).val.val =
      typeDGraphInclusion (Fin.last m) A *
        Matrix.reindex
          (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr
            (finSuccAboveEquiv (Fin.last m)) (finSuccAboveEquiv (Fin.last m))))
          (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr
            (finSuccAboveEquiv (Fin.last m)) (finSuccAboveEquiv (Fin.last m)))) Y.val *
        typeDGraphProjection (Fin.last m) A := by
  simp only [typeDGraphFixedNumberedLieEquiv, LieEquiv.symm_trans, LieEquiv.trans_apply,
    typeDGraphFixedLieEquiv_symm_apply_val, typeBReindexLieEquiv_symm_apply_val,
    Equiv.symm_symm]

end TauCeti
