/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.Lie.Subalgebra.Fixed
public import TauCeti.LinearAlgebra.Matrix.SkewAdjoint

/-!
# The native type-A fixed Lie algebra as skew-adjoint matrices

When `2` is invertible, the fixed Lie subalgebra of the native type-A graph automorphism is
Lie equivalent to the matrices skew-adjoint for the inverse signed reversal form. Both maps
retain the underlying matrix.
-/

public section

open Matrix LieAlgebra.SpecialLinear

namespace TauCeti

variable (r : ℕ) (A : Type*) [CommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A trace-zero matrix is fixed exactly when it is skew-adjoint for the inverse conjugator. -/
theorem mem_typeASpecialLinearGraphAutomorphism_fixedSubalgebra_iff
    (X : sl (Fin (r + 1)) A) :
    X ∈ (typeASpecialLinearGraphAutomorphism r A).toLieHom.fixedSubalgebra ↔
      (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹.IsSkewAdjoint X :=
  LieHom.mem_fixedSubalgebra.trans (typeASpecialLinearGraphAutomorphism_eq_self_iff r A X)

private theorem isUnit_typeAGraphConjugator_inv :
    IsUnit ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹) := by
  rw [← GeneralLinearGroup.coe_inv]
  exact ((typeAGraphConjugator r A)⁻¹).isUnit

variable [Invertible (2 : A)]

/-- The native fixed special linear Lie algebra is the skew-adjoint matrix Lie algebra for
the inverse signed reversal form. Both directions retain the underlying matrix. -/
def typeASpecialLinearFixedSkewAdjointEquiv :
    (typeASpecialLinearGraphAutomorphism r A).toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
      skewAdjointMatricesLieSubalgebra
        ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹) where
  toFun X := ⟨X.val.val, by
    simpa only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] using
      (mem_typeASpecialLinearGraphAutomorphism_fixedSubalgebra_iff r A X.val).mp X.property⟩
  invFun Y :=
    let hY :
        ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹).IsSkewAdjoint
          Y.val := by
      simpa only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] using
        Y.property
    ⟨⟨Y.val, Matrix.IsSkewAdjoint.trace_eq_zero (isUnit_typeAGraphConjugator_inv r A) hY⟩,
      (mem_typeASpecialLinearGraphAutomorphism_fixedSubalgebra_iff r A _).mpr hY⟩
  -- The carriers inherit their operations from matrices, and both maps retain the matrix.
  left_inv X := Subtype.ext (Subtype.ext rfl)
  right_inv Y := Subtype.ext rfl
  map_add' X Y := Subtype.ext rfl
  map_smul' a X := Subtype.ext rfl
  map_lie' {X Y} := Subtype.ext rfl

/-- The forward equivalence retains the underlying matrix of a fixed trace-zero element. -/
@[simp]
theorem coe_typeASpecialLinearFixedSkewAdjointEquiv_apply
    (X : (typeASpecialLinearGraphAutomorphism r A).toLieHom.fixedSubalgebra) :
    (typeASpecialLinearFixedSkewAdjointEquiv r A X :
      Matrix (Fin (r + 1)) (Fin (r + 1)) A) = X.val.val := by
  ext i j
  rfl

/-- The inverse equivalence retains the underlying skew-adjoint matrix. -/
@[simp]
theorem coe_typeASpecialLinearFixedSkewAdjointEquiv_symm_apply
    (Y : skewAdjointMatricesLieSubalgebra
      ((typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A)⁻¹)) :
    ((typeASpecialLinearFixedSkewAdjointEquiv r A).symm Y).val.val = Y.val := by
  ext i j
  rfl

end TauCeti
