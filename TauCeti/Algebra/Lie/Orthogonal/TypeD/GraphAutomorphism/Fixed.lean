/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.GraphAutomorphism.Restriction
public import TauCeti.Algebra.Lie.Subalgebra.Fixed

/-!
# The type-D graph fixed algebra as native type B

Restriction to the graph-invariant coordinates identifies the canonical fixed
Lie subalgebra of the native type-D graph involution with the native type-B Lie
algebra on the complementary indices. Its inverse extends by zero on the
anti-invariant line. The native odd orthogonal form retains its norm-two coordinate.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti

variable {I : Type*} [DecidableEq I] [Fintype I] (c : I)
  (A : Type*) [CommRing A] [Invertible (2 : A)]

/-- The fixed algebra of the chosen-pair involution is the native odd orthogonal
Lie algebra on the indices other than the chosen index. -/
def typeDGraphFixedLieEquiv :
    (typeDGraphLieEquiv c A).toLieHom.fixedSubalgebra ≃ₗ⁅A⁆ typeB {i : I // i ≠ c} A where
  toFun X := typeDGraphRestriction c A X.val
  invFun Y := ⟨typeDGraphExtension c A Y,
    LieHom.mem_fixedSubalgebra.mpr (typeDGraphLieEquiv_extension c A Y)⟩
  left_inv X := Subtype.ext (typeDGraphExtension_restriction c A X.val
    (LieHom.mem_fixedSubalgebra.mp X.property))
  right_inv Y := typeDGraphRestriction_extension c A Y
  map_add' X Y := (typeDGraphRestriction c A).map_add X.val Y.val
  map_smul' a X := (typeDGraphRestriction c A).map_smul a X.val
  map_lie' {X Y} := typeDGraphRestriction_lie_of_fixed c A X.val Y.val
    (LieHom.mem_fixedSubalgebra.mp X.property) (LieHom.mem_fixedSubalgebra.mp Y.property)

/-- The forward equivalence compresses the underlying matrix to invariant coordinates. -/
@[simp]
theorem typeDGraphFixedLieEquiv_apply_val
    (X : (typeDGraphLieEquiv c A).toLieHom.fixedSubalgebra) :
    (typeDGraphFixedLieEquiv c A X : Matrix
      (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c})
      (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) A) =
      typeDGraphProjection c A * X.val.val * typeDGraphInclusion c A := by
  exact typeDGraphRestriction_apply_val c A X.val

/-- The inverse equivalence extends the underlying matrix by zero on the anti-invariant line. -/
@[simp]
theorem typeDGraphFixedLieEquiv_symm_apply_val (Y : typeB {i : I // i ≠ c} A) :
    ((typeDGraphFixedLieEquiv c A).symm Y).val.val =
      typeDGraphInclusion c A * Y.val * typeDGraphProjection c A := by
  exact typeDGraphExtension_apply_val c A Y

end TauCeti
