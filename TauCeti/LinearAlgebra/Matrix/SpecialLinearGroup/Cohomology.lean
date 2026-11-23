/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Non-vanishing central extension class of `SL(2, R)`

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and
`Matrix.SpecialLinearGroup.not_exists_isComplement'_center`, over any commutative ring `R` with
`(2 : R) ≠ 0`, the central quotient extension `1 → Z(SL₂(R)) → SL₂(R) → PSL₂(R) → 1` has nonzero
class in `H²(SL₂(R) ⧸ Z(SL₂(R)), Z(SL₂(R)))` (in particular for `SL(2, ZMod 3)`).

This is separated from `TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic` so the elementary
matrix-group API of `SL₂(R)` does not pull in group cohomology.

## Main results

* `Matrix.SpecialLinearGroup.cohomologyClass_center_ne_zero`: over any commutative ring `R` with
  `[NeZero (2 : R)]`, the central quotient extension of `SL(2, R)` has nonzero class in `H²`.
-/

public section

open scoped IsMulCommutative MatrixGroups

namespace Matrix.SpecialLinearGroup

attribute [local instance] Subgroup.quotientConjugationAction

/-- Over any commutative ring `R` with `(2 : R) ≠ 0`, the central quotient extension
`1 → Z(SL₂(R)) → SL₂(R) → PSL₂(R) → 1` has nonzero cohomology class in `H²`. -/
theorem cohomologyClass_center_ne_zero {R : Type} [CommRing R] [NeZero (2 : R)]
    (σ : (Subgroup.center SL(2, R)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
      (Subgroup.center SL(2, R)).quotientExtension_inducesAction).cohomologyClass ≠ 0 :=
  mt ((Subgroup.center SL(2, R)).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mpr
    not_exists_isComplement'_center

end Matrix.SpecialLinearGroup
