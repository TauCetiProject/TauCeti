/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZModThree.Basic

/-!
# Non-vanishing central extension class of `SL(2, ZMod 3)`

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and
`TauCeti.not_exists_isComplement'_center_sl2_zmod_three`, the central extension
`1 → {±1} → SL(2, ZMod 3) → PSL(2, ZMod 3) → 1` has nonzero class in
`H²(SL(2, ZMod 3) ⧸ Subgroup.center SL(2, ZMod 3), Subgroup.center SL(2, ZMod 3))`.

This is separated from `TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZModThree.Basic` so the
Sylow and matrix-subgroup API of `SL(2, ZMod 3)` does not pull in group cohomology.

## Main results

* `TauCeti.cohomologyClass_center_sl2_zmod_three_ne_zero`: the central quotient extension of
  `SL(2, ZMod 3)` has nonzero class in `H²`.
-/

public section

open scoped IsMulCommutative MatrixGroups

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction

/-- The central extension `1 → {±1} → SL(2, ZMod 3) → PSL(2, ZMod 3) → 1` has nonzero cohomology
class in `H²`. -/
theorem cohomologyClass_center_sl2_zmod_three_ne_zero
    (σ : (Subgroup.center SL(2, ZMod 3)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (Subgroup.center SL(2, ZMod 3)).quotientExtension_inducesAction).cohomologyClass ≠ 0 :=
  mt ((Subgroup.center SL(2, ZMod 3)).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mpr
    not_exists_isComplement'_center_sl2_zmod_three

end TauCeti
