/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Second cohomology class of the dihedral rotation extension

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and the semidirect decomposition
`DihedralGroup n = C_n ⋊ C₂` (`TauCeti.isComplement'_dihedralRotations_zpowers_sr`), the quotient
extension class of `TauCeti.dihedralRotations n` in
`H²(DihedralGroup n ⧸ dihedralRotations n, dihedralRotations n)` vanishes at every `n : ℕ`
(including the infinite dihedral group at `n = 0`, `V₄` at `n = 2`, and `D₈` at `n = 4`).

This is separated from `TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic` so the subgroup and
recognition API of `DihedralGroup` does not pull in group cohomology.

## Main results

* `TauCeti.cohomologyClass_dihedralRotations_eq_zero`: the quotient extension class of
  `dihedralRotations n` vanishes in `H²` for every `n : ℕ`.
-/

public section

open scoped IsMulCommutative

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction

/-- The quotient extension class of the cyclic rotation subgroup in `DihedralGroup n` vanishes in
`H²` at every `n : ℕ` (including `D₈` at `n = 4` and `V₄` at `n = 2`), reflecting the semidirect
decomposition `DihedralGroup n = C_n ⋊ C₂`. -/
theorem cohomologyClass_dihedralRotations_eq_zero (n : ℕ)
    (σ : (dihedralRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (dihedralRotations n).quotientExtension_inducesAction).cohomologyClass = 0 :=
  ((dihedralRotations n).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mp
    ⟨_, isComplement'_dihedralRotations_zpowers_sr 0⟩

end TauCeti
