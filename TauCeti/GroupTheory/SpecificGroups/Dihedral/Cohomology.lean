/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Cyclic.Inversion
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.GroupExtension.Relabel
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Extension

/-!
# Second cohomology class of the dihedral rotation extension

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and the semidirect decomposition
`DihedralGroup n = C_n ⋊ C₂` (`TauCeti.isComplement'_dihedralRotations_zpowers_sr`), the quotient
extension class of `TauCeti.dihedralRotations n` in
`H²(DihedralGroup n ⧸ dihedralRotations n, dihedralRotations n)` vanishes at every `n : ℕ`
(including the infinite dihedral group at `n = 0`, `V₄` at `n = 2`, and `D₈` at `n = 4`).

For `DihedralGroup (2 * n)`, transporting the quotient extension along the coordinate
equivalences `dihedralRotationsMulEquiv (2 * n)` and `dihedralQuotientEquiv (2 * n)` via
`TauCeti.groupCohomology.relabelCohomologyIso` places its class
`TauCeti.dihedralEvenExtensionClass n` inside `H²(C₂, C_{2n}^{inv})`, where it vanishes and maps to
`0 : ZMod 2` under `Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n`.

This is separated from `TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic` so the subgroup and
recognition API of `DihedralGroup` does not pull in group cohomology.

## Main definitions

* `TauCeti.dihedralEvenExtensionClass`: the cohomology class of
  `1 → C_{2n} → DihedralGroup (2 * n) → C₂ → 1` inside `H²(C₂, C_{2n}^{inv})`.

## Main results

* `TauCeti.cohomologyClass_dihedralRotations_eq_zero`: the quotient extension class of
  `dihedralRotations n` vanishes in `H²` for every `n : ℕ`.
* `TauCeti.cohomologyClass_factorSet_dihedralExtension`: any normalized section of
  `dihedralExtension (2 * n)` has factor-set class `dihedralEvenExtensionClass n`.
* `TauCeti.relabelCohomologyIso_dihedral_cohomologyClass`: relabelling sends the quotient
  extension class of `DihedralGroup (2 * n)` to `dihedralEvenExtensionClass n`.
* `TauCeti.groupCohomologyTwoInvEquivZModTwo_dihedralEvenExtensionClass`:
  `dihedralEvenExtensionClass n` maps to `0 : ZMod 2`.
* `TauCeti.dihedralEvenExtensionClass_eq_zero`: `dihedralEvenExtensionClass n = 0`.
-/

public section

open CategoryTheory

open scoped IsMulCommutative

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- The quotient extension class of the cyclic rotation subgroup in `DihedralGroup n` vanishes in
`H²` at every `n : ℕ` (including `D₈` at `n = 4` and `V₄` at `n = 2`), reflecting the semidirect
decomposition `DihedralGroup n = C_n ⋊ C₂`. -/
theorem cohomologyClass_dihedralRotations_eq_zero (n : ℕ)
    (σ : (dihedralRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (dihedralRotations n).quotientExtension_inducesAction).cohomologyClass = 0 :=
  ((dihedralRotations n).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mp
    ⟨_, isComplement'_dihedralRotations_zpowers_sr 0⟩

/-- The cohomology class of `1 → C_{2n} → DihedralGroup (2 * n) → C₂ → 1` inside
`H²(C₂, C_{2n}^{inv})`. -/
noncomputable def dihedralEvenExtensionClass (n : ℕ) :
    groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2 :=
  (GroupExtension.factorSet
    ((dihedralExtension (2 * n)).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := DihedralGroup.sr 0) (by simp))
    ((dihedralExtension (2 * n)).cyclicPowerSection_one _ _ _)
    (dihedralExtension_inducesAction (2 * n))).cohomologyClass

/-- Every normalized section of `TauCeti.dihedralExtension (2 * n)` has factor-set cohomology
class equal to `TauCeti.dihedralEvenExtensionClass n`. -/
theorem cohomologyClass_factorSet_dihedralExtension (n : ℕ)
    (σ : (dihedralExtension (2 * n)).Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (dihedralExtension_inducesAction (2 * n))).cohomologyClass =
      dihedralEvenExtensionClass n :=
  GroupExtension.cohomologyClass_factorSet_eq σ _ hσ _
    (dihedralExtension_inducesAction (2 * n))

/-- Relabelling sends the cohomology class of any normalized section of the dihedral quotient
extension to `dihedralEvenExtensionClass n`. -/
theorem relabelCohomologyIso_dihedral_cohomologyClass (n : ℕ)
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (groupCohomology.relabelCohomologyIso (dihedralRotationsMulEquiv (2 * n)).symm
        (dihedralQuotientEquiv (2 * n)) (dihedralRotationsMulEquiv_symm_smul (2 * n)) 2).hom
      (GroupExtension.factorSet σ hσ
        (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass =
      dihedralEvenExtensionClass n := by
  rw [dihedralEvenExtensionClass]
  exact GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet
    (dihedralRotationsMulEquiv (2 * n)).symm (dihedralQuotientEquiv (2 * n))
    (dihedralRotationsMulEquiv_symm_smul (2 * n)) (dihedralExtension_def (2 * n)) σ hσ
    (dihedralRotations (2 * n)).quotientExtension_inducesAction _ _
    (dihedralExtension_inducesAction (2 * n))

/-- The dihedral extension class vanishes in `H²(C₂, C_{2n}^{inv})`. -/
@[simp]
theorem dihedralEvenExtensionClass_eq_zero (n : ℕ) : dihedralEvenExtensionClass n = 0 := by
  let σ := GroupExtension.normalizeSection
    (dihedralRotations (2 * n)).quotientExtension.surjInvRightHom
  have hσ : σ 1 = 1 := GroupExtension.normalizeSection_one _
  rw [← relabelCohomologyIso_dihedral_cohomologyClass n σ hσ,
    cohomologyClass_dihedralRotations_eq_zero (2 * n) σ hσ, map_zero]

/-- The dihedral extension class maps to `0 : ZMod 2` under
`Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n`. -/
theorem groupCohomologyTwoInvEquivZModTwo_dihedralEvenExtensionClass (n : ℕ) [NeZero n] :
    Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n
      (dihedralEvenExtensionClass n) = 0 := by
  rw [dihedralEvenExtensionClass_eq_zero, map_zero]

end TauCeti
