/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.InversionAction
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Quotient extension of the dihedral rotation subgroup

Identifying the rotation subgroup `TauCeti.dihedralRotations n` with
`Multiplicative (ZMod n)` and the quotient `DihedralGroup n ⧸ dihedralRotations n` with
`Multiplicative (ZMod 2)` intertwines the quotient conjugation action with the inversion action
`TauCeti.invMulDistribMulAction` (`TauCeti.dihedralRotationsMulEquiv_symm_smul`).

Relabelling the canonical quotient extension `(dihedralRotations n).quotientExtension` along
these two equivalences gives `TauCeti.dihedralExtension n`, an extension of
`Multiplicative (ZMod 2)` by `Multiplicative (ZMod n)` inducing
`TauCeti.invMulDistribMulAction` (`TauCeti.dihedralExtension_inducesAction`).

## Main definitions

* `TauCeti.dihedralExtension`: the quotient extension of `DihedralGroup n` by its rotation
  subgroup, relabelled to kernel `Multiplicative (ZMod n)` and quotient `Multiplicative (ZMod 2)`.

## Main results

* `TauCeti.dihedralRotationsMulEquiv_symm_smul`: the dihedral coordinate equivalences intertwine
  the quotient conjugation action with `TauCeti.invMulDistribMulAction`.
* `TauCeti.dihedralExtension_def`: `dihedralExtension n` as a relabelling of the quotient
  extension.
* `TauCeti.dihedralExtension_inl`, `TauCeti.dihedralExtension_rightHom`: inclusion and
  projection of `dihedralExtension`.
* `TauCeti.dihedralExtension_inducesAction`: `dihedralExtension n` induces the inversion action.
-/

public section

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- The dihedral coordinate equivalences intertwine the quotient conjugation action on
`dihedralRotations n` with `TauCeti.invMulDistribMulAction`. -/
theorem dihedralRotationsMulEquiv_symm_smul (n : ℕ)
    (q : DihedralGroup n ⧸ dihedralRotations n) (m : Multiplicative (ZMod n)) :
    (dihedralRotationsMulEquiv n).symm (dihedralQuotientEquiv n q • m) =
      q • (dihedralRotationsMulEquiv n).symm m :=
  (dihedralRotations n).quotientConjugationAction_smul_eq_of_mulEquiv_zmodTwo
    (dihedralRotationsMulEquiv n).symm (dihedralQuotientEquiv n)
    (fun _ hg ↦ conjNormal_eq_inv_of_notMem_dihedralRotations hg) q m

/-- The quotient extension of `DihedralGroup n` by its rotation subgroup, relabelled to kernel
`Multiplicative (ZMod n)` and quotient `Multiplicative (ZMod 2)`. -/
noncomputable def dihedralExtension (n : ℕ) :
    GroupExtension (Multiplicative (ZMod n)) (DihedralGroup n) (Multiplicative (ZMod 2)) :=
  (dihedralRotations n).quotientExtension.relabel
    (dihedralRotationsMulEquiv n).symm (dihedralQuotientEquiv n)

/-- `dihedralExtension n` is the quotient extension of `dihedralRotations n` relabelled along
`dihedralRotationsMulEquiv n` and `dihedralQuotientEquiv n`. -/
theorem dihedralExtension_def (n : ℕ) :
    dihedralExtension n =
      (dihedralRotations n).quotientExtension.relabel
        (dihedralRotationsMulEquiv n).symm (dihedralQuotientEquiv n) :=
  (rfl)

/-- The inclusion of `dihedralExtension n` sends `ofAdd i` to the rotation `r i`. -/
@[simp]
theorem dihedralExtension_inl (n : ℕ) (m : Multiplicative (ZMod n)) :
    (dihedralExtension n).inl m = DihedralGroup.r (Multiplicative.toAdd m) := by
  rw [dihedralExtension_def]
  simp

/-- The projection of `dihedralExtension n` is the reflection parity. -/
@[simp]
theorem dihedralExtension_rightHom (n : ℕ) (g : DihedralGroup n) :
    (dihedralExtension n).rightHom g = dihedralReflectionParity n g := by
  rw [dihedralExtension_def]
  simp

/-- The relabelled dihedral extension induces the inversion action of `C₂` on `Cₙ`. -/
theorem dihedralExtension_inducesAction (n : ℕ) :
    GroupExtension.InducesAction (dihedralExtension n) :=
  (dihedralRotations n).quotientExtension_inducesAction.relabel
    (dihedralRotationsMulEquiv n).symm (dihedralQuotientEquiv n)
    (dihedralRotationsMulEquiv_symm_smul n)

end TauCeti
