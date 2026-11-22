/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Inversion
public import TauCeti.GroupTheory.GroupExtension.Quotient.Action
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Quotient extension of the dihedral rotation subgroup

Identifying the rotation subgroup `TauCeti.dihedralRotations (2 * n)` with
`Multiplicative (ZMod (2 * n))` and the quotient `DihedralGroup (2 * n) ⧸ dihedralRotations (2 * n)`
with `Multiplicative (ZMod 2)` intertwines the quotient conjugation action with the inversion
action `TauCeti.invMulDistribMulAction` (`TauCeti.dihedralRotationsMulEquiv_symm_smul`).

Relabelling the canonical quotient extension `(dihedralRotations (2 * n)).quotientExtension` along
these two equivalences gives `TauCeti.dihedralEvenExtension n`, an extension of
`Multiplicative (ZMod 2)` by `Multiplicative (ZMod (2 * n))` inducing
`TauCeti.invMulDistribMulAction` (`TauCeti.dihedralEvenExtension_inducesAction`).

## Main definitions

* `TauCeti.dihedralEvenExtension`: the quotient extension of `DihedralGroup (2 * n)` by its
  rotation subgroup, relabelled to kernel `Multiplicative (ZMod (2 * n))` and quotient
  `Multiplicative (ZMod 2)`.

## Main results

* `TauCeti.dihedralRotationsMulEquiv_symm_smul`: the dihedral coordinate equivalences intertwine
  the quotient conjugation action with `TauCeti.invMulDistribMulAction`.
* `TauCeti.dihedralEvenExtension_def`: `dihedralEvenExtension n` as a relabelling of the quotient
  extension.
* `TauCeti.dihedralEvenExtension_inl`, `TauCeti.dihedralEvenExtension_rightHom`: inclusion and
  projection of `dihedralEvenExtension`.
* `TauCeti.dihedralEvenExtension_inducesAction`: `dihedralEvenExtension n` induces the inversion
  action.
-/

public section

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- The dihedral coordinate equivalences intertwine the quotient conjugation action on
`dihedralRotations n` with `TauCeti.invMulDistribMulAction`. -/
theorem dihedralRotationsMulEquiv_symm_smul (n : ℕ)
    (q : DihedralGroup n ⧸ dihedralRotations n) (m : Multiplicative (ZMod n)) :
    (dihedralRotationsMulEquiv n).symm (dihedralQuotientEquiv n q • m) =
      q • (dihedralRotationsMulEquiv n).symm m := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  cases g with
  | r i =>
    have h1 : (DihedralGroup.r i : DihedralGroup n ⧸ dihedralRotations n) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (r_mem_dihedralRotations i)
    rw [h1, map_one, one_smul, one_smul]
  | sr i =>
    rw [dihedralQuotientEquiv_mk, dihedralReflectionParity_sr,
      invMulDistribMulAction_ofAdd_one_smul, map_inv, Subgroup.quotientConjugationAction_mk_smul,
      conjNormal_eq_inv_of_notMem_dihedralRotations (sr_notMem_dihedralRotations i)]

/-- The quotient extension of `DihedralGroup (2 * n)` by its rotation subgroup, relabelled to
kernel `Multiplicative (ZMod (2 * n))` and quotient `Multiplicative (ZMod 2)`. -/
noncomputable def dihedralEvenExtension (n : ℕ) :
    GroupExtension (Multiplicative (ZMod (2 * n))) (DihedralGroup (2 * n))
      (Multiplicative (ZMod 2)) :=
  (dihedralRotations (2 * n)).quotientExtension.relabel
    (dihedralRotationsMulEquiv (2 * n)).symm (dihedralQuotientEquiv (2 * n))

/-- `dihedralEvenExtension n` is the quotient extension of `dihedralRotations (2 * n)` relabelled
along `dihedralRotationsMulEquiv (2 * n)` and `dihedralQuotientEquiv (2 * n)`. -/
theorem dihedralEvenExtension_def (n : ℕ) :
    dihedralEvenExtension n =
      (dihedralRotations (2 * n)).quotientExtension.relabel
        (dihedralRotationsMulEquiv (2 * n)).symm (dihedralQuotientEquiv (2 * n)) :=
  (rfl)

/-- The inclusion of `dihedralEvenExtension n` sends `ofAdd i` to the rotation `r i`. -/
@[simp]
theorem dihedralEvenExtension_inl (n : ℕ) (m : Multiplicative (ZMod (2 * n))) :
    (dihedralEvenExtension n).inl m = DihedralGroup.r (Multiplicative.toAdd m) := by
  rw [dihedralEvenExtension_def]
  simp

/-- The projection of `dihedralEvenExtension n` is the reflection parity. -/
@[simp]
theorem dihedralEvenExtension_rightHom (n : ℕ) (g : DihedralGroup (2 * n)) :
    (dihedralEvenExtension n).rightHom g = dihedralReflectionParity (2 * n) g := by
  rw [dihedralEvenExtension_def]
  simp

/-- The relabelled dihedral extension induces the inversion action of `C₂` on `C_{2n}`. -/
theorem dihedralEvenExtension_inducesAction (n : ℕ) :
    TauCeti.GroupExtension.InducesAction (dihedralEvenExtension n) :=
  (dihedralRotations (2 * n)).quotientExtension_inducesAction.relabel
    (dihedralRotationsMulEquiv (2 * n)).symm (dihedralQuotientEquiv (2 * n))
    (dihedralRotationsMulEquiv_symm_smul (2 * n))

end TauCeti
