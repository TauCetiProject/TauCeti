/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Inversion
public import TauCeti.GroupTheory.GroupExtension.Quotient.Action
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Quotient extension of the quaternion rotation subgroup

Identifying the rotation subgroup `TauCeti.quaternionRotations n` with
`Multiplicative (ZMod (2 * n))` and the quotient `QuaternionGroup n ⧸ quaternionRotations n` with
`Multiplicative (ZMod 2)` intertwines the quotient conjugation action with the inversion action
`TauCeti.invMulDistribMulAction` (`TauCeti.quaternionRotationsMulEquiv_symm_smul`).

Relabelling the canonical quotient extension `(quaternionRotations n).quotientExtension` along
these two equivalences gives `TauCeti.quaternionExtension n`, an extension of
`Multiplicative (ZMod 2)` by `Multiplicative (ZMod (2 * n))` inducing
`TauCeti.invMulDistribMulAction` (`TauCeti.quaternionExtension_inducesAction`).

## Main definitions

* `TauCeti.quaternionExtension`: the quotient extension of `QuaternionGroup n` by its rotation
  subgroup, relabelled to kernel `Multiplicative (ZMod (2 * n))` and quotient
  `Multiplicative (ZMod 2)`.

## Main results

* `TauCeti.quaternionRotationsMulEquiv_symm_smul`: the quaternion coordinate equivalences
  intertwine the quotient conjugation action with `TauCeti.invMulDistribMulAction`.
* `TauCeti.quaternionExtension_def`: `quaternionExtension n` as a relabelling of the quotient
  extension.
* `TauCeti.quaternionExtension_inl`, `TauCeti.quaternionExtension_rightHom`: inclusion and
  projection of `quaternionExtension`.
* `TauCeti.quaternionExtension_inducesAction`: `quaternionExtension n` induces the inversion action.
-/

public section

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- The quaternion coordinate equivalences intertwine the quotient conjugation action on
`quaternionRotations n` with `TauCeti.invMulDistribMulAction`. -/
theorem quaternionRotationsMulEquiv_symm_smul (n : ℕ)
    (q : QuaternionGroup n ⧸ quaternionRotations n) (m : Multiplicative (ZMod (2 * n))) :
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n q • m) =
      q • (quaternionRotationsMulEquiv n).symm m :=
  (quaternionRotations n).quotientConjugationAction_smul_eq_of_mulEquiv_zmodTwo
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n)
    (fun _ hg ↦ conjNormal_eq_inv_of_notMem_quaternionRotations hg) q m

/-- The quotient extension of `QuaternionGroup n` by its rotation subgroup, relabelled to
kernel `Multiplicative (ZMod (2 * n))` and quotient `Multiplicative (ZMod 2)`. -/
noncomputable def quaternionExtension (n : ℕ) :
    GroupExtension (Multiplicative (ZMod (2 * n))) (QuaternionGroup n)
      (Multiplicative (ZMod 2)) :=
  (quaternionRotations n).quotientExtension.relabel
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n)

/-- `quaternionExtension n` is the quotient extension of `quaternionRotations n` relabelled
along `quaternionRotationsMulEquiv n` and `quaternionQuotientEquiv n`. -/
theorem quaternionExtension_def (n : ℕ) :
    quaternionExtension n =
      (quaternionRotations n).quotientExtension.relabel
        (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n) :=
  (rfl)

/-- The inclusion of `quaternionExtension n` sends `ofAdd i` to `a i`. -/
@[simp]
theorem quaternionExtension_inl (n : ℕ) (m : Multiplicative (ZMod (2 * n))) :
    (quaternionExtension n).inl m = QuaternionGroup.a (Multiplicative.toAdd m) := by
  rw [quaternionExtension_def]
  simp

/-- The projection of `quaternionExtension n` is the coset parity. -/
@[simp]
theorem quaternionExtension_rightHom (n : ℕ) (g : QuaternionGroup n) :
    (quaternionExtension n).rightHom g = quaternionCosetParity n g := by
  rw [quaternionExtension_def]
  simp

/-- The relabelled quaternion extension induces the inversion action of `C₂` on `C_{2n}`. -/
theorem quaternionExtension_inducesAction (n : ℕ) :
    TauCeti.GroupExtension.InducesAction (quaternionExtension n) :=
  (quaternionRotations n).quotientExtension_inducesAction.relabel
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n)
    (quaternionRotationsMulEquiv_symm_smul n)

end TauCeti
