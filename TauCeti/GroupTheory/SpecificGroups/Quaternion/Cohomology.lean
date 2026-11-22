/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Cyclic.Cohomology
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.GroupExtension.Relabel
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Extension
import TauCeti.Data.ZMod.MonoidHomEquiv

/-!
# Non-splitting second cohomology classes of generalized quaternion groups

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and the non-complementability
results of `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic`, for every nonzero `n : ℕ` the
cyclic rotation subgroup `TauCeti.quaternionRotations n` in `QuaternionGroup n` has nonzero
quotient extension class in `H²` (including `C₄` at `n = 1` and `Q₈` at `n = 2`), and for `n ≠ 1`
the order-two centre of `QuaternionGroup n` likewise has nonzero central extension class in `H²`
(in particular `1 → C₂ → Q₈ → V₄ → 1` at `n = 2`).

Transporting the rotation quotient extension along `quaternionRotationsMulEquiv n` and
`quaternionQuotientEquiv n` places its class `TauCeti.quaternionExtensionClass n` inside
`H²(C₂, C_{2n}^{inv})`, where it maps to `1 : ZMod 2` under
`Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n` and is nonzero for `n ≠ 0`.

This is separated from `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic` so the elementary
subgroup and recognition API of `QuaternionGroup` does not pull in group cohomology.

## Main definitions

* `TauCeti.quaternionExtensionClass`: the cohomology class of
  `1 → C_{2n} → QuaternionGroup n → C₂ → 1` inside `H²(C₂, C_{2n}^{inv})`.

## Main results

* `TauCeti.cohomologyClass_quaternionRotations_ne_zero`: for nonzero `n`, the rotation quotient
  extension class of `QuaternionGroup n` is nonzero in `H²`.
* `TauCeti.cohomologyClass_center_quaternionGroup_ne_zero`: for `n ≠ 0` and `n ≠ 1`, the central
  quotient extension class of `QuaternionGroup n` is nonzero in `H²`.
* `TauCeti.cohomologyClass_factorSet_quaternionExtension`: any normalized section of
  `quaternionExtension n` has factor-set class `quaternionExtensionClass n`.
* `TauCeti.relabelCohomologyIso_quaternion_cohomologyClass`: relabelling sends the rotation
  quotient extension class of `QuaternionGroup n` to `quaternionExtensionClass n`.
* `TauCeti.groupCohomologyTwoInvEquivZModTwo_quaternionExtensionClass`:
  `quaternionExtensionClass n` maps to `1 : ZMod 2` for `n ≠ 0`.
* `TauCeti.quaternionExtensionClass_ne_zero`: `quaternionExtensionClass n ≠ 0` for `n ≠ 0`.
-/

public section

open scoped IsMulCommutative

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- For nonzero `n`, the quotient extension class of the cyclic rotation subgroup in
`QuaternionGroup n` is nonzero in `H²` (including `C₄` at `n = 1` and `Q₈` at `n = 2`). -/
theorem cohomologyClass_quaternionRotations_ne_zero (n : ℕ) [NeZero n]
    (σ : (quaternionRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass ≠ 0 :=
  mt ((quaternionRotations n).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mpr
    (not_exists_isComplement'_quaternionRotations n)

/-- For `n ≠ 0` and `n ≠ 1`, the central quotient extension of `QuaternionGroup n` by its
order-two centre has nonzero class in `H²` (in particular for `Q₈` at `n = 2`, where the quotient
is `V₄`). -/
theorem cohomologyClass_center_quaternionGroup_ne_zero {n : ℕ} [NeZero n] (hn : n ≠ 1)
    (σ : (Subgroup.center (QuaternionGroup n)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (Subgroup.center (QuaternionGroup n)).quotientExtension_inducesAction).cohomologyClass ≠ 0 :=
  mt ((Subgroup.center (QuaternionGroup n)).exists_complement_iff_cohomologyClass_eq_zero
    σ hσ).mpr
    (not_exists_isComplement'_center_quaternionGroup hn)

/-- The cohomology class of `1 → C_{2n} → QuaternionGroup n → C₂ → 1` inside
`H²(C₂, C_{2n}^{inv})`. -/
noncomputable def quaternionExtensionClass (n : ℕ) :
    groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2 :=
  (GroupExtension.factorSet
    ((quaternionExtension n).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := QuaternionGroup.xa 0) (by simp))
    ((quaternionExtension n).cyclicPowerSection_one _ _ _)
    (quaternionExtension_inducesAction n)).cohomologyClass

/-- Every normalized section of `TauCeti.quaternionExtension n` has factor-set cohomology class
equal to `TauCeti.quaternionExtensionClass n`. -/
theorem cohomologyClass_factorSet_quaternionExtension (n : ℕ)
    (σ : (quaternionExtension n).Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ (quaternionExtension_inducesAction n)).cohomologyClass =
      quaternionExtensionClass n :=
  GroupExtension.cohomologyClass_factorSet_eq σ _ hσ _
    (quaternionExtension_inducesAction n)

/-- Relabelling sends the cohomology class of any normalized section of the quaternion quotient
extension to `quaternionExtensionClass n`. -/
theorem relabelCohomologyIso_quaternion_cohomologyClass (n : ℕ)
    (σ : (quaternionRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (groupCohomology.relabelCohomologyIso (quaternionRotationsMulEquiv n).symm
        (quaternionQuotientEquiv n) (quaternionRotationsMulEquiv_symm_smul n) 2).hom
      (GroupExtension.factorSet σ hσ
        (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass =
      quaternionExtensionClass n := by
  rw [quaternionExtensionClass]
  exact GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n)
    (quaternionRotationsMulEquiv_symm_smul n) (quaternionExtension_def n) σ hσ
    (quaternionRotations n).quotientExtension_inducesAction _ _
    (quaternionExtension_inducesAction n)

/-- The quaternion extension class maps to `1 : ZMod 2` under
`Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n`, because the lift `xa 0` satisfies
`(xa 0) ^ 2 = a n`. -/
@[simp]
theorem groupCohomologyTwoInvEquivZModTwo_quaternionExtensionClass (n : ℕ) [NeZero n] :
    Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n
      (quaternionExtensionClass n) = 1 := by
  rw [quaternionExtensionClass]
  let σ := (quaternionExtension n).cyclicPowerSection (Multiplicative.ofAdd 1)
    Multiplicative.mem_zpowers_ofAdd_one (e := QuaternionGroup.xa 0) (by simp)
  refine (σ.groupCohomologyTwoInvEquivZModTwo_cohomologyClass_factorSet_iff
    ((quaternionExtension n).cyclicPowerSection_one _ _ _)
    (quaternionExtension_inducesAction n) (e := QuaternionGroup.xa 0) (by simp)
    (a := (n : ZMod (2 * n))) ?_ 1).2 (by rw [ZMod.val_one, one_mul])
  simp [sq, QuaternionGroup.xa_mul_xa]

/-- The quaternion extension class is nonzero in `H²(C₂, C_{2n}^{inv})`. -/
theorem quaternionExtensionClass_ne_zero (n : ℕ) [NeZero n] :
    quaternionExtensionClass n ≠ 0 := fun h ↦ by
  have h1 := congrArg (Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n) h
  rw [groupCohomologyTwoInvEquivZModTwo_quaternionExtensionClass, map_zero] at h1
  exact one_ne_zero h1

end TauCeti
