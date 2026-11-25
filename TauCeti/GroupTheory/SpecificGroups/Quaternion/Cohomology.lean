/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.GroupExtension.Quotient.Inversion
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Non-splitting second cohomology classes of generalized quaternion groups

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and the non-complementability
results of `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic`, for every nonzero `n : ℕ` the
cyclic rotation subgroup `TauCeti.quaternionRotations n` in `QuaternionGroup n` has nonzero
quotient extension class in `H²` (including `C₄` at `n = 1` and `Q₈` at `n = 2`), and for `n ≠ 1`
the order-two centre of `QuaternionGroup n` likewise has nonzero central extension class in `H²`
(in particular `1 → C₂ → Q₈ → V₄ → 1` at `n = 2`).

Every element outside the rotations inverts them, so through `Q₄ₙ ⧸ C₂ₙ ≃* C₂` and the rotation
coordinate `C₂ₙ ≃* ZMod (2 * n)` the rotation cohomology is that of `C₂` acting on `ZMod (2 * n)`
by negation (`TauCeti.quaternionRotationsGroupCohomologyIsoNeg`), and there too the class is
nonzero.

This is separated from `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic` so the elementary
subgroup and recognition API of `QuaternionGroup` does not pull in group cohomology.

## Main definitions

* `TauCeti.quaternionRotationsGroupCohomologyIsoNeg`: the cohomology of the rotation quotient
  module of `QuaternionGroup n`, identified with that of `C₂` acting on `ZMod (2 * n)` by
  negation.

## Main results

* `TauCeti.cohomologyClass_quaternionRotations_ne_zero`: for nonzero `n`, the rotation quotient
  extension class of `QuaternionGroup n` is nonzero in `H²`.
* `TauCeti.cohomologyClass_center_quaternionGroup_ne_zero`: for `n ≠ 0` and `n ≠ 1`, the central
  quotient extension class of `QuaternionGroup n` is nonzero in `H²`.
* `TauCeti.quaternionRotationsGroupCohomologyIsoNeg_def`: that identification is
  `Subgroup.quotientGroupCohomologyIsoNeg` for `xa 0` and the rotation coordinate.
* `TauCeti.quaternionRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_ne_zero`: for nonzero
  `n`, so is the image of the rotation class in `H²(C₂, ZMod (2 * n))`.
-/

public section

open CategoryTheory

open scoped IsMulCommutative

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction

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

/-- The cohomology of the quotient module of `Q₄ₙ = QuaternionGroup n` on its rotations,
identified with the cohomology of `C₂` acting on `ZMod (2 * n)` by negation through
`Q₄ₙ ⧸ C₂ₙ ≃* C₂` and the rotation coordinate `C₂ₙ ≃* ZMod (2 * n)`. -/
noncomputable def quaternionRotationsGroupCohomologyIsoNeg (n k : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction (QuaternionGroup n ⧸ quaternionRotations n)
        (quaternionRotations n)) k ≅
      groupCohomology ((AddEquiv.neg (ZMod (2 * n))).cyclicRep (AddEquiv.iterate_neg_two _)) k :=
  Subgroup.quotientGroupCohomologyIsoNeg (index_quaternionRotations n)
    (xa_notMem_quaternionRotations 0)
    (fun _ hx ↦ conj_eq_inv_of_notMem_quaternionRotations (xa_notMem_quaternionRotations 0) hx)
    (quaternionRotationsMulEquiv n) k

/-- `TauCeti.quaternionRotationsGroupCohomologyIsoNeg` is `Subgroup.quotientGroupCohomologyIsoNeg`
for the element `xa 0` outside the rotations and the rotation coordinate
`quaternionRotationsMulEquiv n`. -/
theorem quaternionRotationsGroupCohomologyIsoNeg_def (n k : ℕ) :
    quaternionRotationsGroupCohomologyIsoNeg n k =
      Subgroup.quotientGroupCohomologyIsoNeg (index_quaternionRotations n)
        (xa_notMem_quaternionRotations 0)
        (fun _ hx ↦ conj_eq_inv_of_notMem_quaternionRotations (xa_notMem_quaternionRotations 0) hx)
        (quaternionRotationsMulEquiv n) k :=
  (rfl)

/-- For `n ≠ 0`, the class of the quaternion extension `C₂ₙ → Q₄ₙ → C₂` is nonzero in
`H²(C₂, ZMod (2 * n))`. -/
theorem quaternionRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_ne_zero (n : ℕ) [NeZero n]
    (σ : (quaternionRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (quaternionRotationsGroupCohomologyIsoNeg n 2).hom (GroupExtension.factorSet σ hσ
      (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass ≠ 0 :=
  (map_ne_zero_iff _ (quaternionRotationsGroupCohomologyIsoNeg n 2).toLinearEquiv.injective).2
    (cohomologyClass_quaternionRotations_ne_zero n σ hσ)

end TauCeti
