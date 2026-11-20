/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Non-splitting second cohomology classes of generalized quaternion groups

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and the non-complementability
results of `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic`, for every nonzero `n : ℕ` the
cyclic rotation subgroup `TauCeti.quaternionRotations n` in `QuaternionGroup n` has nonzero
quotient extension class in `H²` (including `C₄` at `n = 1` and `Q₈` at `n = 2`), and for `n ≠ 1`
the order-two centre of `QuaternionGroup n` likewise has nonzero central extension class in `H²`
(in particular `1 → C₂ → Q₈ → V₄ → 1` at `n = 2`).

This is separated from `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic` so the elementary
subgroup and recognition API of `QuaternionGroup` does not pull in group cohomology.

## Main results

* `TauCeti.cohomologyClass_quaternionRotations_ne_zero`: for nonzero `n`, the rotation quotient
  extension class of `QuaternionGroup n` is nonzero in `H²`.
* `TauCeti.cohomologyClass_center_quaternionGroup_ne_zero`: for `n ≠ 0` and `n ≠ 1`, the central
  quotient extension class of `QuaternionGroup n` is nonzero in `H²`.
-/

public section

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

end TauCeti
