/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Non-splitting second cohomology classes of generalized quaternion `2`-groups

Through `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` and the non-complementability
results of `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic`, the cyclic rotation subgroup
`TauCeti.quaternionRotations (2 ^ k)` in `QuaternionGroup (2 ^ k)` has nonzero quotient extension
class in `H²` at every `k : ℕ` (including `C₄` at `k = 0` and `Q₈` at `k = 1`), and for `k ≠ 0` the
order-two centre of `QuaternionGroup (2 ^ k)` likewise has nonzero central extension class in `H²`
(in particular `1 → C₂ → Q₈ → V₄ → 1` at `k = 1`).

This is separated from `TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic` so the elementary
subgroup and recognition API of `QuaternionGroup` does not pull in group cohomology.

## Main results

* `TauCeti.cohomologyClass_quaternionRotations_ne_zero`: the rotation quotient extension class of
  `QuaternionGroup (2 ^ k)` is nonzero in `H²` for every `k : ℕ`.
* `TauCeti.cohomologyClass_center_quaternionGroup_ne_zero`: for `k ≠ 0`, the central quotient
  extension class of `QuaternionGroup (2 ^ k)` is nonzero in `H²`.
-/

public section

open scoped IsMulCommutative

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction

/-- The quotient extension class of the cyclic rotation subgroup in `QuaternionGroup (2 ^ k)` is
nonzero in `H²` at every `k : ℕ` (including `C₄` at `k = 0` and `Q₈` at `k = 1`). -/
theorem cohomologyClass_quaternionRotations_ne_zero (k : ℕ)
    (σ : (quaternionRotations (2 ^ k)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (quaternionRotations (2 ^ k)).quotientExtension_inducesAction).cohomologyClass ≠ 0 :=
  mt ((quaternionRotations (2 ^ k)).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mpr
    (not_exists_isComplement'_quaternionRotations (2 ^ k))

/-- For `k ≠ 0`, the central quotient extension of `QuaternionGroup (2 ^ k)` by its order-two
centre has nonzero class in `H²` (in particular for `Q₈` at `k = 1`, where the quotient is `V₄`). -/
theorem cohomologyClass_center_quaternionGroup_ne_zero {k : ℕ} (hk : k ≠ 0)
    (σ : (Subgroup.center (QuaternionGroup (2 ^ k))).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (Subgroup.center (QuaternionGroup (2 ^ k))).quotientExtension_inducesAction).cohomologyClass ≠
        0 :=
  mt ((Subgroup.center (QuaternionGroup (2 ^ k))).exists_complement_iff_cohomologyClass_eq_zero
    σ hσ).mpr
    (not_exists_isComplement'_center_quaternionGroup (Nat.ne_of_gt (one_lt_pow₀ (by decide) hk)))

end TauCeti
