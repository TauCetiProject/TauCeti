/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.RingTheory.Ideal.Defs

/-!
# The units congruent to one modulo an ideal

For an ideal `I` of a ring `R`, the units `u` with `u - 1 ∈ I` form a subgroup of `Rˣ`, the
principal unit group of `I`. For the maximal ideal of a valuation ring this is Mathlib's
`ValuationSubring.principalUnitGroup`; here `I` is arbitrary. When `I` consists of topologically
nilpotent elements of a complete linearly topologized `ℚ`-algebra, the exponential is an
isomorphism from the additive group of `I` onto this group (`Ideal.expMulEquiv`).

## Main definitions

* `Ideal.principalUnitGroup`: the units `u` with `u - 1 ∈ I`.
-/

public section

namespace Ideal

variable {R : Type*} [Ring R]

variable (I : Ideal R) in
/-- The principal unit group of an ideal `I`: the units `u` with `u - 1 ∈ I`. -/
def principalUnitGroup : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have huv : ((u * v : Rˣ) : R) - 1 = u * ((v : R) - 1) + ((u : R) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [Set.mem_ofPred_eq, huv]
    exact add_mem (I.mul_mem_left _ hv) hu
  inv_mem' {u} hu := by
    have hu' : ((u⁻¹ : Rˣ) : R) - 1 = -(↑u⁻¹ * ((u : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [Set.mem_ofPred_eq, hu']
    exact neg_mem (I.mul_mem_left _ hu)

@[simp]
theorem mem_principalUnitGroup {I : Ideal R} {u : Rˣ} :
    u ∈ I.principalUnitGroup ↔ (u : R) - 1 ∈ I :=
  Iff.rfl

end Ideal
