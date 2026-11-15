/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The quaternion group in Hamilton's quaternions

The standard homomorphism from `QuaternionGroup 2` to Hamilton's quaternions sends the
rotation generator to i and the other generator to j. Its images span ℍ over ℝ, providing
concrete operators for real representations of the quaternion group.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §13.2.
-/

public section

open scoped Quaternion

namespace TauCeti

local notation "Q₈" => QuaternionGroup 2

private noncomputable def quaternionValue : Q₈ → ℍ
  | .a i => Quaternion.ofComplex (Complex.I ^ i.val)
  | .xa i => ⟨0, 0, 1, 0⟩ * Quaternion.ofComplex (Complex.I ^ i.val)

private theorem quaternionValue_mul (g h : Q₈) :
    quaternionValue (g * h) = quaternionValue g * quaternionValue h := by
  have hc : ∀ x : ZMod (2 * 2), x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  cases g <;> cases h <;>
    simp only [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
      QuaternionGroup.xa_mul_xa] <;>
    rename_i i j <;>
    rcases hc i with rfl | rfl | rfl | rfl <;>
    rcases hc j with rfl | rfl | rfl | rfl <;> ext <;>
    norm_num [quaternionValue, Quaternion.coe_ofComplex, Quaternion.coeComplex,
      ZMod.val_add, ZMod.val_sub, ZMod.neg_val', ZMod.val_natCast, ZMod.val_ofNat,
      ZMod.val_one_eq_one_mod, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]


/-- The standard homomorphism from Q₈ to the multiplicative monoid of Hamilton's quaternions,
sending `a 1` to i and `xa 0` to j. -/
noncomputable def quaternionGroupTwoToQuaternion : Q₈ →* ℍ where
  toFun := quaternionValue
  map_one' := by
    rw [QuaternionGroup.one_def]
    norm_num [quaternionValue, Quaternion.coe_ofComplex]
  map_mul' := quaternionValue_mul

/-- A rotation acts by the corresponding power of i. -/
@[simp]
theorem quaternionGroupTwoToQuaternion_a (i : ZMod (2 * 2)) :
    quaternionGroupTwoToQuaternion (QuaternionGroup.a i) =
      Quaternion.ofComplex (Complex.I ^ i.val) := (rfl)

/-- The second coset acts by j times the corresponding power of i. -/
@[simp]
theorem quaternionGroupTwoToQuaternion_xa (i : ZMod (2 * 2)) :
    quaternionGroupTwoToQuaternion (QuaternionGroup.xa i) =
      (⟨0, 0, 1, 0⟩ : ℍ) * Quaternion.ofComplex (Complex.I ^ i.val) := (rfl)

end TauCeti
