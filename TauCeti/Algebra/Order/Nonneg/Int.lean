/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Nonnegative integers

This file identifies nonnegative integers with natural numbers as ordered additive monoids.
The forward map is `Int.toNat`, and the inverse map is the natural-number coercion into the
nonnegative subtype.
-/

public section

namespace Nonneg

/-- Nonnegative integers are order-additively equivalent to natural numbers via `Int.toNat`. -/
def intOrderAddMonoidIsoNat : Nonneg ℤ ≃+o ℕ :=
  let e : ℕ ≃+o Nonneg ℤ :=
    {
      toFun := fun n ↦ ⟨(n : ℤ), Int.natCast_nonneg n⟩
      invFun := fun n ↦ n.val.toNat
      left_inv := fun n ↦ by simp
      right_inv := fun n ↦ Subtype.ext (Int.toNat_of_nonneg n.property)
      map_add' := fun _ _ ↦ rfl
      map_le_map_iff' := Int.ofNat_le
    }
  e.symm

@[simp]
theorem intOrderAddMonoidIsoNat_apply (n : Nonneg ℤ) :
    intOrderAddMonoidIsoNat n = n.val.toNat :=
  (rfl)

@[simp]
theorem intOrderAddMonoidIsoNat_symm_apply (n : ℕ) :
    intOrderAddMonoidIsoNat.symm n = (Nat.cast n : Nonneg ℤ) :=
  (rfl)

end Nonneg
