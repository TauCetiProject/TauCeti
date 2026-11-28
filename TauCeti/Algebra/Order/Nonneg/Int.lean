/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Nonnegative integers

This file identifies nonnegative integers with natural numbers as ordered additive monoids.
The forward map is `Int.toNat`, and the inverse map is the natural-number coercion into the
nonnegative subtype.
-/

public section

namespace TauCeti

/-- Nonnegative integers are order-additively equivalent to natural numbers via `Int.toNat`. -/
def nonnegIntOrderAddMonoidIsoNat : Nonneg ℤ ≃+o ℕ :=
  let e : ℕ ≃+o Nonneg ℤ :=
    {
      toFun := fun n ↦ (n : Nonneg ℤ)
      invFun := fun n ↦ n.val.toNat
      left_inv := fun n ↦ by simp
      right_inv := fun n ↦ by
        ext
        simp [Int.toNat_of_nonneg n.property]
      map_add' := fun a b ↦ Nat.cast_add a b
      map_le_map_iff' := fun {a b} ↦ by
        rw [← Subtype.coe_le_coe, Nonneg.coe_natCast, Nonneg.coe_natCast, Nat.cast_le]
    }
  e.symm

end TauCeti

namespace Nonneg

theorem nonnegIntOrderAddMonoidIsoNat_apply (n : Nonneg ℤ) :
    TauCeti.nonnegIntOrderAddMonoidIsoNat n = n.val.toNat :=
  by
    rw [TauCeti.nonnegIntOrderAddMonoidIsoNat, ← OrderAddMonoidIso.invFun_eq_symm]

end Nonneg

namespace Nat

theorem nonnegIntOrderAddMonoidIsoNat_symm_apply (n : ℕ) :
    TauCeti.nonnegIntOrderAddMonoidIsoNat.symm n = (Nat.cast n : Nonneg ℤ) :=
  by
    rw [TauCeti.nonnegIntOrderAddMonoidIsoNat, OrderAddMonoidIso.symm_symm]
    rfl

end Nat
