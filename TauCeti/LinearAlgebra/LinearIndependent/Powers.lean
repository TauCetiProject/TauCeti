/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Finset.Order

/-!
# Linear independence of integer powers

The integer powers of a unit are linearly independent exactly when its natural powers are.
Multiplying a finite relation on the right by a suitable power shifts every exponent into
the natural numbers. Scalars need only associate with multiplication; neither the ambient
semiring nor the scalars need be commutative. This permits left coefficients in skew
Laurent expansions.
-/

public section

namespace Units

variable {R B : Type*} [Semiring R] [Semiring B] [Module R B]
  [IsScalarTower R B B]

/-- Integer powers of a unit are linearly independent if and only if its natural powers are.
The scalar action need not be central. -/
theorem linearIndependent_zpow_iff (x : Bˣ) :
    LinearIndependent R (fun n : ℤ ↦ (↑(x ^ n) : B)) ↔
      LinearIndependent R (fun n : ℕ ↦ (↑(x ^ n) : B)) := by
  constructor
  · intro h
    simpa only [Function.comp_def, zpow_natCast] using
      h.comp (fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective
  · intro h
    classical
    apply linearIndependent_iff_finset_linearIndependent.mpr
    intro s
    obtain ⟨m, hm⟩ := s.exists_ge
    have hnonneg (i : s) : 0 ≤ (i : ℤ) - m := sub_nonneg.mpr (hm i i.property)
    have hinj : Function.Injective (fun i : s ↦ ((i : ℤ) - m).toNat) := by
      intro i j hij
      have := congrArg (fun n : ℕ ↦ (n : ℤ)) hij
      simp only [Int.toNat_of_nonneg (hnonneg _)] at this
      exact Subtype.ext (by omega)
    let f : B →ₗ[R] B :=
      { toFun := fun b ↦ b * (x ^ m : Bˣ)
        map_add' := fun a b ↦ add_mul a b _
        map_smul' := fun r b ↦ smul_mul_assoc r b _ }
    have hf : Function.Injective f := (x ^ m).isUnit.mul_left_injective
    convert (h.comp _ hinj).map_injOn f hf.injOn using 1
    ext i
    simp only [Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      ← Units.val_mul, ← zpow_natCast, ← zpow_add, Int.toNat_of_nonneg (hnonneg i),
      sub_add_cancel, f]

end Units
