/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Finset.Order

/-!
# Linear independence of integer powers

For a linear automorphism `e` of a module and a vector `v`, the vectors `(e ^ n) v` for
integer `n` are linearly independent exactly when those for natural `n` are. Applying a
suitable power of `e` to a finite relation shifts every exponent into the natural numbers.

Specializing to right multiplication by a unit of a semiring shows that the integer powers
of a unit are linearly independent exactly when its natural powers are. Scalars need only
associate with multiplication; neither the ambient semiring nor the scalars need be
commutative. This permits left coefficients in skew Laurent expansions.
-/

public section

namespace LinearEquiv

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The integer iterates of a linear automorphism on a vector are linearly independent if and
only if its natural iterates are. -/
theorem linearIndependent_zpow_iff (e : M ≃ₗ[R] M) (v : M) :
    LinearIndependent R (fun n : ℤ ↦ (e ^ n) v) ↔
      LinearIndependent R (fun n : ℕ ↦ (e ^ n) v) := by
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
    convert (h.comp _ hinj).map_injOn (e ^ m).toLinearMap (e ^ m).injective.injOn using 1
    ext i
    simp only [Function.comp_apply, coe_coe, ← zpow_natCast, Int.toNat_of_nonneg (hnonneg i)]
    rw [← mul_apply_eq_comp, ← zpow_add, add_sub_cancel]

end LinearEquiv

namespace Units

variable {R B : Type*} [Semiring R] [Semiring B] [Module R B]
  [IsScalarTower R B B]

/-- Integer powers of a unit are linearly independent if and only if its natural powers are.
The scalar action need not be central. This specializes
`LinearEquiv.linearIndependent_zpow_iff` to right multiplication by the unit. -/
theorem linearIndependent_zpow_iff (x : Bˣ) :
    LinearIndependent R (fun n : ℤ ↦ (↑(x ^ n) : B)) ↔
      LinearIndependent R (fun n : ℕ ↦ (↑(x ^ n) : B)) := by
  have h (n : ℤ) (b : B) : (x.mulRightLinearEquiv R ^ n) b = b * ↑(x ^ n) := by
    induction n using Int.induction_on generalizing b with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, mul_apply_eq_comp, ih, mulRightLinearEquiv_apply, mul_assoc,
        ← Units.val_mul, ← zpow_one_add, add_comm]
    | pred n ih =>
      rw [zpow_sub_one, mul_apply_eq_comp, ih, LinearEquiv.coe_inv,
        symm_mulRightLinearEquiv_apply, mul_assoc, ← Units.val_mul, ← zpow_neg_one, ← zpow_add,
        neg_add_eq_sub]
  simpa only [← zpow_natCast, h, one_mul] using
    (x.mulRightLinearEquiv R).linearIndependent_zpow_iff 1

end Units
