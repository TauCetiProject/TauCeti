/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Units.Hom

import Mathlib.Algebra.Group.Commute.Units

/-!
# Units in monoids

This file lifts units in the range of a local monoid homomorphism to units of its source, and
relates squares in a monoid to squares in its group of units. It also rewrites integer
powers of products of units as monomials with consecutive natural exponents. These identities
let bilateral sums over integer powers split into two sums over natural numbers, without
requiring a zero in the ambient monoid.

## Main results

* `TauCeti.mem_range_iff_exists_units_map_eq`: a unit lies in the range of a local monoid
  homomorphism exactly when it is the image of a unit under `Units.map`.
* `TauCeti.isSquare_units_val_iff`: a unit is a square exactly when its underlying monoid element
  is a square.
* `Units.val_mul_zpow_natCast_mul`: nonnegative product powers give consecutive monomials.
* `Units.val_mul_zpow_neg_natCast_succ_mul`: negative product powers give inverse monomials.
-/

public section

namespace TauCeti

/-- A unit in the range of a local monoid homomorphism comes from a unit of the source. -/
theorem mem_range_iff_exists_units_map_eq {M N F : Type*} [Monoid M] [Monoid N]
    [FunLike F M N] [MonoidHomClass F M N] (f : F) [IsLocalHom f] (u : Nˣ) :
    (u : N) ∈ Set.range f ↔ ∃ a : Mˣ, Units.map (f : M →* N) a = u := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(IsUnit.of_map f a (ha ▸ u.isUnit)).unit, Units.ext (by simp [ha])⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

/-- A unit is a square exactly when its underlying monoid element is a square. -/
@[simp]
theorem isSquare_units_val_iff {M : Type*} [Monoid M] {u : Mˣ} :
    IsSquare (u : M) ↔ IsSquare u := by
  constructor
  · rintro ⟨x, hx⟩
    have hxu : IsUnit x := isUnit_mul_self_iff.mp (hx ▸ u.isUnit)
    exact ⟨hxu.unit, Units.ext (by simpa using hx)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(v : M), by simp⟩

end TauCeti

namespace Units

/-- A nonnegative power of the product of two units gives consecutive monomial exponents
after multiplication by the first unit. -/
theorem val_mul_zpow_natCast_mul {M : Type*} [DivisionCommMonoid M] (u v : Mˣ) (n : ℕ) :
    ((u * v : Mˣ) : M) ^ (n : ℤ) * (u : M) = (u : M) ^ (n + 1) * (v : M) ^ n := by
  simp only [Units.val_mul, zpow_natCast, mul_pow, pow_succ]
  ac_rfl

/-- A strictly negative power of the product of two units gives the inverse monomial with
the consecutive exponents exchanged. -/
theorem val_mul_zpow_neg_natCast_succ_mul {M : Type*} [DivisionCommMonoid M]
    (u v : Mˣ) (n : ℕ) :
    ((u * v : Mˣ) : M) ^ (-((n : ℤ) + 1)) * (u : M) =
      ((v : M) ^ (n + 1) * (u : M) ^ n)⁻¹ := by
  have h : (u * v) ^ (-((n : ℤ) + 1)) * u = (v ^ (n + 1) * u ^ n)⁻¹ := by
    simp [zpow_neg, zpow_add, mul_pow, pow_succ, mul_assoc, mul_left_comm, mul_comm]
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val] using congrArg (fun w : Mˣ ↦ (w : M)) h

end Units
