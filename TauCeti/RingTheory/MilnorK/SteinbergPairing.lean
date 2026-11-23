/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Units

/-!
# Steinberg pairings on commutative semirings and rings

This file defines `TauCeti.IsSteinbergPairing` and proves the basic identities that hold for any
commutative semiring or commutative ring. Field-specific identities (such as skew-symmetry and
finite-field vanishing) are in `TauCeti.FieldTheory.MilnorK.SteinbergPairing`.

## Main definitions

* `TauCeti.IsSteinbergPairing`: predicate expressing that a map `c : Rˣ → Rˣ → A` is biadditive
  (multiplicative in each unit argument) and satisfies the Steinberg relation `c a b = 0` whenever
  `(a : R) + b = 1`.

## Main results

* `TauCeti.IsSteinbergPairing.map_one_left`, `TauCeti.IsSteinbergPairing.map_one_right`:
  vanishing when either argument is `1`.
* `TauCeti.IsSteinbergPairing.map_inv_left`, `TauCeti.IsSteinbergPairing.map_inv_right`:
  inverting a unit negates the pairing.
* `TauCeti.IsSteinbergPairing.map_pow_left`, `TauCeti.IsSteinbergPairing.map_pow_right`,
  `TauCeti.IsSteinbergPairing.map_zpow_left`, `TauCeti.IsSteinbergPairing.map_zpow_right`:
  scaling under natural and integer powers.
* `TauCeti.IsSteinbergPairing.comp_addMonoidHom`, `TauCeti.IsSteinbergPairing.comp_ringHom`:
  pushforward along additive homomorphisms and pullback along ring homomorphisms.
* `TauCeti.IsSteinbergPairing.map_neg_one_right_add_self_eq_zero`:
  `c a (-1) + c a (-1) = 0` over any commutative ring.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §III.6.1.
-/

public section

namespace TauCeti

/-- A map `c : Rˣ → Rˣ → A` from pairs of units of a commutative semiring `R` to an additive
commutative monoid `A` is a *Steinberg pairing* if it is bimultiplicative (sending multiplication
in each unit slot to addition in `A`) and satisfies the Steinberg relation `c a b = 0` whenever
`(a : R) + b = 1`. -/
structure IsSteinbergPairing {R : Type*} [CommSemiring R] {A : Type*} [AddCommMonoid A]
    (c : Rˣ → Rˣ → A) : Prop where
  /-- Multiplicativity in the left unit argument. -/
  map_mul_left : ∀ a₁ a₂ b : Rˣ, c (a₁ * a₂) b = c a₁ b + c a₂ b
  /-- Multiplicativity in the right unit argument. -/
  map_mul_right : ∀ a b₁ b₂ : Rˣ, c a (b₁ * b₂) = c a b₁ + c a b₂
  /-- The Steinberg relation: complementary units pairing to `0`. -/
  steinberg : ∀ {a b : Rˣ}, (a : R) + b = 1 → c a b = 0

namespace IsSteinbergPairing

section CommSemiring

variable {R : Type*} [CommSemiring R] {A : Type*} [AddCommGroup A] {c : Rˣ → Rˣ → A}

/-- A Steinberg pairing vanishes when the left argument is `1`. -/
theorem map_one_left (hc : IsSteinbergPairing c) (b : Rˣ) : c 1 b = 0 := by
  simpa using (hc.map_mul_left 1 1 b).symm

/-- A Steinberg pairing vanishes when the right argument is `1`. -/
theorem map_one_right (hc : IsSteinbergPairing c) (a : Rˣ) : c a 1 = 0 := by
  simpa using (hc.map_mul_right a 1 1).symm

/-- Inverting the left unit negates the pairing value. -/
theorem map_inv_left (hc : IsSteinbergPairing c) (a b : Rˣ) : c a⁻¹ b = -c a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← hc.map_mul_left, inv_mul_cancel, hc.map_one_left]

/-- Inverting the right unit negates the pairing value. -/
theorem map_inv_right (hc : IsSteinbergPairing c) (a b : Rˣ) : c a b⁻¹ = -c a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← hc.map_mul_right, inv_mul_cancel, hc.map_one_right]

/-- Raising the left unit to a natural power scales the pairing value. -/
theorem map_pow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) :
    c (a ^ n) b = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_left]
  | succ n ih => rw [pow_succ, hc.map_mul_left, ih, succ_nsmul]

/-- Raising the right unit to a natural power scales the pairing value. -/
theorem map_pow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) :
    c a (b ^ n) = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_right]
  | succ n ih => rw [pow_succ, hc.map_mul_right, ih, succ_nsmul]

/-- Raising the left unit to an integer power scales the pairing value. -/
theorem map_zpow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c (a ^ n) b = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_left a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_left, hc.map_pow_left, negSucc_zsmul]

/-- Raising the right unit to an integer power scales the pairing value. -/
theorem map_zpow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c a (b ^ n) = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_right a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_right, hc.map_pow_right, negSucc_zsmul]

/-- Post-composing a Steinberg pairing with an additive homomorphism gives a Steinberg pairing. -/
theorem comp_addMonoidHom {B : Type*} [AddCommMonoid B] {c : Rˣ → Rˣ → B}
    (hc : IsSteinbergPairing c) {C : Type*} [AddCommMonoid C] (f : B →+ C) :
    IsSteinbergPairing (fun a b ↦ f (c a b)) where
  map_mul_left a₁ a₂ b := by rw [hc.map_mul_left, map_add]
  map_mul_right a b₁ b₂ := by rw [hc.map_mul_right, map_add]
  steinberg hab := by rw [hc.steinberg hab, map_zero]

/-- Pulling back a Steinberg pairing along a ring homomorphism gives a Steinberg pairing. -/
theorem comp_ringHom {S : Type*} [CommSemiring S] {B : Type*} [AddCommMonoid B]
    {c : Sˣ → Sˣ → B} (hc : IsSteinbergPairing c) (f : R →+* S) :
    IsSteinbergPairing (fun a b : Rˣ ↦ c (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b))
    where
  map_mul_left a₁ a₂ b := by rw [map_mul, hc.map_mul_left]
  map_mul_right a b₁ b₂ := by rw [map_mul, hc.map_mul_right]
  steinberg {a b} hab := hc.steinberg (by
    rw [Units.coe_map, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      ← map_add, hab, map_one])

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {A : Type*} [AddCommGroup A] {c : Rˣ → Rˣ → A}

/-- For any commutative ring and Steinberg pairing, `c a (-1) + c a (-1) = 0`. -/
theorem map_neg_one_right_add_self_eq_zero (hc : IsSteinbergPairing c) (a : Rˣ) :
    c a (-1 : Rˣ) + c a (-1 : Rˣ) = 0 := by
  rw [← hc.map_mul_right, show (-1 : Rˣ) * (-1 : Rˣ) = 1 by ext; simp, hc.map_one_right]

end CommRing

end IsSteinbergPairing

end TauCeti
