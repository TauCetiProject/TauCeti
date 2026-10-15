/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Data.Int.GCD

/-!
# Basic facts about local rings

This file records basic facts about possibly noncommutative local rings. Their only idempotents
are `0` and `1`; this fact applies to endomorphism rings in the Krull-Schmidt theorem. In
characteristic two the idempotent criterion identifies the zeros of the Artin–Schreier map
`t ↦ t² + t`, without a finiteness assumption.

## Main results

* `IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing`: an idempotent of a local ring is `0`
  or `1`.
* `TauCeti.IsLocalRing.isDedekindFiniteMonoid`: a local ring is Dedekind-finite.
* `TauCeti.IsLocalRing.sq_add_self_eq_zero_iff`: in characteristic two, `t² + t = 0` exactly
  when `t = 0` or `t = 1`.
* `Nat.Coprime.isUnit_natCast`: if a natural number is not a unit, every coprime natural
  number is a unit.
* `IsCoprime.isUnit_or_isUnit`: of two coprime elements of a commutative local semiring, one is a
  unit.
-/

public section

/-- An idempotent of a possibly noncommutative local ring is `0` or `1`. -/
theorem IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing {R : Type*} [Ring R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  -- One of `a` and `1 - a` is a unit, and an idempotent unit is `1`.
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha)
  · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha.one_sub))

namespace TauCeti

/-- A local ring is Dedekind-finite: a left inverse is also a right inverse. -/
instance IsLocalRing.isDedekindFiniteMonoid {R : Type*} [Ring R] [IsLocalRing R] :
    IsDedekindFiniteMonoid R where
  mul_eq_one_symm := by
    intro p q hpq
    have he : IsIdempotentElem (q * p) := by
      rw [IsIdempotentElem]
      calc
        (q * p) * (q * p) = q * (p * q) * p := by simp only [mul_assoc]
        _ = q * p := by rw [hpq, mul_one]
    rcases IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing he with h0 | h1
    · exfalso
      exact one_ne_zero (by
        simpa only [mul_assoc, hpq, mul_one, mul_zero, zero_mul] using
          congrArg (fun a ↦ p * a * q) h0)
    · exact h1

/-- Over a local ring of characteristic two, the zeros of `t ↦ t² + t` are `0` and `1`. -/
@[simp]
theorem IsLocalRing.sq_add_self_eq_zero_iff {R : Type*} [Ring R] [IsLocalRing R] [CharP R 2]
    (t : R) : t ^ 2 + t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [CharTwo.add_eq_zero, pow_two]
  constructor
  · exact IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing
  · rintro (rfl | rfl) <;> simp

end TauCeti

/-- Of two coprime elements of a commutative local semiring, one is a unit: a relation
`u * a + v * b = 1` makes one of the two summands a unit. -/
theorem IsCoprime.isUnit_or_isUnit {R : Type*} [CommSemiring R] [IsLocalRing R] {a b : R}
    (h : IsCoprime a b) : IsUnit a ∨ IsUnit b := by
  obtain ⟨u, v, huv⟩ := h
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one huv).imp isUnit_of_mul_isUnit_right
    isUnit_of_mul_isUnit_right

/-- In a possibly noncommutative local ring, a natural number coprime to a nonunit natural
number is a unit. -/
theorem Nat.Coprime.isUnit_natCast {R : Type*} [Ring R] [IsLocalRing R] {m n : ℕ}
    (h : m.Coprime n) (hn : ¬IsUnit (n : R)) : IsUnit (m : R) := by
  have hab := Nat.gcd_eq_gcd_ab m n
  rw [h.gcd_eq_one, Nat.cast_one] at hab
  have hab' : (m : R) * (m.gcdA n : R) + n * (m.gcdB n : R) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → R) hab.symm
  exact ((IsLocalRing.isUnit_or_isUnit_of_add_one hab').imp isUnit_of_mul_isUnit_left
    isUnit_of_mul_isUnit_left).resolve_right hn
