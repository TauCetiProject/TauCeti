/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic

/-!
# Local rings that are not commutative

This file records basic facts about possibly noncommutative local rings. Their only idempotents
are `0` and `1`, and locality transfers along a ring equivalence; these facts apply to endomorphism
rings in the Krull-Schmidt theorem. In characteristic two the idempotent criterion identifies the
zeros of the Artin–Schreier map `t ↦ t² + t`, without a finiteness assumption.

## Main results

* `TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`: an idempotent of a local ring is `0`
  or `1`.
* `TauCeti.IsLocalRing.isDedekindFiniteMonoid`: a local ring is Dedekind-finite.
* `TauCeti.IsLocalRing.sq_add_self_eq_zero_iff`: in characteristic two, `t² + t = 0` exactly
  when `t = 0` or `t = 1`.
* `TauCeti.IsLocalRing.of_ringEquiv`: a semiring equivalent to a local semiring is local.
* `TauCeti.IsLocalRing.isUnit_natCast_of_not_dvd`: if the prime `p` is not a unit, every natural
  number prime to `p` is a unit.
-/

public section

namespace TauCeti

/-- An idempotent of a local ring is `0` or `1`. Mathlib's
`IsLocalRing.isUnit_or_isUnit_one_sub_self` is stated over a commutative ring, so the splitting of
`1 = a + (1 - a)` is taken here from `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`, which holds over
any semiring. -/
theorem IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem {R : Type*} [Ring R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  have hsum : IsUnit (a + (1 - a)) := by simp
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
  · exact Or.inr (hu.mul_left_cancel (by rw [ha, mul_one]))
  · refine Or.inl ?_
    have hidem : IsIdempotentElem (1 - a) := IsIdempotentElem.one_sub ha
    have hone : (1 : R) - a = 1 := hu.mul_left_cancel (by rw [hidem, mul_one])
    exact sub_eq_self.mp hone

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
    rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem he with h0 | h1
    · have hp0 : p = 0 := by
        calc
          p = (p * q) * p := by rw [hpq, one_mul]
          _ = p * (q * p) := by rw [mul_assoc]
          _ = 0 := by rw [h0, mul_zero]
      simpa only [hp0, mul_zero, zero_mul] using hpq
    · exact h1

/-- Over a local ring of characteristic two, the zeros of `t ↦ t² + t` are `0` and `1`. -/
@[simp]
theorem IsLocalRing.sq_add_self_eq_zero_iff {R : Type*} [Ring R] [IsLocalRing R] [CharP R 2]
    (t : R) : t ^ 2 + t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [CharTwo.add_eq_zero, pow_two]
  constructor
  · exact IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
  · rintro (rfl | rfl) <;> simp

/-- A semiring equivalent to a local semiring is local. Mathlib's `RingEquiv.isLocalRing` asks the
source to be commutative, since it goes through `IsLocalRing.of_surjective`; transporting the
defining condition on a pair of elements summing to a unit needs no commutativity. -/
theorem IsLocalRing.of_ringEquiv {R S : Type*} [Semiring R] [Semiring S] [IsLocalRing R]
    (e : R ≃+* S) : IsLocalRing S := by
  have := e.symm.toEquiv.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun a b hab ↦ ?_
  have hsum : IsUnit (e.symm a + e.symm b) := by simpa using hab.map e.symm
  exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).imp (fun hu ↦ by simpa using hu.map e)
    fun hu ↦ by simpa using hu.map e

/-- In a local ring in which the prime `p` is not a unit, every natural number prime to `p` is a
unit. -/
theorem IsLocalRing.isUnit_natCast_of_not_dvd {R : Type*} [Ring R] [IsLocalRing R] {p : ℕ}
    (hp : p.Prime) (hpR : ¬IsUnit (p : R)) {m : ℕ} (hpm : ¬p ∣ m) : IsUnit (m : R) := by
  have hab := Nat.gcd_eq_gcd_ab m p
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)),
    Nat.cast_one] at hab
  have hab' : (m : R) * (m.gcdA p : R) + p * (m.gcdB p : R) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → R) hab.symm
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab' with h | h
  · exact (((Nat.cast_commute m _).isUnit_mul_iff).mp h).1
  · exact absurd (((Nat.cast_commute p _).isUnit_mul_iff).mp h).1 hpR

end TauCeti
