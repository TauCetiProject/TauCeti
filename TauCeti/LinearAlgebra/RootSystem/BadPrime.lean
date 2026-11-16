/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
import Mathlib.Algebra.CharP.Basic

/-!
# Bad primes of Dynkin types

A prime number `p` is **bad** for an irreducible reduced crystallographic root system when it
divides a coefficient of the highest root expressed in the basis of simple roots (equivalently,
when some closed root subsystem has `p`-torsion in the quotient of root lattices):

* type `Aₙ` has no bad primes;
* types `Bₙ`, `Cₙ` and `Dₙ` have `2` as their only bad prime;
* types `E₆`, `E₇`, `F₄` and `G₂` have `2` and `3` as their bad primes;
* type `E₈` has `2`, `3` and `5` as its bad primes.

This file defines `TauCeti.DynkinType.IsBadPrime` by family constructor on `TauCeti.DynkinType`,
parallel to `TauCeti.DynkinType.IsSimplyLaced`. For every valid type (`TauCeti.DynkinType.Valid`)
this agrees with the primes dividing a coefficient of the highest root; outside the valid rank
ranges (such as `B₁`, `C₁` or `D₃`) it follows the family rule. Passing `ringChar k` treats
characteristic zero as good for every type (`TauCeti.DynkinType.not_isBadPrime_zero`), and over a
division semiring (in particular a field) inverting every bad prime is equivalent to `ringChar k`
not being bad (`TauCeti.DynkinType.forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar`).

## Main definitions

* `TauCeti.DynkinType.IsBadPrime`: the predicate that a natural number is a bad prime for a given
  Dynkin type.

## Main results

* `TauCeti.DynkinType.not_isBadPrime_zero`: `0` (characteristic zero) is never bad.
* `TauCeti.DynkinType.IsBadPrime.prime`: every bad number is prime.
* `TauCeti.DynkinType.not_isBadPrime_of_six_le`: no integer `p ≥ 6` (in particular, no prime
  `p ≥ 7`) is bad for any Dynkin type.
* `TauCeti.DynkinType.forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar`: over a division
  semiring, every bad prime of `t` is a unit if and only if `ringChar k` is not bad for `t`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, Plates I--IX.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, Section
  1.14, for the bad primes of irreducible root systems.
* T. A. Springer and R. Steinberg, *Conjugacy Classes*, in *Seminar on Algebraic Groups and
  Related Finite Groups*, Lecture Notes in Math. 131, Part E, Section I.4.
-/

public section

namespace TauCeti

namespace DynkinType

/-- A natural number `p` is a **bad prime** for a Dynkin type when it belongs to the
Springer--Steinberg list of bad primes for that type's family: none for `Aₙ`; `2` for `Bₙ`, `Cₙ`
and `Dₙ`; `2` and `3` for `E₆`, `E₇`, `F₄` and `G₂`; and `2`, `3` and `5` for `E₈`.

For every valid type (`TauCeti.DynkinType.Valid`), these are the primes dividing a coefficient of
the highest root in the basis of simple roots. In particular `0` (characteristic zero) is never
bad. -/
def IsBadPrime : DynkinType → ℕ → Prop
  | .A _, _ => False
  | .B _, p | .C _, p | .D _, p => p = 2
  | .E6, p | .E7, p | .F4, p | .G2, p => p = 2 ∨ p = 3
  | .E8, p => p = 2 ∨ p = 3 ∨ p = 5

instance : DecidableRel IsBadPrime := fun t p =>
  match t with
  | .A _ => inferInstanceAs (Decidable False)
  | .B _ | .C _ | .D _ => inferInstanceAs (Decidable (p = 2))
  | .E6 | .E7 | .F4 | .G2 => inferInstanceAs (Decidable (p = 2 ∨ p = 3))
  | .E8 => inferInstanceAs (Decidable (p = 2 ∨ p = 3 ∨ p = 5))

@[simp] theorem not_isBadPrime_A (n p : ℕ) : ¬ (A n).IsBadPrime p := not_false
@[simp] theorem isBadPrime_B_iff (n p : ℕ) : (B n).IsBadPrime p ↔ p = 2 := Iff.rfl
@[simp] theorem isBadPrime_C_iff (n p : ℕ) : (C n).IsBadPrime p ↔ p = 2 := Iff.rfl
@[simp] theorem isBadPrime_D_iff (n p : ℕ) : (D n).IsBadPrime p ↔ p = 2 := Iff.rfl
@[simp] theorem isBadPrime_E6_iff (p : ℕ) : E6.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E7_iff (p : ℕ) : E7.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_E8_iff (p : ℕ) : E8.IsBadPrime p ↔ p = 2 ∨ p = 3 ∨ p = 5 := Iff.rfl
@[simp] theorem isBadPrime_F4_iff (p : ℕ) : F4.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl
@[simp] theorem isBadPrime_G2_iff (p : ℕ) : G2.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl

/-- Characteristic zero is never bad for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ t.IsBadPrime 0 := by
  cases t <;> simp

/-- Every bad prime of a Dynkin type is a prime number (one of `2`, `3`, or `5`). -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) : p.Prime := by
  cases t with
  | A _ => exact False.elim h
  | B _ | C _ | D _ =>
    obtain rfl : p = 2 := h
    exact Nat.prime_two
  | E6 | E7 | F4 | G2 =>
    rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  | E8 =>
    rcases h with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five

/-- No integer at least `6` (in particular, no prime `p ≥ 7`) is bad for any Dynkin type. -/
theorem not_isBadPrime_of_six_le (t : DynkinType) {p : ℕ} (hp : 6 ≤ p) : ¬ t.IsBadPrime p := by
  cases t <;> simp <;> omega

/-- Over a division semiring (in particular a field), every bad prime of `t` is invertible if and
only if `ringChar k` is not a bad prime of `t`. -/
theorem forall_isBadPrime_isUnit_iff_not_isBadPrime_ringChar (k : Type*) [DivisionSemiring k]
    (t : DynkinType) :
    (∀ p, t.IsBadPrime p → IsUnit (p : k)) ↔ ¬ t.IsBadPrime (ringChar k) :=
  ⟨fun h hbad => isUnit_iff_ne_zero.mp (h _ hbad) ringChar.Nat.cast_ringChar,
   fun h _ hp => isUnit_iff_ne_zero.mpr <|
     CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k) hp.prime (fun h' => h (h' ▸ hp))⟩

end DynkinType

end TauCeti
