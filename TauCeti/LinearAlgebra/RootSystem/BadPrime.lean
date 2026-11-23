/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Basic
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
import Mathlib.Data.Nat.Prime.Basic

/-!
# Bad primes of Dynkin types

For an irreducible reduced crystallographic root system, a prime `p` is a **bad prime** if `p`
divides the coefficient of some simple root in the highest root: type `Aₙ` has no bad primes, `Bₙ`,
`Cₙ` and `Dₙ` have bad prime `2`, `E₆`, `E₇`, `F₄` and `G₂` have bad primes `2` and `3`, and `E₈`
has bad primes `2`, `3` and `5`.

Like `TauCeti.DynkinType.IsSimplyLaced` and `TauCeti.DynkinType.lacingNumber`, this file defines
`TauCeti.DynkinType.IsBadPrime` directly by family constructor on `TauCeti.DynkinType`; the rank
bounds on which the families name pairwise distinct irreducible root systems (`1 ≤ n` for `Aₙ`,
`2 ≤ n` for `Bₙ`, `3 ≤ n` for `Cₙ`, `4 ≤ n` for `Dₙ`) are carried by `TauCeti.DynkinType.Valid`.

## Main definitions

* `TauCeti.DynkinType.IsBadPrime`: the bad primes of a `TauCeti.DynkinType`.

## Main results

* `TauCeti.DynkinType.IsBadPrime.prime` and `TauCeti.DynkinType.IsBadPrime.le_five`: every bad
  prime is one of `2`, `3` or `5`.
* `TauCeti.DynkinType.not_isBadPrime_of_six_le`: no natural number `p ≥ 6` is a bad prime.
* `TauCeti.DynkinType.forall_isBadPrime_isUnit_iff`: over a division semiring `k`, every bad prime
  of `t` is invertible in `k` if and only if `ringChar k` is not a bad prime for `t`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, plates I--IX, for the highest-root
  coefficients in each family.
* T. A. Springer and R. Steinberg, *Conjugacy classes*, in *Seminar on Algebraic Groups and Related
  Finite Groups*, Lecture Notes in Math. 131, Springer (1970), Part E, §I.4, for bad primes of root
  systems.
-/

public section

namespace TauCeti.DynkinType

/-- The **bad primes** of a Dynkin type: for a valid type (`TauCeti.DynkinType.Valid`), these are
the primes dividing a simple-root coefficient of the highest root (`2` for `Bₙ`, `Cₙ` and `Dₙ`; `2`
and `3` for `E₆`, `E₇`, `F₄` and `G₂`; `2`, `3` and `5` for `E₈`; and none for `Aₙ`). Like
`TauCeti.DynkinType.IsSimplyLaced` and `TauCeti.DynkinType.lacingNumber`, the predicate is defined
uniformly by family constructor, with the irreducibility rank bounds (`1 ≤ n` for `Aₙ`, `2 ≤ n` for
`Bₙ`, `3 ≤ n` for `Cₙ`, `4 ≤ n` for `Dₙ`) carried separately by `TauCeti.DynkinType.Valid`.
Characteristic zero (`p = 0`) is never bad. -/
def IsBadPrime : DynkinType → ℕ → Prop
  | .A _, _ => False
  | .B _, p | .C _, p | .D _, p => p = 2
  | .E6, p | .E7, p | .F4, p | .G2, p => p = 2 ∨ p = 3
  | .E8, p => p = 2 ∨ p = 3 ∨ p = 5

instance instDecidableIsBadPrime (t : DynkinType) (p : ℕ) : Decidable (t.IsBadPrime p) :=
  match t with
  | .A _ => inferInstanceAs (Decidable False)
  | .B _ | .C _ | .D _ => inferInstanceAs (Decidable (p = 2))
  | .E6 | .E7 | .F4 | .G2 => inferInstanceAs (Decidable (p = 2 ∨ p = 3))
  | .E8 => inferInstanceAs (Decidable (p = 2 ∨ p = 3 ∨ p = 5))

/-- Type `Aₙ` has no bad primes. -/
@[simp]
theorem not_isBadPrime_A (n p : ℕ) : ¬ (A n).IsBadPrime p := id

/-- `2` is the unique bad prime for type `Bₙ`. -/
@[simp]
theorem isBadPrime_B_iff {n p : ℕ} : (B n).IsBadPrime p ↔ p = 2 := Iff.rfl

/-- `2` is the unique bad prime for type `Cₙ`. -/
@[simp]
theorem isBadPrime_C_iff {n p : ℕ} : (C n).IsBadPrime p ↔ p = 2 := Iff.rfl

/-- `2` is the unique bad prime for type `Dₙ`. -/
@[simp]
theorem isBadPrime_D_iff {n p : ℕ} : (D n).IsBadPrime p ↔ p = 2 := Iff.rfl

/-- `2` and `3` are the bad primes for `E₆`. -/
@[simp]
theorem isBadPrime_E6_iff {p : ℕ} : E6.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl

/-- `2` and `3` are the bad primes for `E₇`. -/
@[simp]
theorem isBadPrime_E7_iff {p : ℕ} : E7.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl

/-- `2`, `3` and `5` are the bad primes for `E₈`. -/
@[simp]
theorem isBadPrime_E8_iff {p : ℕ} : E8.IsBadPrime p ↔ p = 2 ∨ p = 3 ∨ p = 5 := Iff.rfl

/-- `2` and `3` are the bad primes for `F₄`. -/
@[simp]
theorem isBadPrime_F4_iff {p : ℕ} : F4.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl

/-- `2` and `3` are the bad primes for `G₂`. -/
@[simp]
theorem isBadPrime_G2_iff {p : ℕ} : G2.IsBadPrime p ↔ p = 2 ∨ p = 3 := Iff.rfl

/-- Characteristic zero (`p = 0`) is never bad for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_zero (t : DynkinType) : ¬ t.IsBadPrime 0 := by
  cases t <;> simp

/-- `1` is never a bad prime for any Dynkin type. -/
@[simp]
theorem not_isBadPrime_one (t : DynkinType) : ¬ t.IsBadPrime 1 := by
  cases t <;> simp

/-- Every number satisfying `IsBadPrime` is prime (`2`, `3` or `5`). -/
theorem IsBadPrime.prime {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) : Nat.Prime p := by
  cases t <;> simp only [not_isBadPrime_A, isBadPrime_B_iff, isBadPrime_C_iff, isBadPrime_D_iff,
    isBadPrime_E6_iff, isBadPrime_E7_iff, isBadPrime_E8_iff, isBadPrime_F4_iff,
    isBadPrime_G2_iff] at h
  · exact h ▸ Nat.prime_two
  · exact h ▸ Nat.prime_two
  · exact h ▸ Nat.prime_two
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · rcases h with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · rcases h with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three

/-- Every bad prime of a Dynkin type is at most `5`. -/
theorem IsBadPrime.le_five {t : DynkinType} {p : ℕ} (h : t.IsBadPrime p) : p ≤ 5 := by
  cases t <;> simp_all <;> omega

/-- No natural number `p ≥ 6` is a bad prime for any Dynkin type. -/
theorem not_isBadPrime_of_six_le (t : DynkinType) {p : ℕ} (hp : 6 ≤ p) : ¬ t.IsBadPrime p :=
  fun h => by have := h.le_five; omega

/-- Over a division semiring `k`, every bad prime of `t` is invertible in `k` if and only if
`ringChar k` is not a bad prime for `t`. -/
theorem forall_isBadPrime_isUnit_iff (t : DynkinType) (k : Type*) [DivisionSemiring k] :
    (∀ p, t.IsBadPrime p → IsUnit (p : k)) ↔ ¬ t.IsBadPrime (ringChar k) :=
  ⟨fun h hp => (h _ hp).ne_zero ringChar.Nat.cast_ringChar,
   fun h _ hp => isUnit_iff_ne_zero.mpr <|
     CharP.cast_ne_zero_of_ne_of_prime k hp.prime fun heq => h (heq ▸ hp)⟩

end TauCeti.DynkinType
