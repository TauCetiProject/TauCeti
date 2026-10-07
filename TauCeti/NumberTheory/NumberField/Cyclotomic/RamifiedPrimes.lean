/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import TauCeti.NumberTheory.Cyclotomic.OddLevel
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes

/-!
# The ramified primes of a rational cyclotomic field

Let `K` be an `n`-th cyclotomic field over `ℚ`. Mathlib computes the ramification index of every
rational prime in `K` (`IsCyclotomicExtension.Rat.ramificationIdx_eq`): writing
`n = p ^ (k + 1) * m` with `p ∤ m`, it is `p ^ k * (p - 1)`, and it is `1` when `p ∤ n`. This
file reads off which primes ramify.

The answer is *not* "the primes dividing `n`". The prime `2` divides `6`, but it is unramified in
`ℚ(ζ₆) = ℚ(ζ₃)`: its ramification index is `2 ^ 0 * (2 - 1) = 1`. Exactly this exception occurs:
a prime `p` ramifies in `K` iff `p ∣ n`, and, when `p = 2`, also `4 ∣ n`. The statement becomes
"the primes dividing the level" once the level is normalised to be `≢ 2 mod 4`, as the conductor
of `K` always is: when `n ≡ 2 mod 4` the field `K` is also an `n / 2`-th cyclotomic field,
because `n / 2` is odd (`IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two`).

## Main results

All results are in the namespace `IsCyclotomicExtension.Rat`.

* `mem_ramifiedPrimes_iff`: `p` ramifies in `K` iff `p` is a prime dividing `n` and `4 ∣ n` in
  case `p = 2`.
* `ramifiedPrimes_eq_primeFactors`: if `n ≢ 2 mod 4`, the ramified primes are the prime factors
  of `n`.
* `ramifiedPrimes_eq_primeFactors_div_two`: if `n ≡ 2 mod 4`, the ramified primes are the prime
  factors of `n / 2`.
* `ramifiedPrimes_eq_singleton_three`: the only prime ramified in `ℚ(ζ₆)` is `3`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §10.
-/

public section

open NumberField

namespace IsCyclotomicExtension.Rat

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]

section Level

variable [IsCyclotomicExtension {n} ℚ K]

/-- **The ramified primes of a cyclotomic field.** A natural number `p` is a prime ramified in an
`n`-th cyclotomic field over `ℚ` exactly when `p` is a prime dividing `n` and, if `p = 2`, then
`4 ∣ n`. -/
theorem mem_ramifiedPrimes_iff {p : ℕ} :
    p ∈ ramifiedPrimes K ↔ p.Prime ∧ p ∣ n ∧ (p = 2 → 4 ∣ n) := by
  by_cases hp : p.Prime
  swap
  · simp [hp]
  have : Fact p.Prime := ⟨hp⟩
  rw [NumberField.mem_ramifiedPrimes_iff, and_iff_right hp, and_iff_right hp,
    Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  obtain ⟨⟨P, _, _⟩⟩ := (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  obtain ⟨e, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.ne_one
  cases e with
  | zero =>
    rw [pow_zero, one_mul] at hnm
    subst hnm
    simp only [hpm, false_and, iff_false, not_not]
    intro Q _ _
    exact ramificationIdx_eq_of_not_dvd p K Q hpm
  | succ k =>
    have he (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})] :
        Ideal.ramificationIdx Q ℤ = p ^ k * (p - 1) :=
      ramificationIdx_eq n K Q hnm hpm
    have key : (∀ (Q : Ideal (𝓞 K)) [Q.IsPrime], Q.LiesOver (Ideal.span {(p : ℤ)}) →
        Ideal.ramificationIdx Q ℤ = 1) ↔ p ^ k * (p - 1) = 1 :=
      ⟨fun h ↦ he P ▸ h P ‹_›, fun h Q _ _ ↦ (he Q).trans h⟩
    have := hp.two_le
    subst hnm
    rw [key, mul_eq_one, Nat.pow_eq_one,
      and_iff_right (Dvd.dvd.mul_right (dvd_pow_self p k.succ_ne_zero) m)]
    constructor
    · rintro h rfl
      cases k with
      | zero => exact absurd ⟨Or.inr rfl, rfl⟩ h
      | succ j => exact ⟨2 ^ j * m, by ring⟩
    · rintro h ⟨hk, hp1⟩
      obtain rfl : p = 2 := by omega
      obtain rfl : k = 0 := by omega
      have := h rfl
      omega

/-- **Ramified primes at a level `≢ 2 mod 4`.** If `n ≢ 2 mod 4`, the primes ramified in an
`n`-th cyclotomic field over `ℚ` are exactly the prime factors of `n`. -/
theorem ramifiedPrimes_eq_primeFactors (hn : n % 4 ≠ 2) :
    ramifiedPrimes K = n.primeFactors := by
  ext p
  rw [mem_ramifiedPrimes_iff (n := n), Finset.mem_coe,
    Nat.mem_primeFactors_of_ne_zero (NeZero.ne n)]
  refine ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
  rintro rfl
  have := h.2
  omega

omit [NeZero n] in
/-- **Ramified primes at a level `≡ 2 mod 4`.** If `n ≡ 2 mod 4`, the primes ramified in an
`n`-th cyclotomic field over `ℚ` are exactly the prime factors of `n / 2`: the field is also an
`n / 2`-th cyclotomic field, and `2` is unramified in it. -/
theorem ramifiedPrimes_eq_primeFactors_div_two (hn : n % 4 = 2) :
    ramifiedPrimes K = (n / 2).primeFactors := by
  have : IsCyclotomicExtension {n / 2} ℚ K :=
    IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two hn two_ne_zero
  have : NeZero (n / 2) := ⟨by omega⟩
  exact ramifiedPrimes_eq_primeFactors (by omega)

end Level

/-- **`ℚ(ζ₆)` is unramified at `2`.** The only prime ramified in a sixth cyclotomic field over `ℚ`
is `3`, although `2` divides the level `6`. -/
theorem ramifiedPrimes_eq_singleton_three [IsCyclotomicExtension {6} ℚ K] :
    ramifiedPrimes K = {3} := by
  rw [ramifiedPrimes_eq_primeFactors_div_two (n := 6) rfl, Nat.prime_three.primeFactors,
    Finset.coe_singleton]

end IsCyclotomicExtension.Rat
