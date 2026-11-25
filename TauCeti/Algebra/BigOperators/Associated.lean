/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import TauCeti.Algebra.GroupWithZero.Associated
import Mathlib.RingTheory.Multiplicity

/-!
# Divisors and products of prime elements

In a commutative monoid with zero, if each member of a finite family of primes divides `n`, and no
member of the family divides another, then the product of the family divides `n`. Mathlib's
`Finset.prod_primes_dvd` states this for a finset of primes in a cancellative monoid with trivial
units, and `Multiset.prod_primes_dvd` for a multiset counted up to association; this file gives the
form for an indexed family.

In a cancellative commutative monoid with zero, Mathlib's `dvd_prime_pow` characterizes the
divisors of `p ^ n` for a prime element `p` without assuming unique factorization, and Tau Ceti's
`Prime.exists_eq_pow_mul_of_dvd_pow_mul` (in `TauCeti.Algebra.GroupWithZero.Associated`)
extends that characterization to divisors of `p ^ n * a`. This file extends that characterization
to finite products of prime elements and their powers.

## Main results

* `Finset.prod_primes_dvd_of_pairwise_not_dvd`: the product of a finite family of primes, each
  dividing `n` and none dividing another, divides `n`.
* `Finset.dvd_prod_pow_primes_iff` and `Finset.dvd_prod_primes_pow_iff`: `x` divides
  `∏ i ∈ s, p i ^ n i` (or `(∏ i ∈ s, p i) ^ k`) if and only if `x` is associated to
  `∏ i ∈ s, p i ^ m i` with bounded exponents.
* `Finset.eq_of_associated_prod_pow_primes`: for pairwise non-associated primes on `s`, if
  `∏ i ∈ s, p i ^ m i` and `∏ i ∈ s, p i ^ n i` are associated, then `m i = n i` for every `i ∈ s`.
-/

public section

assert_not_exists Field

namespace Finset

section CommMonoidWithZero

variable {ι M : Type*} [CommMonoidWithZero M]

/-- The product of a finite family of primes, each of which divides `n` and none of which divides
another, divides `n`. -/
theorem prod_primes_dvd_of_pairwise_not_dvd {s : Finset ι} {f : ι → M} {n : M}
    (hprime : ∀ i ∈ s, Prime (f i)) (hndvd : (s : Set ι).Pairwise fun i j ↦ ¬ f i ∣ f j)
    (hdvd : ∀ i ∈ s, f i ∣ n) : ∏ i ∈ s, f i ∣ n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨w, rfl⟩ := ih (fun i hi ↦ hprime i (mem_insert_of_mem hi))
      (hndvd.mono (by simp)) fun i hi ↦ hdvd i (mem_insert_of_mem hi)
    -- `f a` divides `(∏ i ∈ s, f i) * w` but none of the `f i`, so it divides `w`.
    have hpa := hprime a (mem_insert_self a s)
    have hnot : ¬ f a ∣ ∏ i ∈ s, f i := hpa.not_dvd_finsetProd fun i hi ↦
      hndvd (mem_insert_self a s) (mem_insert_of_mem hi) fun hai ↦ ha (hai ▸ hi)
    obtain ⟨v, rfl⟩ := (hpa.dvd_or_dvd (hdvd a (mem_insert_self a s))).resolve_left hnot
    exact ⟨v, by ac_rfl⟩

end CommMonoidWithZero

section IsCancelMulZero

variable {ι M₀ : Type*} [CommMonoidWithZero M₀] [IsCancelMulZero M₀]

/-- In a cancellative commutative monoid with zero, an element divides `∏ i ∈ s, p i ^ n i` for
prime elements `p i` (`i ∈ s`) if and only if it is associated to `∏ i ∈ s, p i ^ m i` for some
exponent function `m` bounded by `n` on `s`. -/
theorem dvd_prod_pow_primes_iff (s : Finset ι) {p : ι → M₀} (hp : ∀ i ∈ s, Prime (p i))
    (n : ι → ℕ) {x : M₀} :
    x ∣ ∏ i ∈ s, p i ^ n i ↔
      ∃ m : ι → ℕ, (∀ i ∈ s, m i ≤ n i) ∧ Associated x (∏ i ∈ s, p i ^ m i) := by
  classical
  refine ⟨fun hx ↦ ?_, fun ⟨m, hm, hxm⟩ ↦
    hxm.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow (p i) (hm i hi))⟩
  induction s using Finset.induction generalizing x with
  | empty =>
    rw [prod_empty, ← isUnit_iff_dvd_one, ← associated_one_iff_isUnit] at hx
    exact ⟨0, fun _ h ↦ absurd h (notMem_empty _), by simpa using hx⟩
  | insert a s ha ih =>
    have hpa : Prime (p a) := hp a (mem_insert_self a s)
    have hps : ∀ i ∈ s, Prime (p i) := fun i hi ↦ hp i (mem_insert_of_mem hi)
    rw [prod_insert ha] at hx
    obtain ⟨j, hj, y, hy, rfl⟩ := hpa.exists_eq_pow_mul_of_dvd_pow_mul hx
    obtain ⟨m, hm, hym⟩ := ih hps hy
    refine ⟨Function.update m a j, fun i hi ↦ ?_, ?_⟩
    · rcases mem_insert.mp hi with rfl | his
      · simpa using hj
      · simpa [ne_of_mem_of_not_mem his ha] using hm i his
    · rw [prod_insert ha, Function.update_self,
        prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]]
      exact hym.mul_left (p a ^ j)

/-- In a cancellative commutative monoid with zero, an element divides `(∏ i ∈ s, p i) ^ k` for
prime elements `p i` (`i ∈ s`) if and only if it is associated to `∏ i ∈ s, p i ^ m i` with
`m i ≤ k` for every `i ∈ s`. -/
theorem dvd_prod_primes_pow_iff (s : Finset ι) {p : ι → M₀} (hp : ∀ i ∈ s, Prime (p i))
    (k : ℕ) {x : M₀} :
    x ∣ (∏ i ∈ s, p i) ^ k ↔
      ∃ m : ι → ℕ, (∀ i ∈ s, m i ≤ k) ∧ Associated x (∏ i ∈ s, p i ^ m i) := by
  rw [← prod_pow]
  exact s.dvd_prod_pow_primes_iff hp fun _ ↦ k

/-- If `p i` (`i ∈ s`) are pairwise non-associated primes in a cancellative commutative monoid with
zero and `∏ i ∈ s, p i ^ m i` is associated to `∏ i ∈ s, p i ^ n i`, then `m i = n i` for every
`i ∈ s`. -/
theorem eq_of_associated_prod_pow_primes (s : Finset ι) {p : ι → M₀} (hp : ∀ i ∈ s, Prime (p i))
    (hs : (s : Set ι).Pairwise fun i j ↦ ¬Associated (p i) (p j)) {m n : ι → ℕ}
    (h : Associated (∏ i ∈ s, p i ^ m i) (∏ i ∈ s, p i ^ n i)) ⦃i : ι⦄ (hi : i ∈ s) :
    m i = n i := by
  have hpi : Prime (p i) := hp i hi
  have key := emultiplicity_eq_of_associated_right (a := p i) h
  have hzero (j : ι) (hj : j ∈ s) (hji : j ≠ i) (k : ℕ) : emultiplicity (p i) (p j ^ k) = 0 := by
    rw [emultiplicity_pow hpi, emultiplicity_eq_zero.mpr fun hdvd ↦
      hs hi hj hji.symm (hpi.associated_of_dvd (hp j hj) hdvd), mul_zero]
  have hmult (k : ι → ℕ) : emultiplicity (p i) (∏ j ∈ s, p j ^ k j) = k i := by
    rw [Finset.emultiplicity_prod hpi,
      Finset.sum_eq_single i (fun j hj hji ↦ hzero j hj hji _) (fun hni ↦ absurd hi hni),
      emultiplicity_pow_self_of_prime hpi]
  rw [hmult m, hmult n] at key
  exact Nat.cast_inj.mp key

end IsCancelMulZero

end Finset
