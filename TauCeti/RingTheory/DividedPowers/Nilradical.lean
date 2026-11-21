/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas

import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Nilradical criterion and factorial annihilation for divided power ideals

This file develops a factorial-annihilation nilpotence criterion
(`DividedPowers.pow_eq_zero_of_factorial_eq_zero`, assuming `(n ! : R) = 0`, related to
`DividedPowers.nilpotent_of_mem_dpIdeal`, which assumes `n ≠ 0` and `∀ {y}, y ∈ I → n • y = 0`)
and the nilradical criterion: if `m ≠ 0` is a natural number that is nilpotent modulo `I` (or has
some power in `I`), then `I ≤ nilradical R` if and only if `(m : R)` is nilpotent in `R`. No
primality assumption on `m` is required.

## Main results

* `DividedPowers.pow_eq_zero_of_factorial_eq_zero`: if `(n ! : R) = 0`, then `x ^ n = 0` for
  every `x ∈ I`.
* `DividedPowers.pow_eq_zero_of_natCast_pow_eq_zero`: if `m ≠ 0` and `(m : R) ^ k = 0`, then
  `x ^ (m * k) = 0` for every `x ∈ I`.
* `DividedPowers.le_nilradical_of_isNilpotent_natCast`: if `m ≠ 0` and `(m : R)` is nilpotent,
  then `I ≤ nilradical R`.
* `DividedPowers.le_nilradical_iff_isNilpotent_natCast` and
  `DividedPowers.le_nilradical_iff_isNilpotent_of_quotient`: if `m ≠ 0` has a power in `I` (or is
  nilpotent in `R ⧸ I`), then `I ≤ nilradical R ↔ IsNilpotent (m : R)`.

## References

* Mathlib's `DividedPowers` formalization by A. Chambert-Loir and M. I. de Frutos-Fernández.
* [Stacks Project, Section 23.2 (Tag 07GR)](https://stacks.math.columbia.edu/tag/07GR),
  Lemma 23.2.6.
-/

public section

namespace DividedPowers

section NilradicalCriterion

variable {R : Type*} [CommSemiring R] {I : Ideal R}

/-- Factorial-annihilation nilpotence criterion: if `(n.factorial : R) = 0`, then `x ^ n = 0` for
every `x ∈ I`. This holds for all `n : ℕ` (including `n = 0`, where `R` is a subsingleton) and is
a related criterion to `DividedPowers.nilpotent_of_mem_dpIdeal` (which instead assumes `n ≠ 0` and
`∀ {y}, y ∈ I → n • y = 0`). -/
theorem pow_eq_zero_of_factorial_eq_zero (hI : DividedPowers I) {n : ℕ}
    (hn : (n.factorial : R) = 0) {x : R} (hx : x ∈ I) : x ^ n = 0 := by
  rw [← hI.factorial_mul_dpow_eq_pow hx, hn, zero_mul]

/-- If `m ≠ 0` and `(m : R) ^ k = 0`, then `x ^ (m * k) = 0` for every `x ∈ I`. -/
theorem pow_eq_zero_of_natCast_pow_eq_zero (hI : DividedPowers I) {m k : ℕ} (hm : m ≠ 0)
    (hk : (m : R) ^ k = 0) {x : R} (hx : x ∈ I) : x ^ (m * k) = 0 := by
  have hdvd : m ^ k ∣ (m * k).factorial := by
    calc m ^ k ∣ m.factorial ^ k :=
          pow_dvd_pow_of_dvd (Nat.dvd_factorial (Nat.pos_of_ne_zero hm) le_rfl) k
      _ = ∏ _ ∈ Finset.range k, m.factorial := by simp
      _ ∣ (∑ _ ∈ Finset.range k, m).factorial := Nat.prod_factorial_dvd_factorial_sum ..
      _ = (m * k).factorial := by simp [mul_comm]
  obtain ⟨c, hc⟩ := hdvd
  refine hI.pow_eq_zero_of_factorial_eq_zero ?_ hx
  rw [hc, Nat.cast_mul, Nat.cast_pow, hk, zero_mul]

/-- If a nonzero natural number `m` is nilpotent in `R`, then every divided power ideal of `R` is
contained in the nilradical of `R`. -/
theorem le_nilradical_of_isNilpotent_natCast (hI : DividedPowers I) {m : ℕ} (hm : m ≠ 0)
    (h : _root_.IsNilpotent (m : R)) : I ≤ nilradical R := by
  obtain ⟨k, hk⟩ := h
  intro x hx
  exact mem_nilradical.mpr ⟨m * k, hI.pow_eq_zero_of_natCast_pow_eq_zero hm hk hx⟩

/-- Let `(I, hI)` be a divided power ideal of a commutative semiring `R` and `m ≠ 0` a natural
number with some power `(m : R) ^ r ∈ I`. Then `I ≤ nilradical R` if and only if `(m : R)` is
nilpotent in `R` (Stacks Project, Tag 07GR). -/
theorem le_nilradical_iff_isNilpotent_natCast (hI : DividedPowers I) {m : ℕ} (hm : m ≠ 0)
    (hmem : ∃ r : ℕ, (m : R) ^ r ∈ I) :
    I ≤ nilradical R ↔ _root_.IsNilpotent (m : R) := by
  constructor
  · intro hle
    obtain ⟨r, hr⟩ := hmem
    exact (mem_nilradical.mp (hle hr)).of_pow
  · exact hI.le_nilradical_of_isNilpotent_natCast hm

/-- Quotient form of the nilradical criterion: if `(I, hI)` is a divided power ideal of a
commutative ring `R` and `m ≠ 0` is nilpotent in `R ⧸ I`, then `I ≤ nilradical R` if and only if
`(m : R)` is nilpotent in `R` (Stacks Project, Tag 07GR). -/
theorem le_nilradical_iff_isNilpotent_of_quotient {A : Type*} [CommRing A] {J : Ideal A}
    (hJ : DividedPowers J) {m : ℕ} (hm : m ≠ 0)
    (hq : _root_.IsNilpotent (Ideal.Quotient.mk J (m : A))) :
    J ≤ nilradical A ↔ _root_.IsNilpotent (m : A) := by
  refine hJ.le_nilradical_iff_isNilpotent_natCast hm ?_
  obtain ⟨r, hr⟩ := hq
  refine ⟨r, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hr
  exact hr

end NilradicalCriterion

end DividedPowers
