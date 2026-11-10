/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The prime `p` divides `(x - 1) ^ p ^ k` when `x ^ p ^ k = 1`

For commuting elements `x` and `y` of a ring and a prime `p`, the binomial theorem gives
`x ^ p ^ k = ((x - y) + y) ^ p ^ k = (x - y) ^ p ^ k + y ^ p ^ k + p * c` for some `c`, because
every binomial coefficient `(p ^ k).choose m` with `0 < m < p ^ k` is divisible by `p`. Hence
`(p : A) ∣ (x - y) ^ p ^ k` if and only if `(p : A) ∣ x ^ p ^ k - y ^ p ^ k`. Taking `y = 1`, an
element `x` with `x ^ p ^ k = 1` satisfies `(p : A) ∣ (x - 1) ^ p ^ k`; no commutativity of the
ring is needed.

This is the integral shadow of the freshman's dream `(x - y) ^ p ^ k = x ^ p ^ k - y ^ p ^ k` in
characteristic `p`. It is what makes the group-like elements `g - 1`, for `g` of `p`-power order
in a group algebra over the `p`-adic integers, topologically nilpotent.

## Main results

* `Nat.Prime.dvd_sub_pow_iff_dvd_pow_sub_pow`: for commuting `x` and `y`,
  `(p : A) ∣ (x - y) ^ p ^ k ↔ (p : A) ∣ x ^ p ^ k - y ^ p ^ k`.
* `Nat.Prime.dvd_sub_one_pow_of_pow_eq_one`: `(p : A) ∣ (x - 1) ^ p ^ k` when `x ^ p ^ k = 1`.
* `exists_one_add_pow_eq_one_of_natCast_eq_zero`: conversely, if `(p : A) = 0` for some `p ≠ 0`,
  not necessarily prime, then `(1 + N) ^ p ^ n = 1` for some `n` when `N` is nilpotent.
-/

public section

variable {A : Type*} [Ring A] {p : ℕ}

/-- For commuting elements `x` and `y` of a ring and a prime `p`, `p` divides `(x - y) ^ p ^ k`
if and only if it divides `x ^ p ^ k - y ^ p ^ k`. -/
theorem Nat.Prime.dvd_sub_pow_iff_dvd_pow_sub_pow (hp : p.Prime) {x y : A} (h : Commute x y)
    (k : ℕ) : (p : A) ∣ (x - y) ^ p ^ k ↔ (p : A) ∣ x ^ p ^ k - y ^ p ^ k := by
  obtain ⟨r, hr⟩ := (h.sub_left (Commute.refl y)).exists_add_pow_prime_pow_eq hp k
  rw [sub_add_cancel] at hr
  rw [hr, add_right_comm, add_sub_cancel_right, mul_assoc, mul_assoc,
    dvd_add_left (dvd_mul_right _ _)]

/-- If `x ^ p ^ k = 1` in a ring, for a prime `p`, then `p` divides `(x - 1) ^ p ^ k`. -/
theorem Nat.Prime.dvd_sub_one_pow_of_pow_eq_one (hp : p.Prime) {x : A} {k : ℕ}
    (hx : x ^ p ^ k = 1) : (p : A) ∣ (x - 1) ^ p ^ k :=
  (hp.dvd_sub_pow_iff_dvd_pow_sub_pow (Commute.one_right x) k).2 (by simp [hx])

section Nilpotent

/-- In a commutative ring in which `p = 0`, for `p ≠ 0`, `(1 + a) ^ p ^ j` is `1` modulo
`a ^ 2 ^ j`. The binomial coefficients `(p).choose 1 = p` and `(p).choose 0` leave only terms
divisible by the square of the increment. -/
private theorem exists_one_add_pow_pow_eq {R : Type*} [CommRing R] {p : ℕ} (hp0 : p ≠ 0)
    (hp : (p : R) = 0) (a : R) (j : ℕ) : ∃ y : R, (1 + a) ^ p ^ j = 1 + a ^ 2 ^ j * y := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨y, hy⟩ := ih
    set b := a ^ 2 ^ j * y with hb
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hbin : (1 + b) ^ (q + 1) = 1 + ((q + 1 : ℕ) : R) * b +
        b ^ 2 * ∑ m ∈ Finset.range q, b ^ m * ((q + 1).choose (m + 2) : R) := by
      rw [add_comm, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
        Finset.mul_sum]
      have h1 : ((q + 1).choose (0 + 1) : R) = ((q + 1 : ℕ) : R) := by simp
      have hsum : ∑ x ∈ Finset.range q, b ^ (x + 1 + 1) * ((q + 1).choose (x + 1 + 1) : R) =
          ∑ i ∈ Finset.range q, b ^ 2 * (b ^ i * ((q + 1).choose (i + 2) : R)) :=
        Finset.sum_congr rfl fun m _ => by ring
      rw [hsum, h1]
      ring
    refine ⟨y ^ 2 * ∑ m ∈ Finset.range q, b ^ m * ((q + 1).choose (m + 2) : R), ?_⟩
    rw [pow_succ, pow_mul, hy, hbin, hp, zero_mul, add_zero, hb]
    ring

/-- If `(p : A) = 0` in a ring `A`, for some `p ≠ 0` which need not be prime, then
`(1 + N) ^ p ^ n = 1` for some `n` whenever `N` is nilpotent. -/
theorem exists_one_add_pow_eq_one_of_natCast_eq_zero {A : Type*} [Ring A] {p : ℕ} (hp0 : p ≠ 0)
    (hp : (p : A) = 0) {N : A} (hN : IsNilpotent N) : ∃ n : ℕ, (1 + N) ^ p ^ n = 1 := by
  obtain ⟨m, hm⟩ := hN
  -- The identity holds in `ℤ[X] ⧸ (p)`, which maps to `A` by sending `X` to `N`.
  let I : Ideal (Polynomial ℤ) := Ideal.span {(p : Polynomial ℤ)}
  have hpI : (p : Polynomial ℤ ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  obtain ⟨y, hy⟩ := exists_one_add_pow_pow_eq hp0 hpI (Ideal.Quotient.mk I Polynomial.X) m
  let Φ : (Polynomial ℤ ⧸ I) →ₐ[ℤ] A := Ideal.Quotient.liftₐ I (Polynomial.aeval N) (by
    intro f hf
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    simp [hp])
  have hΦX : Φ (Ideal.Quotient.mk I Polynomial.X) = N := Polynomial.aeval_X N
  refine ⟨m, ?_⟩
  have h := congrArg Φ hy
  rw [map_pow, map_add, map_one, hΦX, map_add, map_one, map_mul, map_pow, hΦX,
    pow_eq_zero_of_le (Nat.lt_two_pow_self).le hm, zero_mul, add_zero] at h
  exact h

end Nilpotent
