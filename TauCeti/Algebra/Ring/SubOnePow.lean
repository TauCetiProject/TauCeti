/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.Module
import TauCeti.Algebra.Ring.GeomSum

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

For a prime `p > 3` the binomial coefficients `C(p, 2)` and `C(p, 3)` are both divisible by `p`, so
the third-order expansion of `(1 + x) ^ p` gives `(1 + x) ^ p ≡ 1 + p x` modulo `c p²` whenever
`x ^ 2` is a multiple of `c p`. This is how `p`-th powers climb the congruence filtration of
`SL₂(ℤ_p)` in Serre's lifting lemma.

## Main results

* `Nat.Prime.dvd_sub_pow_iff_dvd_pow_sub_pow`: for commuting `x` and `y`,
  `(p : A) ∣ (x - y) ^ p ^ k ↔ (p : A) ∣ x ^ p ^ k - y ^ p ^ k`.
* `Nat.Prime.dvd_sub_one_pow_of_pow_eq_one`: `(p : A) ∣ (x - 1) ^ p ^ k` when `x ^ p ^ k = 1`.
* `TauCeti.exists_one_add_pow_prime_eq_of_sq_eq_nsmul`: for a prime `p > 3`, if
  `x ^ 2 = (c p) • y` then `(1 + x) ^ p = 1 + p • x + (c p²) • w` for some `w`.
* `TauCeti.exists_one_add_pow_pow_eq`: in a commutative ring with `(p : R) = 0`,
  `(1 + a) ^ p ^ j = 1 + a ^ 2 ^ j * y` for some `y`.
* `TauCeti.exists_one_add_pow_eq_one_of_natCast_eq_zero`: conversely, if `(p : A) = 0` for some `p`,
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

namespace TauCeti

/-- **The `p`-th power of a perturbation of `1`.** If `x ^ 2 = (c p) • y` in a ring and `p > 3`
is prime, then `(1 + x) ^ p = 1 + p • x + (c p²) • w` for some `w`: in the third-order binomial
expansion the coefficients `C(p, 2)` and `C(p, 3)` are divisible by `p`, and `x ^ 4` is divisible
by `(c p) ^ 2`. -/
theorem exists_one_add_pow_prime_eq_of_sq_eq_nsmul (hp : p.Prime) (hp3 : 3 < p) {c : ℕ}
    {x y : A} (hxy : x ^ 2 = (c * p) • y) :
    ∃ w, (1 + x) ^ p = 1 + p • x + (c * p ^ 2) • w := by
  obtain ⟨v, hv⟩ := exists_one_add_pow_eq_add_pow_four_mul x p
  obtain ⟨m₂, hm₂⟩ := hp.dvd_choose_self (k := 2) two_ne_zero (by omega)
  obtain ⟨m₃, hm₃⟩ := hp.dvd_choose_self (k := 3) three_ne_zero hp3
  refine ⟨m₂ • y + m₃ • (x * y) + c • (y * y * v), ?_⟩
  have h3 : x ^ 3 = (c * p) • (x * y) := by rw [pow_succ', hxy, mul_smul_comm]
  have h4 : x ^ 4 = ((c * p) * (c * p)) • (y * y) := by
    rw [show 4 = 2 + 2 from rfl, pow_add, hxy, smul_mul_smul_comm]
  rw [hv, hm₂, hm₃, h3, h4, hxy]
  simp only [← nsmul_eq_mul, smul_mul_assoc, smul_add, smul_smul]
  module

section Nilpotent

/-- In a commutative ring in which `p = 0`, `(1 + a) ^ p ^ j` is `1` modulo `a ^ 2 ^ j`. The
second-order expansion `(1 + b) ^ p = 1 + p * b + b ^ 2 * v` leaves only terms divisible by the
square of the increment. -/
theorem exists_one_add_pow_pow_eq {R : Type*} [CommRing R] {p : ℕ} (hp : (p : R) = 0) (a : R)
    (j : ℕ) : ∃ y : R, (1 + a) ^ p ^ j = 1 + a ^ 2 ^ j * y := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨v, -, hv, -⟩ := exists_one_add_pow_eq_and_geom_sum_eq (a ^ 2 ^ j * y) p
    refine ⟨y ^ 2 * v, ?_⟩
    rw [pow_succ, pow_mul, hy, hv, hp, zero_mul, add_zero]
    ring

/-- If `(p : A) = 0` in a ring `A`, where `p` need not be prime (and may be `0`), then
`(1 + N) ^ p ^ n = 1` for some `n` whenever `N` is nilpotent. For `p = 0` the conclusion is
witnessed by `n = 1`, since `(1 + N) ^ 0 = 1`. -/
theorem exists_one_add_pow_eq_one_of_natCast_eq_zero {A : Type*} [Ring A] {p : ℕ}
    (hp : (p : A) = 0) {N : A} (hN : IsNilpotent N) : ∃ n : ℕ, (1 + N) ^ p ^ n = 1 := by
  obtain ⟨m, hm⟩ := hN
  -- The identity holds in `ℤ[X] ⧸ (p)`, which maps to `A` by sending `X` to `N`.
  let I : Ideal (Polynomial ℤ) := Ideal.span {(p : Polynomial ℤ)}
  have hpI : (p : Polynomial ℤ ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  obtain ⟨y, hy⟩ := exists_one_add_pow_pow_eq hpI (Ideal.Quotient.mk I Polynomial.X) m
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

end TauCeti
