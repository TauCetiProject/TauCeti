/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Addition, multiplication, and connection formulas for probabilists' Hermite polynomials

This file develops the algebraic addition, scaling, and connection identities for Mathlib's
probabilists' Hermite polynomials `Polynomial.hermite : ℕ → ℤ[X]` over arbitrary commutative rings,
without any characteristic-zero or invertibility assumptions.

## Main results

* `TauCeti.hasseDeriv_hermite`: the `m`-th Hasse derivative of `hermite n` in `ℤ[X]` is
  `n.choose m • hermite (n - m)`.
* `TauCeti.taylor_map_hermite` and `TauCeti.comp_X_add_C_map_hermite`: polynomial Taylor and
  translation-shift expansions of `hermite n` over any commutative ring.
* `TauCeti.hermite_aeval_add` and `TauCeti.hermite_aeval_sub`: the Appell translation addition
  identity `Heₙ(x + y) = ∑_{m=0}^n C(n, m) He_{n-m}(x) y^m` and its subtraction form.
* `TauCeti.hermite_aeval_mul_add_mul`: the Feldheim–Carlitz linear-combination expansion
  (DLMF 18.18.13) expressing `Heₙ(a x + b y)` for arbitrary `a, b, x, y` in a commutative ring.
* `TauCeti.sum_choose_smul_hermite_aeval_mul`: the dual expansion of
  `∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)` in terms of `He_{n-2k}(a x + b y)`.
* `TauCeti.hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one` and
  `TauCeti.hermite_aeval_mul_sub_mul_of_sq_add_sq_eq_one`: Runge's rotational addition theorem
  (DLMF 18.18.12), `Heₙ(a x + b y) = ∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)` whenever
  `a^2 + b^2 = 1`.
* `TauCeti.hermite_aeval_mul`: the scaling (multiplication) formula (DLMF 18.18.14) for
  `Heₙ(c x)`.
* `TauCeti.X_pow_eq_sum_hermite` and `TauCeti.pow_eq_sum_hermite_aeval`: the inversion formula
  (DLMF 18.18.20) expressing `X^n` as an integer combination of `hermite (n - 2k)`.

## Proof outline

The Hasse derivative identity follows from `Polynomial.iterate_derivative_hermite` and
`Polynomial.factorial_smul_hasseDeriv` using torsion-freeness of `ℤ[X]`, and immediately yields the
Taylor and translation formulas. For linear combinations and scaling, we prove a general connection
identity between any two sequences satisfying three-term recurrences
`z P_m = P_{m+1} + m c₁ P_{m-1}` and `z Q_m = Q_{m+1} + m c₂ Q_{m-1}` at variances `c₁` and `c₂`,
together with the three-term recurrence at variance `a^2 + b^2` for the binomial Hermite sum.
Specializing `(c₁, c₂)` yields Feldheim–Carlitz, Runge's rotational addition theorem, the scaling
theorem, and monomial inversion uniformly over every commutative ring.

## References

* C. Runge, *Über eine besondere Art von Integralgleichungen*, Math. Ann. **75** (1914), 130–132.
* E. Feldheim, *Relations entre les polynômes de Jacobi, Laguerre et Hermite*, Acta Math. **74**
  (1941), 117–138.
* L. Carlitz, *Some formulas of E. Feldheim*, Acta Math. Acad. Sci. Hungar. **14** (1963), 21–29.
* A. Erdélyi et al., *Higher Transcendental Functions*, Vol. II, §10.13.
* NIST Digital Library of Mathematical Functions, [§18.18](https://dlmf.nist.gov/18.18),
  after rescaling from the physicists' `Hₙ` to the probabilists' `Heₙ`.
-/

public section

namespace TauCeti

open Polynomial
open scoped Nat

/-! ### Hasse derivatives and Appell translation -/

/-- The `m`-th Hasse derivative of the probabilists' Hermite polynomial `hermite n` in `ℤ[X]` is
`n.choose m • hermite (n - m)`. For `m > n` both sides vanish. -/
@[simp]
theorem hasseDeriv_hermite (n m : ℕ) :
    hasseDeriv m (hermite n) = n.choose m • hermite (n - m) := by
  apply smul_right_injective ℤ[X] (Nat.factorial_ne_zero m)
  dsimp only
  have h1 : m ! • hasseDeriv m (hermite n) = derivative^[m] (hermite n) :=
    congr_fun (factorial_smul_hasseDeriv (R := ℤ) (k := m)) (hermite n)
  rw [h1, Polynomial.iterate_derivative_hermite, Nat.descFactorial_eq_factorial_mul_choose,
    mul_smul]

/-- Polynomial Taylor expansion of `hermite n` at `r` over any commutative ring `R`. -/
theorem taylor_map_hermite {R : Type*} [CommRing R] (n : ℕ) (r : R) :
    taylor r ((hermite n).map (Int.castRingHom R)) =
      ∑ m ∈ Finset.range (n + 1),
        n.choose m • (C (aeval r (hermite (n - m))) * X ^ m) := by
  have hdeg : (taylor r ((hermite n).map (Int.castRingHom R))).natDegree < n + 1 := by
    rw [natDegree_taylor]
    exact Nat.lt_succ_of_le (natDegree_map_le.trans_eq natDegree_hermite)
  rw [as_sum_range' _ (n + 1) hdeg]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [taylor_coeff, hasseDeriv_map, hasseDeriv_hermite]
  simp [← algebraMap_int_eq, ← C_mul_X_pow_eq_monomial, nsmul_eq_mul, mul_assoc]

/-- **Appell translation addition formula** for probabilists' Hermite polynomials: over any
commutative ring, `Heₙ(x + y) = ∑_{m=0}^n C(n, m) He_{n-m}(x) y^m`. -/
theorem hermite_aeval_add {R : Type*} [CommRing R] (n : ℕ) (x y : R) :
    aeval (x + y) (hermite n) =
      ∑ m ∈ Finset.range (n + 1), n.choose m • (aeval x (hermite (n - m)) * y ^ m) := by
  have heval : aeval (x + y) (hermite n) =
      (taylor x ((hermite n).map (Int.castRingHom R))).eval y := by
    rw [taylor_eval, add_comm, ← algebraMap_int_eq, eval_map_algebraMap]
  rw [heval, taylor_map_hermite, eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [nsmul_eq_mul]

/-- Subtraction form of the Appell translation formula for probabilists' Hermite polynomials. -/
theorem hermite_aeval_sub {R : Type*} [CommRing R] (n : ℕ) (x y : R) :
    aeval (x - y) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        (-1) ^ m * (n.choose m • (aeval x (hermite (n - m)) * y ^ m)) := by
  rw [sub_eq_add_neg, hermite_aeval_add]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- Polynomial shift identity `(hermite n)(X + y) = ∑_{m=0}^n C(n, m) y^m hermite (n - m)` in
`R[X]` over any commutative ring `R`. -/
theorem comp_X_add_C_map_hermite {R : Type*} [CommRing R] (n : ℕ) (y : R) :
    ((hermite n).map (Int.castRingHom R)).comp (X + C y) =
      ∑ m ∈ Finset.range (n + 1),
        n.choose m • (C (y ^ m) * (hermite (n - m)).map (Int.castRingHom R)) := by
  refine Eq.trans ?_ ((hermite_aeval_add (R := R[X]) n X (C y)).trans ?_)
  · rw [comp_eq_aeval, aeval_def, aeval_def, eval₂_map]
    congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hmap : @aeval ℤ R[X] _ _ (Ring.toIntAlgebra R[X]) X (hermite (n - m)) =
        (hermite (n - m)).map (Int.castRingHom R) := by
      rw [aeval_def,
        ← eval₂_C_X (p := (hermite (n - m)).map (Int.castRingHom R)), eval₂_map]
      congr 1
    rw [hmap, ← C_pow, mul_comm]

/-! ### Variance-connection recurrence and binomial Hermite sums -/

/-- Multiplication by `z` on `aeval z (hermite k)` splits into raising and lowering terms:
`z He_k(z) = He_{k+1}(z) + k He_{k-1}(z)`, including at `k = 0`. -/
private lemma mul_hermite_aeval {R : Type*} [CommRing R] (k : ℕ) (z : R) :
    z * aeval z (hermite k) = aeval z (hermite (k + 1)) + k * aeval z (hermite (k - 1)) := by
  rw [hermite_succ, derivative_hermite, map_sub, map_mul, aeval_X, map_nsmul, nsmul_eq_mul]
  ring

/-- The bivariate binomial sum `∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)`. -/
private noncomputable def binomHermiteSum {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) : R :=
  ∑ m ∈ Finset.range (n + 1),
    n.choose m • (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))

private lemma binomHermiteSum_zero {R : Type*} [CommRing R] (a b x y : R) :
    binomHermiteSum a b x y 0 = 1 := by
  simp [binomHermiteSum]

/-- Pascal combination of the raising terms in `(a x + b y) * binomHermiteSum a b x y n`. -/
private lemma binomHermiteSum_raise {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * (a ^ (n + 1 - m) * b ^ m *
          aeval x (hermite (n + 1 - m)) * aeval y (hermite m))) +
      (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * (a ^ (n - m) * b ^ (m + 1) *
          aeval x (hermite (n - m)) * aeval y (hermite (m + 1)))) =
      binomHermiteSum a b x y (n + 1) := by
  unfold binomHermiteSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.sum_range_succ' _ n, Finset.sum_range_succ _ n, Finset.sum_range_succ' _ (n + 1),
    Finset.sum_range_succ _ n]
  have hmid :
      (∑ k ∈ Finset.range n,
          (n.choose (k + 1) : R) * (a ^ (n + 1 - (k + 1)) * b ^ (k + 1) *
            aeval x (hermite (n + 1 - (k + 1))) * aeval y (hermite (k + 1)))) +
        (∑ k ∈ Finset.range n,
          (n.choose k : R) * (a ^ (n - k) * b ^ (k + 1) *
            aeval x (hermite (n - k)) * aeval y (hermite (k + 1)))) =
      ∑ k ∈ Finset.range n,
        ((n + 1).choose (k + 1) : R) * (a ^ (n + 1 - (k + 1)) * b ^ (k + 1) *
          aeval x (hermite (n + 1 - (k + 1))) * aeval y (hermite (k + 1))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.succ_sub_succ_eq_sub, Nat.choose_succ_succ' n k, Nat.cast_add, add_mul]
    ring
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.sub_zero, Nat.sub_self, pow_zero,
    hermite_zero, map_one, Nat.cast_one, one_mul, mul_one]
  rw [add_right_comm _ (a ^ (n + 1) * aeval x (hermite (n + 1))), ← add_assoc, hmid]

/-- Lowering `x`-terms in `(a x) * binomHermiteSum a b x y n`. -/
private lemma binomHermiteSum_lower_left {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * ((n - m : ℕ) * a ^ 2 *
          (a ^ (n - 1 - m) * b ^ m * aeval x (hermite (n - 1 - m)) * aeval y (hermite m)))) =
      (n : R) * a ^ 2 * binomHermiteSum a b x y (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    unfold binomHermiteSum
    simp_rw [nsmul_eq_mul]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hbinom : (n + 1).choose m * (n + 1 - m) = n.choose m * (n + 1) :=
      (Nat.choose_mul_succ_eq n m).symm
    calc
      ((n + 1).choose m : R) * ((n + 1 - m : ℕ) * a ^ 2 *
          (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) =
          ((((n + 1).choose m * (n + 1 - m) : ℕ) : R)) * (a ^ 2 *
            (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) := by
        push_cast; ring
      _ = _ := by
        rw [hbinom]
        push_cast
        ring

/-- Lowering `y`-terms in `(b y) * binomHermiteSum a b x y n`. -/
private lemma binomHermiteSum_lower_right {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * ((m : R) * b ^ 2 *
          (a ^ (n - m) * b ^ (m - 1) * aeval x (hermite (n - m)) * aeval y (hermite (m - 1))))) =
      (n : R) * b ^ 2 * binomHermiteSum a b x y (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    unfold binomHermiteSum
    simp_rw [nsmul_eq_mul]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hbinom : (n + 1).choose (m + 1) * (m + 1) = (n + 1) * n.choose m :=
      (Nat.add_one_mul_choose_eq n m).symm
    simp only [Nat.succ_sub_succ_eq_sub]
    calc
      ((n + 1).choose (m + 1) : R) * (((m + 1 : ℕ) : R) * b ^ 2 *
          (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) =
          ((((n + 1).choose (m + 1) * (m + 1) : ℕ) : R)) * (b ^ 2 *
            (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) := by
        push_cast; ring
      _ = _ := by
        rw [hbinom]
        push_cast
        ring

/-- Four-way expansion of `(a x + b y) * binomHermiteSum a b x y n` via the raising and lowering
terms of `mul_hermite_aeval`. -/
private lemma binomHermiteSum_mul_expand {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (a * x + b * y) * binomHermiteSum a b x y n =
      ((∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * (a ^ (n + 1 - m) * b ^ m *
            aeval x (hermite (n + 1 - m)) * aeval y (hermite m))) +
        (∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * (a ^ (n - m) * b ^ (m + 1) *
            aeval x (hermite (n - m)) * aeval y (hermite (m + 1))))) +
      (∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * ((n - m : ℕ) * a ^ 2 *
            (a ^ (n - 1 - m) * b ^ m * aeval x (hermite (n - 1 - m)) *
              aeval y (hermite m)))) +
      (∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * ((m : R) * b ^ 2 *
            (a ^ (n - m) * b ^ (m - 1) * aeval x (hermite (n - m)) *
              aeval y (hermite (m - 1))))) := by
  unfold binomHermiteSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_le : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hx := mul_hermite_aeval (n - m) x
  have hy := mul_hermite_aeval m y
  have hsub_x : n - m + 1 = n + 1 - m := by lia
  have hpow_a : a * a ^ (n - m) = a ^ (n + 1 - m) := by rw [← pow_succ', hsub_x]
  have hpow_a2 :
      ((n - m : ℕ) : R) * (a * a ^ (n - m)) =
        ((n - m : ℕ) : R) * (a ^ 2 * a ^ (n - 1 - m)) := by
    rcases eq_or_lt_of_le hm_le with rfl | hlt
    · simp
    · have hidx : n - m + 1 = 2 + (n - 1 - m) := by lia
      congr 1
      rw [← pow_succ', ← pow_add, hidx]
  have hpow_b2 : (m : R) * (b * b ^ m) = (m : R) * (b ^ 2 * b ^ (m - 1)) := by
    rcases m with _ | m
    · simp
    · congr 1
      rw [← pow_succ', ← pow_add, Nat.add_sub_cancel]
      ring
  calc
    (a * x + b * y) * ((n.choose m : R) * (a ^ (n - m) * b ^ m *
        aeval x (hermite (n - m)) * aeval y (hermite m))) =
        (n.choose m : R) * ((a * a ^ (n - m)) * b ^ m *
          (x * aeval x (hermite (n - m))) * aeval y (hermite m)) +
        (n.choose m : R) * (a ^ (n - m) * (b * b ^ m) *
          aeval x (hermite (n - m)) * (y * aeval y (hermite m))) := by ring
    _ = (n.choose m : R) * ((a * a ^ (n - m)) * b ^ m *
          aeval x (hermite (n + 1 - m)) * aeval y (hermite m)) +
        (n.choose m : R) * (a ^ (n - m) * (b * b ^ m) *
          aeval x (hermite (n - m)) * aeval y (hermite (m + 1))) +
        (n.choose m : R) * ((((n - m : ℕ) : R) * (a * a ^ (n - m))) *
          (b ^ m * aeval x (hermite (n - 1 - m)) * aeval y (hermite m))) +
        (n.choose m : R) * (((m : R) * (b * b ^ m)) *
          (a ^ (n - m) * aeval x (hermite (n - m)) * aeval y (hermite (m - 1)))) := by
      rw [hx, hy, hsub_x, Nat.sub_right_comm n m 1]
      ring
    _ = _ := by
      rw [hpow_a2, hpow_b2, hpow_a, pow_succ' b]
      ring

/-- Three-term recurrence for `binomHermiteSum` at variance `a^2 + b^2`: for all `a, b, x, y` in
any commutative ring,
`(a x + b y) Q_n = Q_{n+1} + n (a^2 + b^2) Q_{n-1}`. -/
private lemma mul_binomHermiteSum {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (a * x + b * y) * binomHermiteSum a b x y n =
      binomHermiteSum a b x y (n + 1) +
        (n : R) * (a ^ 2 + b ^ 2) * binomHermiteSum a b x y (n - 1) := by
  rw [binomHermiteSum_mul_expand, binomHermiteSum_raise, binomHermiteSum_lower_left,
    binomHermiteSum_lower_right]
  ring

/-- Auxiliary connection sum indexed up to `n`; terms with `2 * k > n` vanish. -/
private def connectionSum {R : Type*} [CommRing R] (d : R) (Q : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose (2 * k) * (2 * k - 1)‼) • (d ^ k * Q (n - 2 * k))

private lemma connectionSum_eq_sum_div_two {R : Type*} [CommRing R] (d : R) (Q : ℕ → R) (n : ℕ) :
    connectionSum d Q n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k - 1)‼) • (d ^ k * Q (n - 2 * k)) := by
  unfold connectionSum
  refine (Finset.sum_subset (Finset.range_mono (by lia)) fun k _ hk => ?_).symm
  have hlt : n < 2 * k := by simp only [Finset.mem_range, not_lt] at hk; lia
  simp [Nat.choose_eq_zero_of_lt hlt]

private lemma connectionSum_mul_expand {R : Type*} [CommRing R] {z c₂ : R} (d : R) {Q : ℕ → R}
    (hQ : ∀ m, z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)) (n : ℕ) :
    z * connectionSum d Q (n + 1) =
      (∑ k ∈ Finset.range (n + 2),
          (((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) *
            (d ^ k * Q (n + 2 - 2 * k))) +
        (∑ k ∈ Finset.range (n + 2),
          (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
            (c₂ * d ^ k * Q (n - 2 * k))) := by
  unfold connectionSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases le_or_gt (2 * k) (n + 1) with hle | hgt
  · have hsub1 : n + 1 - 2 * k + 1 = n + 2 - 2 * k := by lia
    have hsub2 : n + 1 - 2 * k - 1 = n - 2 * k := by lia
    have hQm := hQ (n + 1 - 2 * k)
    rw [hsub1, hsub2] at hQm
    calc
      z * ((((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) * (d ^ k * Q (n + 1 - 2 * k))) =
          (((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) * d ^ k *
            (z * Q (n + 1 - 2 * k)) := by ring
      _ = _ := by
        rw [hQm]
        push_cast
        ring
  · simp [Nat.choose_eq_zero_of_lt hgt]

private lemma connectionSum_lower_c₁ {R : Type*} [CommRing R] (c₁ d : R) (Q : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
          (c₁ * d ^ k * Q (n - 2 * k))) =
      (n + 1 : ℕ) * c₁ * connectionSum d Q n := by
  unfold connectionSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.sum_range_succ _ (n + 1)]
  have htop : (n + 1).choose (2 * (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  rw [htop, zero_mul, zero_mul, Nat.cast_zero, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbinom : (n + 1).choose (2 * k) * (n + 1 - 2 * k) = n.choose (2 * k) * (n + 1) :=
    (Nat.choose_mul_succ_eq n (2 * k)).symm
  rw [hbinom]
  push_cast
  ring

private lemma connectionSum_raise_add_diff {R : Type*} [CommRing R] (d : R) (Q : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        (((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) *
          (d ^ k * Q (n + 2 - 2 * k))) +
      (∑ k ∈ Finset.range (n + 2),
        (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
          (d * d ^ k * Q (n - 2 * k))) =
      connectionSum d Q (n + 2) := by
  unfold connectionSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ' _ (n + 2)]
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.choose_zero_right, pow_zero, one_mul]
  rw [Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ _ (n + 1)]
  have htop1 : (n + 1).choose (2 * (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  have htop2 : (n + 2).choose (2 * (n + 1 + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  rw [htop1, htop2]
  simp only [zero_mul, Nat.cast_zero, add_zero]
  have hcomb :
      (∑ k ∈ Finset.range (n + 1),
          (((n + 1).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ : ℕ) : R) *
            (d ^ (k + 1) * Q (n + 2 - 2 * (k + 1)))) +
        (∑ k ∈ Finset.range (n + 1),
          (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
            (d * d ^ k * Q (n - 2 * k))) =
        ∑ k ∈ Finset.range (n + 1),
          (((n + 2).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ : ℕ) : R) *
            (d ^ (k + 1) * Q (n + 2 - 2 * (k + 1))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hodd : 2 * (k + 1) - 1 = 2 * k + 1 := by lia
    have hsub : n + 2 - 2 * (k + 1) = n - 2 * k := by lia
    have hnat :
        (n + 1).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ +
            (n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ =
          (n + 2).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ := by
      rw [hodd, ← Nat.choose_succ_right_eq (n + 1) (2 * k), mul_assoc,
        Nat.doubleFactorial_add_one (2 * k), mul_add 2 k 1,
        ← add_mul, add_comm ((n + 1).choose (2 * k + 2)),
        ← Nat.choose_succ_succ' (n + 1) (2 * k + 1)]
    rw [hsub, pow_succ', ← add_mul, ← Nat.cast_add, hnat]
  rw [add_right_comm, hcomb]

/-- One-step recurrence for `connectionSum`: if `z Q_m = Q_{m+1} + m c₂ Q_{m-1}`, then
`S_n = connectionSum (c₂ - c₁) Q n` satisfies `z S_{n+1} = S_{n+2} + (n + 1) c₁ S_n`. -/
private lemma mul_connectionSum_succ {R : Type*} [CommRing R] {z c₁ c₂ : R} {Q : ℕ → R}
    (hQ : ∀ m, z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)) (n : ℕ) :
    z * connectionSum (c₂ - c₁) Q (n + 1) =
      connectionSum (c₂ - c₁) Q (n + 2) + (n + 1 : ℕ) * c₁ * connectionSum (c₂ - c₁) Q n := by
  set d : R := c₂ - c₁
  have hstep1 := connectionSum_mul_expand d hQ n
  have hstep2 := connectionSum_lower_c₁ c₁ d Q n
  have hstep3 := connectionSum_raise_add_diff d Q n
  have hc₂ : ∀ k, c₂ * d ^ k * Q (n - 2 * k) =
      c₁ * d ^ k * Q (n - 2 * k) + d * d ^ k * Q (n - 2 * k) := fun k => by
    dsimp [d]; ring
  simp_rw [hc₂, mul_add, Finset.sum_add_distrib] at hstep1
  rw [hstep1, hstep2, ← add_assoc, add_right_comm _ ((n + 1 : ℕ) * c₁ * _), hstep3, add_comm]

/-- **Variance-connection master identity.** Any two sequences `P, Q : ℕ → R` starting at `1` and
satisfying `z P_m = P_{m+1} + m c₁ P_{m-1}` and `z Q_m = Q_{m+1} + m c₂ Q_{m-1}` are related by
`P_n = ∑_{k=0}^{⌊n/2⌋} C(n, 2k) (2k - 1)‼ (c₂ - c₁)^k Q_{n - 2k}`. -/
private lemma eq_connectionSum_of_recurrence {R : Type*} [CommRing R] {z c₁ c₂ : R}
    {P Q : ℕ → R} (hP0 : P 0 = 1) (hQ0 : Q 0 = 1)
    (hP : ∀ m, z * P m = P (m + 1) + m * c₁ * P (m - 1))
    (hQ : ∀ m, z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)) (n : ℕ) :
    P n = ∑ k ∈ Finset.range (n / 2 + 1),
      (n.choose (2 * k) * (2 * k - 1)‼) • ((c₂ - c₁) ^ k * Q (n - 2 * k)) := by
  rw [← connectionSum_eq_sum_div_two]
  induction n using Nat.twoStepInduction with
  | zero =>
    simp [connectionSum, hP0, hQ0]
  | one =>
    have hP1 : P 1 = z := by simpa [hP0] using (hP 0).symm
    have hQ1 : Q 1 = z := by simpa [hQ0] using (hQ 0).symm
    simp [connectionSum, Finset.sum_range_succ, hP1, hQ1]
  | more n ih0 ih1 =>
    have hP_step := hP (n + 1)
    have hS_step := mul_connectionSum_succ (c₁ := c₁) hQ n
    rw [Nat.add_sub_cancel, ih0, ih1] at hP_step
    exact add_right_cancel (hP_step.symm.trans hS_step)

/-! ### Linear-combination, rotational addition, scaling, and inversion theorems -/

/-- **Feldheim–Carlitz linear-combination theorem** (DLMF 18.18.13) for the probabilists' Hermite
polynomials: for arbitrary `a, b, x, y` in any commutative ring,
`Heₙ(a x + b y)` expands in powers of `a^2 + b^2 - 1` times the binomial Hermite sums. -/
theorem hermite_aeval_mul_add_mul {R : Type*} [CommRing R] (n : ℕ) (a b x y : R) :
    aeval (a * x + b * y) (hermite n) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k - 1)‼) •
          ((a ^ 2 + b ^ 2 - 1) ^ k *
            ∑ m ∈ Finset.range (n - 2 * k + 1),
              (n - 2 * k).choose m •
                (a ^ (n - 2 * k - m) * b ^ m *
                  aeval x (hermite (n - 2 * k - m)) * aeval y (hermite m))) := by
  refine eq_connectionSum_of_recurrence
    (z := a * x + b * y) (c₁ := 1) (c₂ := a ^ 2 + b ^ 2)
    (P := fun m => aeval (a * x + b * y) (hermite m))
    (Q := binomHermiteSum a b x y)
    (by simp) (binomHermiteSum_zero a b x y)
    (fun m => by simpa only [mul_one] using mul_hermite_aeval m (a * x + b * y))
    (mul_binomHermiteSum a b x y) n

/-- **Dual Feldheim–Carlitz expansion**: over any commutative ring, the binomial sum
`∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)` expands in `He_{n - 2k}(a x + b y)` with
powers of `1 - a^2 - b^2`. -/
theorem sum_choose_smul_hermite_aeval_mul {R : Type*} [CommRing R] (n : ℕ) (a b x y : R) :
    (∑ m ∈ Finset.range (n + 1),
        n.choose m • (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k - 1)‼) •
          ((1 - a ^ 2 - b ^ 2) ^ k * aeval (a * x + b * y) (hermite (n - 2 * k))) := by
  have h := eq_connectionSum_of_recurrence
    (z := a * x + b * y) (c₁ := a ^ 2 + b ^ 2) (c₂ := 1)
    (P := binomHermiteSum a b x y)
    (Q := fun m => aeval (a * x + b * y) (hermite m))
    (binomHermiteSum_zero a b x y) (by simp)
    (mul_binomHermiteSum a b x y)
    (fun m => by simpa only [mul_one] using mul_hermite_aeval m (a * x + b * y)) n
  simpa [binomHermiteSum, sub_sub] using h

/-- **Runge's rotational addition theorem** (Runge 1914; DLMF 18.18.12) for the probabilists'
Hermite polynomials: in any commutative ring `R`, whenever `a^2 + b^2 = 1`,
`Heₙ(a x + b y) = ∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one {R : Type*} [CommRing R] (n : ℕ)
    {a b : R} (hab : a ^ 2 + b ^ 2 = 1) (x y : R) :
    aeval (a * x + b * y) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        n.choose m • (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m)) := by
  rw [hermite_aeval_mul_add_mul n a b x y, hab, sub_self, Finset.sum_range_succ',
    Finset.sum_eq_zero fun k _ => by simp [zero_pow (Nat.succ_ne_zero k)]]
  simp

/-- Subtraction form of **Runge's rotational addition theorem**: in any commutative ring `R`,
whenever `a^2 + b^2 = 1`,
`Heₙ(a x - b y) = ∑_{m=0}^n (-1)^m C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_sub_mul_of_sq_add_sq_eq_one {R : Type*} [CommRing R] (n : ℕ)
    {a b : R} (hab : a ^ 2 + b ^ 2 = 1) (x y : R) :
    aeval (a * x - b * y) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        (-1) ^ m *
          (n.choose m •
            (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) := by
  have hab' : a ^ 2 + (-b) ^ 2 = 1 := by simpa [neg_sq] using hab
  have hsub : a * x - b * y = a * x + (-b) * y := by ring
  rw [hsub, hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one n hab' x y]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- **Scaling (multiplication) theorem** (DLMF 18.18.14) for the probabilists' Hermite
polynomials: in any commutative ring `R`,
`Heₙ(c x) = ∑_{k=0}^{⌊n/2⌋} C(n, 2k) (2k - 1)‼ c^{n - 2k} (c^2 - 1)^k He_{n - 2k}(x)`. -/
theorem hermite_aeval_mul {R : Type*} [CommRing R] (n : ℕ) (c x : R) :
    aeval (c * x) (hermite n) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k - 1)‼) •
          (c ^ (n - 2 * k) * (c ^ 2 - 1) ^ k * aeval x (hermite (n - 2 * k))) := by
  have hQ : ∀ m, (c * x) * (c ^ m * aeval x (hermite m)) =
      c ^ (m + 1) * aeval x (hermite (m + 1)) +
        m * c ^ 2 * (c ^ (m - 1) * aeval x (hermite (m - 1))) := by
    intro m
    rcases m with _ | m
    · simp [pow_one]
    · have hm := mul_hermite_aeval (m + 1) x
      rw [Nat.add_sub_cancel] at hm ⊢
      calc
        (c * x) * (c ^ (m + 1) * aeval x (hermite (m + 1))) =
            c ^ (m + 2) * (x * aeval x (hermite (m + 1))) := by ring
        _ = _ := by rw [hm]; ring
  have h := eq_connectionSum_of_recurrence
    (z := c * x) (c₁ := 1) (c₂ := c ^ 2)
    (P := fun m => aeval (c * x) (hermite m))
    (Q := fun m => c ^ m * aeval x (hermite m))
    (by simp) (by simp)
    (fun m => by simpa only [mul_one] using mul_hermite_aeval m (c * x))
    hQ n
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ring

/-- **Monomial-to-Hermite inversion formula** (DLMF 18.18.20) in `ℤ[X]`:
`X^n = ∑_{k=0}^{⌊n/2⌋} C(n, 2k) (2k - 1)‼ hermite (n - 2k)`. -/
theorem X_pow_eq_sum_hermite (n : ℕ) :
    (X : ℤ[X]) ^ n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k - 1)‼) • hermite (n - 2 * k) := by
  have hstep : ∀ m, (X : ℤ[X]) * hermite m =
      hermite (m + 1) + (m : ℤ[X]) * 1 * hermite (m - 1) := by
    intro m
    rw [hermite_succ, derivative_hermite, nsmul_eq_mul]
    ring
  have h := eq_connectionSum_of_recurrence
    (R := ℤ[X]) (z := X) (c₁ := 0) (c₂ := 1)
    (P := fun m => (X : ℤ[X]) ^ m)
    (Q := hermite)
    (by simp) (by simp)
    (fun m => by simp [pow_succ'])
    hstep n
  simpa using h

/-- Pointwise form of the monomial-to-Hermite inversion formula over any commutative ring `R`. -/
theorem pow_eq_sum_hermite_aeval {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    x ^ n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k - 1)‼) • aeval x (hermite (n - 2 * k)) := by
  simpa only [map_pow, aeval_X, map_sum, map_nsmul] using
    congr_arg (aeval x) (X_pow_eq_sum_hermite n)

end TauCeti
