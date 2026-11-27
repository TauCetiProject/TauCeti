/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Coefficients of the inverse of a Frobenius binomial

For a commutative ring of exponential characteristic `p` and `q = p^k > 1`, the inverse series
of `X + s X^q` has no terms outside degrees `q^m`. Its coefficient in degree `q^m` is
`(-s)^(1 + q + ⋯ + q^(m-1))`. The coefficient results also apply to a series given directly by
the equation `f + s f^q = X`. Comparing coefficients relates degree `q n` to degree `n` by
the rule `c ↦ -s * c^q`. When `s^q = s`, the coefficient in degree `q^m` is `(-s)^m`.
For `q = 1`, the equation is linear and forces all coefficients outside degree one to vanish.

In Anthropic's grh-lean (commit `72fead1`), `CMLattice.exists_formal_parameter` in
`grh-compact/src/New/Curve/FormalParameter.lean` gives the minus-sign equation after reduction.
The readable proof `New.CMLattice.norm_coeff_formalParam_of_eq_primeNorm_pow` in
`grh/src/New/Derivatives/Sharpness/OneCurve.lean` uses the coefficient at prime-norm powers.
Here coefficient comparison gives the recurrence for an arbitrary scalar.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p] {k : ℕ} {s : R}
  {f : R⟦X⟧}

/-- In exponential characteristic `p`, put `q = p^k`. For a solution of `f + C s * f^q = X`,
the coefficient in degree `n` is the degree-one term of `X` minus `s * (coeff (n/q) f)^q`
when `q ∣ n`. When `q ∤ n` the Frobenius term vanishes. -/
theorem coeff_of_add_C_mul_pow_eq_X
    (hf : f + C s * f ^ p ^ k = X) (n : ℕ) :
    coeff n f = (if n = 1 then 1 else 0) -
      s * (if p ^ k ∣ n then coeff (n / p ^ k) f else 0) ^ p ^ k := by
  have h := congrArg (coeff (R := R) n) hf
  rw [map_add, coeff_C_mul, ← map_iterateFrobenius_expand p (expChar_ne_zero R p),
    coeff_map, coeff_expand, iterateFrobenius_def, coeff_X] at h
  exact eq_sub_of_add_eq h

/-- In exponential characteristic `p`, let `q = p^k > 1`. A solution of `f + C s * f^q = X`
has coefficient `(-s)^(1 + q + ⋯ + q^(m-1))` in degree `q^m`, with empty sum for `m = 0`. -/
theorem coeff_pow_of_add_C_mul_pow_eq_X (hq : 1 < p ^ k) (hf : f + C s * f ^ p ^ k = X)
    (m : ℕ) : coeff ((p ^ k) ^ m) f = (-s) ^ (∑ i ∈ Finset.range m, (p ^ k) ^ i) := by
  induction m with
  | zero =>
    rw [pow_zero, coeff_of_add_C_mul_pow_eq_X hf]
    simp [Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) hq, zero_pow (by omega : p ^ k ≠ 0)]
  | succ m ih =>
    have hne : (p ^ k) ^ (m + 1) ≠ 1 := (one_lt_pow₀ hq (Nat.succ_ne_zero m)).ne'
    have hstep : coeff ((p ^ k) ^ (m + 1)) f = -s * coeff ((p ^ k) ^ m) f ^ p ^ k := by
      rw [coeff_of_add_C_mul_pow_eq_X hf, ite_eq_right hne, pow_succ']
      simp [Nat.mul_div_cancel_left _ (by omega : 0 < p ^ k), neg_mul]
    rw [hstep, ih, geom_sum_succ, pow_succ', Nat.mul_comm (p ^ k), pow_mul]

/-- In exponential characteristic `p`, put `q = p^k > 1`. If `s^q = s`, a solution of
`f + C s * f^q = X` has coefficient `(-s)^m` in degree `q^m`, giving the signs for `s = ±1`. -/
theorem coeff_pow_of_add_C_mul_pow_eq_X_of_pow_eq_self (hq : 1 < p ^ k) (hs : s ^ p ^ k = s)
    (hf : f + C s * f ^ p ^ k = X) (m : ℕ) : coeff ((p ^ k) ^ m) f = (-s) ^ m := by
  have hneg : (-s) ^ p ^ k = -s := by
    rw [← iterateFrobenius_def (R := R) p k (-s), map_neg, iterateFrobenius_def, hs]
  have hiter (i : ℕ) : (-s) ^ (p ^ k) ^ i = -s := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_mul, ih, hneg]
  rw [coeff_pow_of_add_C_mul_pow_eq_X hq hf]
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_add, ih, hiter, pow_succ]

/-- In exponential characteristic `p`, put `q = p^k`. A solution of `f + C s * f^q = X` with
zero constant term has zero coefficient outside the powers of `q`. For `q = 1`, the equation
forces the degree-one coefficient to be an inverse of `1 + s`. -/
theorem coeff_eq_zero_of_add_C_mul_pow_eq_X (hf : f + C s * f ^ p ^ k = X)
    (hf₀ : constantCoeff f = 0) {n : ℕ} (hn : ∀ m : ℕ, n ≠ (p ^ k) ^ m) : coeff n f = 0 := by
  by_cases hq₁ : p ^ k = 1
  · have hlinear (i : ℕ) : (1 + s) * coeff i f = if i = 1 then 1 else 0 := by
      simpa only [hq₁, pow_one, map_add, coeff_C_mul, coeff_X, add_mul, one_mul]
        using congrArg (coeff (R := R) i) hf
    have hone : (1 + s) * coeff 1 f = 1 := by simpa using hlinear 1
    have hn₁ : n ≠ 1 := by simpa using hn 0
    have hzero : (1 + s) * coeff n f = 0 := by simpa only [ite_eq_right hn₁] using hlinear n
    calc
      coeff n f = ((1 + s) * coeff 1 f) * coeff n f := by rw [hone, one_mul]
      _ = coeff 1 f * ((1 + s) * coeff n f) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  have hq : 1 < p ^ k := by
    have := pow_ne_zero k (expChar_ne_zero R p)
    omega
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain rfl | hn₀ := Nat.eq_zero_or_pos n
    · simpa using hf₀
    have hn₁ : n ≠ 1 := by simpa using hn 0
    rw [coeff_of_add_C_mul_pow_eq_X hf, ite_eq_right hn₁]
    by_cases hdiv : p ^ k ∣ n
    · obtain ⟨r, rfl⟩ := hdiv
      have hr : 0 < r := Nat.pos_of_mul_pos_left hn₀
      have hlt : r < p ^ k * r := by simpa using Nat.mul_lt_mul_of_pos_right hq hr
      have hoff (m : ℕ) : r ≠ (p ^ k) ^ m := fun e ↦ hn (m + 1) (by rw [pow_succ', e])
      simp [Nat.mul_div_cancel_left _ (by omega : 0 < p ^ k), ih r hlt hoff,
        zero_pow (by omega : p ^ k ≠ 0)]
    · simp [hdiv, zero_pow (by omega : p ^ k ≠ 0)]

end PowerSeries

namespace TauCeti.FormalCoordinate

open PowerSeries

/-- The inverse of a coordinate represented by `X + s X^q` satisfies the binomial equation
used by the coefficient formulas. -/
theorem toPowerSeries_inv_add_C_mul_pow_eq_X {R : Type*} [CommRing R] (φ : FormalCoordinate R)
    {s : R} {q : ℕ}
    (hφ : φ.toPowerSeries = X + C s * X ^ q) :
    φ⁻¹.toPowerSeries + C s * φ⁻¹.toPowerSeries ^ q = X := by
  have h := φ.toPowerSeries_mul_inv
  rwa [toPowerSeries_mul, hφ, subst_X_add_C_mul_X_pow φ⁻¹.hasSubst] at h

end TauCeti.FormalCoordinate
