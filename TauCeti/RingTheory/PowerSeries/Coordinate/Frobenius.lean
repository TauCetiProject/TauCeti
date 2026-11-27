/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Coefficients of the inverse of a Frobenius binomial

Over a ring of characteristic `p`, the inverse series of `X + s X^q`, with `q = p^k > 1`,
has no terms outside degrees `q^m`. Its coefficient in degree `q^m` is
`(-s)^(1 + q + ⋯ + q^(m-1))`. The coefficient results also apply to a series given directly by
the equation `f + s f^q = X`. Comparing coefficients relates degree `q n` to degree `n` by
the rule `c ↦ -s * c^q`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] {k : ℕ} {s : R}
  {f : R⟦X⟧}

private theorem coeff_of_add_C_mul_pow_eq_X
    (hf : f + C s * f ^ p ^ k = X) (n : ℕ) :
    coeff n f = (if n = 1 then 1 else 0) -
      s * (if p ^ k ∣ n then coeff (n / p ^ k) f else 0) ^ p ^ k := by
  have h := congrArg (coeff (R := R) n) hf
  rw [map_add, coeff_C_mul, ← map_iterateFrobenius_expand p (Fact.out : p.Prime).ne_zero,
    coeff_map, coeff_expand, iterateFrobenius_def, coeff_X] at h
  exact eq_sub_of_add_eq h

/-- Coefficients in degrees `(p^k)^m` of a solution of `f + s f^(p^k) = X`. -/
theorem coeff_pow_of_add_C_mul_pow_eq_X (hk : k ≠ 0) (hf : f + C s * f ^ p ^ k = X)
    (m : ℕ) : coeff ((p ^ k) ^ m) f = (-s) ^ (∑ i ∈ Finset.range m, (p ^ k) ^ i) := by
  have hq : 1 < p ^ k := one_lt_pow₀ (Fact.out : p.Prime).one_lt hk
  induction m with
  | zero =>
    rw [pow_zero, coeff_of_add_C_mul_pow_eq_X hf]
    simp [Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) hq, zero_pow (by omega : p ^ k ≠ 0)]
  | succ m ih =>
    have hne : (p ^ k) ^ (m + 1) ≠ 1 := (one_lt_pow₀ hq (Nat.succ_ne_zero m)).ne'
    rw [coeff_of_add_C_mul_pow_eq_X hf, ite_eq_right hne, pow_succ',
      ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by omega), ih,
      zero_sub, ← neg_mul, ← pow_mul]
    rw [Finset.sum_range_succ', pow_zero, Finset.sum_congr rfl (fun i _ ↦ pow_succ' _ i),
      ← Finset.mul_sum, pow_add, pow_one]
    ring

/-- A solution with zero constant term has zero coefficient in every degree outside the
powers of `p^k`. -/
theorem coeff_eq_zero_of_add_C_mul_pow_eq_X (hk : k ≠ 0) (hf : f + C s * f ^ p ^ k = X)
    (hf₀ : constantCoeff f = 0) {n : ℕ} (hn : ∀ m : ℕ, n ≠ (p ^ k) ^ m) : coeff n f = 0 := by
  have hq : 1 < p ^ k := one_lt_pow₀ (Fact.out : p.Prime).one_lt hk
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
theorem inv_add_C_mul_pow_eq_X {R : Type*} [CommRing R] (φ : FormalCoordinate R) {s : R} {q : ℕ}
    (hφ : φ.toPowerSeries = X + C s * X ^ q) :
    φ⁻¹.toPowerSeries + C s * φ⁻¹.toPowerSeries ^ q = X := by
  have h := φ.toPowerSeries_mul_inv
  rwa [toPowerSeries_mul, hφ, subst_X_add_C_mul_X_pow φ⁻¹.hasSubst] at h

end TauCeti.FormalCoordinate
