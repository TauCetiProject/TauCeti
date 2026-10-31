/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Int.Lemmas
import TauCeti.Analysis.SpecialFunctions.Log.AddMulLog
import TauCeti.NumberTheory.Padics.PadicValNat
import TauCeti.NumberTheory.SmoothNumbers

/-!
# Gaps between powers and between `S`-integers

A lower bound for linear forms in logarithms, in its multiplicative form
`|b ^ k * a ^ (-l) - 1| ≥ (exp 1 * max(1, |k|, |l|)) ^ (-C)` whenever the left-hand product is
not `1`, controls how close two powers `a ^ m` and `b ^ n` can be:

`|a ^ m - b ^ n| ≥ max(a ^ m, b ^ n) * (exp 1 * max(m, n)) ^ (-C)` whenever `a ^ m ≠ b ^ n`.

For `a, b ≥ 2` the left side is at least `2 ^ max(m, n)` times this factor, so the difference
`a ^ m - b ^ n` bounds the exponents explicitly, and for each nonzero `k` the exponential
equation `a ^ m - b ^ n = k` has only finitely many solutions.

The same argument applied to a quotient `x / y` of two positive integers composed of primes from
a finite set `S` gives the gap `y - x ≥ y * (exp 1 * (log y / log 2)) ^ (-C)` between distinct
such integers `x < y`. Here `x / y = ∏ p ∈ S, p ^ (v_p(x) - v_p(y))` and every exponent is at
most `log y / log 2` in absolute value.

The lower bounds for linear forms in logarithms are hypotheses. For positive algebraic bases
`a` and `b`, Baker's theory, for instance Matveev's theorem, supplies such a constant `C`
depending only on `a` and `b`; for a finite set `S` of primes it supplies one depending only
on `S`. The power-gap results themselves are stated for real bases and assume no
algebraicity.

## Main results

* `TauCeti.max_pow_mul_rpow_neg_le_abs_pow_sub_pow`: the lower bound for `|a ^ m - b ^ n|`.
* `TauCeti.max_le_of_pow_ne_pow`: for `a, b ≥ 2`, the explicit bound
  `max(m, n) ≤ 2 (log |a ^ m - b ^ n| + C) / log 2 + 2 (C / log 2) (log (2 C / log 2) - 1)`.
* `TauCeti.finite_setOf_pow_sub_pow_eq`: for `a, b ≥ 2` and `k ≠ 0`, the equation
  `a ^ m - b ^ n = k` has finitely many solutions `(m, n)`.
* `TauCeti.mul_rpow_neg_le_sub_of_mem_factoredNumbers`: the gap
  `y - x ≥ y * (exp 1 * (log y / log 2)) ^ (-C)` between `S`-integers `x < y`, and
  `TauCeti.div_mul_rpow_le_sub_of_mem_factoredNumbers`, the same gap in the form
  `y - x ≥ y / (c₁ * (log y) ^ C)` with `c₁ = (exp 1 / log 2) ^ C`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Corollary 5.5 and Theorem 5.6, pp. 88–89.
-/

public section

open Real

namespace TauCeti

variable {a b C : ℝ}

/-- **Gap between powers.** Let `a, b > 0` and suppose that `C` is a constant for a lower bound
of linear forms in the logarithms of `a` and `b`:
`|b ^ k * a ^ (-l) - 1| ≥ (exp 1 * max(1, |k|, |l|)) ^ (-C)` for all integers `k, l` with
`b ^ k * a ^ (-l) ≠ 1`. Then `|a ^ m - b ^ n| ≥ max(a ^ m, b ^ n) * (exp 1 * max(m, n)) ^ (-C)`
for all natural numbers `m, n` with `a ^ m ≠ b ^ n`. -/
theorem max_pow_mul_rpow_neg_le_abs_pow_sub_pow (ha : 0 < a) (hb : 0 < b)
    (hLB : ∀ k l : ℤ, b ^ k * a ^ (-l) ≠ 1 →
      (exp 1 * max 1 (max |(k : ℝ)| |(l : ℝ)|)) ^ (-C) ≤ |b ^ k * a ^ (-l) - 1|)
    {m n : ℕ} (h : a ^ m ≠ b ^ n) :
    max (a ^ m) (b ^ n) * (exp 1 * max (m : ℝ) n) ^ (-C) ≤ |a ^ m - b ^ n| := by
  have ham : 0 < a ^ m := pow_pos ha m
  have hbn : 0 < b ^ n := pow_pos hb n
  -- Since `(m, n) ≠ (0, 0)`, the factor `max(1, n, m)` of the hypothesis is `max(m, n)`.
  have hmn : max (1 : ℝ) (max n m) = max (m : ℝ) n := by
    have : 1 ≤ max m n := by
      by_contra! h0
      exact h (by simp [show m = 0 by omega, show n = 0 by omega])
    rw [max_comm (n : ℝ), max_eq_right (by rw [← Nat.cast_max]; exact_mod_cast this)]
  rw [max_mul_of_nonneg _ _ (by positivity)]
  refine max_le ?_ ?_
  · -- Divide by `a ^ m`: `b ^ n * a ^ (-m) - 1 = (b ^ n - a ^ m) / a ^ m`.
    have hq : b ^ (n : ℤ) * a ^ (-(m : ℤ)) - 1 = (b ^ n - a ^ m) / a ^ m := by
      rw [zpow_neg, zpow_natCast, zpow_natCast]
      field_simp
    have := hLB n m (sub_ne_zero.mp (hq ▸ div_ne_zero (sub_ne_zero.mpr h.symm) ham.ne'))
    rw [hq, abs_div, abs_of_pos ham, abs_sub_comm, le_div_iff₀ ham] at this
    simpa [hmn, mul_comm] using this
  · -- Divide by `b ^ n`: `b ^ (-n) * a ^ m - 1 = (a ^ m - b ^ n) / b ^ n`.
    have hq : b ^ (-(n : ℤ)) * a ^ (-(-(m : ℤ))) - 1 = (a ^ m - b ^ n) / b ^ n := by
      rw [neg_neg, zpow_neg, zpow_natCast, zpow_natCast]
      field_simp
    have := hLB (-n) (-m) (sub_ne_zero.mp (hq ▸ div_ne_zero (sub_ne_zero.mpr h) hbn.ne'))
    rw [hq, abs_div, abs_of_pos hbn, le_div_iff₀ hbn] at this
    simpa [hmn, mul_comm] using this

/-- **Exponent bound for the exponential equation `a ^ m - b ^ n = k`.** Let `a, b ≥ 2` and let
`C ≥ 0` be a constant for a lower bound of linear forms in the logarithms of `a` and `b` as in
`TauCeti.max_pow_mul_rpow_neg_le_abs_pow_sub_pow`. If `a ^ m ≠ b ^ n`, then
`max(m, n) ≤ 2 (log |a ^ m - b ^ n| + C) / log 2 + 2 (C / log 2) (log (2 C / log 2) - 1)`. -/
theorem max_le_of_pow_ne_pow (ha : 2 ≤ a) (hb : 2 ≤ b) (hC : 0 ≤ C)
    (hLB : ∀ k l : ℤ, b ^ k * a ^ (-l) ≠ 1 →
      (exp 1 * max 1 (max |(k : ℝ)| |(l : ℝ)|)) ^ (-C) ≤ |b ^ k * a ^ (-l) - 1|)
    {m n : ℕ} (h : a ^ m ≠ b ^ n) :
    max (m : ℝ) n ≤ 2 * (log |a ^ m - b ^ n| + C) / log 2 +
      2 * (C / log 2) * (log (2 * C / log 2) - 1) := by
  set N : ℝ := max (m : ℝ) n
  have hN : 1 ≤ N := by
    have : 1 ≤ max m n := by
      by_contra! h0
      exact h (by simp [show m = 0 by omega, show n = 0 by omega])
    rw [show N = (max m n : ℕ) by simp [N]]
    exact_mod_cast this
  have hgap := max_pow_mul_rpow_neg_le_abs_pow_sub_pow (by linarith) (by linarith) hLB h
  -- The larger of the two powers is at least `2 ^ N`.
  have h2N : (2 : ℝ) ^ N ≤ max (a ^ m) (b ^ n) := by
    rcases le_total m n with hmn | hmn
    · rw [show N = n by simp [N, hmn], rpow_natCast]
      exact (pow_le_pow_left₀ zero_le_two hb n).trans (le_max_right _ _)
    · rw [show N = m by simp [N, hmn], rpow_natCast]
      exact (pow_le_pow_left₀ zero_le_two ha m).trans (le_max_left _ _)
  have hE : 0 < exp 1 * N := by positivity
  have hlow : (2 : ℝ) ^ N * (exp 1 * N) ^ (-C) ≤ |a ^ m - b ^ n| :=
    (mul_le_mul_of_nonneg_right h2N (by positivity)).trans hgap
  -- Taking logarithms: `N log 2 - C (1 + log N) ≤ log |a ^ m - b ^ n|`.
  have hlog : N * log 2 - C * (1 + log N) ≤ log |a ^ m - b ^ n| := by
    have := log_le_log (by positivity) hlow
    rwa [log_mul (by positivity) (by positivity), log_rpow two_pos, log_rpow hE,
      log_mul (exp_pos 1).ne' (by positivity), log_exp, neg_mul, ← sub_eq_add_neg] at this
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have key : N ≤ (log |a ^ m - b ^ n| + C) / log 2 + C / log 2 * log N := by
    rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hlog2]
    linarith
  have := le_two_mul_add_of_le_add_mul_log (div_nonneg hC hlog2.le) (by positivity) key
  simpa only [mul_div_assoc] using this

/-- **Finiteness for the exponential equation `a ^ m - b ^ n = k`.** Let `a, b ≥ 2` and let
`C ≥ 0` be a constant for a lower bound of linear forms in the logarithms of `a` and `b` as in
`TauCeti.max_pow_mul_rpow_neg_le_abs_pow_sub_pow`. For every `k ≠ 0`, only finitely many pairs of
natural numbers `(m, n)` satisfy `a ^ m - b ^ n = k`. -/
theorem finite_setOf_pow_sub_pow_eq (ha : 2 ≤ a) (hb : 2 ≤ b) (hC : 0 ≤ C)
    (hLB : ∀ k l : ℤ, b ^ k * a ^ (-l) ≠ 1 →
      (exp 1 * max 1 (max |(k : ℝ)| |(l : ℝ)|)) ^ (-C) ≤ |b ^ k * a ^ (-l) - 1|)
    {k : ℝ} (hk : k ≠ 0) :
    {mn : ℕ × ℕ | a ^ mn.1 - b ^ mn.2 = k}.Finite := by
  set B := ⌊2 * (log |k| + C) / log 2 + 2 * (C / log 2) * (log (2 * C / log 2) - 1)⌋₊
  refine ((Set.finite_Iic B).prod (Set.finite_Iic B)).subset fun mn hmn ↦ ?_
  have hmn' : a ^ mn.1 - b ^ mn.2 = k := hmn
  have hle := max_le_of_pow_ne_pow ha hb hC hLB (sub_ne_zero.mp (hmn' ▸ hk))
  rw [hmn'] at hle
  have hB : max mn.1 mn.2 ≤ B := Nat.le_floor (by exact_mod_cast hle)
  exact ⟨le_of_max_le_left hB, le_of_max_le_right hB⟩

/-- **Gap between `S`-integers.** Let `S` be a finite set of primes and suppose that `C ≥ 0` is a
constant for a lower bound of linear forms in the logarithms of the primes of `S`:
`|∏ p ∈ S, p ^ e p - 1| ≥ (exp 1 * max(1, maxₚ |e p|)) ^ (-C)` for every integer exponent vector
`e` with `∏ p ∈ S, p ^ e p ≠ 1`. Then any positive integers `x < y` composed of primes from `S`
satisfy `y - x ≥ y * (exp 1 * (log y / log 2)) ^ (-C)`. -/
theorem mul_rpow_neg_le_sub_of_mem_factoredNumbers {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hC : 0 ≤ C)
    (hLB : ∀ e : S → ℤ, ∏ p : S, ((p : ℕ) : ℝ) ^ e p ≠ 1 →
      (exp 1 * max 1 ((Finset.univ.sup fun p ↦ (e p).natAbs : ℕ) : ℝ)) ^ (-C) ≤
        |∏ p : S, ((p : ℕ) : ℝ) ^ e p - 1|)
    {x y : ℕ} (hx : x ∈ Nat.factoredNumbers S) (hy : y ∈ Nat.factoredNumbers S) (hxy : x < y) :
    (y : ℝ) * (exp 1 * (log y / log 2)) ^ (-C) ≤ y - x := by
  have hx0 : x ≠ 0 := Nat.ne_zero_of_mem_factoredNumbers hx
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast (show 2 ≤ y by omega)
  have hypos : (0 : ℝ) < y := by linarith
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have hL : 1 ≤ log y / log 2 := by
    rw [one_le_div hlog2]
    exact log_le_log two_pos hy2
  -- The quotient `x / y` is the product of the `p ^ (v_p(x) - v_p(y))`.
  set e : S → ℤ := fun p ↦ (padicValNat p x : ℤ) - padicValNat p y
  have hprod : ∏ p : S, ((p : ℕ) : ℝ) ^ e p = x / y := by
    have hcast (z : ℕ) (hz : z ∈ Nat.factoredNumbers S) :
        ∏ p ∈ S, ((p : ℕ) : ℝ) ^ padicValNat p z = z := by
      exact_mod_cast prod_pow_padicValNat_eq_self_of_mem_factoredNumbers hS hz
    have hp0 (p : S) : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hS p p.2).ne_zero
    simp only [e, zpow_sub₀ (hp0 _), zpow_natCast]
    rw [Finset.prod_div_distrib, Finset.prod_coe_sort S (fun p ↦ ((p : ℕ) : ℝ) ^ padicValNat p x),
      Finset.prod_coe_sort S (fun p ↦ ((p : ℕ) : ℝ) ^ padicValNat p y), hcast x hx, hcast y hy]
  have hne : ∏ p : S, ((p : ℕ) : ℝ) ^ e p ≠ 1 := by
    rw [hprod, Ne, div_eq_one_iff_eq hypos.ne']
    exact_mod_cast hxy.ne
  -- Every exponent is at most `log y / log 2` in absolute value.
  have hsup : max 1 ((Finset.univ.sup fun p ↦ (e p).natAbs : ℕ) : ℝ) ≤ log y / log 2 := by
    refine max_le hL ((Nat.cast_le.mpr (Finset.sup_le fun p _ ↦
      Int.natAbs_coe_sub_coe_le_of_le (Nat.le_floor ?_) (Nat.le_floor ?_))).trans
      (Nat.floor_le (by positivity)))
    · refine (padicValNat_le_log_div_log_two p x).trans ?_
      gcongr
    · exact padicValNat_le_log_div_log_two p y
  have hq : |(x : ℝ) / y - 1| = (y - x) / y := by
    rw [div_sub_one hypos.ne', abs_div, abs_of_pos hypos,
      abs_of_neg (by linarith [(Nat.cast_lt (α := ℝ)).mpr hxy]), neg_sub]
  have hlb := hLB e hne
  rw [hprod, hq, le_div_iff₀ hypos] at hlb
  calc (y : ℝ) * (exp 1 * (log y / log 2)) ^ (-C)
      ≤ y * (exp 1 * max 1 ((Finset.univ.sup fun p ↦ (e p).natAbs : ℕ) : ℝ)) ^ (-C) := by
        gcongr ?_ * ?_
        exact rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by linarith)
    _ ≤ y - x := by linarith

/-- **Gap between `S`-integers**, in the form `y - x ≥ y / (c₁ * (log y) ^ C)` with
`c₁ = (exp 1 / log 2) ^ C`, under the hypotheses of
`TauCeti.mul_rpow_neg_le_sub_of_mem_factoredNumbers`. Applied to consecutive terms
`a (n - 1) < a n` of the increasing enumeration of the `S`-integers, it gives
`a n - a (n - 1) ≥ a n / (c₁ * (log (a n)) ^ C)`. -/
theorem div_mul_rpow_le_sub_of_mem_factoredNumbers {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hC : 0 ≤ C)
    (hLB : ∀ e : S → ℤ, ∏ p : S, ((p : ℕ) : ℝ) ^ e p ≠ 1 →
      (exp 1 * max 1 ((Finset.univ.sup fun p ↦ (e p).natAbs : ℕ) : ℝ)) ^ (-C) ≤
        |∏ p : S, ((p : ℕ) : ℝ) ^ e p - 1|)
    {x y : ℕ} (hx : x ∈ Nat.factoredNumbers S) (hy : y ∈ Nat.factoredNumbers S) (hxy : x < y) :
    (y : ℝ) / ((exp 1 / log 2) ^ C * log y ^ C) ≤ y - x := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  convert mul_rpow_neg_le_sub_of_mem_factoredNumbers hS hC hLB hx hy hxy using 1
  rw [div_eq_mul_inv, ← mul_rpow (by positivity) (log_nonneg hy1), ← rpow_neg (by positivity),
    div_mul_comm, mul_comm (exp 1)]

end TauCeti
