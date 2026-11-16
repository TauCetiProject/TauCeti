/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Fixed-ratio large-parameter asymptotics of the lower incomplete Gamma function

For a fixed ratio `0 < r < 1` and large shape parameter `a` in a closed sector
`|arg a| ≤ π / 2 - δ` (`δ > 0`), the lower incomplete Gamma function `γ(a, r a)` satisfies the
asymptotic expansion (DLMF 8.11.6)
`(a - r a) (r a)^{-a} e^{r a} γ(a, r a) ~ ∑_{k ≥ 0} (-1)^k b_k(r) / ((1 - r)^{2k} a^k)`,
where `b_k` is the polynomial sequence defined by `b_0(X) = 1` and
`b_{k+1}(X) = X (1 - X) b_k'(X) + (2k + 1) X b_k(X)` (DLMF 8.11.8–8.11.9; second-order Eulerian
polynomials).

After substituting `s = 1 - x` in `Complex.lowerIncompleteGamma_eq_integral`, the scaled function
`(r a)^{-a} e^{r a} γ(a, r a)` becomes `∫₀¹ (1 - x)^{a - 1} e^{a r x} dx`. Writing
`1 - r + r x = 1 - r (1 - x)`, repeated integration by parts against
`∂_x ((1 - x)^a e^{a r x}) = -a (1 - r (1 - x)) (1 - x)^{a - 1} e^{a r x}` acts on functions of
`t = r (1 - x)` as `-t d/dt`, reproducing the exact recurrence of `b_k` and yielding an explicit
`n`-term identity with integral remainder on the entire open right half-plane `0 < Re a`. Since the
coefficients of `b_n` are nonnegative, on the positive real axis the series is strictly enveloping:
each remainder has sign `(-1)^n` and magnitude at most the first neglected term, which immediately
dominates the complex remainder on `0 < Re a` by `b_n(r) / ((1 - r)^{2n + 1} ‖a‖^n Re a)`.

## Main definitions

* `TauCeti.incompleteGammaRatioPoly` — the polynomial sequence `b_k ∈ ℤ[X]` of DLMF 8.11.8–8.11.9.

## Main results

* `TauCeti.incompleteGammaRatioPoly_one`, `TauCeti.incompleteGammaRatioPoly_two`,
  `TauCeti.incompleteGammaRatioPoly_three`, `TauCeti.incompleteGammaRatioPoly_four`: the explicit
  polynomials of DLMF 8.11.9.
* `TauCeti.coeff_incompleteGammaRatioPoly_succ_succ`,
  `TauCeti.natDegree_incompleteGammaRatioPoly`, `TauCeti.eval_one_incompleteGammaRatioPoly`,
  `TauCeti.aeval_incompleteGammaRatioPoly_pos`: the second-order Eulerian coefficient recurrence,
  degree `k`, value `(2k - 1)‼` at `1`, and strict positivity on `(0, ∞)`.
* `Complex.mul_lowerIncompleteGamma_mul_eq_sum_add_integral`: exact `n`-term integration-by-parts
  identity for `(r a)^{-a} e^{r a} γ(a, r a)` on `0 < Re a`.
* `Complex.norm_lowerIncompleteGamma_fixedRatio_sub_sum_le`,
  `Complex.norm_lowerIncompleteGamma_fixedRatio_sub_sum_le_of_abs_arg_le`: explicit remainder
  bounds on `0 < Re a` and on the sector `|arg a| ≤ π / 2 - δ`.
* `Complex.isBigO_sub_mul_lowerIncompleteGamma_fixedRatio`,
  `Complex.isBigO_cpow_one_sub_mul_lowerIncompleteGamma_fixedRatio`: DLMF 8.11.6 to arbitrary
  order `n` in the scale `(‖a‖ ^ n)⁻¹` along
  `Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ π / 2 - δ}`.
* `Complex.lowerIncompleteGamma_fixedRatio_isEquivalent`,
  `Complex.regularizedGamma_fixedRatio_isEquivalent`: leading sectorial asymptotic equivalences
  for `γ(a, r a)` and `P(a, r a)` (combining DLMF 8.11.6 with sectorial Stirling).
* `TauCeti.mul_lowerIncompleteGamma_fixedRatio_sub_sum_nonneg`,
  `TauCeti.mul_lowerIncompleteGamma_fixedRatio_sub_sum_le`,
  `TauCeti.lowerIncompleteGamma_fixedRatio_bounds`,
  `TauCeti.isBigO_sub_mul_lowerIncompleteGamma_fixedRatio`,
  `TauCeti.regularizedGamma_fixedRatio_isEquivalent`,
  `TauCeti.tendsto_regularizedGamma_fixedRatio_atTop`: enveloping inequalities, two-sided bounds,
  asymptotic expansions, and tail decay along the positive real axis.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(ii)](https://dlmf.nist.gov/8.11#ii),
  Eqs. 8.11.6, 8.11.8, and 8.11.9.
* F. G. Tricomi, *Asymptotische Eigenschaften der unvollständigen Gammafunktion*,
  Math. Z. **53** (1950), 136–148.
* N. M. Temme, *Special Functions: An Introduction to the Classical Functions of Mathematical
  Physics*, Wiley, 1996, §11.2.1.
-/

public section

noncomputable section

open Asymptotics Bornology Filter Finset MeasureTheory Polynomial Set
open scoped Interval Nat Topology

namespace TauCeti

/-! ### The fixed-ratio polynomials `b_k` (DLMF 8.11.8–8.11.9) -/

/-- The polynomial sequence `b_k ∈ ℤ[X]` governing the fixed-ratio large-`a` asymptotic expansion
of the incomplete Gamma functions (DLMF 8.11.8–8.11.9):
`b₀(X) = 1` and `b_{k+1}(X) = X (1 - X) b_k'(X) + (2k + 1) X b_k(X)`.
For `k ≥ 1`, its coefficients are the second-order Eulerian numbers. -/
def incompleteGammaRatioPoly : ℕ → ℤ[X]
  | 0 => 1
  | k + 1 =>
      X * (1 - X) * (incompleteGammaRatioPoly k).derivative +
        C (2 * (k : ℤ) + 1) * X * incompleteGammaRatioPoly k

/-- DLMF 8.11.9: `b₀(X) = 1`. -/
@[simp]
theorem incompleteGammaRatioPoly_zero : incompleteGammaRatioPoly 0 = 1 :=
  (rfl)

/-- DLMF 8.11.8: `b_{k+1}(X) = X (1 - X) b_k'(X) + (2k + 1) X b_k(X)`. -/
theorem incompleteGammaRatioPoly_succ (k : ℕ) :
    incompleteGammaRatioPoly (k + 1) =
      X * (1 - X) * (incompleteGammaRatioPoly k).derivative +
        C (2 * (k : ℤ) + 1) * X * incompleteGammaRatioPoly k :=
  (rfl)

/-- DLMF 8.11.9: `b₁(X) = X`. -/
@[simp]
theorem incompleteGammaRatioPoly_one : incompleteGammaRatioPoly 1 = X := by
  simp [incompleteGammaRatioPoly_succ]

/-- DLMF 8.11.9: `b₂(X) = X + 2 X²`. -/
theorem incompleteGammaRatioPoly_two : incompleteGammaRatioPoly 2 = X + 2 * X ^ 2 := by
  rw [incompleteGammaRatioPoly_succ, incompleteGammaRatioPoly_one, derivative_X]
  simp only [Nat.cast_one, mul_one, C_add, C_1, map_ofNat]
  ring

/-- DLMF 8.11.9: `b₃(X) = X + 8 X² + 6 X³`. -/
theorem incompleteGammaRatioPoly_three :
    incompleteGammaRatioPoly 3 = X + 8 * X ^ 2 + 6 * X ^ 3 := by
  rw [incompleteGammaRatioPoly_succ, incompleteGammaRatioPoly_two]
  simp only [derivative_add, derivative_X, derivative_mul, derivative_ofNat, zero_mul, zero_add,
    derivative_X_pow, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, C_add, C_mul, C_1, map_ofNat]
  ring

/-- DLMF 8.11.9: `b₄(X) = X + 22 X² + 58 X³ + 24 X⁴`. -/
theorem incompleteGammaRatioPoly_four :
    incompleteGammaRatioPoly 4 = X + 22 * X ^ 2 + 58 * X ^ 3 + 24 * X ^ 4 := by
  rw [incompleteGammaRatioPoly_succ, incompleteGammaRatioPoly_three]
  simp only [derivative_add, derivative_X, derivative_mul, derivative_ofNat, zero_mul, zero_add,
    derivative_X_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one, C_add, C_mul, C_1, map_ofNat]
  ring

/-- For `k ≥ 1`, `b_k` has zero constant term. -/
@[simp]
theorem eval_zero_incompleteGammaRatioPoly_succ (k : ℕ) :
    (incompleteGammaRatioPoly (k + 1)).eval 0 = 0 := by
  simp [incompleteGammaRatioPoly_succ]

/-- Evaluating `b_k` at `0` gives `1` for `k = 0` and `0` for `k ≥ 1`. -/
theorem eval_zero_incompleteGammaRatioPoly (k : ℕ) :
    (incompleteGammaRatioPoly k).eval 0 = if k = 0 then 1 else 0 := by
  cases k <;> simp

/-- Evaluating `b_k` at `1` gives the odd double factorial `(2k - 1)‼`. -/
@[simp]
theorem eval_one_incompleteGammaRatioPoly (k : ℕ) :
    (incompleteGammaRatioPoly k).eval 1 = ((2 * k - 1)‼ : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [incompleteGammaRatioPoly_succ]
    simp only [eval_add, eval_mul, eval_X, eval_sub, eval_one, sub_self, mul_zero, zero_mul,
      zero_add, eval_C, mul_one, ih]
    cases k with
    | zero => simp
    | succ m =>
      have hsub : 2 * (m + 2) - 1 = (2 * (m + 1) - 1) + 2 := by omega
      have hodd : (2 * ((m + 1 : ℕ) : ℤ) + 1) = ((2 * (m + 1) + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hsub, Nat.doubleFactorial_add_two, Nat.cast_mul, hodd]
      congr 2

/-- Over any commutative ring, `b_{k+1}(0) = 0`. -/
@[simp]
theorem aeval_zero_incompleteGammaRatioPoly_succ {R : Type*} [CommRing R] (k : ℕ) :
    aeval (0 : R) (incompleteGammaRatioPoly (k + 1)) = 0 := by
  simp [incompleteGammaRatioPoly_succ]

/-- Over any commutative ring, `b_k(1) = (2k - 1)‼`. -/
@[simp]
theorem aeval_one_incompleteGammaRatioPoly {R : Type*} [CommRing R] (k : ℕ) :
    aeval (1 : R) (incompleteGammaRatioPoly k) = ((2 * k - 1)‼ : R) := by
  simpa using aeval_algebraMap_apply_eq_algebraMap_eval (A := R) (1 : ℤ)
    (incompleteGammaRatioPoly k)

private theorem coeff_X_mul_derivative (p : ℤ[X]) (j : ℕ) :
    (X * p.derivative).coeff j = (j : ℤ) * p.coeff j := by
  cases j with
  | zero => simp
  | succ i =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- For `k ≥ 1`, the constant coefficient of `b_k` vanishes. -/
@[simp]
theorem coeff_incompleteGammaRatioPoly_zero_right (k : ℕ) :
    (incompleteGammaRatioPoly (k + 1)).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_zero_incompleteGammaRatioPoly_succ]

/-- Second-order Eulerian recurrence on the coefficients of `b_k`:
`[X^{i+1}] b_{k+1} = (i + 1) [X^{i+1}] b_k + (2k + 1 - i) [X^i] b_k`. -/
theorem coeff_incompleteGammaRatioPoly_succ_succ (k i : ℕ) :
    (incompleteGammaRatioPoly (k + 1)).coeff (i + 1) =
      (i + 1 : ℤ) * (incompleteGammaRatioPoly k).coeff (i + 1) +
        (2 * (k : ℤ) + 1 - i) * (incompleteGammaRatioPoly k).coeff i := by
  have hrew : incompleteGammaRatioPoly (k + 1) =
      X * (incompleteGammaRatioPoly k).derivative +
        X * (C (2 * (k : ℤ) + 1) * incompleteGammaRatioPoly k -
          X * (incompleteGammaRatioPoly k).derivative) := by
    rw [incompleteGammaRatioPoly_succ]
    ring
  rw [hrew, coeff_add, coeff_X_mul_derivative, coeff_X_mul, coeff_sub, coeff_C_mul,
    coeff_X_mul_derivative]
  push_cast
  ring

/-- All coefficients of `b_k` strictly above degree `k` vanish. -/
theorem coeff_incompleteGammaRatioPoly_eq_zero_of_lt {k j : ℕ} (hkj : k < j) :
    (incompleteGammaRatioPoly k).coeff j = 0 := by
  induction k generalizing j with
  | zero =>
    rw [incompleteGammaRatioPoly_zero, coeff_one]
    simp [hkj.ne']
  | succ k ih =>
    cases j with
    | zero => omega
    | succ i =>
      rw [coeff_incompleteGammaRatioPoly_succ_succ, ih (by omega), ih (by omega)]
      ring

/-- The degree-`k` coefficient of `b_k` is `k!`. -/
@[simp]
theorem coeff_incompleteGammaRatioPoly_self (k : ℕ) :
    (incompleteGammaRatioPoly k).coeff k = (k ! : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [coeff_incompleteGammaRatioPoly_succ_succ,
      coeff_incompleteGammaRatioPoly_eq_zero_of_lt (Nat.lt_succ_self k), ih, Nat.factorial_succ]
    push_cast
    ring

/-- `b_k` has exact degree `k`. -/
@[simp]
theorem natDegree_incompleteGammaRatioPoly (k : ℕ) :
    (incompleteGammaRatioPoly k).natDegree = k := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr fun j hj =>
    coeff_incompleteGammaRatioPoly_eq_zero_of_lt hj) ?_
  rw [coeff_incompleteGammaRatioPoly_self]
  exact_mod_cast Nat.factorial_ne_zero k

/-- The leading coefficient of `b_k` is `k!`. -/
@[simp]
theorem leadingCoeff_incompleteGammaRatioPoly (k : ℕ) :
    (incompleteGammaRatioPoly k).leadingCoeff = (k ! : ℤ) := by
  rw [leadingCoeff, natDegree_incompleteGammaRatioPoly, coeff_incompleteGammaRatioPoly_self]

/-- Every coefficient of `b_k` is nonnegative. -/
theorem coeff_incompleteGammaRatioPoly_nonneg (k j : ℕ) :
    0 ≤ (incompleteGammaRatioPoly k).coeff j := by
  induction k generalizing j with
  | zero =>
    rw [incompleteGammaRatioPoly_zero, coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    cases j with
    | zero => simp
    | succ i =>
      rcases lt_or_ge k i with hki | hik
      · rw [coeff_incompleteGammaRatioPoly_eq_zero_of_lt (Nat.succ_lt_succ hki)]
      · rw [coeff_incompleteGammaRatioPoly_succ_succ]
        refine add_nonneg (mul_nonneg (by positivity) (ih (i + 1)))
          (mul_nonneg ?_ (ih i))
        omega

/-- For `1 ≤ j ≤ k`, the `j`-th coefficient of `b_k` is strictly positive. -/
theorem coeff_incompleteGammaRatioPoly_pos {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    0 < (incompleteGammaRatioPoly k).coeff j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero => omega
    | succ i =>
      rw [coeff_incompleteGammaRatioPoly_succ_succ]
      rcases eq_or_lt_of_le hjk with heq | hlt
      · obtain rfl : i = k := by omega
        rw [coeff_incompleteGammaRatioPoly_eq_zero_of_lt (Nat.lt_succ_self i),
          coeff_incompleteGammaRatioPoly_self]
        have hfac : (0 : ℤ) < (i ! : ℤ) := by exact_mod_cast Nat.factorial_pos i
        have hmul : (0 : ℤ) < 2 * (i : ℤ) + 1 - i := by omega
        linarith [mul_pos hmul hfac]
      · have hpos : 0 < (incompleteGammaRatioPoly k).coeff (i + 1) := ih (by omega) (by omega)
        have hnn : 0 ≤ (2 * (k : ℤ) + 1 - i) * (incompleteGammaRatioPoly k).coeff i :=
          mul_nonneg (by omega) (coeff_incompleteGammaRatioPoly_nonneg k i)
        have h1 : (0 : ℤ) < (i + 1 : ℤ) * (incompleteGammaRatioPoly k).coeff (i + 1) :=
          mul_pos (by positivity) hpos
        linarith

/-- `b_k(x) ≥ 0` for `x ≥ 0` in any strict ordered commutative ring. -/
theorem aeval_incompleteGammaRatioPoly_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : R} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ aeval x (incompleteGammaRatioPoly k) := by
  rw [aeval_eq_sum_range]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Algebra.smul_def, eq_intCast]
  have hc : (0 : R) ≤ ((incompleteGammaRatioPoly k).coeff i : R) := by
    exact_mod_cast coeff_incompleteGammaRatioPoly_nonneg k i
  exact mul_nonneg hc (pow_nonneg hx i)

/-- `b_k(x) > 0` for `x > 0` in any strict ordered commutative ring. -/
theorem aeval_incompleteGammaRatioPoly_pos {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : R} (hx : 0 < x) (k : ℕ) :
    0 < aeval x (incompleteGammaRatioPoly k) := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_incompleteGammaRatioPoly k).le)]
  refine Finset.sum_pos' (fun i _ => ?_) ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), ?_⟩
  · rw [Algebra.smul_def, eq_intCast]
    have hc : (0 : R) ≤ ((incompleteGammaRatioPoly k).coeff i : R) := by
      exact_mod_cast coeff_incompleteGammaRatioPoly_nonneg k i
    exact mul_nonneg hc (pow_nonneg hx.le i)
  · rw [Algebra.smul_def, eq_intCast, coeff_incompleteGammaRatioPoly_self, Int.cast_natCast]
    exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) (pow_pos hx k)

/-! ### Differential recurrence of the rational fixed-ratio amplitudes -/

/-- Differentiating `(-1)^k b_k(t) / (1 - t)^{2k + 1}` away from `t = 1`. -/
theorem hasDerivAt_incompleteGammaRatioPoly_div (k : ℕ) {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt
      (fun y : ℝ => (-1 : ℝ) ^ k * aeval y (incompleteGammaRatioPoly k) / (1 - y) ^ (2 * k + 1))
      ((-1 : ℝ) ^ k *
        ((1 - t) * aeval t (incompleteGammaRatioPoly k).derivative +
          (2 * (k : ℝ) + 1) * aeval t (incompleteGammaRatioPoly k)) /
        (1 - t) ^ (2 * k + 2)) t := by
  have h1t : 1 - t ≠ 0 := sub_ne_zero.mpr ht.symm
  have hd := (((incompleteGammaRatioPoly k).hasDerivAt_aeval t).const_mul ((-1 : ℝ) ^ k)).div
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow (2 * k + 1))
    (pow_ne_zero _ h1t)
  refine hd.congr_deriv ?_
  dsimp only [id_eq, Pi.sub_apply, Pi.pow_apply]
  have hpow : ((1 - t) ^ (2 * k + 1)) ^ 2 = (1 - t) ^ (2 * k) * (1 - t) ^ (2 * k + 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [Nat.add_sub_cancel, hpow]
  push_cast
  field_simp [h1t]
  ring

/-- Applying `-t d/dt` to `(-1)^k b_k(t) / (1 - t)^{2k + 1}` produces
`(-1)^{k+1} b_{k+1}(t) / (1 - t)^{2k + 2}`. -/
theorem neg_mul_deriv_incompleteGammaRatioPoly_div (k : ℕ) (t : ℝ) :
    -t * ((-1 : ℝ) ^ k *
        ((1 - t) * aeval t (incompleteGammaRatioPoly k).derivative +
          (2 * (k : ℝ) + 1) * aeval t (incompleteGammaRatioPoly k)) /
        (1 - t) ^ (2 * k + 2)) =
      (-1 : ℝ) ^ (k + 1) * aeval t (incompleteGammaRatioPoly (k + 1)) /
        (1 - t) ^ (2 * k + 2) := by
  have hpoly : aeval t (incompleteGammaRatioPoly (k + 1)) =
      t * ((1 - t) * aeval t (incompleteGammaRatioPoly k).derivative +
        (2 * (k : ℝ) + 1) * aeval t (incompleteGammaRatioPoly k)) := by
    rw [incompleteGammaRatioPoly_succ]
    simp only [map_add, map_mul, map_sub, map_one, map_ofNat, map_natCast, aeval_X]
    ring
  rw [hpoly, pow_succ (-1 : ℝ)]
  ring

end TauCeti

namespace Complex

/-! ### Exact integration-by-parts expansion on the open right half-plane -/

private theorem one_sub_mul_pos {r x : ℝ} (hr1 : r < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < 1 - r * (1 - x) := by
  have h1 : 0 ≤ (1 - r) * (1 - x) := mul_nonneg (sub_pos.mpr hr1).le (sub_nonneg.mpr hx.2)
  rcases eq_or_lt_of_le hx.2 with rfl | hxlt
  · norm_num
  · linarith [hx.1, mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hxlt)]

private theorem aeval_ofReal_intPoly (p : ℤ[X]) (r : ℝ) :
    aeval (r : ℂ) p = (aeval r p : ℂ) :=
  aeval_algHom_apply Complex.ofRealHom.toIntAlgHom r p

/-- Auxiliary `k`-th remainder integral `∫₀¹ f_k(r, x) (1 - x)^{a - 1} e^{a r x} dx` on `[0, 1]`. -/
private def fixedRatioRemIntegral (a : ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    (((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
        (1 - r * (1 - x)) ^ (2 * k) : ℝ) : ℂ) *
      ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)

private theorem intervalIntegrable_one_sub_cpow {p : ℂ} (hp : -1 < p.re) :
    IntervalIntegrable (fun x : ℝ => ((1 - x : ℝ) : ℂ) ^ p) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_cpow' (a := (1 : ℝ)) (b := 0) hp).comp_sub_left 1
  simpa using h

private theorem continuousOn_ratio_div {r : ℝ} (hr1 : r < 1) (p : ℤ[X]) (m : ℕ) :
    ContinuousOn
      (fun x : ℝ => aeval (r * (1 - x)) p / (1 - r * (1 - x)) ^ m) [[0, 1]] := by
  rw [Set.uIcc_of_le zero_le_one]
  refine ContinuousOn.div ?_ ?_ fun x hx => pow_ne_zero _ (one_sub_mul_pos hr1 hx).ne'
  · exact (p.continuous_aeval.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  · exact ((continuous_const.sub
      (continuous_const.mul (continuous_const.sub continuous_id))).pow m).continuousOn

private theorem hasDerivAt_one_sub_cpow_mul_cexp {a : ℂ} (ha0 : a ≠ 0) (r : ℝ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ) ^ a * cexp (a * r * y))
      (-a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)) x := by
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hpow1 : HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ) ^ a)
      (-a * ((1 - x : ℝ) : ℂ) ^ (a - 1)) x := by
    have hout := _root_.hasDerivAt_ofReal_cpow_const hx1.ne' ha0
    have hin := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    exact (hout.scomp x hin).congr_deriv (by simp)
  have hexp1 : HasDerivAt (fun y : ℝ => cexp (a * r * y))
      (a * r * cexp (a * r * x)) x := by
    have hlin : HasDerivAt (fun z : ℂ => a * r * z) (a * r * 1) (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_mul (a * r)
    have hc := ((Complex.hasDerivAt_exp (a * r * (x : ℂ))).comp (x : ℂ) hlin).comp_ofReal
    exact hc.congr_deriv (by ring)
  refine (hpow1.mul hexp1).congr_deriv ?_
  have hsplit : ((1 - x : ℝ) : ℂ) ^ a = ((1 - x : ℝ) : ℂ) ^ (a - 1) * ((1 - x : ℝ) : ℂ) := by
    conv_rhs => enter [2]; rw [← cpow_one ((1 - x : ℝ) : ℂ)]
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr hx1.ne'), sub_add_cancel]
  rw [hsplit]
  push_cast
  ring

/-- Derivative of the real rational kernel `g_k(r, x) = (-1)^k b_k(t) / (1 - t)^{2k + 1}` along
`t = r (1 - x)`, lifted to `ℂ`. -/
private def ratioKernelDeriv (r : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  -r * ((-1 : ℝ) ^ k *
    ((1 - r * (1 - x)) * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k).derivative +
      (2 * (k : ℝ) + 1) * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k)) /
    (1 - r * (1 - x)) ^ (2 * k + 2))

private theorem continuousOn_ratioKernelDeriv {r : ℝ} (hr1 : r < 1) (k : ℕ) :
    ContinuousOn (fun x : ℝ => (ratioKernelDeriv r k x : ℂ)) [[0, 1]] := by
  rw [Set.uIcc_of_le zero_le_one]
  refine continuous_ofReal.comp_continuousOn (continuousOn_const.mul (ContinuousOn.div ?_ ?_
    fun x hx => pow_ne_zero _ (one_sub_mul_pos hr1 hx).ne'))
  · refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · exact ((continuous_const.sub (continuous_const.mul
        (continuous_const.sub continuous_id))).mul
        ((TauCeti.incompleteGammaRatioPoly k).derivative.continuous_aeval.comp
          (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn
    · exact (continuous_const.mul ((TauCeti.incompleteGammaRatioPoly k).continuous_aeval.comp
        (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn
  · exact ((continuous_const.sub
      (continuous_const.mul (continuous_const.sub continuous_id))).pow _).continuousOn

private theorem integral_ratioKernel_mul_deriv (a : ℂ) {r : ℝ} (hr1 : r < 1) (k : ℕ) :
    (∫ x in (0 : ℝ)..1,
      (((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
          (1 - r * (1 - x)) ^ (2 * k + 1) : ℝ) : ℂ) *
        (-a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x))) =
      -a * fixedRatioRemIntegral a r k := by
  rw [fixedRatioRemIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with x hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hden : 1 - r * (1 - x) ≠ 0 := (one_sub_mul_pos hr1 (Ioc_subset_Icc_self hx)).ne'
  have hreal : ((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
        (1 - r * (1 - x)) ^ (2 * k + 1)) * (1 - r * (1 - x)) =
      (-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
        (1 - r * (1 - x)) ^ (2 * k) := by
    rw [pow_succ (1 - r * (1 - x)) (2 * k)]
    field_simp [hden]
  calc _
    _ = -a * (((((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
          (1 - r * (1 - x)) ^ (2 * k + 1)) * (1 - r * (1 - x)) : ℝ) : ℂ) *
          ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)) := by
      push_cast; ring
    _ = _ := by rw [hreal]

private theorem integral_ratioKernelDeriv_mul (a : ℂ) (r : ℝ) (k : ℕ) :
    (∫ x in (0 : ℝ)..1,
      (ratioKernelDeriv r k x : ℂ) * (((1 - x : ℝ) : ℂ) ^ a * cexp (a * r * x))) =
      fixedRatioRemIntegral a r (k + 1) := by
  rw [fixedRatioRemIntegral]
  refine intervalIntegral.integral_congr_ae ?_
  have hno1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by simp [ae_iff]
  filter_upwards [hno1] with x hxne hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hxpos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hxne)
  have hsplit : ((1 - x : ℝ) : ℂ) ^ a = ((1 - x : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) := by
    conv_rhs => enter [1]; rw [← cpow_one ((1 - x : ℝ) : ℂ)]
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr hxpos.ne')]
    congr 1; ring
  have hreal : ratioKernelDeriv r k x * (1 - x) =
      (-1 : ℝ) ^ (k + 1) * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly (k + 1)) /
        (1 - r * (1 - x)) ^ (2 * (k + 1)) := by
    calc ratioKernelDeriv r k x * (1 - x)
      _ = -(r * (1 - x)) * ((-1 : ℝ) ^ k *
          ((1 - r * (1 - x)) *
            aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k).derivative +
            (2 * (k : ℝ) + 1) * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k)) /
          (1 - r * (1 - x)) ^ (2 * k + 2)) := by
        dsimp [ratioKernelDeriv]; ring
      _ = _ := TauCeti.neg_mul_deriv_incompleteGammaRatioPoly_div k (r * (1 - x))
  calc _
    _ = ((ratioKernelDeriv r k x * (1 - x) : ℝ) : ℂ) *
        ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x) := by
      rw [hsplit]; push_cast; ring
    _ = _ := by rw [hreal]

private theorem hasDerivAt_ratioKernel {r : ℝ} (hr1 : r < 1) (k : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y : ℝ => (((-1 : ℝ) ^ k * aeval (r * (1 - y)) (TauCeti.incompleteGammaRatioPoly k) /
        (1 - r * (1 - y)) ^ (2 * k + 1) : ℝ) : ℂ))
      (ratioKernelDeriv r k x : ℂ) x := by
  have hrx : r * (1 - x) ≠ 1 := by linarith [one_sub_mul_pos hr1 (Ioo_subset_Icc_self hx)]
  have hin := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul r
  refine (((TauCeti.hasDerivAt_incompleteGammaRatioPoly_div k hrx).comp x hin).ofReal_comp)
    |>.congr_deriv ?_
  dsimp [ratioKernelDeriv]; push_cast; ring

private theorem intervalIntegrable_deriv_one_sub_cpow_mul_cexp {a : ℂ} (ha : 0 < a.re) (r : ℝ) :
    IntervalIntegrable
      (fun x : ℝ =>
        -a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x))
      volume 0 1 := by
  have h1 := intervalIntegrable_one_sub_cpow (p := a - 1) (by simp [ha])
  have hc1 : ContinuousOn (fun x : ℝ => -a * ((1 - r * (1 - x) : ℝ) : ℂ)) [[0, 1]] :=
    (continuous_const.mul (continuous_ofReal.comp
      (continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id)))))
      |>.continuousOn
  have hc2 : ContinuousOn (fun x : ℝ => cexp (a * r * x)) [[0, 1]] :=
    (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)).continuousOn
  simpa [mul_assoc] using (h1.continuousOn_mul hc1).mul_continuousOn hc2

/-- One integration-by-parts step on `fixedRatioRemIntegral`. -/
private theorem fixedRatioRemIntegral_step {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr1 : r < 1)
    (k : ℕ) :
    fixedRatioRemIntegral a r k =
      (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
          ((1 - (r : ℂ)) ^ (2 * k + 1) * a) +
        a⁻¹ * fixedRatioRemIntegral a r (k + 1) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let u : ℝ → ℂ := fun x =>
    (((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
      (1 - r * (1 - x)) ^ (2 * k + 1) : ℝ) : ℂ)
  let v : ℝ → ℂ := fun x => ((1 - x : ℝ) : ℂ) ^ a * cexp (a * r * x)
  have hu_cont : ContinuousOn u [[0, 1]] := by
    have hc : ContinuousOn
        (fun x : ℝ => (-1 : ℝ) ^ k *
          (aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
            (1 - r * (1 - x)) ^ (2 * k + 1))) [[0, 1]] :=
      continuousOn_const.mul
        (continuousOn_ratio_div hr1 (TauCeti.incompleteGammaRatioPoly k) (2 * k + 1))
    exact continuous_ofReal.comp_continuousOn (hc.congr fun x _ => by simp [mul_div_assoc])
  have hv_cont : ContinuousOn v [[0, 1]] :=
    (((Complex.continuous_ofReal_cpow_const ha).comp
      (continuous_const.sub continuous_id)).mul
        (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal))).continuousOn
  have hu_deriv : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt u (ratioKernelDeriv r k x : ℂ) x := by
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one]
    exact fun x hx => hasDerivAt_ratioKernel hr1 k hx
  have hv_deriv : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt v
        (-a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)) x := by
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one]
    exact fun x hx => hasDerivAt_one_sub_cpow_mul_cexp ha0 r hx
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu_cont hv_cont hu_deriv hv_deriv (continuousOn_ratioKernelDeriv hr1 k).intervalIntegrable
    (intervalIntegrable_deriv_one_sub_cpow_mul_cexp ha r)
  have hv1 : v 1 = 0 := by simp [v, zero_cpow ha0]
  have hv0 : v 0 = 1 := by simp [v]
  have hu0 : u 0 = (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
      (1 - (r : ℂ)) ^ (2 * k + 1) := by
    dsimp [u]; rw [sub_zero, mul_one, aeval_ofReal_intPoly]; push_cast; rfl
  rw [integral_ratioKernel_mul_deriv a hr1 k, hv1, hv0, mul_zero, mul_one, zero_sub,
    integral_ratioKernelDeriv_mul a r k, hu0] at hibp
  have heq := congr_arg (fun z : ℂ => (-a)⁻¹ * z) hibp
  have h1r : (1 - (r : ℂ)) ^ (2 * k + 1) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (ofReal_inj.not.mpr hr1.ne'))
  rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr ha0), one_mul] at heq
  rw [heq]
  field_simp [ha0, h1r]
  ring

/-- On `0 < Re a` and `0 < r`, scaling `γ(a, r a)` by `(r a)^{-a} e^{r a}` gives the Euler
integral `∫₀¹ (1 - x)^{a - 1} e^{a r x} dx`. -/
theorem mul_lowerIncompleteGamma_mul_eq_integral {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) =
      ∫ x in (0 : ℝ)..1, ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hra0 : (r : ℂ) * a ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr.ne') ha0
  have hcpow : ((r : ℂ) * a) ^ (-a) * ((r : ℂ) * a) ^ a = 1 := by
    rw [cpow_neg, inv_mul_cancel₀]
    rw [cpow_def_of_ne_zero hra0]
    exact Complex.exp_ne_zero _
  rw [lowerIncompleteGamma_eq_integral ha (r * a), ← mul_assoc,
    mul_right_comm (((r : ℂ) * a) ^ (-a)) (cexp (r * a)) (((r : ℂ) * a) ^ a),
    hcpow, one_mul, ← intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => cexp (r * a) * ((s : ℂ) ^ (a - 1) * cexp (-(r * a * s)))) (1 : ℝ)
    (a := (0 : ℝ)) (b := 1)
  rw [sub_self, sub_zero] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← mul_assoc, mul_comm (cexp (r * a)), mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- **Exact `n`-term fixed-ratio expansion of `γ(a, r a)`** on the open right half-plane
`0 < Re a`, for `0 < r < 1`: `n` integrations by parts peel off the first `n` terms of DLMF 8.11.6
with an explicit integral remainder. -/
theorem mul_lowerIncompleteGamma_mul_eq_sum_add_integral {a : ℂ} (ha : 0 < a.re)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) =
      (∑ k ∈ Finset.range n,
        (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
          ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))) +
      (a ^ n)⁻¹ * ∫ x in (0 : ℝ)..1,
        (((-1 : ℝ) ^ n * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly n) /
            (1 - r * (1 - x)) ^ (2 * n) : ℝ) : ℂ) *
          ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x) := by
  -- Express the integral in terms of `fixedRatioRemIntegral` for induction on `n`
  change _ = _ + (a ^ n)⁻¹ * fixedRatioRemIntegral a r n
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, inv_one, one_mul,
      mul_lowerIncompleteGamma_mul_eq_integral ha hr0, fixedRatioRemIntegral]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp
  | succ n ih =>
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    rw [ih, fixedRatioRemIntegral_step ha hr1 n, Finset.sum_range_succ, mul_add, add_assoc]
    congr 2
    · field_simp [ha0]
      ring
    · rw [pow_succ, mul_inv, ← mul_assoc]

/-! ### Remainder bounds on the right half-plane and sectorial asymptotics (DLMF 8.11.6) -/

/-- For real parameter `s` and `r : ℝ`, `(-1)^k * fixedRatioRemIntegral s r k` equals the real
integral of the unsigned amplitude. -/
private theorem neg_one_pow_mul_fixedRatioRemIntegral_ofReal (s r : ℝ) (k : ℕ) :
    (-1 : ℂ) ^ k * fixedRatioRemIntegral s r k =
      ((∫ x in (0 : ℝ)..1,
        (aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
          (1 - r * (1 - x)) ^ (2 * k)) *
          (1 - x) ^ (s - 1) * Real.exp (s * r * x) : ℝ) : ℂ) := by
  rw [fixedRatioRemIntegral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr_ae ?_
  have hno1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by simp [ae_iff]
  filter_upwards [hno1] with x hxne hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hxpos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hxne)
  have hcpow : ((1 - x : ℝ) : ℂ) ^ ((s : ℂ) - 1) = (((1 - x) ^ (s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hxpos.le]; push_cast; rfl
  have hexp : cexp ((s : ℂ) * r * x) = (Real.exp (s * r * x) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  rw [hcpow, hexp]
  have hreal : (-1 : ℂ) ^ k *
      ((((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
          (1 - r * (1 - x)) ^ (2 * k) : ℝ) : ℂ) *
        (((1 - x) ^ (s - 1) : ℝ) : ℂ) * (Real.exp (s * r * x) : ℂ)) =
      ((((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
        ((aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) /
          (1 - r * (1 - x)) ^ (2 * k)) *
          (1 - x) ^ (s - 1) * Real.exp (s * r * x)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal, hsign, one_mul]

private theorem neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg (s : ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    0 ≤ ((-1 : ℂ) ^ k * fixedRatioRemIntegral s r k).re ∧
      ((-1 : ℂ) ^ k * fixedRatioRemIntegral s r k).im = 0 := by
  rw [neg_one_pow_mul_fixedRatioRemIntegral_ofReal s r k, ofReal_re, ofReal_im]
  refine ⟨intervalIntegral.integral_nonneg zero_le_one fun x hx => ?_, rfl⟩
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hpoly : 0 ≤ aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) :=
    TauCeti.aeval_incompleteGammaRatioPoly_nonneg (mul_nonneg hr0 hx1) k
  have hden : 0 ≤ (1 - r * (1 - x)) ^ (2 * k) := pow_nonneg (one_sub_mul_pos hr1 hx).le _
  exact mul_nonneg (mul_nonneg (div_nonneg hpoly hden) (Real.rpow_nonneg hx1 _))
    (Real.exp_pos _).le

private theorem norm_fixedRatioRemIntegral_le_re (a : ℂ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (k : ℕ) :
    ‖fixedRatioRemIntegral a r k‖ ≤
      ((-1 : ℂ) ^ k * fixedRatioRemIntegral a.re r k).re := by
  rw [neg_one_pow_mul_fixedRatioRemIntegral_ofReal a.re r k, ofReal_re, fixedRatioRemIntegral]
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans_eq ?_
  refine intervalIntegral.integral_congr_ae ?_
  have hno1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by simp [ae_iff]
  filter_upwards [hno1] with x hxne hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hxpos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hxne)
  have hpoly : 0 ≤ aeval (r * (1 - x)) (TauCeti.incompleteGammaRatioPoly k) :=
    TauCeti.aeval_incompleteGammaRatioPoly_nonneg (mul_nonneg hr0 hxpos.le) k
  have hden : 0 < (1 - r * (1 - x)) ^ (2 * k) :=
    pow_pos (one_sub_mul_pos hr1 (Ioc_subset_Icc_self hx)) _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hpoly, abs_of_pos hden,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos, sub_re, one_re, Complex.norm_exp]
  have hre : (a * r * x).re = a.re * r * x := by simp [mul_assoc]
  rw [hre]

/-- Pointwise norm bound on `fixedRatioRemIntegral` on the open right half-plane `0 < Re a`. -/
private theorem norm_fixedRatioRemIntegral_le {a : ℂ} (ha : 0 < a.re) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ‖fixedRatioRemIntegral a r k‖ ≤
      aeval r (TauCeti.incompleteGammaRatioPoly k) /
        ((1 - r) ^ (2 * k + 1) * a.re) := by
  refine (norm_fixedRatioRemIntegral_le_re a hr0 hr1 k).trans ?_
  have hstep := congr_arg (fun z : ℂ => ((-1 : ℂ) ^ k * z).re)
    (fixedRatioRemIntegral_step (a := (a.re : ℂ)) (by simpa using ha) hr1 k)
  have hnext := (neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg a.re hr0 hr1 (k + 1)).1
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hterm : ((-1 : ℂ) ^ k *
      ((-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
        ((1 - (r : ℂ)) ^ (2 * k + 1) * (a.re : ℂ)))).re =
      aeval r (TauCeti.incompleteGammaRatioPoly k) / ((1 - r) ^ (2 * k + 1) * a.re) := by
    rw [aeval_ofReal_intPoly]
    have hcast : (-1 : ℂ) ^ k *
        ((-1 : ℂ) ^ k * (aeval r (TauCeti.incompleteGammaRatioPoly k) : ℂ) /
          ((1 - (r : ℂ)) ^ (2 * k + 1) * (a.re : ℂ))) =
        ((((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          (aeval r (TauCeti.incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k + 1) * a.re)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, hsign, one_mul, ofReal_re]
  have htail : ((-1 : ℂ) ^ k * ((a.re : ℂ)⁻¹ * fixedRatioRemIntegral a.re r (k + 1))).re =
      -(a.re⁻¹ * ((-1 : ℂ) ^ (k + 1) * fixedRatioRemIntegral a.re r (k + 1)).re) := by
    have him := (neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg a.re hr0 hr1 (k + 1)).2
    have hrew_tail : (-1 : ℂ) ^ k * ((a.re : ℂ)⁻¹ * fixedRatioRemIntegral a.re r (k + 1)) =
        -((a.re⁻¹ : ℝ) : ℂ) * ((-1 : ℂ) ^ (k + 1) * fixedRatioRemIntegral a.re r (k + 1)) := by
      rw [pow_succ, ofReal_inv]; ring
    rw [hrew_tail, neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, him, zero_mul, sub_zero]
  rw [mul_add, add_re, hterm, htail] at hstep
  have hnn : 0 ≤ a.re⁻¹ * ((-1 : ℂ) ^ (k + 1) * fixedRatioRemIntegral a.re r (k + 1)).re :=
    mul_nonneg (inv_nonneg.mpr ha.le) hnext
  linarith

/-- **Explicit remainder bound for `γ(a, r a)` on the open right half-plane `0 < Re a`**:
for `0 < r < 1` and every `n : ℕ`, the `n`-th remainder of `(r a)^{-a} e^{r a} γ(a, r a)` has
norm at most `b_n(r) / ((1 - r)^{2n + 1} ‖a‖^n Re a)`. -/
theorem norm_lowerIncompleteGamma_fixedRatio_sub_sum_le {a : ℂ} (ha : 0 < a.re)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    ‖(r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
            ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))‖ ≤
      aeval r (TauCeti.incompleteGammaRatioPoly n) /
        ((1 - r) ^ (2 * n + 1) * ‖a‖ ^ n * a.re) := by
  rw [mul_lowerIncompleteGamma_mul_eq_sum_add_integral ha hr0 hr1 n, add_sub_cancel_left]
  -- Rewrite the remainder integral via `fixedRatioRemIntegral`
  change ‖(a ^ n)⁻¹ * fixedRatioRemIntegral a r n‖ ≤ _
  rw [norm_mul, norm_inv, norm_pow]
  refine (mul_le_mul_of_nonneg_left (norm_fixedRatioRemIntegral_le ha hr0.le hr1 n)
    (by positivity)).trans_eq ?_
  rw [inv_mul_eq_div, div_div]
  ring

private theorem norm_mul_sin_le_re_of_abs_arg_le {a : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (ha : |a.arg| ≤ Real.pi / 2 - δ) :
    ‖a‖ * Real.sin δ ≤ a.re := by
  have hδ2 : δ ≤ Real.pi / 2 := by linarith [abs_nonneg a.arg]
  have hmem : Real.pi / 2 - δ ∈ Icc (0 : ℝ) Real.pi :=
    ⟨sub_nonneg.mpr hδ2, by linarith⟩
  have h := (TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re hmem).mp (abs_le.mp ha)
  rwa [Real.cos_pi_div_two_sub] at h

/-- **Explicit sectorial remainder bound for `γ(a, r a)`**: for `0 < δ`, nonzero `a` with
`|arg a| ≤ π / 2 - δ`, and `0 < r < 1`, the `n`-th remainder of `(r a)^{-a} e^{r a} γ(a, r a)`
is bounded by `b_n(r) / ((1 - r)^{2n + 1} sin δ · ‖a‖^{n + 1})`. -/
theorem norm_lowerIncompleteGamma_fixedRatio_sub_sum_le_of_abs_arg_le {a : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (ha : |a.arg| ≤ Real.pi / 2 - δ) (ha0 : a ≠ 0) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (n : ℕ) :
    ‖(r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
            ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))‖ ≤
      aeval r (TauCeti.incompleteGammaRatioPoly n) /
        ((1 - r) ^ (2 * n + 1) * Real.sin δ * ‖a‖ ^ (n + 1)) := by
  have hδ2 : δ ≤ Real.pi / 2 := by linarith [abs_nonneg a.arg]
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hre_ge := norm_mul_sin_le_re_of_abs_arg_le hδ ha
  have hre : 0 < a.re := lt_of_lt_of_le (mul_pos (norm_pos_iff.mpr ha0) hsin) hre_ge
  refine (norm_lowerIncompleteGamma_fixedRatio_sub_sum_le hre hr0 hr1 n).trans ?_
  have hnum : 0 ≤ aeval r (TauCeti.incompleteGammaRatioPoly n) :=
    TauCeti.aeval_incompleteGammaRatioPoly_nonneg hr0.le n
  have _ : 0 < (1 - r) ^ (2 * n + 1) := pow_pos (sub_pos.mpr hr1) _
  refine div_le_div_of_nonneg_left hnum (by positivity) ?_
  calc (1 - r) ^ (2 * n + 1) * Real.sin δ * ‖a‖ ^ (n + 1)
    _ = (1 - r) ^ (2 * n + 1) * ‖a‖ ^ n * (‖a‖ * Real.sin δ) := by rw [pow_succ]; ring
    _ ≤ (1 - r) ^ (2 * n + 1) * ‖a‖ ^ n * a.re :=
      mul_le_mul_of_nonneg_left hre_ge (by positivity)

/-- **DLMF 8.11.6 (normalized form)**: for fixed `0 < r < 1`, every truncation order `n : ℕ`, and
every `δ > 0`,
`(a - r a) (r a)^{-a} e^{r a} γ(a, r a) - ∑_{k < n} (-1)^k b_k(r) / ((1 - r)^{2k} a^k)
= O((‖a‖ ^ n)⁻¹)` as `a → ∞` in `|arg a| ≤ π / 2 - δ`. -/
theorem isBigO_sub_mul_lowerIncompleteGamma_fixedRatio {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ =>
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
              ((1 - (r : ℂ)) ^ (2 * k) * a ^ k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ => (‖a‖ ^ n)⁻¹ := by
  rcases lt_or_ge (Real.pi / 2) δ with hδbig | hδ2
  · have hempty : {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ} = ∅ := by
      ext a; simp only [mem_ofPred, mem_empty_iff_false, iff_false, not_le]
      linarith [abs_nonneg a.arg]
    simp [hempty]
  · have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
    refine IsBigO.of_bound
      (aeval r (TauCeti.incompleteGammaRatioPoly n) / ((1 - r) ^ (2 * n) * Real.sin δ)) ?_
    rw [eventually_inf_principal]
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with a ha_norm ha_arg
    have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
    have h1r : 0 < 1 - r := sub_pos.mpr hr1
    have hfactor :
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
          (∑ k ∈ Finset.range n,
            (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
              ((1 - (r : ℂ)) ^ (2 * k) * a ^ k)) =
        (1 - (r : ℂ)) * a *
          ((r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
            ∑ k ∈ Finset.range n,
              (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
                ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun k _ => ?_
        have h1rc : 1 - (r : ℂ) ≠ 0 := sub_ne_zero.mpr (ofReal_inj.not.mpr hr1.ne')
        rw [pow_succ (1 - (r : ℂ)) (2 * k), pow_succ a k]
        field_simp [h1rc, ha0]
    have hnorm1r : ‖(1 - (r : ℂ))‖ = 1 - r := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1r]
    rw [hfactor, norm_mul, norm_mul, hnorm1r, norm_inv, norm_pow, norm_norm]
    have hbd := norm_lowerIncompleteGamma_fixedRatio_sub_sum_le_of_abs_arg_le
      hδ ha_arg ha0 hr0 hr1 n
    refine (mul_le_mul_of_nonneg_left hbd (mul_nonneg h1r.le (norm_nonneg a))).trans_eq ?_
    rw [pow_succ (1 - r) (2 * n), pow_succ ‖a‖ n]
    field_simp [h1r.ne', hsin.ne', ha_norm.ne']

/-- **DLMF 8.11.6 (`z^{1 - a} e^z γ(a, z)` form)**: for fixed `0 < r < 1`, every `n : ℕ`, and
every `δ > 0`,
`(r a)^{1 - a} e^{r a} γ(a, r a) - ∑_{k < n} (-1)^k r b_k(r) / ((1 - r)^{2k + 1} a^k)
= O((‖a‖ ^ n)⁻¹)` as `a → ∞` in `|arg a| ≤ π / 2 - δ`. -/
theorem isBigO_cpow_one_sub_mul_lowerIncompleteGamma_fixedRatio {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ =>
        (r * a) ^ (1 - a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℂ) ^ k * r * aeval (r : ℂ) (TauCeti.incompleteGammaRatioPoly k) /
              ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ => (‖a‖ ^ n)⁻¹ := by
  have hmain := (isBigO_sub_mul_lowerIncompleteGamma_fixedRatio hr0 hr1 n hδ).const_mul_left
    ((r : ℂ) / (1 - (r : ℂ)))
  refine hmain.congr' ?_ EventuallyEq.rfl
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono
    inf_le_left] with a ha_norm
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
  have hra0 : (r : ℂ) * a ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') ha0
  have h1rc : 1 - (r : ℂ) ≠ 0 := sub_ne_zero.mpr (ofReal_inj.not.mpr hr1.ne')
  have hcpow : ((r : ℂ) * a) ^ (1 - a) = (r : ℂ) * a * ((r : ℂ) * a) ^ (-a) := by
    rw [sub_eq_add_neg, cpow_add _ _ hra0, cpow_one]
  rw [hcpow, mul_sub, Finset.mul_sum]
  congr 1
  · field_simp [h1rc]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ (1 - (r : ℂ)) (2 * k)]
    field_simp [h1rc]

/-- **Leading sectorial asymptotic of `γ(a, r a)`** (DLMF 8.11.6, `n = 1`): for `0 < r < 1` and
`δ > 0`, `γ(a, r a) ~ (r a)^a e^{-r a} / ((1 - r) a)` as `a → ∞` in `|arg a| ≤ π / 2 - δ`. -/
theorem lowerIncompleteGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ => lowerIncompleteGamma a (r * a))
      ~[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ => (r * a) ^ a * cexp (-(r * a)) / ((1 - r) * a) := by
  have hbig := isBigO_sub_mul_lowerIncompleteGamma_fixedRatio hr0 hr1 1 hδ
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_zero, one_mul,
    TauCeti.incompleteGammaRatioPoly_zero, map_one, div_one, pow_one] at hbig
  have hlim0 : Tendsto (fun a : ℂ => ‖a‖⁻¹)
      (Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}) (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop).mono_left inf_le_left
  have hsub0 : Tendsto
      (fun a : ℂ =>
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) - 1)
      (Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}) (𝓝 0) :=
    hbig.trans_tendsto hlim0
  refine isEquivalent_of_tendsto_one ?_
  have hquot : Tendsto
      (fun a : ℂ =>
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a))
      (Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}) (𝓝 1) := by
    simpa using hsub0.add_const (1 : ℂ)
  refine hquot.congr' ?_
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono
    inf_le_left] with a ha_norm
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
  have hra0 : (r : ℂ) * a ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') ha0
  have h1rc : 1 - (r : ℂ) ≠ 0 := sub_ne_zero.mpr (ofReal_inj.not.mpr hr1.ne')
  have hc1 : ((r : ℂ) * a) ^ a ≠ 0 := by
    rw [cpow_def_of_ne_zero hra0]; exact Complex.exp_ne_zero _
  dsimp [Pi.div_apply]
  rw [cpow_neg, Complex.exp_neg]
  field_simp [ha0, h1rc, hc1, Complex.exp_ne_zero ((r : ℂ) * a)]

private theorem gamma_isEquivalent_stirling_sector {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ Real.pi / 2) :
    (fun a : ℂ => Gamma a)
      ~[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ => (Real.sqrt (2 * Real.pi) : ℂ) * a ^ (a - 1 / 2) * cexp (-a) := by
  have hδπ : δ < Real.pi := by linarith [Real.pi_pos]
  have hsub_sec : {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ} ⊆ {a : ℂ | |a.arg| ≤ Real.pi - δ} :=
    fun a ha => le_trans (mem_ofPred.mp ha) (by linarith [Real.pi_pos])
  have hstir_big := (TauCeti.isBigO_logGamma_sub_stirling hδ hδπ).mono
    (inf_le_inf_left (Bornology.cobounded ℂ) (principal_mono.mpr hsub_sec))
  have hstir_lim : Tendsto
      (fun a : ℂ =>
        TauCeti.logGamma a -
          ((a - 1 / 2) * Complex.log a - a + (Real.log (2 * Real.pi) / 2 : ℝ)))
      (Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}) (𝓝 0) :=
    hstir_big.trans_tendsto
      ((tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop).mono_left inf_le_left)
  refine isEquivalent_of_tendsto_one ?_
  have hexp := (Complex.continuous_exp.tendsto 0).comp hstir_lim
  rw [Complex.exp_zero] at hexp
  refine hexp.congr' ?_
  rw [EventuallyEq, eventually_inf_principal]
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with a ha_norm ha_arg
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  have hre : 0 < a.re := lt_of_lt_of_le (mul_pos ha_norm hsin)
    (norm_mul_sin_le_re_of_abs_arg_le hδ ha_arg)
  have hsqrt : cexp ((Real.log (2 * Real.pi) / 2 : ℝ)) = (Real.sqrt (2 * Real.pi) : ℂ) := by
    rw [← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    ring_nf
  dsimp [Function.comp_def, Pi.div_apply]
  rw [Complex.exp_sub, TauCeti.exp_logGamma (Or.inl hre), Complex.exp_add, Complex.exp_sub,
    hsqrt, cpow_def_of_ne_zero ha0]
  have hexpa : cexp a ≠ 0 := Complex.exp_ne_zero a
  field_simp [hexpa, Complex.exp_neg]
  rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- **Leading sectorial asymptotic of `P(a, r a)`**: combining DLMF 8.11.6 with sectorial
Stirling's formula gives
`P(a, r a) ~ r^a e^{(1 - r) a} / (√(2π) (1 - r) a^{1/2})` as `a → ∞` in `|arg a| ≤ π / 2 - δ`,
for fixed `0 < r < 1` and `δ > 0`. -/
theorem regularizedGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ => regularizedGamma a (r * a))
      ~[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ =>
          (r : ℂ) ^ a * cexp ((1 - r) * a) /
            ((Real.sqrt (2 * Real.pi) : ℂ) * (1 - r) * a ^ (1 / 2 : ℂ)) := by
  rcases lt_or_ge (Real.pi / 2) δ with hδbig | hδ2
  · have hempty : {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ} = ∅ := by
      ext a; simp only [mem_ofPred, mem_empty_iff_false, iff_false, not_le]
      linarith [abs_nonneg a.arg]
    rw [hempty, principal_empty, inf_bot_eq]
    exact isEquivalent_of_tendsto_one tendsto_bot
  · have hδπ : δ < Real.pi := by linarith [Real.pi_pos]
    have hdiv := (lowerIncompleteGamma_fixedRatio_isEquivalent hr0 hr1 hδ).div
      (gamma_isEquivalent_stirling_sector hδ hδ2)
    refine (IsEquivalent.congr_left hdiv ?_).congr_right ?_
    · rw [EventuallyEq, eventually_inf_principal]
      filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with a ha_norm ha_arg
      have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
      have hre : 0 < a.re := lt_of_lt_of_le (mul_pos ha_norm hsin)
        (norm_mul_sin_le_re_of_abs_arg_le hδ ha_arg)
      dsimp [Pi.div_apply]
      rw [lowerIncompleteGamma_def, mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos hre)]
    · rw [EventuallyEq, eventually_inf_principal]
      filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with a ha_norm _
      have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
      have hra0 : (r : ℂ) * a ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') ha0
      dsimp [Pi.div_apply]
      rw [cpow_def_of_ne_zero hra0, Complex.log_ofReal_mul hr0 ha0, add_mul, Complex.exp_add,
        cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr0.ne'), ← Complex.ofReal_log hr0.le,
        cpow_def_of_ne_zero ha0, cpow_def_of_ne_zero ha0]
      have hl : a = cexp (Complex.log a) := (Complex.exp_log ha0).symm
      conv_lhs => enter [1, 2, 2]; rw [hl]
      have h1r : 1 - (r : ℂ) ≠ 0 := sub_ne_zero.mpr (ofReal_inj.not.mpr hr1.ne')
      have hsq0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
      field_simp [h1r, hsq0, Complex.exp_ne_zero _]
      simp only [← Complex.exp_add]
      congr 1
      ring

end Complex

namespace TauCeti

/-! ### Enveloping inequalities and asymptotics on the positive real axis -/

/-- Internal bridge from `TauCeti.lowerIncompleteGamma` to `Complex.lowerIncompleteGamma` on the
positive half-axes. -/
private theorem ofReal_lowerIncompleteGamma_eq_complex {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    ((lowerIncompleteGamma s x : ℝ) : ℂ) = Complex.lowerIncompleteGamma s x := by
  have hsre : 0 < (s : ℂ).re := by simpa using hs
  have hsub := congr_arg (fun y : ℝ => x * y)
    (intervalIntegral.integral_comp_mul_right
      (fun t : ℝ => t ^ (s - 1) * Real.exp (-t)) hx.ne' (a := (0 : ℝ)) (b := 1))
  dsimp at hsub
  rw [zero_mul, one_mul, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul] at hsub
  rw [lowerIncompleteGamma_eq_integral hx.le, ← hsub, Complex.ofReal_mul,
    ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul,
    Complex.lowerIncompleteGamma_eq_integral hsre, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  have hno0 : ∀ᵐ u ∂volume, u ≠ (0 : ℝ) := by simp [ae_iff]
  filter_upwards [hno0] with u hune hu
  rw [Set.uIoc_of_le zero_le_one] at hu
  have hupos : 0 < u := lt_of_le_of_ne hu.1.le hune.symm
  have hxpow : x * (u * x) ^ (s - 1) = x ^ s * u ^ (s - 1) := by
    have hx1 : x * x ^ (s - 1) = x ^ s := by
      conv_lhs => enter [1]; rw [← Real.rpow_one x]
      rw [← Real.rpow_add hx]
      congr 1
      ring
    rw [Real.mul_rpow hupos.le hx.le, mul_left_comm, hx1, mul_comm]
  have hcpow_x : (x : ℂ) ^ (s : ℂ) = ((x ^ s : ℝ) : ℂ) := (Complex.ofReal_cpow hx.le s).symm
  have hcpow_u : (u : ℂ) ^ ((s : ℂ) - 1) = ((u ^ (s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hupos.le]; push_cast; rfl
  have hexp : Complex.exp (-((x : ℂ) * u)) = (Real.exp (-(u * x)) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hcpow_x, hcpow_u, hexp, Complex.ofReal_mul]
  have hmul : (x : ℂ) * (((((u * x) ^ (s - 1) : ℝ) : ℂ) * (Real.exp (-(u * x)) : ℂ))) =
      (((x * (u * x) ^ (s - 1) : ℝ) : ℂ) * (Real.exp (-(u * x)) : ℂ)) := by
    push_cast; ring
  rw [hmul, hxpow]
  push_cast
  ring

/-- **Enveloping lower bound on the `n`-th remainder** of `(r a)^{-a} e^{r a} γ(a, r a)` for real
`a > 0` and `0 < r < 1`: multiplying the `n`-th remainder by `(-1)^n` gives a nonnegative number. -/
theorem mul_lowerIncompleteGamma_fixedRatio_sub_sum_nonneg {a r : ℝ} (ha : 0 < a)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n *
      ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) := by
  have hare : 0 < (a : ℂ).re := by simpa using ha
  have hcast : (((-1 : ℝ) ^ n *
      ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) : ℝ) : ℂ) =
      ((a ^ n)⁻¹ : ℝ) * ((-1 : ℂ) ^ n * Complex.fixedRatioRemIntegral a r n) := by
    have hmain := Complex.mul_lowerIncompleteGamma_mul_eq_sum_add_integral hare hr0 hr1 n
    have hra : 0 < r * a := mul_pos hr0 ha
    have hpow : (((r * a) ^ (-a) : ℝ) : ℂ) = ((r : ℂ) * a) ^ (-(a : ℂ)) := by
      rw [Complex.ofReal_cpow hra.le]; push_cast; rfl
    have hexp_ra : (Real.exp (r * a) : ℂ) = Complex.exp ((r : ℂ) * a) := by
      rw [Complex.ofReal_exp]; push_cast; rfl
    have hsum : ((∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1)) : ℝ) : ℂ) =
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * aeval (r : ℂ) (incompleteGammaRatioPoly k) /
            ((1 - (r : ℂ)) ^ (2 * k + 1) * (a : ℂ) ^ (k + 1)) := by
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.aeval_ofReal_intPoly]
    rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul, hpow,
      hexp_ra, ofReal_lowerIncompleteGamma_eq_complex ha hra, hsum]
    have hgam : Complex.lowerIncompleteGamma (a : ℂ) ((r * a : ℝ) : ℂ) =
        Complex.lowerIncompleteGamma (a : ℂ) ((r : ℂ) * a) := by push_cast; rfl
    rw [hgam, hmain, add_sub_cancel_left, Complex.fixedRatioRemIntegral]
    push_cast
    ring
  have hre := congr_arg Complex.re hcast
  rw [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  rw [hre]
  exact mul_nonneg (by positivity)
    (Complex.neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg a hr0.le hr1 n).1

/-- **Enveloping upper bound on the `n`-th remainder** of `(r a)^{-a} e^{r a} γ(a, r a)` for real
`a > 0` and `0 < r < 1`: the remainder is bounded in magnitude by the first neglected term
`b_n(r) / ((1 - r)^{2n + 1} a^{n + 1})`. -/
theorem mul_lowerIncompleteGamma_fixedRatio_sub_sum_le {a r : ℝ} (ha : 0 < a)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (-1 : ℝ) ^ n *
      ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) ≤
      aeval r (incompleteGammaRatioPoly n) / ((1 - r) ^ (2 * n + 1) * a ^ (n + 1)) := by
  have hnext := mul_lowerIncompleteGamma_fixedRatio_sub_sum_nonneg ha hr0 hr1 (n + 1)
  rw [Finset.sum_range_succ, sub_add_eq_sub_sub, pow_succ (-1 : ℝ)] at hnext
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hrew : ((-1 : ℝ) ^ n * (-1 : ℝ)) *
      (((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) -
        (-1 : ℝ) ^ n * aeval r (incompleteGammaRatioPoly n) /
          ((1 - r) ^ (2 * n + 1) * a ^ (n + 1))) =
      ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        (aeval r (incompleteGammaRatioPoly n) / ((1 - r) ^ (2 * n + 1) * a ^ (n + 1))) -
      (-1 : ℝ) ^ n *
        ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
              ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) := by ring
  rw [hrew, hsign, one_mul] at hnext
  linarith

/-- Sharp two-sided bracketing of `γ(a, r a)` from the `n = 0` and `n = 1` enveloping bounds:
for `a > 0` and `0 < r < 1`,
`(r a)^a e^{-r a} / ((1 - r) a) * (1 - r / ((1 - r)^2 a)) ≤ γ(a, r a) ≤
(r a)^a e^{-r a} / ((1 - r) a)`. -/
theorem lowerIncompleteGamma_fixedRatio_bounds {a r : ℝ} (ha : 0 < a) (hr0 : 0 < r)
    (hr1 : r < 1) :
    (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) * (1 - r / ((1 - r) ^ 2 * a)) ≤
        lowerIncompleteGamma a (r * a) ∧
      lowerIncompleteGamma a (r * a) ≤
        (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) := by
  have hra : 0 < r * a := mul_pos hr0 ha
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hpow_pos : 0 < (r * a) ^ a * Real.exp (-(r * a)) :=
    mul_pos (Real.rpow_pos_of_pos hra a) (Real.exp_pos _)
  have hcancel : (r * a) ^ a * Real.exp (-(r * a)) * ((r * a) ^ (-a) * Real.exp (r * a)) = 1 := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hra, add_neg_cancel, Real.rpow_zero,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have h0 := mul_lowerIncompleteGamma_fixedRatio_sub_sum_le ha hr0 hr1 0
  simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, sub_zero,
    incompleteGammaRatioPoly_zero, map_one, mul_zero, zero_add, pow_one] at h0
  have h1' := mul_lowerIncompleteGamma_fixedRatio_sub_sum_le ha hr0 hr1 1
  simp only [pow_one, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
    incompleteGammaRatioPoly_zero, map_one, incompleteGammaRatioPoly_one, aeval_X,
    neg_one_mul] at h1'
  constructor
  · have hlow : 1 / ((1 - r) * a) - r / ((1 - r) ^ 3 * a ^ 2) ≤
        (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) := by
      have h1'' : -( (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
            1 / ((1 - r) * a)) ≤ r / ((1 - r) ^ 3 * a ^ 2) := by
        simpa using h1'
      linarith
    have hm := mul_le_mul_of_nonneg_left hlow hpow_pos.le
    have hl : (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) * (1 - r / ((1 - r) ^ 2 * a)) =
        (r * a) ^ a * Real.exp (-(r * a)) *
          (1 / ((1 - r) * a) - r / ((1 - r) ^ 3 * a ^ 2)) := by
      field_simp [h1r.ne', ha.ne']
    have hr : (r * a) ^ a * Real.exp (-(r * a)) *
        ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a)) =
        lowerIncompleteGamma a (r * a) := by
      rw [← mul_assoc, hcancel, one_mul]
    linarith
  · have hm := mul_le_mul_of_nonneg_left h0 hpow_pos.le
    have hl : lowerIncompleteGamma a (r * a) =
        (r * a) ^ a * Real.exp (-(r * a)) *
          ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a)) := by
      rw [← mul_assoc, hcancel, one_mul]
    have hr : (r * a) ^ a * Real.exp (-(r * a)) * (1 / ((1 - r) * a)) =
        (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) := by ring
    linarith

/-- **Real fixed-ratio asymptotic expansion of `γ(a, r a)`** (DLMF 8.11.6 on `(0, ∞)`):
for fixed `0 < r < 1` and every `n : ℕ`,
`(a - r a) (r a)^{-a} e^{r a} γ(a, r a) - ∑_{k < n} (-1)^k b_k(r) / ((1 - r)^{2k} a^k)
= O((a ^ n)⁻¹)` as `a → +∞`. -/
theorem isBigO_sub_mul_lowerIncompleteGamma_fixedRatio {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) :
    (fun a : ℝ =>
        (a - r * a) * (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
              ((1 - r) ^ (2 * k) * a ^ k))
      =O[atTop] fun a : ℝ => (a ^ n)⁻¹ := by
  refine IsBigO.of_bound (aeval r (incompleteGammaRatioPoly n) / (1 - r) ^ (2 * n)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hfactor :
      (a - r * a) * (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        (∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k) * a ^ k)) =
      (1 - r) * a *
        ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
              ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ (1 - r) (2 * k), pow_succ a k]
      field_simp [h1r.ne', ha.ne']
  have hnn := mul_lowerIncompleteGamma_fixedRatio_sub_sum_nonneg ha hr0 hr1 n
  have hup := mul_lowerIncompleteGamma_fixedRatio_sub_sum_le ha hr0 hr1 n
  have habs : |(r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))| ≤
      aeval r (incompleteGammaRatioPoly n) / ((1 - r) ^ (2 * n + 1) * a ^ (n + 1)) := by
    have hmul_abs : |(-1 : ℝ) ^ n *
        ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
              ((1 - r) ^ (2 * k + 1) * a ^ (k + 1)))| =
        |(r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * aeval r (incompleteGammaRatioPoly k) /
              ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [← hmul_abs, abs_of_nonneg hnn]
    exact hup
  rw [hfactor, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos h1r,
    abs_of_pos ha, abs_inv, abs_pow, abs_of_pos ha]
  refine (mul_le_mul_of_nonneg_left habs (mul_nonneg h1r.le ha.le)).trans_eq ?_
  rw [pow_succ (1 - r) (2 * n), pow_succ a n]
  field_simp [h1r.ne', ha.ne']

/-- **Real leading asymptotic of `γ(a, r a)`**: for `0 < r < 1`,
`γ(a, r a) ~ (r a)^a e^{-r a} / ((1 - r) a)` as `a → +∞`. -/
theorem lowerIncompleteGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (fun a : ℝ => lowerIncompleteGamma a (r * a)) ~[atTop]
      fun a : ℝ => (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) := by
  refine isEquivalent_of_tendsto_one ?_
  have hbig := isBigO_sub_mul_lowerIncompleteGamma_fixedRatio hr0 hr1 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_zero, one_mul,
    incompleteGammaRatioPoly_zero, map_one, div_one, pow_one] at hbig
  have hsub0 : Tendsto
      (fun a : ℝ =>
        (a - r * a) * (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) - 1)
      atTop (𝓝 0) :=
    hbig.trans_tendsto tendsto_inv_atTop_zero
  have hquot : Tendsto
      (fun a : ℝ =>
        (a - r * a) * (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a))
      atTop (𝓝 1) := by
    simpa using hsub0.add_const (1 : ℝ)
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hra : 0 < r * a := mul_pos hr0 ha
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hpow : (r * a) ^ (-a) = ((r * a) ^ a)⁻¹ := Real.rpow_neg hra.le a
  dsimp [Pi.div_apply]
  rw [hpow, Real.exp_neg]
  field_simp [ha.ne', h1r.ne', (Real.rpow_pos_of_pos hra a).ne', (Real.exp_pos (r * a)).ne']

private theorem ofReal_regularizedGamma_eq_complex {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    ((regularizedGamma s x : ℝ) : ℂ) = Complex.regularizedGamma s x := by
  have hlow := ofReal_lowerIncompleteGamma_eq_complex hs hx
  rw [Complex.lowerIncompleteGamma_def, Complex.Gamma_ofReal] at hlow
  have hG : (Real.Gamma s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos hs).ne'
  rw [regularizedGamma_eq_div, Complex.ofReal_div]
  exact (eq_div_of_mul_eq hG (by rw [mul_comm]; exact hlow.symm)).symm

private theorem tendsto_ofReal_cobounded_sector :
    Tendsto (fun a : ℝ => (a : ℂ)) atTop
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |z.arg| ≤ Real.pi / 2 - Real.pi / 4}) := by
  rw [tendsto_inf, tendsto_principal]
  refine ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, ?_⟩
  · simpa [Complex.norm_real] using tendsto_abs_atTop_atTop
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [Complex.arg_ofReal_of_nonneg ha, abs_zero]
    linarith [Real.pi_pos]

/-- **Real leading asymptotic of `P(a, r a)`**: for `0 < r < 1`,
`P(a, r a) ~ r^a e^{(1 - r) a} / (√(2π) (1 - r) √a)` as `a → +∞`. -/
theorem regularizedGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (fun a : ℝ => regularizedGamma a (r * a)) ~[atTop]
      fun a : ℝ =>
        r ^ a * Real.exp ((1 - r) * a) /
          (Real.sqrt (2 * Real.pi) * (1 - r) * Real.sqrt a) := by
  have hce := (Complex.regularizedGamma_fixedRatio_isEquivalent hr0 hr1
    (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)).comp_tendsto
      tendsto_ofReal_cobounded_sector
  refine isEquivalent_of_tendsto_one ?_
  have hclim : Tendsto
      (fun a : ℝ =>
        Complex.regularizedGamma (a : ℂ) ((r : ℂ) * (a : ℂ)) /
          ((r : ℂ) ^ (a : ℂ) * Complex.exp ((1 - (r : ℂ)) * (a : ℂ)) /
            ((Real.sqrt (2 * Real.pi) : ℂ) * (1 - (r : ℂ)) * (a : ℂ) ^ (1 / 2 : ℂ))))
      atTop (𝓝 1) := by
    refine (isEquivalent_iff_tendsto_one ?_).mp hce
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hr0c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
    have h1rc : 1 - (r : ℂ) ≠ 0 := sub_ne_zero.mpr (Complex.ofReal_inj.not.mpr hr1.ne')
    have hsq : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
    refine div_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _))
      (mul_ne_zero (mul_ne_zero hsq h1rc) ?_)
    · rw [Complex.cpow_def_of_ne_zero hr0c]; exact Complex.exp_ne_zero _
    · rw [Complex.cpow_def_of_ne_zero ha0]; exact Complex.exp_ne_zero _
  have hre := (Complex.continuous_re.tendsto 1).comp hclim
  rw [Complex.one_re] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hreg : Complex.regularizedGamma (a : ℂ) ((r : ℂ) * (a : ℂ)) =
      (regularizedGamma a (r * a) : ℂ) := by
    have hcast_ra : (r : ℂ) * (a : ℂ) = ((r * a : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast_ra, ← ofReal_regularizedGamma_eq_complex ha (mul_pos hr0 ha)]
  have hrhs : ((r : ℂ) ^ (a : ℂ) * Complex.exp ((1 - (r : ℂ)) * (a : ℂ)) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * (1 - (r : ℂ)) * (a : ℂ) ^ (1 / 2 : ℂ))) =
      ((r ^ a * Real.exp ((1 - r) * a) /
        (Real.sqrt (2 * Real.pi) * (1 - r) * Real.sqrt a) : ℝ) : ℂ) := by
    have h1 : (r : ℂ) ^ (a : ℂ) = ((r ^ a : ℝ) : ℂ) := (Complex.ofReal_cpow hr0.le a).symm
    have h2 : (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]; push_cast; rfl
    have h3 : Complex.exp ((1 - (r : ℂ)) * (a : ℂ)) = (Real.exp ((1 - r) * a) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [h1, h2, h3]
    push_cast
    rfl
  dsimp [Function.comp_def, Pi.div_apply]
  rw [hreg, hrhs, ← Complex.ofReal_div, Complex.ofReal_re]

/-- For every fixed ratio `r < 1`, the lower tail `P(a, r a)` of the Gamma law tends to `0` as
`a → +∞`. -/
theorem tendsto_regularizedGamma_fixedRatio_atTop {r : ℝ} (hr1 : r < 1) :
    Tendsto (fun a : ℝ => regularizedGamma a (r * a)) atTop (𝓝 0) := by
  rcases le_or_gt r 0 with hr0 | hr0
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact (regularizedGamma_eq_zero_of_nonpos_right a (mul_nonpos_of_nonpos_of_nonneg hr0 ha.le))
      |>.symm
  · refine (regularizedGamma_fixedRatio_isEquivalent hr0 hr1).symm.tendsto_nhds ?_
    have hrate : Real.log r + (1 - r) < 0 := by
      have hexp : Real.exp (Real.log r) < Real.exp (r - 1) := by
        rw [Real.exp_log hr0]
        linarith [Real.add_one_lt_exp (sub_ne_zero.mpr hr1.ne)]
      linarith [Real.exp_lt_exp.mp hexp]
    have hnum0 : Tendsto (fun a : ℝ => Real.exp ((Real.log r + (1 - r)) * a)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hrate)
    have hden_top : Tendsto
        (fun a : ℝ => Real.sqrt (2 * Real.pi) * (1 - r) * Real.sqrt a) atTop atTop :=
      Real.tendsto_sqrt_atTop.const_mul_atTop
        (mul_pos (Real.sqrt_pos.mpr (by positivity)) (sub_pos.mpr hr1))
    have hquot0 := hnum0.div_atTop hden_top
    refine hquot0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a _
    rw [Real.rpow_def_of_pos hr0, ← Real.exp_add]
    congr 2
    ring

end TauCeti

end
