/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.MellinTransform.Sawtooth
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.NumberTheory.ZetaValues

/-!
# Continuation and derivatives of `ζ` by the Euler–Maclaurin formula

Write `B₁({x}) = {x} - 1/2` for the sawtooth function, the periodic Bernoulli function
`bernoulliFun 1 (Int.fract x)`. For real `a > 0` and complex `s` with `0 < Re s` and `s ≠ 1`,
the Riemann zeta function is
`ζ(s) = ∑_{1 ≤ n ≤ a} n^(-s) + a^(1-s)/(s - 1) + B₁({a}) a^(-s) - s ∫_a^∞ B₁({x}) x^(-s-1) dx`,
the integral converging absolutely with `|∫_a^∞ B₁({x}) x^(-s-1) dx| ≤ a^(-σ)/(2σ)`, `σ = Re s`.

This is the classical continuation of `ζ` to the half-plane `0 < Re s` and the starting point of
explicit bounds for `ζ` in the critical strip: the finite sum is the main term, `a^(1-s)/(s - 1)`
carries the pole, and the tail integral is controlled by the bound above. The point `a` is free,
so the length of the sum can be chosen according to the height `Im s`.

Applying the even-order (`2m`) Euler–Maclaurin summation formula on `[1, N]` to `x ↦ (x : ℂ) ^ (-s)`
and letting `N → ∞` on `1 < Re s` extends the continuation to arbitrary left half-planes
`1 - 2m < Re s`, `s ≠ 1` (DLMF 25.2.9):
`ζ(s) = 1 / (s - 1) + 1 / 2 - ∑_{r=1}^{m-1} B_{2r}/(2r)! (-s)_{2r-1}
  + (-s)_{2m} ∫_1^∞ (B_{2m} - B_{2m}({x}))/(2m)! x^(-s - 2m) dx`.
Specializing `m = 2` near `s = -1` isolates a factor `(s + 1)` in front of the remainder integral,
evaluating `deriv riemannZeta (-1)` in terms of `∫ x in Ioi 1, (B_4 - B_4({x})) * x ^ (-3 : ℤ)`
without differentiating under the integral sign, and differentiating the functional equation
`riemannZeta_one_sub` at `s = 2` relates `1 / 12 - deriv riemannZeta (-1)` to `deriv riemannZeta 2`
and Euler's constant `γ` (DLMF 2.10.6).

The absolute convergence of the sawtooth tail integral and its bound are
`TauCeti.integrableOn_sawtooth_mul_cpow` and `TauCeti.norm_integral_sawtooth_mul_cpow_le` in
`TauCeti.Analysis.MellinTransform.Sawtooth`.

## Main results

* `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth`: the first-order formula for every `a > 0`.
* `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth_natCast` and
  `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth_natCast_add_half`: its cases at an integer
  `a = N ≥ 1`, where `B₁({N}) = -1/2`, and at a half-integer `a = N + 1/2`, where `B₁({a}) = 0`.
* `TauCeti.riemannZeta_eq_one_add_inv_sub_integral_fract`: the case `a = 1`, written with the
  fractional part, `ζ(s) = 1 + (s - 1)⁻¹ - s ∫_1^∞ {x} x^(-s-1) dx`.
* `TauCeti.riemannZeta₀_eq_one_sub_mul_integral`: the same at `a = 1` for `riemannZeta₀`, on all
  of `0 < Re s`.
* `TauCeti.riemannZeta_re_eq_one_add_inv_sub_mul_integral`: its real form at real `σ > 0`, `σ ≠ 1`.
* `TauCeti.riemannZeta₁_eq_add_mul_sum_sawtooth` and
  `TauCeti.riemannZeta₀_eq_one_half_sub_integral_sawtooth`: integral formulas for Mathlib's entire
  functions `riemannZeta₁` and `riemannZeta₀`, the extensions of `(s - 1) ζ(s)` and
  `ζ(s) - (s - 1)⁻¹` from `s ≠ 1` (with values `1` and `γ` at `s = 1`). The formulas hold on all
  of `0 < Re s`, including `s = 1`.
* `TauCeti.eulerMascheroniConstant_eq_sum_sub_log_add_sawtooth` and
  `TauCeti.integral_Ioi_bernoulliFun_one_fract_div_sq`: their derivative and value at `s = 1`,
  `γ = ∑_{1 ≤ n ≤ a} 1/n - log a + B₁({a})/a - ∫_a^∞ B₁({x})/x² dx` and
  `∫_1^∞ B₁({x})/x² dx = 1/2 - γ`.
* `TauCeti.riemannZeta_eq_eulerMaclaurin`: the order-`2m` Euler–Maclaurin representation of
  `riemannZeta s` on `1 - 2m < Re s`, `s ≠ 1`, together with its real specialization
  `TauCeti.riemannZeta_neg_ofReal_re_eq_eulerMaclaurin`.
* `TauCeti.deriv_riemannZeta_neg_one` and `TauCeti.deriv_riemannZeta_neg_one_re`: integral
  evaluation of `ζ'(-1)` via `B_4 - B_4({x})`.
* `TauCeti.one_div_twelve_sub_deriv_riemannZeta_neg_one` and
  `TauCeti.one_div_twelve_sub_deriv_riemannZeta_neg_one_re`:
  `1 / 12 - ζ'(-1) = (γ + log(2π)) / 12 - ζ'(2) / (2π²)` (DLMF 2.10.6).

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §2.1.
* NIST *Digital Library of Mathematical Functions*, §§2.10(i), 25.2(ii), formulas 2.10.6 and
  25.2.9.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §2.
-/

public section

open Complex Filter Finset intervalIntegral MeasureTheory
open scoped Nat Real Topology

namespace TauCeti

/-- The right side of the Euler–Maclaurin formula for `ζ(s)` cut at `a`, without the polar term
`a^(1-s)/(s - 1)`. For `a > 0` it is holomorphic on `0 < Re s`. -/
private noncomputable def sawtoothReg (a : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) + bernoulliFun 1 (Int.fract a) * (a : ℂ) ^ (-s) -
    s * ∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- The right side of the Euler–Maclaurin formula for `ζ(s)` cut at `a`: `sawtoothReg a s` plus the
polar term `a^(1-s)/(s - 1)`. -/
private noncomputable def zetaSawtooth (a : ℝ) (s : ℂ) : ℂ :=
  sawtoothReg a s + (a : ℂ) ^ (1 - s) / (s - 1)

/-- The first-order Euler–Maclaurin formula on `[a, b]` for `x ↦ x^(-s)` shows that the cut point
does not matter. -/
private theorem zetaSawtooth_eq_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hs : 0 < s.re) (hs₁ : s ≠ 1) : zetaSawtooth a s = zetaSawtooth b s := by
  have hs₀ : -s ≠ 0 := neg_ne_zero.mpr fun h ↦ by simp [h] at hs
  have hpos {t : ℝ} (ht : t ∈ Set.uIcc a b) : 0 < t := by
    rw [Set.uIcc_of_le hab] at ht; exact ha.trans_le ht.1
  have hderiv {t : ℝ} (ht : 0 < t) :
      deriv (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t = -s * (t : ℂ) ^ (-(s + 1)) := by
    rw [Complex.deriv_ofReal_cpow_const _ ht.ne', neg_sub_left, add_comm]
  have hcont : ContinuousOn (fun t : ℝ ↦ -s * (t : ℂ) ^ (-(s + 1))) (Set.uIcc a b) :=
    continuousOn_const.mul fun t ht ↦
      (continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos ht).ne')).continuousWithinAt
  have hEM := sum_Ioc_floor_eq_eulerMaclaurin_one (f := fun x : ℝ ↦ (x : ℂ) ^ (-s)) ha.le hab
    (fun t ht ↦ (hasDerivAt_ofReal_cpow_const (ha.trans_le ht.1).ne' hs₀).differentiableAt)
    ((hcont.congr fun t ht ↦ hderiv (hpos ht)).intervalIntegrable)
  have hint : ∫ t in a..b, (bernoulliFun 1 (Int.fract t) : ℂ) *
        deriv (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t =
      -s * ∫ t in a..b, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [hderiv (hpos ht)]
    ring
  have hpow : ∫ t in a..b, (t : ℂ) ^ (-s) = ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [integral_cpow (Or.inr ⟨fun h ↦ hs₁ (by linear_combination -h), fun h ↦
      (hpos h).ne' rfl⟩), neg_add_eq_sub]
  have hsplit := intervalIntegral.integral_interval_add_Ioi (integrableOn_sawtooth_mul_cpow ha hs)
    (integrableOn_sawtooth_mul_cpow (ha.trans_le hab) hs)
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) +
        ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) := by
    have hIcc (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [hIcc, hIcc, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hab)]
  simp only [ofReal_natCast, real_smul] at hEM
  rw [hint, hpow] at hEM
  have h1s : (1 - s) = -(s - 1) := by ring
  have hs₁' : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  unfold zetaSawtooth sawtoothReg
  rw [hsum, hEM, ← hsplit, h1s, div_neg]
  field_simp
  ring

/-- On `1 < Re s` the right side of the formula is `ζ(s)`: it does not depend on the cut point,
and along the integers `N → ∞` its sum tends to `ζ(s)` while its other terms tend to `0`. -/
private theorem zetaSawtooth_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaSawtooth 1 s = riemannZeta s := by
  have hs₀ : 0 < s.re := zero_lt_one.trans hs
  have hs₁ : s ≠ 1 := fun h ↦ by simp [h] at hs
  have hsum : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    have hS : Summable fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s := by
      simpa using (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine (hS.hasSum.tendsto_sum_nat).congr fun N ↦ ?_
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [cpow_neg, one_div, Nat.cast_add, Nat.cast_one, add_comm]
  have hpole : Tendsto (fun N : ℕ ↦ ((N : ℝ) : ℂ) ^ (1 - s) / (s - 1)) atTop (𝓝 0) := by
    have h := (tendsto_natCast_cpow_neg_atTop (y := s - 1) (by simpa using hs)).const_mul (s - 1)⁻¹
    rw [mul_zero] at h
    refine h.congr fun N ↦ ?_
    rw [ofReal_natCast, neg_sub, div_eq_inv_mul]
  have hboundary : Tendsto (fun N : ℕ ↦
      (bernoulliFun 1 (Int.fract (N : ℝ)) : ℂ) * ((N : ℝ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have h := (tendsto_natCast_cpow_neg_atTop hs₀).const_mul (bernoulliFun 1 0 : ℂ)
    rw [mul_zero] at h
    refine h.congr fun N ↦ ?_
    rw [ofReal_natCast, Int.fract_natCast]
  have htail : Tendsto (fun N : ℕ ↦ s * ∫ x in Set.Ioi (N : ℝ),
      (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := ((tendsto_natCast_cpow_neg_atTop hs₀).const_mul
      ((‖s‖ / (2 * s.re) : ℝ) : ℂ)).norm
    rw [mul_zero, norm_zero] at h
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ h
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hN, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), neg_re]
    calc _ ≤ ‖s‖ * ((N : ℝ) ^ (-s.re) / (2 * s.re)) :=
          mul_le_mul_of_nonneg_left (norm_integral_sawtooth_mul_cpow_le hN' hs₀) (norm_nonneg _)
      _ = ‖s‖ / (2 * s.re) * (N : ℝ) ^ (-s.re) := by ring
  have hlim : Tendsto (fun N : ℕ ↦ zetaSawtooth N s) atTop (𝓝 (riemannZeta s)) := by
    have h := ((hsum.add hpole).add hboundary).sub htail
    rw [add_zero, add_zero, sub_zero] at h
    refine h.congr fun N ↦ ?_
    simp only [zetaSawtooth, sawtoothReg, Nat.floor_natCast]
    ring
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact zetaSawtooth_eq_of_le one_pos (by exact_mod_cast hN) hs₀ hs₁

/-- The right side of the formula cut at `1`, where the sum is `1` and `B₁({1}) = -1/2`. -/
private theorem zetaSawtooth_one_eq (z : ℂ) :
    zetaSawtooth 1 z = 1 + 1 / (z - 1) - 1 / 2 -
      z * ∫ x in Set.Ioi (1 : ℝ), (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(z + 1)) := by
  simp only [zetaSawtooth, sawtoothReg, Nat.floor_one, Finset.Icc_self, Finset.sum_singleton,
    Nat.cast_one, ofReal_one, one_cpow, Int.fract_one, bernoulliFun_one]
  push_cast
  ring

/-- **The formula for `riemannZeta₀` cut at `1`.** For every `s` with `0 < Re s`,
`riemannZeta₀ s = 1/2 - s ∫_1^∞ B₁({x}) x^(-s-1) dx`. Mathlib's `riemannZeta₀` is the entire
extension of `ζ(s) - (s - 1)⁻¹` from `s ≠ 1`, with value `γ` at `s = 1`; the integral formula holds
at `s = 1` too. Both sides are holomorphic on `0 < Re s`, so the identity theorem extends the
formula from `1 < Re s`. -/
theorem riemannZeta₀_eq_one_half_sub_integral_sawtooth {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s = 1 / 2 -
      s * ∫ x in Set.Ioi (1 : ℝ), (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hR : AnalyticOnNhd ℂ (fun z ↦ 1 / 2 -
      z * ∫ x in Set.Ioi (1 : ℝ), (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(z + 1)))
      {z : ℂ | 0 < z.re} :=
    ((differentiableOn_const _).sub (differentiableOn_id.mul
      (differentiableOn_integral_mul_cpow_of_isBigO one_pos isBigO_sawtooth))).analyticOnNhd hopen
  refine (differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hopen
    |>.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt 0).isPreconnected
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) ?_) hs
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z (hz : 1 < z.re)
  have hz₁ : z ≠ 1 := fun h ↦ by simp [h] at hz
  have h := zetaSawtooth_one_of_one_lt_re hz
  rw [zetaSawtooth_one_eq, riemannZeta_eq_inv_sub_add hz₁, one_div (z - 1)] at h
  linear_combination -h

/-- On `0 < Re s`, `s ≠ 1`, the right side of the formula cut at `1` is `ζ(s)`: restore the pole
in `TauCeti.riemannZeta₀_eq_one_half_sub_integral_sawtooth`. -/
private theorem zetaSawtooth_one {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    zetaSawtooth 1 s = riemannZeta s := by
  rw [zetaSawtooth_one_eq, riemannZeta_eq_inv_sub_add hs₁,
    riemannZeta₀_eq_one_half_sub_integral_sawtooth hs, one_div (s - 1)]
  ring

/-- **The continuation of `ζ` by the first-order Euler–Maclaurin formula.** For real `a > 0` and
`0 < Re s`, `s ≠ 1`,
`ζ(s) = ∑_{1 ≤ n ≤ a} n^(-s) + a^(1-s)/(s - 1) + B₁({a}) a^(-s) - s ∫_a^∞ B₁({x}) x^(-s-1) dx`,
where `B₁({x}) = {x} - 1/2` is the sawtooth, the periodic Bernoulli function
`bernoulliFun 1 (Int.fract x)`. The integral converges absolutely
(`TauCeti.integrableOn_sawtooth_mul_cpow`) and has norm at most `a^(-Re s)/(2 Re s)`
(`TauCeti.norm_integral_sawtooth_mul_cpow_le`). -/
theorem riemannZeta_eq_sum_add_integral_sawtooth {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re)
    (hs₁ : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) + (a : ℂ) ^ (1 - s) / (s - 1) +
      bernoulliFun 1 (Int.fract a) * (a : ℂ) ^ (-s) -
      s * ∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have h : zetaSawtooth a s = zetaSawtooth 1 s := by
    rcases le_total a 1 with h | h
    · exact zetaSawtooth_eq_of_le ha h hs hs₁
    · exact (zetaSawtooth_eq_of_le one_pos h hs hs₁).symm
  rw [← zetaSawtooth_one hs hs₁, ← h, zetaSawtooth, sawtoothReg]
  ring

/-- The Euler–Maclaurin formula for `ζ(s)` cut at an integer `N ≥ 1`, where `B₁({N}) = -1/2`:
`ζ(s) = ∑_{n ≤ N} n^(-s) + N^(1-s)/(s - 1) - N^(-s)/2 - s ∫_N^∞ B₁({x}) x^(-s-1) dx`
for `0 < Re s`, `s ≠ 1`. -/
theorem riemannZeta_eq_sum_add_integral_sawtooth_natCast {N : ℕ} (hN : N ≠ 0) {s : ℂ}
    (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1) -
      (N : ℂ) ^ (-s) / 2 -
      s * ∫ x in Set.Ioi (N : ℝ), (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_sum_add_integral_sawtooth (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)) hs hs₁,
    Nat.floor_natCast, Int.fract_natCast, bernoulliFun_one, ofReal_natCast]
  push_cast
  ring

/-- The Euler–Maclaurin formula for `ζ(s)` cut at a half-integer `a = N + 1/2`, where
`B₁({a}) = 0`: `ζ(s) = ∑_{n ≤ N} n^(-s) + a^(1-s)/(s - 1) - s ∫_a^∞ B₁({x}) x^(-s-1) dx`
for `0 < Re s`, `s ≠ 1`. -/
theorem riemannZeta_eq_sum_add_integral_sawtooth_natCast_add_half (N : ℕ) {s : ℂ}
    (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) +
      ((N : ℂ) + 1 / 2) ^ (1 - s) / (s - 1) -
      s * ∫ x in Set.Ioi ((N : ℝ) + 1 / 2),
        (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_sum_add_integral_sawtooth (a := (N : ℝ) + 1 / 2) (by positivity) hs hs₁]
  simp [bernoulliFun_one]

/-- **The fractional-part formula for `riemannZeta₀`.** For every `s` with `Re s > 0`,
`riemannZeta₀ s = 1 - s ∫_1^∞ {x} x^(-s-1) dx`, the integral converging absolutely. -/
theorem riemannZeta₀_eq_one_sub_mul_integral {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s =
      1 - s * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  rw [integral_fract_mul_cpow_eq_integral_sawtooth_add one_pos hs, ofReal_one, one_cpow,
    riemannZeta₀_eq_one_half_sub_integral_sawtooth hs]
  field_simp
  ring

/-- The Euler–Maclaurin formula for `ζ(s)` cut at `1`, written with the fractional part:
`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_1^∞ {x} x^(-s-1) dx` for `0 < Re s`, `s ≠ 1`, the integral
converging absolutely. -/
theorem riemannZeta_eq_one_add_inv_sub_integral_fract {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s = 1 + (s - 1)⁻¹ -
      s * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_inv_sub_add hs₁, riemannZeta₀_eq_one_sub_mul_integral hs]
  ring

/-- The real form of `TauCeti.riemannZeta_eq_one_add_inv_sub_integral_fract`: for real `σ > 0`,
`σ ≠ 1`, `Re ζ(σ) = 1 + (σ - 1)⁻¹ - σ ∫_1^∞ x^(-1-σ) {x} dx`. -/
theorem riemannZeta_re_eq_one_add_inv_sub_mul_integral {σ : ℝ} (hσ : 0 < σ)
    (hσ₁ : σ ≠ 1) :
    (riemannZeta σ).re =
      1 + (σ - 1)⁻¹ - σ * ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * Int.fract t := by
  have h := riemannZeta_eq_one_add_inv_sub_integral_fract (s := σ) (by simpa using hσ)
    (by exact_mod_cast hσ₁)
  have hI : ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-((σ : ℂ) + 1)) =
      ((∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * Int.fract t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
    have hexp : -((σ : ℂ) + 1) = ((-1 - σ : ℝ) : ℂ) := by push_cast; ring
    rw [hexp, ← ofReal_cpow (by linarith : (0 : ℝ) ≤ t), ← ofReal_mul, mul_comm]
  rw [hI] at h
  have h' : riemannZeta σ = ((1 + (σ - 1)⁻¹ - σ *
      ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * Int.fract t : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  rw [h', ofReal_re]

/-! ### The regularized formula and the Euler–Mascheroni constant -/

/-- **The regularized Euler–Maclaurin formula.** For real `a > 0` and every `s` with `0 < Re s`,
`riemannZeta₁ s = a^(1-s) + (s - 1) (∑_{1 ≤ n ≤ a} n^(-s) + B₁({a}) a^(-s) - s I)` with
`I = ∫_a^∞ B₁({x}) x^(-s-1) dx`.
Mathlib's `riemannZeta₁` is the entire extension of `(s - 1) ζ(s)` from `s ≠ 1`, with value `1` at
`s = 1` (where `(s - 1) ζ(s)` itself is `0`); the integral formula holds at `s = 1` too. -/
theorem riemannZeta₁_eq_add_mul_sum_sawtooth {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₁ s = (a : ℂ) ^ (1 - s) + (s - 1) * (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) +
      bernoulliFun 1 (Int.fract a) * (a : ℂ) ^ (-s) -
      s * ∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp [riemannZeta₁_one]
  have hs₁' : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  have h : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs₁]
    field_simp
  rw [h, riemannZeta_eq_sum_add_integral_sawtooth ha hs hs₁]
  field_simp
  ring

/-- **The Euler–Mascheroni constant by the first-order Euler–Maclaurin formula.** For real `a > 0`,
`γ = ∑_{1 ≤ n ≤ a} 1/n - log a + B₁({a})/a - ∫_a^∞ B₁({x})/x² dx`. This is the derivative at
`s = 1` of the regularized formula `TauCeti.riemannZeta₁_eq_add_mul_sum_sawtooth`, since
`deriv riemannZeta₁ 1 = γ`. -/
theorem eulerMascheroniConstant_eq_sum_sub_log_add_sawtooth {a : ℝ} (ha : 0 < a) :
    Real.eulerMascheroniConstant = ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℝ)⁻¹ - Real.log a +
      bernoulliFun 1 (Int.fract a) / a -
      ∫ x in Set.Ioi a, bernoulliFun 1 (Int.fract x) / x ^ 2 := by
  have hmem : {z : ℂ | 0 < z.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
  have heq : riemannZeta₁ =ᶠ[𝓝 1] fun z ↦ (a : ℂ) ^ (1 - z) + (z - 1) * sawtoothReg a z := by
    filter_upwards [hmem] with z hz
    simpa only [sawtoothReg] using riemannZeta₁_eq_add_mul_sum_sawtooth ha hz
  have hd₁ : HasDerivAt (fun z : ℂ ↦ (a : ℂ) ^ (1 - z)) (-(Real.log a : ℂ)) 1 := by
    simpa [ofReal_log ha.le] using ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
      (hasDerivAt_id (1 : ℂ))).const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))
  have hsum : Differentiable ℂ fun s : ℂ ↦ ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) :=
    Differentiable.fun_sum fun n hn ↦ differentiable_id.neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)))
  have hbd : Differentiable ℂ fun s : ℂ ↦ (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s) :=
    (differentiable_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))).const_mul _
  have hreg : DifferentiableOn ℂ (sawtoothReg a) {s : ℂ | 0 < s.re} := by
    unfold sawtoothReg
    exact (hsum.differentiableOn.add hbd.differentiableOn).sub
      (differentiableOn_id.mul (differentiableOn_integral_mul_cpow_of_isBigO ha isBigO_sawtooth))
  have hd₂ : HasDerivAt (fun z : ℂ ↦ (z - 1) * sawtoothReg a z) (sawtoothReg a 1) 1 := by
    simpa using ((hasDerivAt_id (1 : ℂ)).sub_const (1 : ℂ)).fun_mul
      (hreg.differentiableAt hmem).hasDerivAt
  have hγ : (Real.eulerMascheroniConstant : ℂ) = -(Real.log a : ℂ) + sawtoothReg a 1 := by
    rw [← deriv_riemannZeta₁_one, heq.deriv_eq, (hd₁.fun_add hd₂).deriv]
  have hI : ∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-((1 : ℂ) + 1)) =
      ((∫ x in Set.Ioi a, bernoulliFun 1 (Int.fract x) / x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    have hexp : -((1 : ℂ) + 1) = -(2 : ℕ) := by norm_num
    rw [hexp, cpow_neg, cpow_natCast]
    push_cast
    ring
  have hval : sawtoothReg a 1 = ((∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℝ)⁻¹ +
      bernoulliFun 1 (Int.fract a) / a -
      ∫ x in Set.Ioi a, bernoulliFun 1 (Int.fract x) / x ^ 2 : ℝ) : ℂ) := by
    rw [sawtoothReg, one_mul, hI, cpow_neg_one]
    simp_rw [cpow_neg_one]
    push_cast
    ring
  rw [hval] at hγ
  have h : Real.eulerMascheroniConstant = -Real.log a + (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℝ)⁻¹ +
      bernoulliFun 1 (Int.fract a) / a -
      ∫ x in Set.Ioi a, bernoulliFun 1 (Int.fract x) / x ^ 2) := by
    exact_mod_cast hγ
  rw [h]
  ring

/-- `∫_1^∞ B₁({x})/x² dx = 1/2 - γ`, the case `a = 1` of
`TauCeti.eulerMascheroniConstant_eq_sum_sub_log_add_sawtooth`. -/
theorem integral_Ioi_bernoulliFun_one_fract_div_sq :
    ∫ x in Set.Ioi (1 : ℝ), bernoulliFun 1 (Int.fract x) / x ^ 2 =
      1 / 2 - Real.eulerMascheroniConstant := by
  have h := eulerMascheroniConstant_eq_sum_sub_log_add_sawtooth one_pos
  have hB : bernoulliFun 1 0 = -1 / 2 := by
    rw [bernoulliFun_one]
    norm_num
  rw [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, inv_one, Real.log_one,
    Int.fract_one, hB] at h
  linarith

/-! ### Higher-order Euler–Maclaurin continuation -/

/-- The order-`2m` Euler–Maclaurin tail integral on `(1, ∞)` is complex-differentiable on
`1 - 2 * m < Re s`. -/
private theorem differentiableAt_tailIntegral {m : ℕ} {s : ℂ}
    (hs : 1 - 2 * (m : ℝ) < s.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
          (x : ℂ) ^ (-z - 2 * m)) s := by
  set ψ : ℝ → ℂ := fun x =>
    ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ)
  have hO : ψ =O[atTop] fun x : ℝ => x ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (2 * |(bernoulli (2 * m) : ℝ)| / (2 * m)!) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
    have hψ : ψ x = (((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) /
        (2 * m)! : ℝ) := by simp [ψ]
    rw [hψ, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * m)!), Real.rpow_zero, Real.norm_eq_abs,
      abs_one, mul_one]
    exact div_le_div_of_nonneg_right (abs_bernoulli_sub_bernoulliFun_fract_le m x) (by positivity)
  have hd : DifferentiableAt ℂ
      (fun w : ℂ => ∫ x in Set.Ioi (1 : ℝ), ψ x * (x : ℂ) ^ (-(w + 1))) (s + 2 * m - 1) :=
    (differentiableOn_integral_mul_cpow_of_isBigO one_pos hO).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp; linarith))
  have hcomp := hd.comp s ((differentiableAt_id.add_const (2 * (m : ℂ))).sub_const 1)
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  dsimp [Function.comp_def, ψ]
  congr 1; ext x; congr 2; ring

/-- Finite-interval Euler–Maclaurin identity on `[1, N]` for `∑_{j=1}^N 1 / j ^ s` (`s ≠ 1`). -/
private theorem sum_Icc_one_div_cpow_eq_eulerMaclaurin {s : ℂ} (hs₁ : s ≠ 1) {m N : ℕ}
    (hm : 1 ≤ m) (hN1 : 1 ≤ N) :
    ∑ j ∈ Icc 1 N, (1 / (j : ℂ) ^ s) =
      ((N : ℂ) ^ (-s + 1) - 1) / (-s + 1) + 1 / 2 + (N : ℂ) ^ (-s) / 2 +
        ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
          ((descPochhammer ℂ (2 * r - 1)).eval (-s) * ((N : ℂ) ^ (-s - (2 * r - 1 : ℕ)) - 1)) +
        (descPochhammer ℂ (2 * m)).eval (-s) *
          ∫ x in (1 : ℝ)..N,
            ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
              (x : ℂ) ^ (-s - 2 * m) := by
  set g : ℕ → ℝ → ℂ := fun i x => (descPochhammer ℂ i).eval (-s) * (x : ℂ) ^ (-s - i)
  have hs1 : -s ≠ -1 := fun h => hs₁ (neg_inj.mp h)
  have h0pos : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) N := by
    rw [Set.uIcc_of_le (by exact_mod_cast hN1), Set.mem_Icc]; intro h; linarith [h.1]
  have hcont : ∀ i, ContinuousOn (g i) (Set.Icc ((1 : ℤ) : ℝ) ((N : ℤ) : ℝ)) := fun i x hx => by
    have hx1 : 1 ≤ x := by simpa using hx.1
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const x _
      (Or.inr (by linarith)))).continuousWithinAt
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt_two_mul (g := g)
    (a := 1) (n := (N : ℤ)) (by exact_mod_cast hN1) hm (fun i _ => hcont i)
    (fun i _ x hx => hasDerivAt_descPochhammer_mul_ofReal_cpow (-s) i
      (zero_lt_one.trans (by simpa using hx.1)).ne')
    ((hcont (2 * m)).intervalIntegrable_of_Icc (by exact_mod_cast hN1))
  have hsum_cast : ∑ j ∈ Icc 1 N, (1 / (j : ℂ) ^ s) = ∑ j ∈ Icc (1 : ℤ) N, g 0 j := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, Finset.sum_Icc_intCast]
    exact sum_congr rfl fun j _ => by simp [g, cpow_neg, one_div]
  have hint0 : ∫ x in (1 : ℝ)..N, g 0 x = ((N : ℂ) ^ (-s + 1) - 1) / (-s + 1) := by
    have : (fun x : ℝ => g 0 x) = fun x : ℝ => (x : ℂ) ^ (-s) := by ext x; simp [g]
    rw [this, integral_cpow (Or.inr ⟨hs1, h0pos⟩), ofReal_one, one_cpow, ofReal_natCast]
  have hrem : ∫ x in (1 : ℝ)..N,
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)!) • g (2 * m) x =
      (descPochhammer ℂ (2 * m)).eval (-s) *
        ∫ x in (1 : ℝ)..N,
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m) := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun x _ => by simp only [g, Complex.real_smul]; push_cast; ring
  rw [Int.cast_one, Int.cast_natCast] at hEM
  rw [hsum_cast, hEM, hint0, hrem]
  simp only [g, Complex.real_smul, descPochhammer_zero, Polynomial.eval_one, one_mul,
    Nat.cast_zero, sub_zero, ofReal_one, one_cpow, ofReal_natCast]
  have hsum_mid : ∑ x ∈ Ico 1 m, (((bernoulli (2 * x) : ℝ) / (2 * x)! : ℝ) : ℂ) *
        ((descPochhammer ℂ (2 * x - 1)).eval (-s) * (N : ℂ) ^ (-s - (2 * x - 1 : ℕ)) -
          (descPochhammer ℂ (2 * x - 1)).eval (-s) * 1) =
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        ((descPochhammer ℂ (2 * r - 1)).eval (-s) *
          ((N : ℂ) ^ (-s - (2 * r - 1 : ℕ)) - 1)) :=
    sum_congr rfl fun r _ => by push_cast; ring
  rw [hsum_mid]
  push_cast; ring

/-- Integrability of the order-`2m` Euler–Maclaurin tail on `(1, ∞)` when `1 < Re s`. -/
private theorem integrableOn_tail_of_one_lt_re {s : ℂ} (m : ℕ) (hs : 1 < s.re) :
    IntegrableOn
      (fun x : ℝ => ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
        (x : ℂ) ^ (-s - 2 * m)) (Set.Ioi 1) := by
  have hre : (-s - 2 * (m : ℂ)).re < -1 := by
    simp only [sub_re, neg_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero,
      sub_zero]
    linarith
  refine IntegrableOn.congr_fun
    (((integrableOn_Ioi_cpow_of_lt hre zero_lt_one).bernoulli_sub_bernoulliFun_fract_smul
      (2 * m)).smul ((2 * m)! : ℝ)⁻¹) (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.smul_apply, Complex.real_smul]; push_cast; ring

/-- Limit of the finite Euler–Maclaurin formula on `[1, N]` as `N → ∞` when `1 < Re s`. -/
private theorem riemannZeta_eq_eulerMaclaurin_of_one_lt_re {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 1 < s.re) :
    riemannZeta s = 1 / (s - 1) + 1 / 2 -
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        (descPochhammer ℂ (2 * r - 1)).eval (-s) +
      (descPochhammer ℂ (2 * m)).eval (-s) *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m) := by
  have hs₁ : s ≠ 1 := fun h => by simp [h] at hs
  have hpow0 : ∀ w : ℂ, w.re < 0 → Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := fun w hw =>
    tendsto_zero_iff_norm_tendsto_zero.mpr <|
      (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp tendsto_natCast_atTop_atTop |>.congr' <| by
        filter_upwards [eventually_gt_atTop 0] with N hN; simp [Complex.norm_natCast_cpow_of_pos hN]
  have hLHS : Tendsto (fun N : ℕ => ∑ j ∈ Icc 1 N, (1 / (j : ℂ) ^ s)) atTop
      (𝓝 (riemannZeta s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs,
      show (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) = ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ s from
        tsum_congr fun n => by push_cast; rfl]
    refine ((Complex.summable_one_div_nat_cpow.mpr hs).comp_injective
      (add_left_injective 1)).hasSum.tendsto_sum_nat.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N _
    rw [← Finset.Ico_add_one_right_eq_Icc 1 N, Finset.sum_Ico_eq_sum_range]
    exact sum_congr rfl fun k _ => by simp [add_comm]
  have hint_tail := integrableOn_tail_of_one_lt_re m hs
  have hRHS : Tendsto (fun N : ℕ =>
      ((N : ℂ) ^ (-s + 1) - 1) / (-s + 1) + 1 / 2 + (N : ℂ) ^ (-s) / 2 +
        ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
          ((descPochhammer ℂ (2 * r - 1)).eval (-s) * ((N : ℂ) ^ (-s - (2 * r - 1 : ℕ)) - 1)) +
        (descPochhammer ℂ (2 * m)).eval (-s) * ∫ x in (1 : ℝ)..N,
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m)) atTop
      (𝓝 ((0 - 1) / (-s + 1) + 1 / 2 + 0 / 2 +
        ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
          ((descPochhammer ℂ (2 * r - 1)).eval (-s) * (0 - 1)) +
        (descPochhammer ℂ (2 * m)).eval (-s) * ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m))) :=
    (((((hpow0 _ (by simp; linarith)).sub tendsto_const_nhds).div_const _).add
      tendsto_const_nhds).add ((hpow0 _ (by simp; linarith)).div_const _)).add
      (tendsto_finsetSum _ fun r _ => (((hpow0 _ (by simp; linarith)).sub
        tendsto_const_nhds).const_mul _).const_mul _) |>.add
      ((intervalIntegral_tendsto_integral_Ioi 1 hint_tail
        tendsto_natCast_atTop_atTop).const_mul _)
  have heq := tendsto_nhds_unique hLHS (hRHS.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    exact (sum_Icc_one_div_cpow_eq_eulerMaclaurin hs₁ hm hN1).symm))
  have hdiv : ((0 : ℂ) - 1) / (-s + 1) = 1 / (s - 1) := by
    have hsub : -s + 1 = -(s - 1) := by ring
    rw [hsub, zero_sub, neg_div_neg_eq]
  rw [heq, hdiv]
  simp only [zero_sub, zero_div, mul_neg, mul_one, sum_neg_distrib]
  ring

/-- **Euler–Maclaurin continuation of `riemannZeta`** (DLMF 25.2.9). For `m ≥ 1` and every `s ≠ 1`
in the half-plane `1 - 2 * m < Re s`,
`ζ(s) = 1 / (s - 1) + 1 / 2 - ∑_{r=1}^{m-1} B_{2r}/(2r)! * (-s)_{2r-1}
  + (-s)_{2m} * ∫_1^∞ (B_{2m} - B_{2m}({x}))/(2m)! * x^(-s - 2m) dx`,
where `(z)_k` denotes the descending Pochhammer polynomial `(descPochhammer ℂ k).eval z`. -/
theorem riemannZeta_eq_eulerMaclaurin {s : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hs : 1 - 2 * (m : ℝ) < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2 -
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        (descPochhammer ℂ (2 * r - 1)).eval (-s) +
      (descPochhammer ℂ (2 * m)).eval (-s) *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
            (x : ℂ) ^ (-s - 2 * m) := by
  -- Clear the simple pole at `s = 1` by multiplying by `s - 1` on the convex half-plane.
  set H : ℂ → ℂ := fun z => 1 / 2 -
    ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
      (descPochhammer ℂ (2 * r - 1)).eval (-z) +
    (descPochhammer ℂ (2 * m)).eval (-z) *
      ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
          (x : ℂ) ^ (-z - 2 * m)
  have hopen : IsOpen {z : ℂ | 1 - 2 * (m : ℝ) < z.re} :=
    isOpen_lt continuous_const continuous_re
  have hpoly : ∀ k : ℕ, Differentiable ℂ (fun z : ℂ => (descPochhammer ℂ k).eval (-z)) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      simp_rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_natCast]
      exact ih.mul (differentiable_neg.sub_const _)
  have hH_diff : DifferentiableOn ℂ H {z : ℂ | 1 - 2 * (m : ℝ) < z.re} := fun z hz =>
    ((((differentiableAt_const _).sub
      (DifferentiableAt.fun_sum fun r _ => ((hpoly _).differentiableAt).const_mul _)).add
      (((hpoly _).differentiableAt).mul
        (differentiableAt_tailIntegral hz)))).differentiableWithinAt
  have hF : AnalyticOnNhd ℂ (fun z => 1 + (z - 1) * H z) {z : ℂ | 1 - 2 * (m : ℝ) < z.re} :=
    ((differentiableOn_const 1).add ((differentiableOn_id.sub_const 1).mul hH_diff)).analyticOnNhd
      hopen
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 1 - 2 * (m : ℝ) < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  have heq : (fun z => 1 + (z - 1) * H z) =ᶠ[𝓝 (2 : ℂ)] riemannZeta₁ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := fun h => by simp [h] at hz
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    calc
      1 + (z - 1) * H z = (z - 1) * (1 / (z - 1) + H z) := by field_simp
      _ = (z - 1) * riemannZeta z := by
        rw [riemannZeta_eq_eulerMaclaurin_of_one_lt_re hm hz]; dsimp [H]; ring
      _ = riemannZeta₁ z := by rw [riemannZeta_eq_inv_sub_mul hz1]; field_simp
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 - 2 * (m : ℝ) < z.re} := by
    simp only [Set.mem_ofPred, re_ofNat]; linarith
  have hid := hF.eqOn_of_preconnected_of_eventuallyEq hZ
    (convex_halfSpace_re_gt _).isPreconnected h2mem heq hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  rw [riemannZeta_eq_inv_sub_mul hs₁, ← hid]
  dsimp [H]; field_simp; ring

/-- Real specialization of `riemannZeta_eq_eulerMaclaurin` at `-α` for real `α ≠ -1` with
`α < 2 * m - 1`. -/
theorem riemannZeta_neg_ofReal_re_eq_eulerMaclaurin {α : ℝ} (hα : α ≠ -1) {m : ℕ} (hm : 1 ≤ m)
    (hαm : α < 2 * (m : ℝ) - 1) :
    (riemannZeta (-α : ℂ)).re = -1 / (α + 1) + 1 / 2 -
      ∑ r ∈ Ico 1 m, (bernoulli (2 * r) : ℝ) / (2 * r)! *
        (descPochhammer ℝ (2 * r - 1)).eval α +
      (descPochhammer ℝ (2 * m)).eval α *
        ∫ x in Set.Ioi (1 : ℝ),
          ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! *
            x ^ (α - 2 * m) := by
  have hs : 1 - 2 * (m : ℝ) < (-(α : ℂ)).re := by simp; linarith
  have hs1 : (-(α : ℂ)) ≠ 1 := fun h => hα (by
    have := congrArg re h; simp at this; linarith)
  have hpoch : ∀ k : ℕ, (descPochhammer ℂ k).eval (-(-(α : ℂ))) =
      (((descPochhammer ℝ k).eval α : ℝ) : ℂ) := fun k => by
    simp [descPochhammer_eval_eq_prod_range]
  have hint_eq : ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! : ℂ) *
          (x : ℂ) ^ (-(-(α : ℂ)) - 2 * m) =
      ((∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) / (2 * m)! *
          x ^ (α - 2 * m) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [ofReal_mul, ofReal_cpow (zero_lt_one.trans hx).le]
    push_cast; congr 2; ring
  have hζ := riemannZeta_eq_eulerMaclaurin hm hs hs1
  have h1 : (1 : ℂ) / (-(α : ℂ) - 1) = ((-1 / (α + 1) : ℝ) : ℂ) := by
    have hne : (α : ℂ) + 1 ≠ 0 := by exact_mod_cast fun h : α + 1 = 0 => hα (by linarith)
    push_cast; field_simp; ring
  have hsum_eq : ∑ r ∈ Ico 1 m, (bernoulli (2 * r) / (2 * r)! : ℂ) *
        (descPochhammer ℂ (2 * r - 1)).eval (-(-(α : ℂ))) =
      ((∑ r ∈ Ico 1 m, (bernoulli (2 * r) : ℝ) / (2 * r)! *
        (descPochhammer ℝ (2 * r - 1)).eval α : ℝ) : ℂ) := by
    push_cast
    exact sum_congr rfl fun r _ => by rw [hpoch]
  have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
  rw [hζ, h1, hsum_eq, hpoch, hint_eq]
  simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, hhalf]

/-! ### Evaluation of `ζ'(-1)` and DLMF 2.10.6 -/

/-- Order-`4` Euler–Maclaurin expansion of `riemannZeta` near `s = -1`, factoring `(z + 1)` out of
`(descPochhammer ℂ 4).eval (-z)` so the remainder vanishes to first order at `z = -1`. -/
private theorem riemannZeta_eventuallyEq_near_neg_one :
    riemannZeta =ᶠ[𝓝 (-1 : ℂ)] fun z => 1 / (z - 1) + 1 / 2 + z / 12 +
      (z + 1) * (z * (z + 2) * (z + 3) * ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli 4 - bernoulliFun 4 (Int.fract x)) / (4 : ℕ)! : ℂ) *
          (x : ℂ) ^ (-z - 2 * (2 : ℕ))) := by
  filter_upwards [((isOpen_lt continuous_const continuous_re).inter
    isOpen_compl_singleton).mem_nhds
    ⟨(by norm_num : (1 - 2 * (2 : ℝ)) < (-1 : ℂ).re), (by norm_num : (-1 : ℂ) ≠ 1)⟩] with z hz
  have hsum : ∑ r ∈ Ico 1 2, (bernoulli (2 * r) / (2 * r)! : ℂ) *
      (descPochhammer ℂ (2 * r - 1)).eval (-z) = -z / 12 := by
    rw [Nat.Ico_succ_singleton]
    simp [descPochhammer_eval_eq_prod_range,
      bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two, Nat.factorial]
    ring
  have hpoch4 : (descPochhammer ℂ 4).eval (-z) = (z + 1) * (z * (z + 2) * (z + 3)) := by
    simp [descPochhammer_eval_eq_prod_range, Finset.prod_range_succ]; ring
  have h22 : 2 * 2 = 4 := rfl
  rw [riemannZeta_eq_eulerMaclaurin (m := 2) (by omega) hz.1 hz.2, hsum, h22, hpoch4]
  ring

/-- Integral representation of `deriv riemannZeta (-1)` from the order-`4` Euler–Maclaurin
formula:
`ζ'(-1) = -1/6 - 1/12 * ∫_1^∞ (B_4 - B_4({x})) * x ^ (-3 : ℤ) dx`. -/
theorem deriv_riemannZeta_neg_one :
    deriv riemannZeta (-1) = -1 / 6 - (1 / 12 : ℂ) *
      ∫ x in Set.Ioi (1 : ℝ),
        (((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-3 : ℤ) := by
  set G : ℂ → ℂ := fun z => z * (z + 2) * (z + 3) * ∫ x in Set.Ioi (1 : ℝ),
    ((bernoulli 4 - bernoulliFun 4 (Int.fract x)) / (4 : ℕ)! : ℂ) * (x : ℂ) ^ (-z - 2 * (2 : ℕ))
  -- Differentiate `1 / (z - 1) + 1 / 2 + z / 12 + (z + 1) * G z` at `z = -1`; the factor `z + 1`
  -- kills the derivative of `G`, leaving `G (-1)`.
  have hd1 : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-1 / 4) (-1) := by
    simpa [one_div] using
      (((hasDerivAt_id' (-1 : ℂ)).sub_const 1).fun_inv (by norm_num)).congr_deriv (by norm_num)
  have hd2 : HasDerivAt (fun z : ℂ => z / 12) (1 / 12) (-1) := by
    simpa using (hasDerivAt_id' (-1 : ℂ)).div_const (12 : ℂ)
  have hG_diff : DifferentiableAt ℂ G (-1) :=
    (((differentiableAt_id.mul (differentiableAt_id.add_const 2)).mul
      (differentiableAt_id.add_const 3)).mul
      (differentiableAt_tailIntegral (m := 2) (s := -1) (by norm_num)))
  have hdG : HasDerivAt (fun z : ℂ => (z + 1) * G z) (G (-1)) (-1) := by
    simpa using ((hasDerivAt_id' (-1 : ℂ)).add_const 1).fun_mul hG_diff.hasDerivAt
  rw [((((hd1.add (hasDerivAt_const (-1 : ℂ) (1 / 2))).add hd2).add hdG).congr_of_eventuallyEq
    riemannZeta_eventuallyEq_near_neg_one).deriv]
  -- Simplify the prefactor `(-1) * 1 * 2 / 4! = -1 / 12` inside `G (-1)`.
  have hG_val : G (-1) = -(1 / 12 : ℂ) * ∫ x in Set.Ioi (1 : ℝ),
      (((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-3 : ℤ) := by
    dsimp [G]
    have hc : (-1 : ℂ) * (-1 + 2) * (-1 + 3) = -2 := by norm_num
    rw [hc, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have hexp : (-(-1 : ℂ) - 2 * 2 : ℂ) = ((-3 : ℤ) : ℂ) := by norm_num
    have hfac4 : (4 : ℕ)! = 24 := by decide
    rw [hexp, cpow_intCast, hfac4]
    push_cast; ring
  rw [hG_val]; ring

/-- Real-part form of `deriv_riemannZeta_neg_one`:
`(deriv riemannZeta (-1)).re = -1/6 - 1/12 * ∫_1^∞ (B_4 - B_4({x})) * x ^ (-3 : ℤ) dx`. -/
theorem deriv_riemannZeta_neg_one_re :
    (deriv riemannZeta (-1)).re = -1 / 6 - (1 / 12 : ℝ) *
      ∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x)) * x ^ (-3 : ℤ) := by
  have hint : ∫ x in Set.Ioi (1 : ℝ),
        (((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x) : ℝ) : ℂ) * (x : ℂ) ^ (-3 : ℤ) =
      ((∫ x in Set.Ioi (1 : ℝ),
        ((bernoulli 4 : ℝ) - bernoulliFun 4 (Int.fract x)) * x ^ (-3 : ℤ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp
  have h := congrArg re deriv_riemannZeta_neg_one
  have h6 : (-1 / 6 : ℂ).re = (-1 / 6 : ℝ) := by norm_num
  have h12 : (1 / 12 : ℂ).re = (1 / 12 : ℝ) := by norm_num
  have h12i : (1 / 12 : ℂ).im = 0 := by norm_num
  rw [hint] at h
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, h6, h12, h12i, mul_zero, sub_zero] at h
  exact h

/-- Derivative at `z = 2` of the functional-equation prefactor
`z ↦ 2 * (2 * π) ^ (-z) * Gamma z * cos (π * z / 2)` from `riemannZeta_one_sub`. Since
`cos (π * z / 2)` has derivative `0` and value `-1` at `z = 2`, only the derivatives of
`2 * (2 * π) ^ (-z)` and `Gamma` contribute. -/
private theorem hasDerivAt_two_mul_two_pi_cpow_mul_Gamma_mul_cos_two :
    HasDerivAt (fun z : ℂ => 2 * (2 * π : ℂ) ^ (-z) * Gamma z * Complex.cos (π * z / 2))
      ((Real.eulerMascheroniConstant + Complex.log (2 * π) - 1) / (2 * π ^ 2)) 2 := by
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hexp : -(2 : ℂ) = ((-2 : ℤ) : ℂ) := by norm_num
  have hd_pow :
      HasDerivAt (fun z : ℂ => 2 * (2 * π : ℂ) ^ (-z))
        (-Complex.log (2 * π) / (2 * π ^ 2)) 2 := by
    refine (((hasDerivAt_neg' (2 : ℂ)).const_cpow (c := 2 * π) (Or.inl h2π)).const_mul
      2).congr_deriv ?_
    rw [hexp, cpow_intCast, zpow_neg, zpow_ofNat]; field_simp
  have hd_gam : HasDerivAt Gamma (1 - Real.eulerMascheroniConstant) 2 := by
    have h := Complex.hasDerivAt_Gamma_nat 1
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, harmonic_succ, zero_add,
      harmonic_zero, inv_one, Rat.cast_one] at h
    have hd_eq : (-Real.eulerMascheroniConstant : ℂ) + 1 = 1 - Real.eulerMascheroniConstant := by
      ring
    have h2_eq : (1 : ℂ) + 1 = 2 := by norm_num
    rwa [hd_eq, h2_eq] at h
  have hd_cos : HasDerivAt (fun z : ℂ => Complex.cos (π * z / 2)) 0 2 := by
    have hlin : HasDerivAt (fun z : ℂ => π * z / 2) (π / 2) 2 := by
      simpa using ((hasDerivAt_id' (2 : ℂ)).const_mul (π : ℂ)).div_const 2
    simpa [mul_div_cancel_right₀ (π : ℂ) two_ne_zero] using hlin.ccos
  have hval_pow : 2 * (2 * π : ℂ) ^ (-(2 : ℂ)) = 1 / (2 * π ^ 2) := by
    rw [hexp, cpow_intCast, zpow_neg, zpow_ofNat]; field_simp
  have hval_gam : Gamma (2 : ℂ) = 1 := by simp
  have hval_cos : Complex.cos (π * (2 : ℂ) / 2) = -1 := by
    rw [mul_div_cancel_right₀ (π : ℂ) two_ne_zero, Complex.cos_pi]
  refine ((hd_pow.fun_mul hd_gam).fun_mul hd_cos).congr_deriv ?_
  rw [hval_pow, hval_gam, hval_cos]
  field_simp; ring

/-- **Functional-equation evaluation of `1 / 12 - ζ'(-1)`** (DLMF 2.10.6, complex form):
`1 / 12 - deriv riemannZeta (-1) = (γ + log(2π)) / 12 - deriv riemannZeta 2 / (2π²)`. -/
theorem one_div_twelve_sub_deriv_riemannZeta_neg_one :
    1 / 12 - deriv riemannZeta (-1) =
      (Real.eulerMascheroniConstant + Complex.log (2 * π)) / 12 -
        deriv riemannZeta 2 / (2 * π ^ 2) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  -- Apply `riemannZeta_one_sub` on `1 < Re z` (a neighborhood of `z = 2`) and differentiate at `2`.
  have hev : (fun z : ℂ => riemannZeta (1 - z)) =ᶠ[𝓝 (2 : ℂ)]
      fun z => 2 * (2 * π) ^ (-z) * Gamma z * Complex.cos (π * z / 2) * riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact riemannZeta_one_sub
      (fun n h => by simp [h] at hz; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      (fun h => by simp [h] at hz)
  have hd_lhs : HasDerivAt (fun z : ℂ => riemannZeta (1 - z)) (-deriv riemannZeta (-1)) 2 := by
    have h := (differentiableAt_riemannZeta (s := 1 - (2 : ℂ)) (by norm_num)).hasDerivAt.comp
      (2 : ℂ) ((hasDerivAt_const (2 : ℂ) (1 : ℂ)).sub (hasDerivAt_id' 2))
    have h12 : (1 : ℂ) - 2 = -1 := by norm_num
    simpa [Function.comp_def, h12] using h
  have hval_pre : 2 * (2 * π : ℂ) ^ (-(2 : ℂ)) * Gamma 2 * Complex.cos (π * 2 / 2) =
      -1 / (2 * π ^ 2) := by
    have hexp : -(2 : ℂ) = ((-2 : ℤ) : ℂ) := by norm_num
    have hgam : Gamma (2 : ℂ) = 1 := by simp
    rw [hexp, cpow_intCast, zpow_neg, zpow_ofNat, hgam,
      mul_div_cancel_right₀ (π : ℂ) two_ne_zero, Complex.cos_pi]
    field_simp
  have hd_rhs := (hasDerivAt_two_mul_two_pi_cpow_mul_Gamma_mul_cos_two.fun_mul
    (differentiableAt_riemannZeta (by norm_num)).hasDerivAt).congr_of_eventuallyEq hev
  have heq := hd_lhs.unique hd_rhs
  rw [hval_pre, riemannZeta_two] at heq
  linear_combination (norm := (field_simp; ring)) heq

/-- **DLMF 2.10.6** (real form):
`1 / 12 - (deriv riemannZeta (-1)).re = (γ + log(2π)) / 12 - (deriv riemannZeta 2).re / (2π²)`. -/
theorem one_div_twelve_sub_deriv_riemannZeta_neg_one_re :
    1 / 12 - (deriv riemannZeta (-1)).re =
      (Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 -
        (deriv riemannZeta 2).re / (2 * π ^ 2) := by
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [← ofReal_ofNat, ← ofReal_mul, ofReal_log Real.two_pi_pos.le]
  have h := congrArg re one_div_twelve_sub_deriv_riemannZeta_neg_one
  have h12 : (1 / 12 : ℂ).re = (1 / 12 : ℝ) := by norm_num
  have hmid : (((Real.eulerMascheroniConstant : ℂ) + Complex.log (2 * π)) / 12).re =
      (Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 := by
    rw [hlog, ← ofReal_add, show (12 : ℂ) = ((12 : ℝ) : ℂ) by norm_num, div_ofReal_re, ofReal_re]
  have hlast : (deriv riemannZeta 2 / (2 * (π : ℂ) ^ 2)).re =
      (deriv riemannZeta 2).re / (2 * π ^ 2) := by
    rw [show (2 * (π : ℂ) ^ 2 : ℂ) = ((2 * π ^ 2 : ℝ) : ℂ) by push_cast; ring, div_ofReal_re]
  simp only [sub_re] at h
  linarith [h, h12, hmid, hlast]

end TauCeti
