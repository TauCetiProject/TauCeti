/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeriesComplex
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.MellinTransform.Sawtooth
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The continuation of `ζ` by the first-order Euler–Maclaurin formula

Write `B₁({x}) = {x} - 1/2` for the sawtooth function, the periodic Bernoulli function
`bernoulliFun 1 (Int.fract x)`. For real `a > 0` and complex `s` with `0 < Re s` and `s ≠ 1`,
the Riemann zeta function is
`ζ(s) = ∑_{1 ≤ n ≤ a} n^(-s) + a^(1-s)/(s - 1) + B₁({a}) a^(-s) - s ∫_a^∞ B₁({x}) x^(-s-1) dx`,
the integral converging absolutely with `|∫_a^∞ B₁({x}) x^(-s-1) dx| ≤ a^(-σ)/(2σ)`, `σ = Re s`.

This is the classical continuation of `ζ` to the half-plane `0 < Re s` and the starting point of
explicit bounds for `ζ` in the critical strip: the finite sum is the main term, `a^(1-s)/(s - 1)`
carries the pole, and the tail integral is controlled by the bound above. The point `a` is free,
so the length of the sum can be chosen according to the height `Im s`.

The absolute convergence of the tail integral and its bound are
`TauCeti.integrableOn_sawtooth_mul_cpow` and `TauCeti.norm_integral_sawtooth_mul_cpow_le` in
`TauCeti.Analysis.MellinTransform.Sawtooth`.

## Main results

* `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth`: the formula above for every `a > 0`.
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

The proof applies the first-order Euler–Maclaurin formula with real endpoints to `x ↦ x^(-s)`
on `[a, b]`. This shows that the right side does not depend on `a`; for `1 < Re s` it tends to
`ζ(s)` along the integers `a = N → ∞`. At `a = 1`, after subtracting the pole `(s - 1)⁻¹`, both
sides are holomorphic on `0 < Re s`, so the identity theorem extends the formula for `riemannZeta₀`
from `1 < Re s`; restoring the pole gives the formula for `ζ` at every cut point.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §2.1.
-/

public section

open Complex Filter MeasureTheory
open scoped Topology

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

end TauCeti
