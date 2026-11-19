/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.MellinTransform.UpperTail
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

## Main results

* `TauCeti.integrableOn_sawtooth_mul_cpow`: the tail integral converges absolutely.
* `TauCeti.norm_integral_sawtooth_mul_cpow_le`: its bound `a^(-σ)/(2σ)`.
* `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth`: the formula above for every `a > 0`.
* `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth_natCast` and
  `TauCeti.riemannZeta_eq_sum_add_integral_sawtooth_natCast_add_half`: its cases at an integer
  `a = N ≥ 1`, where `B₁({N}) = -1/2`, and at a half-integer `a = N + 1/2`, where `B₁({a}) = 0`.
* `TauCeti.riemannZeta_eq_one_add_inv_sub_integral_fract`: the case `a = 1`, written with the
  fractional part, `ζ(s) = 1 + (s - 1)⁻¹ - s ∫_1^∞ {x} x^(-s-1) dx`.

The proof applies the first-order Euler–Maclaurin formula with real endpoints to `x ↦ x^(-s)`
on `[a, b]`. This shows that the right side does not depend on `a`; for `1 < Re s` it tends to
`ζ(s)` along the integers `a = N → ∞`. Both sides are holomorphic on `0 < Re s` after
multiplication by `s - 1`, so the identity theorem extends the formula from `1 < Re s`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §2.1.
-/

public section

open Complex Filter MeasureTheory
open scoped Topology

namespace TauCeti

/-- The sawtooth `B₁({x})`, viewed in `ℂ`, has norm at most `1/2`. -/
private theorem norm_sawtooth_le (x : ℝ) : ‖(bernoulliFun 1 (Int.fract x) : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_real, Real.norm_eq_abs]
  exact abs_bernoulliFun_one_fract_le x

/-- The tail integral of the sawtooth `B₁({x}) = {x} - 1/2` against `x^(-s-1)` converges
absolutely on `(a, ∞)` for `a > 0` and `0 < Re s`. -/
theorem integrableOn_sawtooth_mul_cpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi a) :=
  integrableOn_mul_cpow_of_bound ha
    ((continuous_ofReal.comp (continuous_bernoulliFun 1)).measurable.comp
      measurable_fract).aestronglyMeasurable (fun x _ ↦ norm_sawtooth_le x) hs

/-- **The bound for the sawtooth tail.** For `a > 0` and `σ = Re s > 0`,
`‖∫_a^∞ B₁({x}) x^(-s-1) dx‖ ≤ a^(-σ)/(2σ)`, where `B₁({x}) = {x} - 1/2`. -/
theorem norm_integral_sawtooth_mul_cpow_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))‖ ≤
      a ^ (-s.re) / (2 * s.re) :=
  (norm_integral_mul_cpow_le_of_bound ha (fun x _ ↦ norm_sawtooth_le x) hs).trans_eq (by ring)

/-- The right side of the Euler–Maclaurin formula for `ζ(s)` cut at `a`. -/
private noncomputable def zetaSawtooth (a : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) + (a : ℂ) ^ (1 - s) / (s - 1) +
    bernoulliFun 1 (Int.fract a) * (a : ℂ) ^ (-s) -
    s * ∫ x in Set.Ioi a, (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))

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
  unfold zetaSawtooth
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
    simp only [zetaSawtooth, Nat.floor_natCast]
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact zetaSawtooth_eq_of_le one_pos (by exact_mod_cast hN) hs₀ hs₁

/-- The right side of the formula cut at `1`, where the sum is `1` and `B₁({1}) = -1/2`. -/
private theorem zetaSawtooth_one_eq (z : ℂ) :
    zetaSawtooth 1 z = 1 + 1 / (z - 1) - 1 / 2 -
      z * ∫ x in Set.Ioi (1 : ℝ), (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(z + 1)) := by
  simp only [zetaSawtooth, Nat.floor_one, Finset.Icc_self, Finset.sum_singleton,
    Nat.cast_one, ofReal_one, one_cpow, Int.fract_one, bernoulliFun_one]
  push_cast
  ring

/-- On `0 < Re s`, `s ≠ 1`, the right side of the formula cut at `1` is `ζ(s)`, by the identity
theorem applied to its product with `s - 1`. -/
private theorem zetaSawtooth_one {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    zetaSawtooth 1 s = riemannZeta s := by
  set I : ℂ → ℂ := fun z ↦
    ∫ x in Set.Ioi (1 : ℝ), (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(z + 1))
  have hone (z : ℂ) : zetaSawtooth 1 z = 1 + 1 / (z - 1) - 1 / 2 - z * I z :=
    zetaSawtooth_one_eq z
  have hO : (fun x : ℝ ↦ (bernoulliFun 1 (Int.fract x) : ℂ)) =O[atTop]
      fun x : ℝ ↦ x ^ (0 : ℝ) :=
    Asymptotics.IsBigO.of_bound (1 / 2) (Eventually.of_forall fun x ↦ by
      rw [Real.rpow_zero, norm_one, mul_one]
      exact norm_sawtooth_le x)
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hI : DifferentiableOn ℂ I {z : ℂ | 0 < z.re} :=
    differentiableOn_integral_mul_cpow_of_isBigO hO
  have hH : AnalyticOnNhd ℂ (fun z ↦ 1 + (z - 1) * (1 / 2 - z * I z)) {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (by fun_prop) hopen
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  have hcancel {z : ℂ} (hz : z ≠ 1) :
      1 + (z - 1) * (1 / 2 - z * I z) = (z - 1) * zetaSawtooth 1 z := by
    rw [hone]
    field_simp [sub_ne_zero.mpr hz]
    ring
  have heq : (fun z ↦ 1 + (z - 1) * (1 / 2 - z * I z)) =ᶠ[𝓝 2] riemannZeta₁ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz₁ : z ≠ 1 := fun h ↦ by simp [h] at hz
    rw [hcancel hz₁, zetaSawtooth_one_of_one_lt_re hz, riemannZeta_eq_inv_sub_mul hz₁]
    field_simp [sub_ne_zero.mpr hz₁]
  have h := hH.eqOn_of_preconnected_of_eventuallyEq hZ (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq hs
  beta_reduce at h
  rw [hcancel hs₁] at h
  rw [riemannZeta_eq_inv_sub_mul hs₁, ← h]
  field_simp [sub_ne_zero.mpr hs₁]

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
  rw [← zetaSawtooth_one hs hs₁, ← h, zetaSawtooth]

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
  have hfloor : ⌊(N : ℝ) + 1 / 2⌋₊ = N :=
    Nat.floor_eq_iff (by positivity) |>.mpr ⟨by linarith, by linarith⟩
  have hfract : Int.fract ((N : ℝ) + 1 / 2) = 1 / 2 := by
    rw [add_comm, Int.fract_add_natCast, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  rw [riemannZeta_eq_sum_add_integral_sawtooth (a := (N : ℝ) + 1 / 2) (by positivity) hs hs₁,
    hfloor, hfract, bernoulliFun_one]
  push_cast
  ring

/-- The Euler–Maclaurin formula for `ζ(s)` cut at `1`, written with the fractional part:
`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_1^∞ {x} x^(-s-1) dx` for `0 < Re s`, `s ≠ 1`, the integral
converging absolutely. -/
theorem riemannZeta_eq_one_add_inv_sub_integral_fract {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s = 1 + (s - 1)⁻¹ -
      s * ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hpow : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hs) one_pos
  have hsplit : ∫ x in Set.Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      (∫ x in Set.Ioi (1 : ℝ), (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1))) +
        1 / 2 * ∫ x in Set.Ioi (1 : ℝ), (x : ℂ) ^ (-(s + 1)) := by
    rw [← integral_const_mul, ← integral_add (integrableOn_sawtooth_mul_cpow one_pos hs)
      (hpow.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    rw [bernoulliFun_one]
    push_cast
    ring
  have hexp : -(s + 1) + 1 = -s := by ring
  rw [hsplit, integral_Ioi_cpow_of_lt (by simpa using hs) one_pos, hexp,
    ← zetaSawtooth_one hs hs₁, zetaSawtooth_one_eq]
  generalize ∫ x in Set.Ioi (1 : ℝ),
    (bernoulliFun 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + 1)) = J
  rw [ofReal_one, one_cpow]
  field_simp
  ring

end TauCeti
