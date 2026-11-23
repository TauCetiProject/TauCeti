/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.MellinTransform.UpperTail
import TauCeti.Analysis.SpecialFunctions.Integrals.MellinWeight
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin

/-!
# Right-half-plane integral representation and bounds for `riemannZeta`

On `Re s > 0`, `s ≠ 1`, the first-order Euler–Maclaurin formula cut at `1` expresses the Riemann
zeta function as

`ζ(s) = s / (s - 1) - s ∫₁^∞ {t} t^{-(s + 1)} dt`,

where `{t} = t - ⌊t⌋₊ ∈ [0, 1)` is the fractional part of `t`. Subtracting `(s - 1)⁻¹` gives

`riemannZeta₀ s = 1 - s ∫₁^∞ {t} t^{-(s + 1)} dt`

on all of `Re s > 0`. Both come from the sawtooth formula
`TauCeti.riemannZeta₀_eq_one_half_sub_integral_sawtooth` by writing `{t} = B₁({t}) + 1/2`.
Bounding `|{t}| ≤ 1` in the integral immediately gives the explicit vertical-line growth bounds

`‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`   and   `‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s`

for all `Re s > 0` (including at `s = 1`, where Mathlib's junk value `(γ - log(4π)) / 2` has norm
strictly less than `2`).

The first-order Euler–Maclaurin formula of
`TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin`, whose sawtooth kernel
`B₁({t}) = {t} - 1/2` is bounded by `1/2`, sharpens these. Its tail bound gives the truncation
error `‖s‖ a^(-Re s)/(2 Re s)` at every cut point `a > 0`, and at `a = 1` the bound
`‖riemannZeta₀ s - 1/2‖ ≤ ‖s‖/(2 Re s)`. Hence `‖ζ(z)‖ ≤ 1/2 + 1/‖z - 1‖ + ‖z‖/(2 Re z)`, which
on the discs `‖z - (3/2 + it)‖ ≤ 1` with `|t| ≥ 2` is at most `4 + |t|`: the input that
Borel–Carathéodory arguments near the line `Re s = 1` take. On the real axis, the fractional-part
formula and `0 ≤ {t} < 1` give `1/(σ - 1) < ζ(σ) < 1 + 1/(σ - 1)` for real `σ > 0`, `σ ≠ 1`.

## Main results

* `TauCeti.riemannZeta₀_eq_one_sub_mul_integral`: the fractional-part integral formula for
  `riemannZeta₀` on `Re s > 0`.
* `TauCeti.riemannZeta_eq_div_sub_mul_integral`: `ζ(s) = s / (s - 1) - s ∫₁^∞ {t} t^{-(s + 1)} dt`
  for `Re s > 0` and `s ≠ 1`.
* `TauCeti.norm_riemannZeta₀_le_one_add_norm_div_re`: `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s` on
  `Re s > 0`.
* `TauCeti.norm_riemannZeta_le_of_re_pos`: `‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s` on
  `Re s > 0`.
* `TauCeti.norm_riemannZeta_sub_sum_sawtooth_le`, with its cases
  `TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_le` and
  `TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_add_half_le`: the truncation error of the
  first-order Euler–Maclaurin formula at a cut point `a > 0`, an integer and a half-integer.
* `TauCeti.norm_riemannZeta₀_sub_one_half_le`: `‖riemannZeta₀ s - 1/2‖ ≤ ‖s‖/(2 Re s)` on
  `Re s > 0`.
* `TauCeti.norm_riemannZeta_le_one_half_add_inv_add_div`,
  `TauCeti.norm_riemannZeta_le_three_halves_add_norm` and `TauCeti.norm_riemannZeta_le_linear`:
  linear bounds in the right half-plane and on the discs about `3/2 + it`.
* `TauCeti.one_div_sub_one_lt_riemannZeta_re`, `TauCeti.riemannZeta_re_lt_one_add_one_div_sub_one`
  and `TauCeti.norm_riemannZeta_lt_one_add_one_div_sub_one`: `1/(σ - 1) < ζ(σ) < 1 + 1/(σ - 1)`
  for real `σ > 0`, `σ ≠ 1`, and `‖ζ(s)‖ < 1 + 1/(Re s - 1)` on `Re s > 1`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1, eq. (2.1.4).
* H. Davenport, *Multiplicative Number Theory*, Ch. 12 and Ch. 21.
-/

public section

open Complex Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace TauCeti

/-- **Fractional-part integral representation of `riemannZeta₀`.** For every `s` with `Re s > 0`,
`riemannZeta₀ s = 1 - s * ∫_{t > 1} (t - ⌊t⌋₊) t^{-(s + 1)} dt`. -/
theorem riemannZeta₀_eq_one_sub_mul_integral {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s =
      1 - s * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hfract : ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ by
      rw [Int.fract, natCast_floor_eq_intCast_floor (by linarith : (0 : ℝ) ≤ t)]
  rw [hfract, integral_fract_mul_cpow_eq_integral_sawtooth_add one_pos hs, ofReal_one, one_cpow,
    riemannZeta₀_eq_one_half_sub_integral_sawtooth hs]
  field_simp
  ring

/-- **Fractional-part integral representation of `riemannZeta`.** For `Re s > 0` and `s ≠ 1`,
`ζ(s) = s / (s - 1) - s * ∫_{t > 1} (t - ⌊t⌋₊) t^{-(s + 1)} dt`. -/
theorem riemannZeta_eq_div_sub_mul_integral {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s =
      s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_inv_sub_add hs1, riemannZeta₀_eq_one_sub_mul_integral hs]
  field_simp [sub_ne_zero.mpr hs1]
  ring

/-- On the open right half-plane `Re s > 0`, `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`. -/
theorem norm_riemannZeta₀_le_one_add_norm_div_re {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  rw [riemannZeta₀_eq_one_sub_mul_integral hs]
  have hint_bound : ‖∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
      1 / s.re :=
    (norm_integral_mul_cpow_le_of_bound one_pos (fun t (ht : 1 < t) ↦ by
      simpa only [norm_real, Real.norm_eq_abs] using
        Nat.abs_sub_floor_le (zero_lt_one.trans ht).le) hs).trans_eq
      (by rw [Real.one_rpow, one_mul])
  calc ‖1 - s * ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖(1 : ℂ)‖ + ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ :=
        (norm_sub_le _ _).trans (by rw [norm_mul])
    _ ≤ 1 + ‖s‖ * (1 / s.re) := by
        rw [norm_one]
        exact add_le_add_right (mul_le_mul_of_nonneg_left hint_bound (norm_nonneg s)) 1
    _ = 1 + ‖s‖ / s.re := by ring

/-- **Explicit vertical growth bound for `riemannZeta` on `Re s > 0`.** For every `s` with
`Re s > 0` (including `s = 1`, where `(1 - 1)⁻¹ = 0`),
`‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s`. -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have hval : riemannZeta 1 = ((Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 : ℝ) := by
      rw [riemannZeta_one, ofReal_div, ofReal_sub, ofReal_log (by positivity : (0 : ℝ) ≤ 4 * π)]
      norm_cast
    have hlog_pos : 0 < Real.log (4 * π) :=
      Real.log_pos (by linarith [Real.two_le_pi])
    have hlog_lt : Real.log (4 * π) < 4 := by
      rw [Real.log_lt_iff_lt_exp (by positivity)]
      have h2e : (2 : ℝ) < Real.exp 1 := by
        linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
      have h16 : (16 : ℝ) < Real.exp 4 := by
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ < Real.exp 1 ^ 4 := pow_lt_pow_left₀ h2e (by norm_num) (by norm_num)
          _ = Real.exp 4 := by rw [← Real.exp_natCast_mul]; norm_num
      linarith [Real.pi_lt_four]
    rw [hval, norm_real, Real.norm_eq_abs]
    simp only [sub_self, norm_zero, inv_zero, zero_add, norm_one, one_re, div_one]
    rw [abs_le]
    have hγ₁ := Real.one_half_lt_eulerMascheroniConstant
    have hγ₂ := Real.eulerMascheroniConstant_lt_two_thirds
    constructor <;> linarith
  · rw [riemannZeta_eq_inv_sub_add hs1]
    calc ‖(s - 1)⁻¹ + riemannZeta₀ s‖
        ≤ ‖(s - 1)⁻¹‖ + ‖riemannZeta₀ s‖ := norm_add_le _ _
      _ ≤ ‖s - 1‖⁻¹ + (1 + ‖s‖ / s.re) := by
          rw [norm_inv]
          exact add_le_add_right (norm_riemannZeta₀_le_one_add_norm_div_re hs) _
      _ = ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re := by ring

/-! ### Truncation bounds from the first-order Euler–Maclaurin formula -/

/-- **The truncation error of the first-order Euler–Maclaurin formula.** For real `a > 0` and
`0 < Re s`, `s ≠ 1`, `ζ(s)` differs from `∑_{1 ≤ n ≤ a} n^(-s) + a^(1-s)/(s - 1) + B₁({a}) a^(-s)`
by at most `‖s‖ a^(-Re s)/(2 Re s)`, where `B₁({x}) = {x} - 1/2` is the sawtooth. -/
theorem norm_riemannZeta_sub_sum_sawtooth_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re)
    (hs₁ : s ≠ 1) :
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s) + (a : ℂ) ^ (1 - s) / (s - 1) +
      bernoulliFun 1 (Int.fract a) * (a : ℂ) ^ (-s))‖ ≤ ‖s‖ * a ^ (-s.re) / (2 * s.re) := by
  rw [riemannZeta_eq_sum_add_integral_sawtooth ha hs hs₁, sub_sub_cancel_left, norm_neg, norm_mul,
    mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_integral_sawtooth_mul_cpow_le ha hs) (norm_nonneg s)

/-- The truncation bound at an integer `N ≥ 1`, where `B₁({N}) = -1/2`:
`‖ζ(s) - (∑_{n ≤ N} n^(-s) + N^(1-s)/(s - 1) - N^(-s)/2)‖ ≤ ‖s‖ N^(-Re s)/(2 Re s)`
for `0 < Re s`, `s ≠ 1`. -/
theorem norm_riemannZeta_sub_sum_sawtooth_natCast_le {N : ℕ} (hN : N ≠ 0) {s : ℂ}
    (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1) -
      (N : ℂ) ^ (-s) / 2)‖ ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / (2 * s.re) := by
  have h := norm_riemannZeta_sub_sum_sawtooth_le (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)) hs hs₁
  rw [Nat.floor_natCast, Int.fract_natCast, bernoulliFun_one, ofReal_natCast] at h
  convert h using 4
  push_cast
  ring

/-- The truncation bound at a half-integer `N + 1/2`, where `B₁({N + 1/2}) = 0`:
`‖ζ(s) - (∑_{n ≤ N} n^(-s) + (N + 1/2)^(1-s)/(s - 1))‖ ≤ ‖s‖ (N + 1/2)^(-Re s)/(2 Re s)`
for `0 < Re s`, `s ≠ 1`. -/
theorem norm_riemannZeta_sub_sum_sawtooth_natCast_add_half_le (N : ℕ) {s : ℂ} (hs : 0 < s.re)
    (hs₁ : s ≠ 1) :
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) +
      ((N : ℂ) + 1 / 2) ^ (1 - s) / (s - 1))‖ ≤
      ‖s‖ * ((N : ℝ) + 1 / 2) ^ (-s.re) / (2 * s.re) := by
  have hfloor : ⌊(N : ℝ) + 1 / 2⌋₊ = N :=
    Nat.floor_eq_iff (by positivity) |>.mpr ⟨by linarith, by linarith⟩
  have hfract : Int.fract ((N : ℝ) + 1 / 2) = 1 / 2 := by
    rw [add_comm, Int.fract_add_natCast, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  have hcast : (((N : ℝ) + 1 / 2 : ℝ) : ℂ) = (N : ℂ) + 1 / 2 := by push_cast; ring
  have h := norm_riemannZeta_sub_sum_sawtooth_le (a := (N : ℝ) + 1 / 2) (by positivity) hs hs₁
  rwa [hfloor, hfract, bernoulliFun_one, sub_self, ofReal_zero, zero_mul, add_zero, hcast] at h

/-- On `Re s > 0`, including `s = 1`, `‖riemannZeta₀ s - 1/2‖ ≤ ‖s‖/(2 Re s)`, from the
sawtooth formula `riemannZeta₀ s = 1/2 - s ∫_1^∞ B₁({x}) x^(-s-1) dx`. -/
theorem norm_riemannZeta₀_sub_one_half_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s - 1 / 2‖ ≤ ‖s‖ / (2 * s.re) := by
  rw [riemannZeta₀_eq_one_half_sub_integral_sawtooth hs, sub_sub_cancel_left, norm_neg, norm_mul]
  have hI := norm_integral_sawtooth_mul_cpow_le one_pos hs
  rw [Real.one_rpow] at hI
  calc _ ≤ ‖s‖ * (1 / (2 * s.re)) := mul_le_mul_of_nonneg_left hI (norm_nonneg s)
    _ = ‖s‖ / (2 * s.re) := by ring

/-! ### Linear bounds in the right half-plane -/

/-- **A linear bound in the right half-plane.** For `0 < Re z` and `z ≠ 1`,
`‖ζ(z)‖ ≤ 1/2 + 1/‖z - 1‖ + ‖z‖/(2 Re z)`. -/
theorem norm_riemannZeta_le_one_half_add_inv_add_div {z : ℂ} (hz : 0 < z.re) (hz₁ : z ≠ 1) :
    ‖riemannZeta z‖ ≤ 1 / 2 + 1 / ‖z - 1‖ + ‖z‖ / (2 * z.re) := by
  have hdecomp : riemannZeta z = (1 / 2 : ℂ) + (z - 1)⁻¹ + (riemannZeta₀ z - 1 / 2) := by
    rw [riemannZeta_eq_inv_sub_add hz₁]
    ring
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hinv : ‖(z - 1)⁻¹‖ = 1 / ‖z - 1‖ := by rw [norm_inv, one_div]
  rw [hdecomp]
  have htri1 := norm_add_le ((1 / 2 : ℂ) + (z - 1)⁻¹) (riemannZeta₀ z - 1 / 2)
  have htri2 := norm_add_le (1 / 2 : ℂ) (z - 1)⁻¹
  linarith [norm_riemannZeta₀_sub_one_half_le hz]

/-- For `1/2 ≤ Re z` and `1 ≤ ‖z - 1‖`, `‖ζ(z)‖ ≤ 3/2 + ‖z‖`. -/
theorem norm_riemannZeta_le_three_halves_add_norm {z : ℂ} (hre : 1 / 2 ≤ z.re)
    (hpole : 1 ≤ ‖z - 1‖) :
    ‖riemannZeta z‖ ≤ 3 / 2 + ‖z‖ := by
  have hz₁ : z ≠ 1 := fun h ↦ by
    rw [h, sub_self, norm_zero] at hpole
    linarith
  have hinv : 1 / ‖z - 1‖ ≤ 1 := div_le_one_of_le₀ hpole (norm_nonneg _)
  have hdiv : ‖z‖ / (2 * z.re) ≤ ‖z‖ := div_le_self (norm_nonneg z) (by linarith)
  linarith [norm_riemannZeta_le_one_half_add_inv_add_div (by linarith) hz₁]

/-- **A linear bound on the discs about `3/2 + it`.** For real `t` with `2 ≤ |t|` and
`z ∈ Metric.closedBall (3/2 + it) 1`, `‖ζ(z)‖ ≤ 4 + |t|`. -/
theorem norm_riemannZeta_le_linear {t : ℝ} (ht : 2 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.closedBall (3 / 2 + t * I) 1) :
    ‖riemannZeta z‖ ≤ 4 + |t| := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  set w : ℂ := z - (3 / 2 + t * I)
  have hzw : z = w + 3 / 2 + t * I := by simp only [w]; ring
  have hw_re : |w.re| ≤ 1 := (abs_re_le_norm w).trans hz
  have hw_im : |w.im| ≤ 1 := (abs_im_le_norm w).trans hz
  have hz_re : 1 / 2 ≤ z.re := by
    have hre_eq : z.re = w.re + 3 / 2 := by rw [hzw]; simp
    linarith [(abs_le.mp hw_re).1]
  have hpole : 1 ≤ ‖z - 1‖ := by
    have him_eq : (z - 1).im = w.im + t := by rw [hzw]; simp
    have htri : |t| - |w.im| ≤ |w.im + t| := by
      simpa only [abs_neg, sub_neg_eq_add, add_comm t] using abs_sub_abs_le_abs_sub t (-w.im)
    have := abs_im_le_norm (z - 1)
    rw [him_eq] at this
    linarith
  have hnorm : ‖z‖ ≤ 5 / 2 + |t| := by
    have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    have htI : ‖(t : ℂ) * I‖ = |t| := by simp [norm_real]
    have htri1 := norm_add_le (w + 3 / 2) ((t : ℂ) * I)
    have htri2 := norm_add_le w (3 / 2 : ℂ)
    rw [hzw]
    linarith
  linarith [norm_riemannZeta_le_three_halves_add_norm hz_re hpole]

/-! ### Comparison with `1/(σ - 1)` on the real axis -/

/-- The real form of `TauCeti.riemannZeta_eq_div_sub_mul_integral` at real `σ > 0`, `σ ≠ 1`. -/
private theorem riemannZeta_re_eq_div_sub_mul_integral {σ : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≠ 1) :
    (riemannZeta σ).re = σ / (σ - 1) - σ * ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * (t - ⌊t⌋₊) := by
  have h := riemannZeta_eq_div_sub_mul_integral (s := σ) (by simpa using hσ)
    (by exact_mod_cast hσ₁)
  have hI : ∫ t in Set.Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-((σ : ℂ) + 1)) =
      ((∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * (t - ⌊t⌋₊) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
    rw [show -((σ : ℂ) + 1) = ((-1 - σ : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by linarith : (0 : ℝ) ≤ t), ← ofReal_mul, mul_comm]
  rw [hI] at h
  have h' : riemannZeta σ = ((σ / (σ - 1) - σ *
      ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * (t - ⌊t⌋₊) : ℝ) : ℂ) := by
    rw [h]
    push_cast
    rfl
  rw [h', ofReal_re]

/-- **The lower bound by the pole.** For real `σ > 0`, `σ ≠ 1`, `1/(σ - 1) < Re ζ(σ)`. -/
theorem one_div_sub_one_lt_riemannZeta_re {σ : ℝ} (hσ0 : 0 < σ) (hσ₁ : σ ≠ 1) :
    1 / (σ - 1) < (riemannZeta σ).re := by
  have hint_f := integrableOn_rpow_mul_sub_natFloor hσ0
  have hint_r : IntegrableOn (fun t : ℝ ↦ t ^ (-1 - σ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hpos : 0 < ∫ t in Set.Ioi (1 : ℝ), (t ^ (-1 - σ) - t ^ (-1 - σ) * (t - ⌊t⌋₊)) := by
    refine setIntegral_pos_of_ae_pos (by simp) (hint_r.sub hint_f) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
    have hlt : t - ⌊t⌋₊ < 1 := by linarith [Nat.lt_floor_add_one t]
    have hp : 0 < t ^ (-1 - σ) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  have hr : ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) = 1 / σ := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -1 - σ + 1 = -σ by ring, neg_div_neg_eq]
  rw [integral_sub hint_r hint_f, hr] at hpos
  have hmul : σ * ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * (t - ⌊t⌋₊) < 1 := by
    have := mul_lt_mul_of_pos_left hpos hσ0
    rw [mul_sub, mul_one_div_cancel hσ0.ne'] at this
    linarith
  have halg : σ / (σ - 1) = 1 / (σ - 1) + 1 := by
    field_simp [sub_ne_zero.mpr hσ₁]
    ring
  rw [riemannZeta_re_eq_div_sub_mul_integral hσ0 hσ₁, halg]
  linarith

/-- **The upper bound by the pole.** For real `σ > 0`, `σ ≠ 1`, `Re ζ(σ) < 1 + 1/(σ - 1)`. -/
theorem riemannZeta_re_lt_one_add_one_div_sub_one {σ : ℝ} (hσ0 : 0 < σ) (hσ₁ : σ ≠ 1) :
    (riemannZeta σ).re < 1 + 1 / (σ - 1) := by
  have hint := integrableOn_rpow_mul_sub_natFloor hσ0
  have hIoo : 0 < ∫ t in Set.Ioo (1 : ℝ) 2, t ^ (-1 - σ) * (t - ⌊t⌋₊) := by
    refine setIntegral_pos_of_ae_pos (by simp) (hint.mono_set Set.Ioo_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ⟨ht1, ht2⟩
    have hfl : ⌊t⌋₊ = 1 := Nat.floor_eq_iff (by linarith) |>.mpr ⟨by simpa using ht1.le, by
      norm_num; linarith⟩
    rw [hfl, Nat.cast_one]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)
  have hpos : 0 < ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * (t - ⌊t⌋₊) :=
    hIoo.trans_le (setIntegral_mono_set hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) ↦
        mul_nonneg (Real.rpow_nonneg (by linarith) _)
          (by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ t)]))
      Set.Ioo_subset_Ioi_self.eventuallySubset)
  have halg : σ / (σ - 1) = 1 + 1 / (σ - 1) := by
    field_simp [sub_ne_zero.mpr hσ₁]
    ring
  rw [riemannZeta_re_eq_div_sub_mul_integral hσ0 hσ₁, halg]
  linarith [mul_pos hσ0 hpos]

/-- On `1 < Re s`, `‖ζ(s)‖ < 1 + 1/(Re s - 1)`. -/
theorem norm_riemannZeta_lt_one_add_one_div_sub_one {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ < 1 + 1 / (s.re - 1) :=
  (norm_riemannZeta_le hs).trans_lt
    (riemannZeta_re_lt_one_add_one_div_sub_one (zero_lt_one.trans hs) (by linarith : s.re ≠ 1))

end TauCeti
